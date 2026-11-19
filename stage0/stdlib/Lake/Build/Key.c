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
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object* v_x_222_, lean_object* v_x_223_){
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
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey_decEq___boxed(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_253_, v_x_254_);
lean_dec_ref(v_x_254_);
lean_dec_ref(v_x_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_257_, v_x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Lake_instDecidableEqBuildKey(v_x_260_, v_x_261_);
lean_dec_ref(v_x_261_);
lean_dec_ref(v_x_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashableBuildKey_hash(lean_object* v_x_264_){
_start:
{
switch(lean_obj_tag(v_x_264_))
{
case 0:
{
lean_object* v_module_265_; uint64_t v___x_266_; 
v_module_265_ = lean_ctor_get(v_x_264_, 0);
v___x_266_ = 0ULL;
if (lean_obj_tag(v_module_265_) == 0)
{
uint64_t v___x_267_; 
v___x_267_ = 8934034000889494153ULL;
return v___x_267_;
}
else
{
uint64_t v_hash_268_; uint64_t v___x_269_; 
v_hash_268_ = lean_ctor_get_uint64(v_module_265_, sizeof(void*)*2);
v___x_269_ = lean_uint64_mix_hash(v___x_266_, v_hash_268_);
return v___x_269_;
}
}
case 1:
{
lean_object* v_package_270_; uint64_t v___x_271_; 
v_package_270_ = lean_ctor_get(v_x_264_, 0);
v___x_271_ = 1ULL;
if (lean_obj_tag(v_package_270_) == 0)
{
uint64_t v___x_272_; 
v___x_272_ = 13067028307566252276ULL;
return v___x_272_;
}
else
{
uint64_t v_hash_273_; uint64_t v___x_274_; 
v_hash_273_ = lean_ctor_get_uint64(v_package_270_, sizeof(void*)*2);
v___x_274_ = lean_uint64_mix_hash(v___x_271_, v_hash_273_);
return v___x_274_;
}
}
case 2:
{
lean_object* v_package_275_; lean_object* v_module_276_; uint64_t v___x_277_; uint64_t v___y_279_; 
v_package_275_ = lean_ctor_get(v_x_264_, 0);
v_module_276_ = lean_ctor_get(v_x_264_, 1);
v___x_277_ = 2ULL;
if (lean_obj_tag(v_package_275_) == 0)
{
uint64_t v___x_285_; 
v___x_285_ = 1723ULL;
v___y_279_ = v___x_285_;
goto v___jp_278_;
}
else
{
uint64_t v_hash_286_; 
v_hash_286_ = lean_ctor_get_uint64(v_package_275_, sizeof(void*)*2);
v___y_279_ = v_hash_286_;
goto v___jp_278_;
}
v___jp_278_:
{
uint64_t v___x_280_; 
v___x_280_ = lean_uint64_mix_hash(v___x_277_, v___y_279_);
if (lean_obj_tag(v_module_276_) == 0)
{
uint64_t v___x_281_; uint64_t v___x_282_; 
v___x_281_ = 1723ULL;
v___x_282_ = lean_uint64_mix_hash(v___x_280_, v___x_281_);
return v___x_282_;
}
else
{
uint64_t v_hash_283_; uint64_t v___x_284_; 
v_hash_283_ = lean_ctor_get_uint64(v_module_276_, sizeof(void*)*2);
v___x_284_ = lean_uint64_mix_hash(v___x_280_, v_hash_283_);
return v___x_284_;
}
}
}
case 3:
{
lean_object* v_package_287_; lean_object* v_target_288_; uint64_t v___x_289_; uint64_t v___y_291_; 
v_package_287_ = lean_ctor_get(v_x_264_, 0);
v_target_288_ = lean_ctor_get(v_x_264_, 1);
v___x_289_ = 3ULL;
if (lean_obj_tag(v_package_287_) == 0)
{
uint64_t v___x_297_; 
v___x_297_ = 1723ULL;
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
if (lean_obj_tag(v_target_288_) == 0)
{
uint64_t v___x_293_; uint64_t v___x_294_; 
v___x_293_ = 1723ULL;
v___x_294_ = lean_uint64_mix_hash(v___x_292_, v___x_293_);
return v___x_294_;
}
else
{
uint64_t v_hash_295_; uint64_t v___x_296_; 
v_hash_295_ = lean_ctor_get_uint64(v_target_288_, sizeof(void*)*2);
v___x_296_ = lean_uint64_mix_hash(v___x_292_, v_hash_295_);
return v___x_296_;
}
}
}
default: 
{
lean_object* v_target_299_; lean_object* v_facet_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; 
v_target_299_ = lean_ctor_get(v_x_264_, 0);
v_facet_300_ = lean_ctor_get(v_x_264_, 1);
v___x_301_ = 4ULL;
v___x_302_ = l_Lake_instHashableBuildKey_hash(v_target_299_);
v___x_303_ = lean_uint64_mix_hash(v___x_301_, v___x_302_);
if (lean_obj_tag(v_facet_300_) == 0)
{
uint64_t v___x_304_; uint64_t v___x_305_; 
v___x_304_ = 1723ULL;
v___x_305_ = lean_uint64_mix_hash(v___x_303_, v___x_304_);
return v___x_305_;
}
else
{
uint64_t v_hash_306_; uint64_t v___x_307_; 
v_hash_306_ = lean_ctor_get_uint64(v_facet_300_, sizeof(void*)*2);
v___x_307_ = lean_uint64_mix_hash(v___x_303_, v_hash_306_);
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object* v_x_308_){
_start:
{
uint64_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Lake_instHashableBuildKey_hash(v_x_308_);
lean_dec_ref(v_x_308_);
v_r_310_ = lean_box_uint64(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* v_key_313_){
_start:
{
lean_inc_ref(v_key_313_);
return v_key_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* v_key_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lake_PartialBuildKey_mk(v_key_314_);
lean_dec_ref(v_key_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(lean_object* v_x_318_, lean_object* v_prec_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lake_instReprBuildKey_repr(v_x_318_, v_prec_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(lean_object* v_x_321_, lean_object* v_prec_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(v_x_321_, v_prec_322_);
lean_dec(v_prec_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* v_pkg_334_, lean_object* v_target_335_){
_start:
{
lean_object* v_str_336_; lean_object* v_startInclusive_337_; lean_object* v_endExclusive_338_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_str_336_ = lean_ctor_get(v_target_335_, 0);
v_startInclusive_337_ = lean_ctor_get(v_target_335_, 1);
v_endExclusive_338_ = lean_ctor_get(v_target_335_, 2);
v___x_344_ = lean_nat_sub(v_endExclusive_338_, v_startInclusive_337_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_nat_dec_eq(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_dec_le(v___x_347_, v___x_344_);
lean_dec(v___x_344_);
if (v___x_348_ == 0)
{
goto v___jp_339_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_350_ = lean_string_memcmp(v_str_336_, v___x_349_, v_startInclusive_337_, v___x_345_, v___x_347_);
if (v___x_350_ == 0)
{
goto v___jp_339_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_target_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = l_String_Slice_Pos_nextn(v_target_335_, v___x_345_, v___x_347_);
v___x_352_ = lean_nat_add(v_startInclusive_337_, v___x_351_);
lean_dec(v___x_351_);
v___x_353_ = lean_string_utf8_extract_fast(v_str_336_, v___x_352_, v_endExclusive_338_);
lean_dec(v___x_352_);
v_target_354_ = l_Lake_stringToLegalOrSimpleName(v___x_353_);
v___x_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_355_, 0, v_pkg_334_);
lean_ctor_set(v___x_355_, 1, v_target_354_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
}
else
{
lean_object* v___x_357_; 
lean_dec(v___x_344_);
lean_dec(v_pkg_334_);
v___x_357_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2));
return v___x_357_;
}
v___jp_339_:
{
lean_object* v___x_340_; lean_object* v_target_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_340_ = lean_string_utf8_extract_fast(v_str_336_, v_startInclusive_337_, v_endExclusive_338_);
v_target_341_ = l_Lake_stringToLegalOrSimpleName(v___x_340_);
v___x_342_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_342_, 0, v_pkg_334_);
lean_ctor_set(v___x_342_, 1, v_target_341_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_358_, lean_object* v_target_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_358_, v_target_359_);
lean_dec_ref(v_target_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg(){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___boxed(lean_object* v___dummy_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
return v_res_366_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_370_);
lean_dec_ref(v_s_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v_a_375_, lean_object* v_b_376_){
_start:
{
lean_object* v_it_378_; lean_object* v_startInclusive_379_; lean_object* v_endExclusive_380_; 
if (lean_obj_tag(v_a_375_) == 0)
{
lean_object* v_currPos_384_; lean_object* v_searcher_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_408_; 
v_currPos_384_ = lean_ctor_get(v_a_375_, 0);
v_searcher_385_ = lean_ctor_get(v_a_375_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_a_375_);
if (v_isSharedCheck_408_ == 0)
{
v___x_387_ = v_a_375_;
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_searcher_385_);
lean_inc(v_currPos_384_);
lean_dec(v_a_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint8_t v_decide_389_; 
v_decide_389_ = lean_nat_dec_eq(v_searcher_385_, v___x_374_);
if (v_decide_389_ == 0)
{
uint32_t v___x_390_; uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_390_ = 47;
v___x_391_ = lean_string_utf8_get_fast(v_s_372_, v_searcher_385_);
v___x_392_ = lean_uint32_dec_eq(v___x_391_, v___x_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_string_utf8_next_fast(v_s_372_, v_searcher_385_);
lean_dec(v_searcher_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_393_);
v___x_395_ = v___x_387_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_currPos_384_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_397_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
v_a_375_ = v___x_395_;
goto _start;
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_slice_401_; lean_object* v_nextIt_403_; 
v___x_398_ = lean_string_utf8_next_fast(v_s_372_, v_searcher_385_);
v___x_399_ = lean_nat_sub(v___x_398_, v_searcher_385_);
v___x_400_ = lean_nat_add(v_searcher_385_, v___x_399_);
lean_dec(v___x_399_);
v_slice_401_ = l_String_Slice_subslice_x21(v___x_373_, v_currPos_384_, v_searcher_385_);
lean_inc(v___x_400_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_400_);
lean_ctor_set(v___x_387_, 0, v___x_400_);
v_nextIt_403_ = v___x_387_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_400_);
v_nextIt_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v_startInclusive_404_; lean_object* v_endExclusive_405_; 
v_startInclusive_404_ = lean_ctor_get(v_slice_401_, 0);
lean_inc(v_startInclusive_404_);
v_endExclusive_405_ = lean_ctor_get(v_slice_401_, 1);
lean_inc(v_endExclusive_405_);
lean_dec_ref(v_slice_401_);
v_it_378_ = v_nextIt_403_;
v_startInclusive_379_ = v_startInclusive_404_;
v_endExclusive_380_ = v_endExclusive_405_;
goto v___jp_377_;
}
}
}
else
{
lean_object* v___x_407_; 
lean_del_object(v___x_387_);
lean_dec(v_searcher_385_);
v___x_407_ = lean_box(1);
lean_inc(v___x_374_);
v_it_378_ = v___x_407_;
v_startInclusive_379_ = v_currPos_384_;
v_endExclusive_380_ = v___x_374_;
goto v___jp_377_;
}
}
}
else
{
lean_dec(v___x_374_);
lean_dec_ref(v_s_372_);
return v_b_376_;
}
v___jp_377_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_inc_ref(v_s_372_);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v_s_372_);
lean_ctor_set(v___x_381_, 1, v_startInclusive_379_);
lean_ctor_set(v___x_381_, 2, v_endExclusive_380_);
v___x_382_ = lean_array_push(v_b_376_, v___x_381_);
v_a_375_ = v_it_378_;
v_b_376_ = v___x_382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object* v_s_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_409_, v___x_410_, v___x_411_, v_a_412_, v_b_413_);
lean_dec_ref(v___x_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object* v_s_426_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_string_utf8_byte_size(v_s_426_);
lean_inc_ref(v_s_426_);
v___x_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_431_, 0, v_s_426_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
v___x_432_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0);
v___x_433_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2));
v___x_434_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_426_, v___x_431_, v___x_430_, v___x_432_, v___x_433_);
lean_dec_ref_known(v___x_431_, 3);
v___x_435_ = lean_array_to_list(v___x_434_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_head_436_; lean_object* v_tail_437_; 
v_head_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_head_436_);
v_tail_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_tail_437_);
lean_dec_ref_known(v___x_435_, 2);
if (lean_obj_tag(v_tail_437_) == 0)
{
lean_object* v_str_441_; lean_object* v_startInclusive_442_; lean_object* v_endExclusive_443_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_str_441_ = lean_ctor_get(v_head_436_, 0);
v_startInclusive_442_ = lean_ctor_get(v_head_436_, 1);
v_endExclusive_443_ = lean_ctor_get(v_head_436_, 2);
v___x_459_ = lean_nat_sub(v_endExclusive_443_, v_startInclusive_442_);
v___x_460_ = lean_nat_dec_eq(v___x_459_, v___x_429_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_dec_le(v___x_461_, v___x_459_);
lean_dec(v___x_459_);
if (v___x_462_ == 0)
{
goto v___jp_444_;
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_464_ = lean_string_memcmp(v_str_441_, v___x_463_, v_startInclusive_442_, v___x_429_, v___x_461_);
if (v___x_464_ == 0)
{
goto v___jp_444_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
lean_inc(v_endExclusive_443_);
lean_inc(v_startInclusive_442_);
lean_inc_ref(v_str_441_);
v___x_465_ = l_String_Slice_Pos_nextn(v_head_436_, v___x_429_, v___x_461_);
lean_dec(v_head_436_);
v___x_466_ = lean_nat_add(v_startInclusive_442_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v_startInclusive_442_);
v___x_467_ = lean_nat_sub(v_endExclusive_443_, v___x_466_);
v___x_468_ = lean_nat_dec_eq(v___x_467_, v___x_429_);
lean_dec(v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_469_ = lean_string_utf8_extract_fast(v_str_441_, v___x_466_, v_endExclusive_443_);
lean_dec(v_endExclusive_443_);
lean_dec(v___x_466_);
lean_dec_ref(v_str_441_);
v___x_470_ = l_Lake_stringToLegalOrSimpleName(v___x_469_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
lean_dec(v___x_466_);
lean_dec(v_endExclusive_443_);
lean_dec_ref(v_str_441_);
v___x_473_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_459_);
lean_dec(v_head_436_);
v___x_474_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
return v___x_474_;
}
v___jp_444_:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_sub(v_endExclusive_443_, v_startInclusive_442_);
v___x_447_ = lean_nat_dec_le(v___x_445_, v___x_446_);
lean_dec(v___x_446_);
if (v___x_447_ == 0)
{
goto v___jp_438_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_449_ = lean_string_memcmp(v_str_441_, v___x_448_, v_startInclusive_442_, v___x_429_, v___x_445_);
if (v___x_449_ == 0)
{
goto v___jp_438_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
lean_inc(v_endExclusive_443_);
lean_inc(v_startInclusive_442_);
lean_inc_ref(v_str_441_);
v___x_450_ = l_String_Slice_Pos_nextn(v_head_436_, v___x_429_, v___x_445_);
lean_dec(v_head_436_);
v___x_451_ = lean_nat_add(v_startInclusive_442_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v_startInclusive_442_);
v___x_452_ = lean_nat_sub(v_endExclusive_443_, v___x_451_);
v___x_453_ = lean_nat_dec_eq(v___x_452_, v___x_429_);
lean_dec(v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_string_utf8_extract_fast(v_str_441_, v___x_451_, v_endExclusive_443_);
lean_dec(v_endExclusive_443_);
lean_dec(v___x_451_);
lean_dec_ref(v_str_441_);
v___x_455_ = l_Lake_stringToLegalOrSimpleName(v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
lean_dec(v___x_451_);
lean_dec(v_endExclusive_443_);
lean_dec_ref(v_str_441_);
v___x_458_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_458_;
}
}
}
}
}
else
{
lean_object* v_head_475_; lean_object* v_tail_476_; lean_object* v_str_478_; lean_object* v_startInclusive_479_; lean_object* v_endExclusive_480_; 
v_head_475_ = lean_ctor_get(v_tail_437_, 0);
lean_inc(v_head_475_);
v_tail_476_ = lean_ctor_get(v_tail_437_, 1);
lean_inc(v_tail_476_);
lean_dec_ref_known(v_tail_437_, 2);
if (lean_obj_tag(v_tail_476_) == 0)
{
lean_object* v_str_488_; lean_object* v_startInclusive_489_; lean_object* v_endExclusive_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_str_488_ = lean_ctor_get(v_head_436_, 0);
lean_inc_ref(v_str_488_);
v_startInclusive_489_ = lean_ctor_get(v_head_436_, 1);
lean_inc(v_startInclusive_489_);
v_endExclusive_490_ = lean_ctor_get(v_head_436_, 2);
lean_inc(v_endExclusive_490_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_sub(v_endExclusive_490_, v_startInclusive_489_);
v___x_493_ = lean_nat_dec_le(v___x_491_, v___x_492_);
lean_dec(v___x_492_);
if (v___x_493_ == 0)
{
lean_dec(v_head_436_);
v_str_478_ = v_str_488_;
v_startInclusive_479_ = v_startInclusive_489_;
v_endExclusive_480_ = v_endExclusive_490_;
goto v___jp_477_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_495_ = lean_string_memcmp(v_str_488_, v___x_494_, v_startInclusive_489_, v___x_429_, v___x_491_);
if (v___x_495_ == 0)
{
lean_dec(v_head_436_);
v_str_478_ = v_str_488_;
v_startInclusive_479_ = v_startInclusive_489_;
v_endExclusive_480_ = v_endExclusive_490_;
goto v___jp_477_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_String_Slice_Pos_nextn(v_head_436_, v___x_429_, v___x_491_);
lean_dec(v_head_436_);
v___x_497_ = lean_nat_add(v_startInclusive_489_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v_startInclusive_489_);
v_str_478_ = v_str_488_;
v_startInclusive_479_ = v___x_497_;
v_endExclusive_480_ = v_endExclusive_490_;
goto v___jp_477_;
}
}
}
else
{
lean_dec(v_tail_476_);
lean_dec(v_head_475_);
lean_dec(v_head_436_);
goto v___jp_427_;
}
v___jp_477_:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_nat_sub(v_endExclusive_480_, v_startInclusive_479_);
v___x_482_ = lean_nat_dec_eq(v___x_481_, v___x_429_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_string_utf8_extract_fast(v_str_478_, v_startInclusive_479_, v_endExclusive_480_);
lean_dec(v_endExclusive_480_);
lean_dec(v_startInclusive_479_);
lean_dec_ref(v_str_478_);
v___x_484_ = l_Lake_stringToLegalOrSimpleName(v___x_483_);
v___x_485_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_484_, v_head_475_);
lean_dec(v_head_475_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v_endExclusive_480_);
lean_dec(v_startInclusive_479_);
lean_dec_ref(v_str_478_);
v___x_486_ = lean_box(0);
v___x_487_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_486_, v_head_475_);
lean_dec(v_head_475_);
return v___x_487_;
}
}
}
v___jp_438_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_box(0);
v___x_440_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_439_, v_head_436_);
lean_dec(v_head_436_);
return v___x_440_;
}
}
else
{
lean_dec(v___x_435_);
goto v___jp_427_;
}
v___jp_427_:
{
lean_object* v___x_428_; 
v___x_428_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1));
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_498_, lean_object* v___x_499_, lean_object* v___x_500_, lean_object* v_inst_501_, lean_object* v_R_502_, lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_498_, v___x_499_, v___x_500_, v_a_503_, v_b_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_506_, lean_object* v___x_507_, lean_object* v___x_508_, lean_object* v_inst_509_, lean_object* v_R_510_, lean_object* v_a_511_, lean_object* v_b_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_506_, v___x_507_, v___x_508_, v_inst_509_, v_R_510_, v_a_511_, v_b_512_);
lean_dec_ref(v___x_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg___boxed(lean_object* v___dummy_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v_res_517_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_521_);
lean_dec_ref(v_s_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_panic_fn_borrowed(v___x_526_, v_msg_524_);
lean_dec_ref_known(v___x_526_, 1);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v_a_531_, lean_object* v_b_532_){
_start:
{
lean_object* v_it_534_; lean_object* v_startInclusive_535_; lean_object* v_endExclusive_536_; 
if (lean_obj_tag(v_a_531_) == 0)
{
lean_object* v_currPos_541_; lean_object* v_searcher_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_565_; 
v_currPos_541_ = lean_ctor_get(v_a_531_, 0);
v_searcher_542_ = lean_ctor_get(v_a_531_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_565_ == 0)
{
v___x_544_ = v_a_531_;
v_isShared_545_ = v_isSharedCheck_565_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_searcher_542_);
lean_inc(v_currPos_541_);
lean_dec(v_a_531_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_565_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v_decide_546_; 
v_decide_546_ = lean_nat_dec_eq(v_searcher_542_, v___x_530_);
if (v_decide_546_ == 0)
{
uint32_t v___x_547_; uint32_t v___x_548_; uint8_t v___x_549_; 
v___x_547_ = 58;
v___x_548_ = lean_string_utf8_get_fast(v_s_528_, v_searcher_542_);
v___x_549_ = lean_uint32_dec_eq(v___x_548_, v___x_547_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_string_utf8_next_fast(v_s_528_, v_searcher_542_);
lean_dec(v_searcher_542_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_550_);
v___x_552_ = v___x_544_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_currPos_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v_a_531_ = v___x_552_;
goto _start;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_slice_558_; lean_object* v_nextIt_560_; 
v___x_555_ = lean_string_utf8_next_fast(v_s_528_, v_searcher_542_);
v___x_556_ = lean_nat_sub(v___x_555_, v_searcher_542_);
v___x_557_ = lean_nat_add(v_searcher_542_, v___x_556_);
lean_dec(v___x_556_);
v_slice_558_ = l_String_Slice_subslice_x21(v___x_529_, v_currPos_541_, v_searcher_542_);
lean_inc(v___x_557_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_557_);
lean_ctor_set(v___x_544_, 0, v___x_557_);
v_nextIt_560_ = v___x_544_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_557_);
v_nextIt_560_ = v_reuseFailAlloc_563_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v_startInclusive_561_; lean_object* v_endExclusive_562_; 
v_startInclusive_561_ = lean_ctor_get(v_slice_558_, 0);
lean_inc(v_startInclusive_561_);
v_endExclusive_562_ = lean_ctor_get(v_slice_558_, 1);
lean_inc(v_endExclusive_562_);
lean_dec_ref(v_slice_558_);
v_it_534_ = v_nextIt_560_;
v_startInclusive_535_ = v_startInclusive_561_;
v_endExclusive_536_ = v_endExclusive_562_;
goto v___jp_533_;
}
}
}
else
{
lean_object* v___x_564_; 
lean_del_object(v___x_544_);
lean_dec(v_searcher_542_);
v___x_564_ = lean_box(1);
lean_inc(v___x_530_);
v_it_534_ = v___x_564_;
v_startInclusive_535_ = v_currPos_541_;
v_endExclusive_536_ = v___x_530_;
goto v___jp_533_;
}
}
}
else
{
lean_dec(v___x_530_);
lean_dec_ref(v_s_528_);
return v_b_532_;
}
v___jp_533_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_inc_ref(v_s_528_);
v___x_537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_537_, 0, v_s_528_);
lean_ctor_set(v___x_537_, 1, v_startInclusive_535_);
lean_ctor_set(v___x_537_, 2, v_endExclusive_536_);
v___x_538_ = l_String_Slice_toString(v___x_537_);
lean_dec_ref_known(v___x_537_, 3);
v___x_539_ = lean_array_push(v_b_532_, v___x_538_);
v_a_531_ = v_it_534_;
v_b_532_ = v___x_539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_566_, lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_a_569_, lean_object* v_b_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_566_, v___x_567_, v___x_568_, v_a_569_, v_b_570_);
lean_dec_ref(v___x_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_x_575_);
return v___x_577_;
}
else
{
lean_object* v_head_578_; lean_object* v_tail_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_592_; 
v_head_578_ = lean_ctor_get(v_x_576_, 0);
v_tail_579_ = lean_ctor_get(v_x_576_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_592_ == 0)
{
v___x_581_ = v_x_576_;
v_isShared_582_ = v_isSharedCheck_592_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_tail_579_);
lean_inc(v_head_578_);
lean_dec(v_x_576_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_592_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_string_utf8_byte_size(v_head_578_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_nat_dec_eq(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = l_Lake_stringToLegalOrSimpleName(v_head_578_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 4);
lean_ctor_set(v___x_581_, 1, v___x_586_);
lean_ctor_set(v___x_581_, 0, v_x_575_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_x_575_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v_x_575_ = v___x_588_;
v_x_576_ = v_tail_579_;
goto _start;
}
}
else
{
lean_object* v___x_591_; 
lean_del_object(v___x_581_);
lean_dec(v_tail_579_);
lean_dec(v_head_578_);
lean_dec_ref(v_x_575_);
v___x_591_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_591_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_599_ = lean_unsigned_to_nat(4u);
v___x_600_ = lean_unsigned_to_nat(65u);
v___x_601_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_602_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_603_ = l_mkPanicMessageWithDecl(v___x_602_, v___x_601_, v___x_600_, v___x_599_, v___x_598_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_string_utf8_byte_size(v_s_607_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_nat_dec_eq(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc_ref(v_s_607_);
v___x_611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_611_, 0, v_s_607_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_608_);
v___x_612_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
v___x_613_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_614_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_607_, v___x_611_, v___x_608_, v___x_612_, v___x_613_);
lean_dec_ref_known(v___x_611_, 3);
v___x_615_ = lean_array_to_list(v___x_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_617_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_616_);
return v___x_617_;
}
else
{
lean_object* v_head_618_; lean_object* v_tail_619_; lean_object* v___x_620_; 
v_head_618_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_head_618_);
v_tail_619_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_tail_619_);
lean_dec_ref_known(v___x_615_, 2);
v___x_620_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_618_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec(v_tail_619_);
return v___x_620_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_621_, v_tail_619_);
return v___x_622_;
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec_ref(v_s_607_);
v___x_623_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_624_, lean_object* v___x_625_, lean_object* v___x_626_, lean_object* v_inst_627_, lean_object* v_R_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_624_, v___x_625_, v___x_626_, v_a_629_, v_b_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_inst_635_, lean_object* v_R_636_, lean_object* v_a_637_, lean_object* v_b_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_632_, v___x_633_, v___x_634_, v_inst_635_, v_R_636_, v_a_637_, v_b_638_);
lean_dec_ref(v___x_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_640_){
_start:
{
if (lean_obj_tag(v_p_640_) == 2)
{
lean_object* v_pre_641_; 
v_pre_641_ = lean_ctor_get(v_p_640_, 0);
lean_inc(v_pre_641_);
return v_pre_641_;
}
else
{
lean_inc(v_p_640_);
return v_p_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_642_);
lean_dec(v_p_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_647_){
_start:
{
lean_object* v___y_649_; 
switch(lean_obj_tag(v_x_647_))
{
case 0:
{
lean_object* v_module_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_module_655_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_module_655_);
lean_dec_ref_known(v_x_647_, 1);
v___x_656_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_657_ = 1;
v___x_658_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_655_, v___x_657_);
v___x_659_ = lean_string_append(v___x_656_, v___x_658_);
lean_dec_ref(v___x_658_);
return v___x_659_;
}
case 1:
{
lean_object* v_package_660_; 
v_package_660_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_package_660_);
lean_dec_ref_known(v_x_647_, 1);
if (lean_obj_tag(v_package_660_) == 2)
{
lean_object* v_pre_661_; 
v_pre_661_ = lean_ctor_get(v_package_660_, 0);
lean_inc(v_pre_661_);
lean_dec_ref_known(v_package_660_, 2);
v___y_649_ = v_pre_661_;
goto v___jp_648_;
}
else
{
v___y_649_ = v_package_660_;
goto v___jp_648_;
}
}
case 2:
{
lean_object* v_package_662_; lean_object* v_module_663_; lean_object* v___y_665_; 
v_package_662_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_package_662_);
v_module_663_ = lean_ctor_get(v_x_647_, 1);
lean_inc(v_module_663_);
lean_dec_ref_known(v_x_647_, 2);
if (lean_obj_tag(v_package_662_) == 2)
{
lean_object* v_pre_676_; 
v_pre_676_ = lean_ctor_get(v_package_662_, 0);
lean_inc(v_pre_676_);
lean_dec_ref_known(v_package_662_, 2);
v___y_665_ = v_pre_676_;
goto v___jp_664_;
}
else
{
v___y_665_ = v_package_662_;
goto v___jp_664_;
}
v___jp_664_:
{
if (lean_obj_tag(v___y_665_) == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_667_ = 1;
v___x_668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_663_, v___x_667_);
v___x_669_ = lean_string_append(v___x_666_, v___x_668_);
lean_dec_ref(v___x_668_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = 1;
v___x_671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_665_, v___x_670_);
v___x_672_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
v___x_674_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_663_, v___x_670_);
v___x_675_ = lean_string_append(v___x_673_, v___x_674_);
lean_dec_ref(v___x_674_);
return v___x_675_;
}
}
}
case 3:
{
lean_object* v_package_677_; lean_object* v_target_678_; lean_object* v___y_680_; 
v_package_677_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_package_677_);
v_target_678_ = lean_ctor_get(v_x_647_, 1);
lean_inc(v_target_678_);
lean_dec_ref_known(v_x_647_, 2);
if (lean_obj_tag(v_package_677_) == 2)
{
lean_object* v_pre_689_; 
v_pre_689_ = lean_ctor_get(v_package_677_, 0);
lean_inc(v_pre_689_);
lean_dec_ref_known(v_package_677_, 2);
v___y_680_ = v_pre_689_;
goto v___jp_679_;
}
else
{
v___y_680_ = v_package_677_;
goto v___jp_679_;
}
v___jp_679_:
{
if (lean_obj_tag(v___y_680_) == 0)
{
uint8_t v___x_681_; lean_object* v___x_682_; 
v___x_681_ = 1;
v___x_682_ = l_Lean_Name_toString(v_target_678_, v___x_681_);
return v___x_682_;
}
else
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = 1;
v___x_684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_680_, v___x_683_);
v___x_685_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_686_ = lean_string_append(v___x_684_, v___x_685_);
v___x_687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_678_, v___x_683_);
v___x_688_ = lean_string_append(v___x_686_, v___x_687_);
lean_dec_ref(v___x_687_);
return v___x_688_;
}
}
}
default: 
{
lean_object* v_target_690_; lean_object* v_facet_691_; uint8_t v___x_692_; 
v_target_690_ = lean_ctor_get(v_x_647_, 0);
lean_inc_ref(v_target_690_);
v_facet_691_ = lean_ctor_get(v_x_647_, 1);
lean_inc(v_facet_691_);
lean_dec_ref_known(v_x_647_, 2);
v___x_692_ = l_Lean_Name_isAnonymous(v_facet_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = l_Lake_PartialBuildKey_toString(v_target_690_);
v___x_694_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
v___x_696_ = 1;
v___x_697_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_691_, v___x_696_);
v___x_698_ = lean_string_append(v___x_695_, v___x_697_);
lean_dec_ref(v___x_697_);
return v___x_698_;
}
else
{
lean_dec(v_facet_691_);
v_x_647_ = v_target_690_;
goto _start;
}
}
}
v___jp_648_:
{
if (lean_obj_tag(v___y_649_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_650_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_652_ = 1;
v___x_653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_649_, v___x_652_);
v___x_654_ = lean_string_append(v___x_651_, v___x_653_);
lean_dec_ref(v___x_653_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_702_, lean_object* v_facet_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v_module_702_);
v___x_705_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_facet_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_706_, lean_object* v_facet_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_package_706_);
v___x_709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_facet_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_710_, lean_object* v_module_711_, lean_object* v_facet_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v_package_710_);
lean_ctor_set(v___x_713_, 1, v_module_711_);
v___x_714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_facet_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_715_, lean_object* v_target_716_, lean_object* v_facet_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_718_, 0, v_package_715_);
lean_ctor_set(v___x_718_, 1, v_target_716_);
v___x_719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_facet_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_720_, lean_object* v_target_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_722_, 0, v_package_720_);
lean_ctor_set(v___x_722_, 1, v_target_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_723_){
_start:
{
switch(lean_obj_tag(v_x_723_))
{
case 0:
{
lean_object* v_module_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_module_724_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_module_724_);
lean_dec_ref_known(v_x_723_, 1);
v___x_725_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_726_ = 1;
v___x_727_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_724_, v___x_726_);
v___x_728_ = lean_string_append(v___x_725_, v___x_727_);
lean_dec_ref(v___x_727_);
return v___x_728_;
}
case 1:
{
lean_object* v_package_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_package_729_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_package_729_);
lean_dec_ref_known(v_x_723_, 1);
v___x_730_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_731_ = l_Lean_Name_getPrefix(v_package_729_);
lean_dec(v_package_729_);
v___x_732_ = 1;
v___x_733_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_731_, v___x_732_);
v___x_734_ = lean_string_append(v___x_730_, v___x_733_);
lean_dec_ref(v___x_733_);
return v___x_734_;
}
case 2:
{
lean_object* v_package_735_; lean_object* v_module_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_package_735_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_package_735_);
v_module_736_ = lean_ctor_get(v_x_723_, 1);
lean_inc(v_module_736_);
lean_dec_ref_known(v_x_723_, 2);
v___x_737_ = l_Lean_Name_getPrefix(v_package_735_);
lean_dec(v_package_735_);
v___x_738_ = 1;
v___x_739_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_737_, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_741_ = lean_string_append(v___x_739_, v___x_740_);
v___x_742_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_736_, v___x_738_);
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
lean_dec_ref(v___x_742_);
return v___x_743_;
}
case 3:
{
lean_object* v_package_744_; lean_object* v_target_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_package_744_ = lean_ctor_get(v_x_723_, 0);
lean_inc(v_package_744_);
v_target_745_ = lean_ctor_get(v_x_723_, 1);
lean_inc(v_target_745_);
lean_dec_ref_known(v_x_723_, 2);
v___x_746_ = l_Lean_Name_getPrefix(v_package_744_);
lean_dec(v_package_744_);
v___x_747_ = 1;
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_746_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_750_ = lean_string_append(v___x_748_, v___x_749_);
v___x_751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_745_, v___x_747_);
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
lean_dec_ref(v___x_751_);
return v___x_752_;
}
default: 
{
lean_object* v_target_753_; lean_object* v_facet_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_target_753_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_target_753_);
v_facet_754_ = lean_ctor_get(v_x_723_, 1);
lean_inc(v_facet_754_);
lean_dec_ref_known(v_x_723_, 2);
v___x_755_ = l_Lake_BuildKey_toString(v_target_753_);
v___x_756_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_757_ = lean_string_append(v___x_755_, v___x_756_);
v___x_758_ = l_Lake_Name_eraseHead(v_facet_754_);
v___x_759_ = 1;
v___x_760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_758_, v___x_759_);
v___x_761_ = lean_string_append(v___x_757_, v___x_760_);
lean_dec_ref(v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_762_){
_start:
{
lean_object* v_p_764_; lean_object* v_m_765_; 
switch(lean_obj_tag(v_x_762_))
{
case 0:
{
lean_object* v_module_773_; uint8_t v___x_774_; lean_object* v___x_775_; 
v_module_773_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_module_773_);
lean_dec_ref_known(v_x_762_, 1);
v___x_774_ = 1;
v___x_775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_773_, v___x_774_);
return v___x_775_;
}
case 1:
{
lean_object* v_package_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; 
v_package_776_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_package_776_);
lean_dec_ref_known(v_x_762_, 1);
v___x_777_ = l_Lean_Name_getPrefix(v_package_776_);
lean_dec(v_package_776_);
v___x_778_ = 1;
v___x_779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_777_, v___x_778_);
return v___x_779_;
}
case 4:
{
lean_object* v_target_780_; lean_object* v_facet_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_target_780_ = lean_ctor_get(v_x_762_, 0);
lean_inc_ref(v_target_780_);
v_facet_781_ = lean_ctor_get(v_x_762_, 1);
lean_inc(v_facet_781_);
lean_dec_ref_known(v_x_762_, 2);
v___x_782_ = l_Lake_BuildKey_toSimpleString(v_target_780_);
v___x_783_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
v___x_785_ = l_Lake_Name_eraseHead(v_facet_781_);
v___x_786_ = 1;
v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_785_, v___x_786_);
v___x_788_ = lean_string_append(v___x_784_, v___x_787_);
lean_dec_ref(v___x_787_);
return v___x_788_;
}
default: 
{
lean_object* v_package_789_; lean_object* v_module_790_; 
v_package_789_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_package_789_);
v_module_790_ = lean_ctor_get(v_x_762_, 1);
lean_inc(v_module_790_);
lean_dec_ref(v_x_762_);
v_p_764_ = v_package_789_;
v_m_765_ = v_module_790_;
goto v___jp_763_;
}
}
v___jp_763_:
{
lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_766_ = l_Lean_Name_getPrefix(v_p_764_);
lean_dec(v_p_764_);
v___x_767_ = 1;
v___x_768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_766_, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_770_ = lean_string_append(v___x_768_, v___x_769_);
v___x_771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_765_, v___x_767_);
v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
lean_dec_ref(v___x_771_);
return v___x_772_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_793_, lean_object* v_k_x27_794_){
_start:
{
switch(lean_obj_tag(v_k_793_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_794_) == 0)
{
lean_object* v_module_795_; lean_object* v_module_796_; uint8_t v___x_797_; 
v_module_795_ = lean_ctor_get(v_k_793_, 0);
v_module_796_ = lean_ctor_get(v_k_x27_794_, 0);
v___x_797_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_795_, v_module_796_);
return v___x_797_;
}
else
{
uint8_t v___x_798_; 
v___x_798_ = 0;
return v___x_798_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_794_))
{
case 0:
{
uint8_t v___x_799_; 
v___x_799_ = 2;
return v___x_799_;
}
case 1:
{
lean_object* v_package_800_; lean_object* v_package_801_; uint8_t v___x_802_; 
v_package_800_ = lean_ctor_get(v_k_793_, 0);
v_package_801_ = lean_ctor_get(v_k_x27_794_, 0);
v___x_802_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_800_, v_package_801_);
return v___x_802_;
}
default: 
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_794_))
{
case 4:
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
case 3:
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
case 2:
{
lean_object* v_package_806_; lean_object* v_module_807_; lean_object* v_package_808_; lean_object* v_module_809_; uint8_t v___x_810_; 
v_package_806_ = lean_ctor_get(v_k_793_, 0);
v_module_807_ = lean_ctor_get(v_k_793_, 1);
v_package_808_ = lean_ctor_get(v_k_x27_794_, 0);
v_module_809_ = lean_ctor_get(v_k_x27_794_, 1);
v___x_810_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_807_, v_module_809_);
if (v___x_810_ == 1)
{
uint8_t v___x_811_; 
v___x_811_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_806_, v_package_808_);
return v___x_811_;
}
else
{
return v___x_810_;
}
}
default: 
{
uint8_t v___x_812_; 
v___x_812_ = 2;
return v___x_812_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_794_))
{
case 4:
{
uint8_t v___x_813_; 
v___x_813_ = 0;
return v___x_813_;
}
case 3:
{
lean_object* v_package_814_; lean_object* v_target_815_; lean_object* v_package_816_; lean_object* v_target_817_; uint8_t v___x_818_; 
v_package_814_ = lean_ctor_get(v_k_793_, 0);
v_target_815_ = lean_ctor_get(v_k_793_, 1);
v_package_816_ = lean_ctor_get(v_k_x27_794_, 0);
v_target_817_ = lean_ctor_get(v_k_x27_794_, 1);
v___x_818_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_814_, v_package_816_);
if (v___x_818_ == 1)
{
uint8_t v___x_819_; 
v___x_819_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_815_, v_target_817_);
return v___x_819_;
}
else
{
return v___x_818_;
}
}
default: 
{
uint8_t v___x_820_; 
v___x_820_ = 2;
return v___x_820_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_794_) == 4)
{
lean_object* v_target_821_; lean_object* v_facet_822_; lean_object* v_target_823_; lean_object* v_facet_824_; uint8_t v___x_825_; 
v_target_821_ = lean_ctor_get(v_k_793_, 0);
v_facet_822_ = lean_ctor_get(v_k_793_, 1);
v_target_823_ = lean_ctor_get(v_k_x27_794_, 0);
v_facet_824_ = lean_ctor_get(v_k_x27_794_, 1);
v___x_825_ = l_Lake_BuildKey_quickCmp(v_target_821_, v_target_823_);
if (v___x_825_ == 1)
{
uint8_t v___x_826_; 
v___x_826_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_822_, v_facet_824_);
return v___x_826_;
}
else
{
return v___x_825_;
}
}
else
{
uint8_t v___x_827_; 
v___x_827_ = 2;
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_828_, lean_object* v_k_x27_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Lake_BuildKey_quickCmp(v_k_828_, v_k_x27_829_);
lean_dec_ref(v_k_x27_829_);
lean_dec_ref(v_k_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_832_, lean_object* v_h__1_833_, lean_object* v_h__2_834_, lean_object* v_h__3_835_, lean_object* v_h__4_836_, lean_object* v_h__5_837_){
_start:
{
switch(lean_obj_tag(v_x_832_))
{
case 0:
{
lean_object* v_module_838_; lean_object* v___x_839_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__4_836_);
lean_dec(v_h__3_835_);
lean_dec(v_h__2_834_);
v_module_838_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_module_838_);
lean_dec_ref_known(v_x_832_, 1);
v___x_839_ = lean_apply_1(v_h__1_833_, v_module_838_);
return v___x_839_;
}
case 1:
{
lean_object* v_package_840_; lean_object* v___x_841_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__4_836_);
lean_dec(v_h__3_835_);
lean_dec(v_h__1_833_);
v_package_840_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_package_840_);
lean_dec_ref_known(v_x_832_, 1);
v___x_841_ = lean_apply_1(v_h__2_834_, v_package_840_);
return v___x_841_;
}
case 2:
{
lean_object* v_package_842_; lean_object* v_module_843_; lean_object* v___x_844_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__4_836_);
lean_dec(v_h__2_834_);
lean_dec(v_h__1_833_);
v_package_842_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_package_842_);
v_module_843_ = lean_ctor_get(v_x_832_, 1);
lean_inc(v_module_843_);
lean_dec_ref_known(v_x_832_, 2);
v___x_844_ = lean_apply_2(v_h__3_835_, v_package_842_, v_module_843_);
return v___x_844_;
}
case 3:
{
lean_object* v_package_845_; lean_object* v_target_846_; lean_object* v___x_847_; 
lean_dec(v_h__5_837_);
lean_dec(v_h__3_835_);
lean_dec(v_h__2_834_);
lean_dec(v_h__1_833_);
v_package_845_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_package_845_);
v_target_846_ = lean_ctor_get(v_x_832_, 1);
lean_inc(v_target_846_);
lean_dec_ref_known(v_x_832_, 2);
v___x_847_ = lean_apply_2(v_h__4_836_, v_package_845_, v_target_846_);
return v___x_847_;
}
default: 
{
lean_object* v_target_848_; lean_object* v_facet_849_; lean_object* v___x_850_; 
lean_dec(v_h__4_836_);
lean_dec(v_h__3_835_);
lean_dec(v_h__2_834_);
lean_dec(v_h__1_833_);
v_target_848_ = lean_ctor_get(v_x_832_, 0);
lean_inc_ref(v_target_848_);
v_facet_849_ = lean_ctor_get(v_x_832_, 1);
lean_inc(v_facet_849_);
lean_dec_ref_known(v_x_832_, 2);
v___x_850_ = lean_apply_2(v_h__5_837_, v_target_848_, v_facet_849_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_851_, lean_object* v_x_852_, lean_object* v_h__1_853_, lean_object* v_h__2_854_, lean_object* v_h__3_855_, lean_object* v_h__4_856_, lean_object* v_h__5_857_){
_start:
{
switch(lean_obj_tag(v_x_852_))
{
case 0:
{
lean_object* v_module_858_; lean_object* v___x_859_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__4_856_);
lean_dec(v_h__3_855_);
lean_dec(v_h__2_854_);
v_module_858_ = lean_ctor_get(v_x_852_, 0);
lean_inc(v_module_858_);
lean_dec_ref_known(v_x_852_, 1);
v___x_859_ = lean_apply_1(v_h__1_853_, v_module_858_);
return v___x_859_;
}
case 1:
{
lean_object* v_package_860_; lean_object* v___x_861_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__4_856_);
lean_dec(v_h__3_855_);
lean_dec(v_h__1_853_);
v_package_860_ = lean_ctor_get(v_x_852_, 0);
lean_inc(v_package_860_);
lean_dec_ref_known(v_x_852_, 1);
v___x_861_ = lean_apply_1(v_h__2_854_, v_package_860_);
return v___x_861_;
}
case 2:
{
lean_object* v_package_862_; lean_object* v_module_863_; lean_object* v___x_864_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__4_856_);
lean_dec(v_h__2_854_);
lean_dec(v_h__1_853_);
v_package_862_ = lean_ctor_get(v_x_852_, 0);
lean_inc(v_package_862_);
v_module_863_ = lean_ctor_get(v_x_852_, 1);
lean_inc(v_module_863_);
lean_dec_ref_known(v_x_852_, 2);
v___x_864_ = lean_apply_2(v_h__3_855_, v_package_862_, v_module_863_);
return v___x_864_;
}
case 3:
{
lean_object* v_package_865_; lean_object* v_target_866_; lean_object* v___x_867_; 
lean_dec(v_h__5_857_);
lean_dec(v_h__3_855_);
lean_dec(v_h__2_854_);
lean_dec(v_h__1_853_);
v_package_865_ = lean_ctor_get(v_x_852_, 0);
lean_inc(v_package_865_);
v_target_866_ = lean_ctor_get(v_x_852_, 1);
lean_inc(v_target_866_);
lean_dec_ref_known(v_x_852_, 2);
v___x_867_ = lean_apply_2(v_h__4_856_, v_package_865_, v_target_866_);
return v___x_867_;
}
default: 
{
lean_object* v_target_868_; lean_object* v_facet_869_; lean_object* v___x_870_; 
lean_dec(v_h__4_856_);
lean_dec(v_h__3_855_);
lean_dec(v_h__2_854_);
lean_dec(v_h__1_853_);
v_target_868_ = lean_ctor_get(v_x_852_, 0);
lean_inc_ref(v_target_868_);
v_facet_869_ = lean_ctor_get(v_x_852_, 1);
lean_inc(v_facet_869_);
lean_dec_ref_known(v_x_852_, 2);
v___x_870_ = lean_apply_2(v_h__5_857_, v_target_868_, v_facet_869_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_871_, lean_object* v_h__1_872_, lean_object* v_h__2_873_){
_start:
{
if (lean_obj_tag(v_k_x27_871_) == 0)
{
lean_object* v_module_874_; lean_object* v___x_875_; 
lean_dec(v_h__2_873_);
v_module_874_ = lean_ctor_get(v_k_x27_871_, 0);
lean_inc(v_module_874_);
lean_dec_ref_known(v_k_x27_871_, 1);
v___x_875_ = lean_apply_1(v_h__1_872_, v_module_874_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; 
lean_dec(v_h__1_872_);
v___x_876_ = lean_apply_2(v_h__2_873_, v_k_x27_871_, lean_box(0));
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_877_, lean_object* v_k_x27_878_, lean_object* v_h__1_879_, lean_object* v_h__2_880_){
_start:
{
if (lean_obj_tag(v_k_x27_878_) == 0)
{
lean_object* v_module_881_; lean_object* v___x_882_; 
lean_dec(v_h__2_880_);
v_module_881_ = lean_ctor_get(v_k_x27_878_, 0);
lean_inc(v_module_881_);
lean_dec_ref_known(v_k_x27_878_, 1);
v___x_882_ = lean_apply_1(v_h__1_879_, v_module_881_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; 
lean_dec(v_h__1_879_);
v___x_883_ = lean_apply_2(v_h__2_880_, v_k_x27_878_, lean_box(0));
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_, lean_object* v_h__3_887_){
_start:
{
switch(lean_obj_tag(v_k_x27_884_))
{
case 0:
{
lean_object* v_module_888_; lean_object* v___x_889_; 
lean_dec(v_h__3_887_);
lean_dec(v_h__2_886_);
v_module_888_ = lean_ctor_get(v_k_x27_884_, 0);
lean_inc(v_module_888_);
lean_dec_ref_known(v_k_x27_884_, 1);
v___x_889_ = lean_apply_1(v_h__1_885_, v_module_888_);
return v___x_889_;
}
case 1:
{
lean_object* v_package_890_; lean_object* v___x_891_; 
lean_dec(v_h__3_887_);
lean_dec(v_h__1_885_);
v_package_890_ = lean_ctor_get(v_k_x27_884_, 0);
lean_inc(v_package_890_);
lean_dec_ref_known(v_k_x27_884_, 1);
v___x_891_ = lean_apply_1(v_h__2_886_, v_package_890_);
return v___x_891_;
}
default: 
{
lean_object* v___x_892_; 
lean_dec(v_h__2_886_);
lean_dec(v_h__1_885_);
v___x_892_ = lean_apply_3(v_h__3_887_, v_k_x27_884_, lean_box(0), lean_box(0));
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_893_, lean_object* v_k_x27_894_, lean_object* v_h__1_895_, lean_object* v_h__2_896_, lean_object* v_h__3_897_){
_start:
{
switch(lean_obj_tag(v_k_x27_894_))
{
case 0:
{
lean_object* v_module_898_; lean_object* v___x_899_; 
lean_dec(v_h__3_897_);
lean_dec(v_h__2_896_);
v_module_898_ = lean_ctor_get(v_k_x27_894_, 0);
lean_inc(v_module_898_);
lean_dec_ref_known(v_k_x27_894_, 1);
v___x_899_ = lean_apply_1(v_h__1_895_, v_module_898_);
return v___x_899_;
}
case 1:
{
lean_object* v_package_900_; lean_object* v___x_901_; 
lean_dec(v_h__3_897_);
lean_dec(v_h__1_895_);
v_package_900_ = lean_ctor_get(v_k_x27_894_, 0);
lean_inc(v_package_900_);
lean_dec_ref_known(v_k_x27_894_, 1);
v___x_901_ = lean_apply_1(v_h__2_896_, v_package_900_);
return v___x_901_;
}
default: 
{
lean_object* v___x_902_; 
lean_dec(v_h__2_896_);
lean_dec(v_h__1_895_);
v___x_902_ = lean_apply_3(v_h__3_897_, v_k_x27_894_, lean_box(0), lean_box(0));
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_903_, lean_object* v_h__1_904_, lean_object* v_h__2_905_, lean_object* v_h__3_906_, lean_object* v_h__4_907_){
_start:
{
switch(lean_obj_tag(v_k_x27_903_))
{
case 4:
{
lean_object* v_target_908_; lean_object* v_facet_909_; lean_object* v___x_910_; 
lean_dec(v_h__4_907_);
lean_dec(v_h__3_906_);
lean_dec(v_h__2_905_);
v_target_908_ = lean_ctor_get(v_k_x27_903_, 0);
lean_inc_ref(v_target_908_);
v_facet_909_ = lean_ctor_get(v_k_x27_903_, 1);
lean_inc(v_facet_909_);
lean_dec_ref_known(v_k_x27_903_, 2);
v___x_910_ = lean_apply_2(v_h__1_904_, v_target_908_, v_facet_909_);
return v___x_910_;
}
case 3:
{
lean_object* v_package_911_; lean_object* v_target_912_; lean_object* v___x_913_; 
lean_dec(v_h__4_907_);
lean_dec(v_h__3_906_);
lean_dec(v_h__1_904_);
v_package_911_ = lean_ctor_get(v_k_x27_903_, 0);
lean_inc(v_package_911_);
v_target_912_ = lean_ctor_get(v_k_x27_903_, 1);
lean_inc(v_target_912_);
lean_dec_ref_known(v_k_x27_903_, 2);
v___x_913_ = lean_apply_2(v_h__2_905_, v_package_911_, v_target_912_);
return v___x_913_;
}
case 2:
{
lean_object* v_package_914_; lean_object* v_module_915_; lean_object* v___x_916_; 
lean_dec(v_h__4_907_);
lean_dec(v_h__2_905_);
lean_dec(v_h__1_904_);
v_package_914_ = lean_ctor_get(v_k_x27_903_, 0);
lean_inc(v_package_914_);
v_module_915_ = lean_ctor_get(v_k_x27_903_, 1);
lean_inc(v_module_915_);
lean_dec_ref_known(v_k_x27_903_, 2);
v___x_916_ = lean_apply_2(v_h__3_906_, v_package_914_, v_module_915_);
return v___x_916_;
}
default: 
{
lean_object* v___x_917_; 
lean_dec(v_h__3_906_);
lean_dec(v_h__2_905_);
lean_dec(v_h__1_904_);
v___x_917_ = lean_apply_4(v_h__4_907_, v_k_x27_903_, lean_box(0), lean_box(0), lean_box(0));
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_918_, lean_object* v_k_x27_919_, lean_object* v_h__1_920_, lean_object* v_h__2_921_, lean_object* v_h__3_922_, lean_object* v_h__4_923_){
_start:
{
switch(lean_obj_tag(v_k_x27_919_))
{
case 4:
{
lean_object* v_target_924_; lean_object* v_facet_925_; lean_object* v___x_926_; 
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
v_target_924_ = lean_ctor_get(v_k_x27_919_, 0);
lean_inc_ref(v_target_924_);
v_facet_925_ = lean_ctor_get(v_k_x27_919_, 1);
lean_inc(v_facet_925_);
lean_dec_ref_known(v_k_x27_919_, 2);
v___x_926_ = lean_apply_2(v_h__1_920_, v_target_924_, v_facet_925_);
return v___x_926_;
}
case 3:
{
lean_object* v_package_927_; lean_object* v_target_928_; lean_object* v___x_929_; 
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__1_920_);
v_package_927_ = lean_ctor_get(v_k_x27_919_, 0);
lean_inc(v_package_927_);
v_target_928_ = lean_ctor_get(v_k_x27_919_, 1);
lean_inc(v_target_928_);
lean_dec_ref_known(v_k_x27_919_, 2);
v___x_929_ = lean_apply_2(v_h__2_921_, v_package_927_, v_target_928_);
return v___x_929_;
}
case 2:
{
lean_object* v_package_930_; lean_object* v_module_931_; lean_object* v___x_932_; 
lean_dec(v_h__4_923_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v_package_930_ = lean_ctor_get(v_k_x27_919_, 0);
lean_inc(v_package_930_);
v_module_931_ = lean_ctor_get(v_k_x27_919_, 1);
lean_inc(v_module_931_);
lean_dec_ref_known(v_k_x27_919_, 2);
v___x_932_ = lean_apply_2(v_h__3_922_, v_package_930_, v_module_931_);
return v___x_932_;
}
default: 
{
lean_object* v___x_933_; 
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v___x_933_ = lean_apply_4(v_h__4_923_, v_k_x27_919_, lean_box(0), lean_box(0), lean_box(0));
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_934_, lean_object* v_h__1_935_, lean_object* v_h__2_936_){
_start:
{
if (v_x_934_ == 1)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_h__2_936_);
v___x_937_ = lean_box(0);
v___x_938_ = lean_apply_1(v_h__1_935_, v___x_937_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_h__1_935_);
v___x_939_ = lean_box(v_x_934_);
v___x_940_ = lean_apply_2(v_h__2_936_, v___x_939_, lean_box(0));
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_941_, lean_object* v_h__1_942_, lean_object* v_h__2_943_){
_start:
{
uint8_t v_x_13__boxed_944_; lean_object* v_res_945_; 
v_x_13__boxed_944_ = lean_unbox(v_x_941_);
v_res_945_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_13__boxed_944_, v_h__1_942_, v_h__2_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_946_, uint8_t v_x_947_, lean_object* v_h__1_948_, lean_object* v_h__2_949_){
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_954_, lean_object* v_x_955_, lean_object* v_h__1_956_, lean_object* v_h__2_957_){
_start:
{
uint8_t v_x_24__boxed_958_; lean_object* v_res_959_; 
v_x_24__boxed_958_ = lean_unbox(v_x_955_);
v_res_959_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_954_, v_x_24__boxed_958_, v_h__1_956_, v_h__2_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_960_, lean_object* v_h__1_961_, lean_object* v_h__2_962_, lean_object* v_h__3_963_){
_start:
{
switch(lean_obj_tag(v_k_x27_960_))
{
case 4:
{
lean_object* v_target_964_; lean_object* v_facet_965_; lean_object* v___x_966_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
v_target_964_ = lean_ctor_get(v_k_x27_960_, 0);
lean_inc_ref(v_target_964_);
v_facet_965_ = lean_ctor_get(v_k_x27_960_, 1);
lean_inc(v_facet_965_);
lean_dec_ref_known(v_k_x27_960_, 2);
v___x_966_ = lean_apply_2(v_h__1_961_, v_target_964_, v_facet_965_);
return v___x_966_;
}
case 3:
{
lean_object* v_package_967_; lean_object* v_target_968_; lean_object* v___x_969_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__1_961_);
v_package_967_ = lean_ctor_get(v_k_x27_960_, 0);
lean_inc(v_package_967_);
v_target_968_ = lean_ctor_get(v_k_x27_960_, 1);
lean_inc(v_target_968_);
lean_dec_ref_known(v_k_x27_960_, 2);
v___x_969_ = lean_apply_2(v_h__2_962_, v_package_967_, v_target_968_);
return v___x_969_;
}
default: 
{
lean_object* v___x_970_; 
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v___x_970_ = lean_apply_3(v_h__3_963_, v_k_x27_960_, lean_box(0), lean_box(0));
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_971_, lean_object* v_k_x27_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_){
_start:
{
switch(lean_obj_tag(v_k_x27_972_))
{
case 4:
{
lean_object* v_target_976_; lean_object* v_facet_977_; lean_object* v___x_978_; 
lean_dec(v_h__3_975_);
lean_dec(v_h__2_974_);
v_target_976_ = lean_ctor_get(v_k_x27_972_, 0);
lean_inc_ref(v_target_976_);
v_facet_977_ = lean_ctor_get(v_k_x27_972_, 1);
lean_inc(v_facet_977_);
lean_dec_ref_known(v_k_x27_972_, 2);
v___x_978_ = lean_apply_2(v_h__1_973_, v_target_976_, v_facet_977_);
return v___x_978_;
}
case 3:
{
lean_object* v_package_979_; lean_object* v_target_980_; lean_object* v___x_981_; 
lean_dec(v_h__3_975_);
lean_dec(v_h__1_973_);
v_package_979_ = lean_ctor_get(v_k_x27_972_, 0);
lean_inc(v_package_979_);
v_target_980_ = lean_ctor_get(v_k_x27_972_, 1);
lean_inc(v_target_980_);
lean_dec_ref_known(v_k_x27_972_, 2);
v___x_981_ = lean_apply_2(v_h__2_974_, v_package_979_, v_target_980_);
return v___x_981_;
}
default: 
{
lean_object* v___x_982_; 
lean_dec(v_h__2_974_);
lean_dec(v_h__1_973_);
v___x_982_ = lean_apply_3(v_h__3_975_, v_k_x27_972_, lean_box(0), lean_box(0));
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_983_, lean_object* v_h__1_984_, lean_object* v_h__2_985_){
_start:
{
if (lean_obj_tag(v_k_x27_983_) == 4)
{
lean_object* v_target_986_; lean_object* v_facet_987_; lean_object* v___x_988_; 
lean_dec(v_h__2_985_);
v_target_986_ = lean_ctor_get(v_k_x27_983_, 0);
lean_inc_ref(v_target_986_);
v_facet_987_ = lean_ctor_get(v_k_x27_983_, 1);
lean_inc(v_facet_987_);
lean_dec_ref_known(v_k_x27_983_, 2);
v___x_988_ = lean_apply_2(v_h__1_984_, v_target_986_, v_facet_987_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; 
lean_dec(v_h__1_984_);
v___x_989_ = lean_apply_2(v_h__2_985_, v_k_x27_983_, lean_box(0));
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_990_, lean_object* v_k_x27_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_){
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
