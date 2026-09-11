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
static lean_once_cell_t l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_value;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg(){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___boxed(lean_object* v___dummy_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
return v_res_379_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0(void){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_383_);
lean_dec_ref(v_s_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
lean_object* v_it_391_; lean_object* v_startInclusive_392_; lean_object* v_endExclusive_393_; 
if (lean_obj_tag(v_a_388_) == 0)
{
lean_object* v_currPos_397_; lean_object* v_searcher_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_421_; 
v_currPos_397_ = lean_ctor_get(v_a_388_, 0);
v_searcher_398_ = lean_ctor_get(v_a_388_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_388_);
if (v_isSharedCheck_421_ == 0)
{
v___x_400_ = v_a_388_;
v_isShared_401_ = v_isSharedCheck_421_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_searcher_398_);
lean_inc(v_currPos_397_);
lean_dec(v_a_388_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_421_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint8_t v_decide_402_; 
v_decide_402_ = lean_nat_dec_eq(v_searcher_398_, v___x_387_);
if (v_decide_402_ == 0)
{
uint32_t v___x_403_; uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_403_ = 47;
v___x_404_ = lean_string_utf8_get_fast(v_s_385_, v_searcher_398_);
v___x_405_ = lean_uint32_dec_eq(v___x_404_, v___x_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_string_utf8_next_fast(v_s_385_, v_searcher_398_);
lean_dec(v_searcher_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_406_);
v___x_408_ = v___x_400_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_currPos_397_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v_a_388_ = v___x_408_;
goto _start;
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_slice_414_; lean_object* v_nextIt_416_; 
v___x_411_ = lean_string_utf8_next_fast(v_s_385_, v_searcher_398_);
v___x_412_ = lean_nat_sub(v___x_411_, v_searcher_398_);
v___x_413_ = lean_nat_add(v_searcher_398_, v___x_412_);
lean_dec(v___x_412_);
v_slice_414_ = l_String_Slice_subslice_x21(v___x_386_, v_currPos_397_, v_searcher_398_);
lean_inc(v___x_413_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_413_);
lean_ctor_set(v___x_400_, 0, v___x_413_);
v_nextIt_416_ = v___x_400_;
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
v_it_391_ = v_nextIt_416_;
v_startInclusive_392_ = v_startInclusive_417_;
v_endExclusive_393_ = v_endExclusive_418_;
goto v___jp_390_;
}
}
}
else
{
lean_object* v___x_420_; 
lean_del_object(v___x_400_);
lean_dec(v_searcher_398_);
v___x_420_ = lean_box(1);
lean_inc(v___x_387_);
v_it_391_ = v___x_420_;
v_startInclusive_392_ = v_currPos_397_;
v_endExclusive_393_ = v___x_387_;
goto v___jp_390_;
}
}
}
else
{
lean_dec(v___x_387_);
lean_dec_ref(v_s_385_);
return v_b_389_;
}
v___jp_390_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc_ref(v_s_385_);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v_s_385_);
lean_ctor_set(v___x_394_, 1, v_startInclusive_392_);
lean_ctor_set(v___x_394_, 2, v_endExclusive_393_);
v___x_395_ = lean_array_push(v_b_389_, v___x_394_);
v_a_388_ = v_it_391_;
v_b_389_ = v___x_395_;
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
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_438_ = lean_string_utf8_byte_size(v___x_437_);
return v___x_438_;
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
v___x_447_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0);
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
lean_object* v_str_456_; lean_object* v_startInclusive_457_; lean_object* v_endExclusive_458_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_str_456_ = lean_ctor_get(v_head_451_, 0);
v_startInclusive_457_ = lean_ctor_get(v_head_451_, 1);
v_endExclusive_458_ = lean_ctor_get(v_head_451_, 2);
v___x_475_ = lean_nat_sub(v_endExclusive_458_, v_startInclusive_457_);
v___x_476_ = lean_nat_dec_eq(v___x_475_, v___x_444_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_478_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6);
v___x_479_ = lean_nat_dec_le(v___x_478_, v___x_475_);
lean_dec(v___x_475_);
if (v___x_479_ == 0)
{
goto v___jp_459_;
}
else
{
uint8_t v___x_480_; 
v___x_480_ = lean_string_memcmp(v_str_456_, v___x_477_, v_startInclusive_457_, v___x_444_, v___x_478_);
if (v___x_480_ == 0)
{
goto v___jp_459_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
lean_inc(v_endExclusive_458_);
lean_inc(v_startInclusive_457_);
lean_inc_ref(v_str_456_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = l_String_Slice_Pos_nextn(v_head_451_, v___x_444_, v___x_481_);
lean_dec(v_head_451_);
v___x_483_ = lean_nat_add(v_startInclusive_457_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v_startInclusive_457_);
v___x_484_ = lean_nat_sub(v_endExclusive_458_, v___x_483_);
v___x_485_ = lean_nat_dec_eq(v___x_484_, v___x_444_);
lean_dec(v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_string_utf8_extract_fast(v_str_456_, v___x_483_, v_endExclusive_458_);
lean_dec(v_endExclusive_458_);
lean_dec(v___x_483_);
lean_dec_ref(v_str_456_);
v___x_487_ = l_Lake_stringToLegalOrSimpleName(v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v___x_483_);
lean_dec(v_endExclusive_458_);
lean_dec_ref(v_str_456_);
v___x_490_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7));
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_491_; 
lean_dec(v___x_475_);
lean_dec(v_head_451_);
v___x_491_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7));
return v___x_491_;
}
v___jp_459_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_460_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_461_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_462_ = lean_nat_sub(v_endExclusive_458_, v_startInclusive_457_);
v___x_463_ = lean_nat_dec_le(v___x_461_, v___x_462_);
lean_dec(v___x_462_);
if (v___x_463_ == 0)
{
goto v___jp_453_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_string_memcmp(v_str_456_, v___x_460_, v_startInclusive_457_, v___x_444_, v___x_461_);
if (v___x_464_ == 0)
{
goto v___jp_453_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
lean_inc(v_endExclusive_458_);
lean_inc(v_startInclusive_457_);
lean_inc_ref(v_str_456_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = l_String_Slice_Pos_nextn(v_head_451_, v___x_444_, v___x_465_);
lean_dec(v_head_451_);
v___x_467_ = lean_nat_add(v_startInclusive_457_, v___x_466_);
lean_dec(v___x_466_);
lean_dec(v_startInclusive_457_);
v___x_468_ = lean_nat_sub(v_endExclusive_458_, v___x_467_);
v___x_469_ = lean_nat_dec_eq(v___x_468_, v___x_444_);
lean_dec(v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = lean_string_utf8_extract_fast(v_str_456_, v___x_467_, v_endExclusive_458_);
lean_dec(v_endExclusive_458_);
lean_dec(v___x_467_);
lean_dec_ref(v_str_456_);
v___x_471_ = l_Lake_stringToLegalOrSimpleName(v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_467_);
lean_dec(v_endExclusive_458_);
lean_dec_ref(v_str_456_);
v___x_474_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v_head_492_; lean_object* v_tail_493_; lean_object* v_str_495_; lean_object* v_startInclusive_496_; lean_object* v_endExclusive_497_; 
v_head_492_ = lean_ctor_get(v_tail_452_, 0);
lean_inc(v_head_492_);
v_tail_493_ = lean_ctor_get(v_tail_452_, 1);
lean_inc(v_tail_493_);
lean_dec_ref_known(v_tail_452_, 2);
if (lean_obj_tag(v_tail_493_) == 0)
{
lean_object* v_str_505_; lean_object* v_startInclusive_506_; lean_object* v_endExclusive_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_str_505_ = lean_ctor_get(v_head_451_, 0);
lean_inc_ref(v_str_505_);
v_startInclusive_506_ = lean_ctor_get(v_head_451_, 1);
lean_inc(v_startInclusive_506_);
v_endExclusive_507_ = lean_ctor_get(v_head_451_, 2);
lean_inc(v_endExclusive_507_);
v___x_508_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_509_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6);
v___x_510_ = lean_nat_sub(v_endExclusive_507_, v_startInclusive_506_);
v___x_511_ = lean_nat_dec_le(v___x_509_, v___x_510_);
lean_dec(v___x_510_);
if (v___x_511_ == 0)
{
lean_dec(v_head_451_);
v_str_495_ = v_str_505_;
v_startInclusive_496_ = v_startInclusive_506_;
v_endExclusive_497_ = v_endExclusive_507_;
goto v___jp_494_;
}
else
{
uint8_t v___x_512_; 
v___x_512_ = lean_string_memcmp(v_str_505_, v___x_508_, v_startInclusive_506_, v___x_444_, v___x_509_);
if (v___x_512_ == 0)
{
lean_dec(v_head_451_);
v_str_495_ = v_str_505_;
v_startInclusive_496_ = v_startInclusive_506_;
v_endExclusive_497_ = v_endExclusive_507_;
goto v___jp_494_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = l_String_Slice_Pos_nextn(v_head_451_, v___x_444_, v___x_513_);
lean_dec(v_head_451_);
v___x_515_ = lean_nat_add(v_startInclusive_506_, v___x_514_);
lean_dec(v___x_514_);
lean_dec(v_startInclusive_506_);
v_str_495_ = v_str_505_;
v_startInclusive_496_ = v___x_515_;
v_endExclusive_497_ = v_endExclusive_507_;
goto v___jp_494_;
}
}
}
else
{
lean_dec(v_tail_493_);
lean_dec(v_head_492_);
lean_dec(v_head_451_);
goto v___jp_442_;
}
v___jp_494_:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_nat_sub(v_endExclusive_497_, v_startInclusive_496_);
v___x_499_ = lean_nat_dec_eq(v___x_498_, v___x_444_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_string_utf8_extract_fast(v_str_495_, v_startInclusive_496_, v_endExclusive_497_);
lean_dec(v_endExclusive_497_);
lean_dec(v_startInclusive_496_);
lean_dec_ref(v_str_495_);
v___x_501_ = l_Lake_stringToLegalOrSimpleName(v___x_500_);
v___x_502_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_501_, v_head_492_);
lean_dec(v_head_492_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_endExclusive_497_);
lean_dec(v_startInclusive_496_);
lean_dec_ref(v_str_495_);
v___x_503_ = lean_box(0);
v___x_504_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_503_, v_head_492_);
lean_dec(v_head_492_);
return v___x_504_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_inst_519_, lean_object* v_R_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_516_, v___x_517_, v___x_518_, v_a_521_, v_b_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_inst_527_, lean_object* v_R_528_, lean_object* v_a_529_, lean_object* v_b_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_524_, v___x_525_, v___x_526_, v_inst_527_, v_R_528_, v_a_529_, v_b_530_);
lean_dec_ref(v___x_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg___boxed(lean_object* v___dummy_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v_res_535_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_539_);
lean_dec_ref(v_s_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_panic_fn_borrowed(v___x_544_, v_msg_542_);
lean_dec_ref_known(v___x_544_, 1);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v_a_549_, lean_object* v_b_550_){
_start:
{
lean_object* v_it_552_; lean_object* v_startInclusive_553_; lean_object* v_endExclusive_554_; 
if (lean_obj_tag(v_a_549_) == 0)
{
lean_object* v_currPos_559_; lean_object* v_searcher_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_583_; 
v_currPos_559_ = lean_ctor_get(v_a_549_, 0);
v_searcher_560_ = lean_ctor_get(v_a_549_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_583_ == 0)
{
v___x_562_ = v_a_549_;
v_isShared_563_ = v_isSharedCheck_583_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_searcher_560_);
lean_inc(v_currPos_559_);
lean_dec(v_a_549_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_583_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
uint8_t v_decide_564_; 
v_decide_564_ = lean_nat_dec_eq(v_searcher_560_, v___x_548_);
if (v_decide_564_ == 0)
{
uint32_t v___x_565_; uint32_t v___x_566_; uint8_t v___x_567_; 
v___x_565_ = 58;
v___x_566_ = lean_string_utf8_get_fast(v_s_546_, v_searcher_560_);
v___x_567_ = lean_uint32_dec_eq(v___x_566_, v___x_565_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_string_utf8_next_fast(v_s_546_, v_searcher_560_);
lean_dec(v_searcher_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_568_);
v___x_570_ = v___x_562_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_currPos_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v_a_549_ = v___x_570_;
goto _start;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_slice_576_; lean_object* v_nextIt_578_; 
v___x_573_ = lean_string_utf8_next_fast(v_s_546_, v_searcher_560_);
v___x_574_ = lean_nat_sub(v___x_573_, v_searcher_560_);
v___x_575_ = lean_nat_add(v_searcher_560_, v___x_574_);
lean_dec(v___x_574_);
v_slice_576_ = l_String_Slice_subslice_x21(v___x_547_, v_currPos_559_, v_searcher_560_);
lean_inc(v___x_575_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_575_);
lean_ctor_set(v___x_562_, 0, v___x_575_);
v_nextIt_578_ = v___x_562_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_575_);
v_nextIt_578_ = v_reuseFailAlloc_581_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v_startInclusive_579_; lean_object* v_endExclusive_580_; 
v_startInclusive_579_ = lean_ctor_get(v_slice_576_, 0);
lean_inc(v_startInclusive_579_);
v_endExclusive_580_ = lean_ctor_get(v_slice_576_, 1);
lean_inc(v_endExclusive_580_);
lean_dec_ref(v_slice_576_);
v_it_552_ = v_nextIt_578_;
v_startInclusive_553_ = v_startInclusive_579_;
v_endExclusive_554_ = v_endExclusive_580_;
goto v___jp_551_;
}
}
}
else
{
lean_object* v___x_582_; 
lean_del_object(v___x_562_);
lean_dec(v_searcher_560_);
v___x_582_ = lean_box(1);
lean_inc(v___x_548_);
v_it_552_ = v___x_582_;
v_startInclusive_553_ = v_currPos_559_;
v_endExclusive_554_ = v___x_548_;
goto v___jp_551_;
}
}
}
else
{
lean_dec(v___x_548_);
lean_dec_ref(v_s_546_);
return v_b_550_;
}
v___jp_551_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_inc_ref(v_s_546_);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v_s_546_);
lean_ctor_set(v___x_555_, 1, v_startInclusive_553_);
lean_ctor_set(v___x_555_, 2, v_endExclusive_554_);
v___x_556_ = l_String_Slice_toString(v___x_555_);
lean_dec_ref_known(v___x_555_, 3);
v___x_557_ = lean_array_push(v_b_550_, v___x_556_);
v_a_549_ = v_it_552_;
v_b_550_ = v___x_557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_584_, v___x_585_, v___x_586_, v_a_587_, v_b_588_);
lean_dec_ref(v___x_585_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_x_593_);
return v___x_595_;
}
else
{
lean_object* v_head_596_; lean_object* v_tail_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v_head_596_ = lean_ctor_get(v_x_594_, 0);
v_tail_597_ = lean_ctor_get(v_x_594_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_610_ == 0)
{
v___x_599_ = v_x_594_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_tail_597_);
lean_inc(v_head_596_);
lean_dec(v_x_594_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_string_utf8_byte_size(v_head_596_);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_nat_dec_eq(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = l_Lake_stringToLegalOrSimpleName(v_head_596_);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 4);
lean_ctor_set(v___x_599_, 1, v___x_604_);
lean_ctor_set(v___x_599_, 0, v_x_593_);
v___x_606_ = v___x_599_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_x_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_604_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_x_593_ = v___x_606_;
v_x_594_ = v_tail_597_;
goto _start;
}
}
else
{
lean_object* v___x_609_; 
lean_del_object(v___x_599_);
lean_dec(v_tail_597_);
lean_dec(v_head_596_);
lean_dec_ref(v_x_593_);
v___x_609_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_609_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_616_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_617_ = lean_unsigned_to_nat(4u);
v___x_618_ = lean_unsigned_to_nat(65u);
v___x_619_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_620_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_621_ = l_mkPanicMessageWithDecl(v___x_620_, v___x_619_, v___x_618_, v___x_617_, v___x_616_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_string_utf8_byte_size(v_s_625_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_inc_ref(v_s_625_);
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v_s_625_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_626_);
v___x_630_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
v___x_631_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_632_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_625_, v___x_629_, v___x_626_, v___x_630_, v___x_631_);
lean_dec_ref_known(v___x_629_, 3);
v___x_633_ = lean_array_to_list(v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_635_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_634_);
return v___x_635_;
}
else
{
lean_object* v_head_636_; lean_object* v_tail_637_; lean_object* v___x_638_; 
v_head_636_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_head_636_);
v_tail_637_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_tail_637_);
lean_dec_ref_known(v___x_633_, 2);
v___x_638_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec(v_tail_637_);
return v___x_638_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_639_, v_tail_637_);
return v___x_640_;
}
}
}
else
{
lean_object* v___x_641_; 
lean_dec_ref(v_s_625_);
v___x_641_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_642_, lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v_inst_645_, lean_object* v_R_646_, lean_object* v_a_647_, lean_object* v_b_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_642_, v___x_643_, v___x_644_, v_a_647_, v_b_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_inst_653_, lean_object* v_R_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_650_, v___x_651_, v___x_652_, v_inst_653_, v_R_654_, v_a_655_, v_b_656_);
lean_dec_ref(v___x_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_658_){
_start:
{
switch(lean_obj_tag(v_p_658_))
{
case 0:
{
return v_p_658_;
}
case 2:
{
lean_object* v_pre_659_; 
v_pre_659_ = lean_ctor_get(v_p_658_, 0);
if (lean_obj_tag(v_pre_659_) == 0)
{
return v_pre_659_;
}
else
{
lean_inc(v_pre_659_);
return v_pre_659_;
}
}
default: 
{
lean_inc(v_p_658_);
return v_p_658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_660_);
lean_dec(v_p_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_665_){
_start:
{
switch(lean_obj_tag(v_x_665_))
{
case 0:
{
lean_object* v_module_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_module_666_ = lean_ctor_get(v_x_665_, 0);
lean_inc(v_module_666_);
lean_dec_ref_known(v_x_665_, 1);
v___x_667_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_668_ = 1;
v___x_669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_666_, v___x_668_);
v___x_670_ = lean_string_append(v___x_667_, v___x_669_);
lean_dec_ref(v___x_669_);
return v___x_670_;
}
case 1:
{
lean_object* v_package_671_; lean_object* v___x_672_; 
v_package_671_ = lean_ctor_get(v_x_665_, 0);
lean_inc(v_package_671_);
lean_dec_ref_known(v_x_665_, 1);
v___x_672_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_671_);
lean_dec(v_package_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_673_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_675_ = 1;
v___x_676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_672_, v___x_675_);
v___x_677_ = lean_string_append(v___x_674_, v___x_676_);
lean_dec_ref(v___x_676_);
return v___x_677_;
}
}
case 2:
{
lean_object* v_package_678_; lean_object* v_module_679_; lean_object* v___x_680_; 
v_package_678_ = lean_ctor_get(v_x_665_, 0);
lean_inc(v_package_678_);
v_module_679_ = lean_ctor_get(v_x_665_, 1);
lean_inc(v_module_679_);
lean_dec_ref_known(v_x_665_, 2);
v___x_680_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_678_);
lean_dec(v_package_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_682_ = 1;
v___x_683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_679_, v___x_682_);
v___x_684_ = lean_string_append(v___x_681_, v___x_683_);
lean_dec_ref(v___x_683_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_685_ = 1;
v___x_686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_680_, v___x_685_);
v___x_687_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_688_ = lean_string_append(v___x_686_, v___x_687_);
v___x_689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_679_, v___x_685_);
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
lean_dec_ref(v___x_689_);
return v___x_690_;
}
}
case 3:
{
lean_object* v_package_691_; lean_object* v_target_692_; lean_object* v___x_693_; 
v_package_691_ = lean_ctor_get(v_x_665_, 0);
lean_inc(v_package_691_);
v_target_692_ = lean_ctor_get(v_x_665_, 1);
lean_inc(v_target_692_);
lean_dec_ref_known(v_x_665_, 2);
v___x_693_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_691_);
lean_dec(v_package_691_);
if (lean_obj_tag(v___x_693_) == 0)
{
uint8_t v___x_694_; lean_object* v___x_695_; 
v___x_694_ = 1;
v___x_695_ = l_Lean_Name_toString(v_target_692_, v___x_694_);
return v___x_695_;
}
else
{
uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_696_ = 1;
v___x_697_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_693_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
v___x_700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_692_, v___x_696_);
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
lean_dec_ref(v___x_700_);
return v___x_701_;
}
}
default: 
{
lean_object* v_target_702_; lean_object* v_facet_703_; uint8_t v___x_704_; 
v_target_702_ = lean_ctor_get(v_x_665_, 0);
lean_inc_ref(v_target_702_);
v_facet_703_ = lean_ctor_get(v_x_665_, 1);
lean_inc(v_facet_703_);
lean_dec_ref_known(v_x_665_, 2);
v___x_704_ = l_Lean_Name_isAnonymous(v_facet_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_705_ = l_Lake_PartialBuildKey_toString(v_target_702_);
v___x_706_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
v___x_708_ = 1;
v___x_709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_703_, v___x_708_);
v___x_710_ = lean_string_append(v___x_707_, v___x_709_);
lean_dec_ref(v___x_709_);
return v___x_710_;
}
else
{
lean_dec(v_facet_703_);
v_x_665_ = v_target_702_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_714_, lean_object* v_facet_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_module_714_);
v___x_717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_facet_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_718_, lean_object* v_facet_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v_package_718_);
v___x_721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_facet_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_722_, lean_object* v_module_723_, lean_object* v_facet_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_725_, 0, v_package_722_);
lean_ctor_set(v___x_725_, 1, v_module_723_);
v___x_726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_facet_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_727_, lean_object* v_target_728_, lean_object* v_facet_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_730_, 0, v_package_727_);
lean_ctor_set(v___x_730_, 1, v_target_728_);
v___x_731_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_facet_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_732_, lean_object* v_target_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_734_, 0, v_package_732_);
lean_ctor_set(v___x_734_, 1, v_target_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_735_){
_start:
{
switch(lean_obj_tag(v_x_735_))
{
case 0:
{
lean_object* v_module_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_module_736_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_module_736_);
lean_dec_ref_known(v_x_735_, 1);
v___x_737_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_738_ = 1;
v___x_739_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_736_, v___x_738_);
v___x_740_ = lean_string_append(v___x_737_, v___x_739_);
lean_dec_ref(v___x_739_);
return v___x_740_;
}
case 1:
{
lean_object* v_package_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_package_741_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_package_741_);
lean_dec_ref_known(v_x_735_, 1);
v___x_742_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_743_ = l_Lean_Name_getPrefix(v_package_741_);
lean_dec(v_package_741_);
v___x_744_ = 1;
v___x_745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_743_, v___x_744_);
v___x_746_ = lean_string_append(v___x_742_, v___x_745_);
lean_dec_ref(v___x_745_);
return v___x_746_;
}
case 2:
{
lean_object* v_package_747_; lean_object* v_module_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_package_747_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_package_747_);
v_module_748_ = lean_ctor_get(v_x_735_, 1);
lean_inc(v_module_748_);
lean_dec_ref_known(v_x_735_, 2);
v___x_749_ = l_Lean_Name_getPrefix(v_package_747_);
lean_dec(v_package_747_);
v___x_750_ = 1;
v___x_751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_749_, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_748_, v___x_750_);
v___x_755_ = lean_string_append(v___x_753_, v___x_754_);
lean_dec_ref(v___x_754_);
return v___x_755_;
}
case 3:
{
lean_object* v_package_756_; lean_object* v_target_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_package_756_ = lean_ctor_get(v_x_735_, 0);
lean_inc(v_package_756_);
v_target_757_ = lean_ctor_get(v_x_735_, 1);
lean_inc(v_target_757_);
lean_dec_ref_known(v_x_735_, 2);
v___x_758_ = l_Lean_Name_getPrefix(v_package_756_);
lean_dec(v_package_756_);
v___x_759_ = 1;
v___x_760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_758_, v___x_759_);
v___x_761_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_762_ = lean_string_append(v___x_760_, v___x_761_);
v___x_763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_757_, v___x_759_);
v___x_764_ = lean_string_append(v___x_762_, v___x_763_);
lean_dec_ref(v___x_763_);
return v___x_764_;
}
default: 
{
lean_object* v_target_765_; lean_object* v_facet_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_target_765_ = lean_ctor_get(v_x_735_, 0);
lean_inc_ref(v_target_765_);
v_facet_766_ = lean_ctor_get(v_x_735_, 1);
lean_inc(v_facet_766_);
lean_dec_ref_known(v_x_735_, 2);
v___x_767_ = l_Lake_BuildKey_toString(v_target_765_);
v___x_768_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_769_ = lean_string_append(v___x_767_, v___x_768_);
v___x_770_ = l_Lake_Name_eraseHead(v_facet_766_);
v___x_771_ = 1;
v___x_772_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_770_, v___x_771_);
v___x_773_ = lean_string_append(v___x_769_, v___x_772_);
lean_dec_ref(v___x_772_);
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_774_){
_start:
{
lean_object* v_p_776_; lean_object* v_m_777_; 
switch(lean_obj_tag(v_x_774_))
{
case 0:
{
lean_object* v_module_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_module_785_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_module_785_);
lean_dec_ref_known(v_x_774_, 1);
v___x_786_ = 1;
v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_785_, v___x_786_);
return v___x_787_;
}
case 1:
{
lean_object* v_package_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v_package_788_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_package_788_);
lean_dec_ref_known(v_x_774_, 1);
v___x_789_ = l_Lean_Name_getPrefix(v_package_788_);
lean_dec(v_package_788_);
v___x_790_ = 1;
v___x_791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_789_, v___x_790_);
return v___x_791_;
}
case 4:
{
lean_object* v_target_792_; lean_object* v_facet_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_target_792_ = lean_ctor_get(v_x_774_, 0);
lean_inc_ref(v_target_792_);
v_facet_793_ = lean_ctor_get(v_x_774_, 1);
lean_inc(v_facet_793_);
lean_dec_ref_known(v_x_774_, 2);
v___x_794_ = l_Lake_BuildKey_toSimpleString(v_target_792_);
v___x_795_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_796_ = lean_string_append(v___x_794_, v___x_795_);
v___x_797_ = l_Lake_Name_eraseHead(v_facet_793_);
v___x_798_ = 1;
v___x_799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_797_, v___x_798_);
v___x_800_ = lean_string_append(v___x_796_, v___x_799_);
lean_dec_ref(v___x_799_);
return v___x_800_;
}
default: 
{
lean_object* v_package_801_; lean_object* v_module_802_; 
v_package_801_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_package_801_);
v_module_802_ = lean_ctor_get(v_x_774_, 1);
lean_inc(v_module_802_);
lean_dec_ref(v_x_774_);
v_p_776_ = v_package_801_;
v_m_777_ = v_module_802_;
goto v___jp_775_;
}
}
v___jp_775_:
{
lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_778_ = l_Lean_Name_getPrefix(v_p_776_);
lean_dec(v_p_776_);
v___x_779_ = 1;
v___x_780_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_778_, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_782_ = lean_string_append(v___x_780_, v___x_781_);
v___x_783_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_777_, v___x_779_);
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
lean_dec_ref(v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_805_, lean_object* v_k_x27_806_){
_start:
{
switch(lean_obj_tag(v_k_805_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_806_) == 0)
{
lean_object* v_module_807_; lean_object* v_module_808_; uint8_t v___x_809_; 
v_module_807_ = lean_ctor_get(v_k_805_, 0);
v_module_808_ = lean_ctor_get(v_k_x27_806_, 0);
v___x_809_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_807_, v_module_808_);
return v___x_809_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_806_))
{
case 0:
{
uint8_t v___x_811_; 
v___x_811_ = 2;
return v___x_811_;
}
case 1:
{
lean_object* v_package_812_; lean_object* v_package_813_; uint8_t v___x_814_; 
v_package_812_ = lean_ctor_get(v_k_805_, 0);
v_package_813_ = lean_ctor_get(v_k_x27_806_, 0);
v___x_814_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_812_, v_package_813_);
return v___x_814_;
}
default: 
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_806_))
{
case 4:
{
uint8_t v___x_816_; 
v___x_816_ = 0;
return v___x_816_;
}
case 3:
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
case 2:
{
lean_object* v_package_818_; lean_object* v_module_819_; lean_object* v_package_820_; lean_object* v_module_821_; uint8_t v___x_822_; 
v_package_818_ = lean_ctor_get(v_k_805_, 0);
v_module_819_ = lean_ctor_get(v_k_805_, 1);
v_package_820_ = lean_ctor_get(v_k_x27_806_, 0);
v_module_821_ = lean_ctor_get(v_k_x27_806_, 1);
v___x_822_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_819_, v_module_821_);
if (v___x_822_ == 1)
{
uint8_t v___x_823_; 
v___x_823_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_818_, v_package_820_);
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
case 3:
{
switch(lean_obj_tag(v_k_x27_806_))
{
case 4:
{
uint8_t v___x_825_; 
v___x_825_ = 0;
return v___x_825_;
}
case 3:
{
lean_object* v_package_826_; lean_object* v_target_827_; lean_object* v_package_828_; lean_object* v_target_829_; uint8_t v___x_830_; 
v_package_826_ = lean_ctor_get(v_k_805_, 0);
v_target_827_ = lean_ctor_get(v_k_805_, 1);
v_package_828_ = lean_ctor_get(v_k_x27_806_, 0);
v_target_829_ = lean_ctor_get(v_k_x27_806_, 1);
v___x_830_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_826_, v_package_828_);
if (v___x_830_ == 1)
{
uint8_t v___x_831_; 
v___x_831_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_827_, v_target_829_);
return v___x_831_;
}
else
{
return v___x_830_;
}
}
default: 
{
uint8_t v___x_832_; 
v___x_832_ = 2;
return v___x_832_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_806_) == 4)
{
lean_object* v_target_833_; lean_object* v_facet_834_; lean_object* v_target_835_; lean_object* v_facet_836_; uint8_t v___x_837_; 
v_target_833_ = lean_ctor_get(v_k_805_, 0);
v_facet_834_ = lean_ctor_get(v_k_805_, 1);
v_target_835_ = lean_ctor_get(v_k_x27_806_, 0);
v_facet_836_ = lean_ctor_get(v_k_x27_806_, 1);
v___x_837_ = l_Lake_BuildKey_quickCmp(v_target_833_, v_target_835_);
if (v___x_837_ == 1)
{
uint8_t v___x_838_; 
v___x_838_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_834_, v_facet_836_);
return v___x_838_;
}
else
{
return v___x_837_;
}
}
else
{
uint8_t v___x_839_; 
v___x_839_ = 2;
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_840_, lean_object* v_k_x27_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lake_BuildKey_quickCmp(v_k_840_, v_k_x27_841_);
lean_dec_ref(v_k_x27_841_);
lean_dec_ref(v_k_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_844_, lean_object* v_h__1_845_, lean_object* v_h__2_846_, lean_object* v_h__3_847_, lean_object* v_h__4_848_, lean_object* v_h__5_849_){
_start:
{
switch(lean_obj_tag(v_x_844_))
{
case 0:
{
lean_object* v_module_850_; lean_object* v___x_851_; 
lean_dec(v_h__5_849_);
lean_dec(v_h__4_848_);
lean_dec(v_h__3_847_);
lean_dec(v_h__2_846_);
v_module_850_ = lean_ctor_get(v_x_844_, 0);
lean_inc(v_module_850_);
lean_dec_ref_known(v_x_844_, 1);
v___x_851_ = lean_apply_1(v_h__1_845_, v_module_850_);
return v___x_851_;
}
case 1:
{
lean_object* v_package_852_; lean_object* v___x_853_; 
lean_dec(v_h__5_849_);
lean_dec(v_h__4_848_);
lean_dec(v_h__3_847_);
lean_dec(v_h__1_845_);
v_package_852_ = lean_ctor_get(v_x_844_, 0);
lean_inc(v_package_852_);
lean_dec_ref_known(v_x_844_, 1);
v___x_853_ = lean_apply_1(v_h__2_846_, v_package_852_);
return v___x_853_;
}
case 2:
{
lean_object* v_package_854_; lean_object* v_module_855_; lean_object* v___x_856_; 
lean_dec(v_h__5_849_);
lean_dec(v_h__4_848_);
lean_dec(v_h__2_846_);
lean_dec(v_h__1_845_);
v_package_854_ = lean_ctor_get(v_x_844_, 0);
lean_inc(v_package_854_);
v_module_855_ = lean_ctor_get(v_x_844_, 1);
lean_inc(v_module_855_);
lean_dec_ref_known(v_x_844_, 2);
v___x_856_ = lean_apply_2(v_h__3_847_, v_package_854_, v_module_855_);
return v___x_856_;
}
case 3:
{
lean_object* v_package_857_; lean_object* v_target_858_; lean_object* v___x_859_; 
lean_dec(v_h__5_849_);
lean_dec(v_h__3_847_);
lean_dec(v_h__2_846_);
lean_dec(v_h__1_845_);
v_package_857_ = lean_ctor_get(v_x_844_, 0);
lean_inc(v_package_857_);
v_target_858_ = lean_ctor_get(v_x_844_, 1);
lean_inc(v_target_858_);
lean_dec_ref_known(v_x_844_, 2);
v___x_859_ = lean_apply_2(v_h__4_848_, v_package_857_, v_target_858_);
return v___x_859_;
}
default: 
{
lean_object* v_target_860_; lean_object* v_facet_861_; lean_object* v___x_862_; 
lean_dec(v_h__4_848_);
lean_dec(v_h__3_847_);
lean_dec(v_h__2_846_);
lean_dec(v_h__1_845_);
v_target_860_ = lean_ctor_get(v_x_844_, 0);
lean_inc_ref(v_target_860_);
v_facet_861_ = lean_ctor_get(v_x_844_, 1);
lean_inc(v_facet_861_);
lean_dec_ref_known(v_x_844_, 2);
v___x_862_ = lean_apply_2(v_h__5_849_, v_target_860_, v_facet_861_);
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_863_, lean_object* v_x_864_, lean_object* v_h__1_865_, lean_object* v_h__2_866_, lean_object* v_h__3_867_, lean_object* v_h__4_868_, lean_object* v_h__5_869_){
_start:
{
switch(lean_obj_tag(v_x_864_))
{
case 0:
{
lean_object* v_module_870_; lean_object* v___x_871_; 
lean_dec(v_h__5_869_);
lean_dec(v_h__4_868_);
lean_dec(v_h__3_867_);
lean_dec(v_h__2_866_);
v_module_870_ = lean_ctor_get(v_x_864_, 0);
lean_inc(v_module_870_);
lean_dec_ref_known(v_x_864_, 1);
v___x_871_ = lean_apply_1(v_h__1_865_, v_module_870_);
return v___x_871_;
}
case 1:
{
lean_object* v_package_872_; lean_object* v___x_873_; 
lean_dec(v_h__5_869_);
lean_dec(v_h__4_868_);
lean_dec(v_h__3_867_);
lean_dec(v_h__1_865_);
v_package_872_ = lean_ctor_get(v_x_864_, 0);
lean_inc(v_package_872_);
lean_dec_ref_known(v_x_864_, 1);
v___x_873_ = lean_apply_1(v_h__2_866_, v_package_872_);
return v___x_873_;
}
case 2:
{
lean_object* v_package_874_; lean_object* v_module_875_; lean_object* v___x_876_; 
lean_dec(v_h__5_869_);
lean_dec(v_h__4_868_);
lean_dec(v_h__2_866_);
lean_dec(v_h__1_865_);
v_package_874_ = lean_ctor_get(v_x_864_, 0);
lean_inc(v_package_874_);
v_module_875_ = lean_ctor_get(v_x_864_, 1);
lean_inc(v_module_875_);
lean_dec_ref_known(v_x_864_, 2);
v___x_876_ = lean_apply_2(v_h__3_867_, v_package_874_, v_module_875_);
return v___x_876_;
}
case 3:
{
lean_object* v_package_877_; lean_object* v_target_878_; lean_object* v___x_879_; 
lean_dec(v_h__5_869_);
lean_dec(v_h__3_867_);
lean_dec(v_h__2_866_);
lean_dec(v_h__1_865_);
v_package_877_ = lean_ctor_get(v_x_864_, 0);
lean_inc(v_package_877_);
v_target_878_ = lean_ctor_get(v_x_864_, 1);
lean_inc(v_target_878_);
lean_dec_ref_known(v_x_864_, 2);
v___x_879_ = lean_apply_2(v_h__4_868_, v_package_877_, v_target_878_);
return v___x_879_;
}
default: 
{
lean_object* v_target_880_; lean_object* v_facet_881_; lean_object* v___x_882_; 
lean_dec(v_h__4_868_);
lean_dec(v_h__3_867_);
lean_dec(v_h__2_866_);
lean_dec(v_h__1_865_);
v_target_880_ = lean_ctor_get(v_x_864_, 0);
lean_inc_ref(v_target_880_);
v_facet_881_ = lean_ctor_get(v_x_864_, 1);
lean_inc(v_facet_881_);
lean_dec_ref_known(v_x_864_, 2);
v___x_882_ = lean_apply_2(v_h__5_869_, v_target_880_, v_facet_881_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_883_, lean_object* v_h__1_884_, lean_object* v_h__2_885_){
_start:
{
if (lean_obj_tag(v_k_x27_883_) == 0)
{
lean_object* v_module_886_; lean_object* v___x_887_; 
lean_dec(v_h__2_885_);
v_module_886_ = lean_ctor_get(v_k_x27_883_, 0);
lean_inc(v_module_886_);
lean_dec_ref_known(v_k_x27_883_, 1);
v___x_887_ = lean_apply_1(v_h__1_884_, v_module_886_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
lean_dec(v_h__1_884_);
v___x_888_ = lean_apply_2(v_h__2_885_, v_k_x27_883_, lean_box(0));
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_889_, lean_object* v_k_x27_890_, lean_object* v_h__1_891_, lean_object* v_h__2_892_){
_start:
{
if (lean_obj_tag(v_k_x27_890_) == 0)
{
lean_object* v_module_893_; lean_object* v___x_894_; 
lean_dec(v_h__2_892_);
v_module_893_ = lean_ctor_get(v_k_x27_890_, 0);
lean_inc(v_module_893_);
lean_dec_ref_known(v_k_x27_890_, 1);
v___x_894_ = lean_apply_1(v_h__1_891_, v_module_893_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; 
lean_dec(v_h__1_891_);
v___x_895_ = lean_apply_2(v_h__2_892_, v_k_x27_890_, lean_box(0));
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_896_, lean_object* v_h__1_897_, lean_object* v_h__2_898_, lean_object* v_h__3_899_){
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_905_, lean_object* v_k_x27_906_, lean_object* v_h__1_907_, lean_object* v_h__2_908_, lean_object* v_h__3_909_){
_start:
{
switch(lean_obj_tag(v_k_x27_906_))
{
case 0:
{
lean_object* v_module_910_; lean_object* v___x_911_; 
lean_dec(v_h__3_909_);
lean_dec(v_h__2_908_);
v_module_910_ = lean_ctor_get(v_k_x27_906_, 0);
lean_inc(v_module_910_);
lean_dec_ref_known(v_k_x27_906_, 1);
v___x_911_ = lean_apply_1(v_h__1_907_, v_module_910_);
return v___x_911_;
}
case 1:
{
lean_object* v_package_912_; lean_object* v___x_913_; 
lean_dec(v_h__3_909_);
lean_dec(v_h__1_907_);
v_package_912_ = lean_ctor_get(v_k_x27_906_, 0);
lean_inc(v_package_912_);
lean_dec_ref_known(v_k_x27_906_, 1);
v___x_913_ = lean_apply_1(v_h__2_908_, v_package_912_);
return v___x_913_;
}
default: 
{
lean_object* v___x_914_; 
lean_dec(v_h__2_908_);
lean_dec(v_h__1_907_);
v___x_914_ = lean_apply_3(v_h__3_909_, v_k_x27_906_, lean_box(0), lean_box(0));
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_915_, lean_object* v_h__1_916_, lean_object* v_h__2_917_, lean_object* v_h__3_918_, lean_object* v_h__4_919_){
_start:
{
switch(lean_obj_tag(v_k_x27_915_))
{
case 4:
{
lean_object* v_target_920_; lean_object* v_facet_921_; lean_object* v___x_922_; 
lean_dec(v_h__4_919_);
lean_dec(v_h__3_918_);
lean_dec(v_h__2_917_);
v_target_920_ = lean_ctor_get(v_k_x27_915_, 0);
lean_inc_ref(v_target_920_);
v_facet_921_ = lean_ctor_get(v_k_x27_915_, 1);
lean_inc(v_facet_921_);
lean_dec_ref_known(v_k_x27_915_, 2);
v___x_922_ = lean_apply_2(v_h__1_916_, v_target_920_, v_facet_921_);
return v___x_922_;
}
case 3:
{
lean_object* v_package_923_; lean_object* v_target_924_; lean_object* v___x_925_; 
lean_dec(v_h__4_919_);
lean_dec(v_h__3_918_);
lean_dec(v_h__1_916_);
v_package_923_ = lean_ctor_get(v_k_x27_915_, 0);
lean_inc(v_package_923_);
v_target_924_ = lean_ctor_get(v_k_x27_915_, 1);
lean_inc(v_target_924_);
lean_dec_ref_known(v_k_x27_915_, 2);
v___x_925_ = lean_apply_2(v_h__2_917_, v_package_923_, v_target_924_);
return v___x_925_;
}
case 2:
{
lean_object* v_package_926_; lean_object* v_module_927_; lean_object* v___x_928_; 
lean_dec(v_h__4_919_);
lean_dec(v_h__2_917_);
lean_dec(v_h__1_916_);
v_package_926_ = lean_ctor_get(v_k_x27_915_, 0);
lean_inc(v_package_926_);
v_module_927_ = lean_ctor_get(v_k_x27_915_, 1);
lean_inc(v_module_927_);
lean_dec_ref_known(v_k_x27_915_, 2);
v___x_928_ = lean_apply_2(v_h__3_918_, v_package_926_, v_module_927_);
return v___x_928_;
}
default: 
{
lean_object* v___x_929_; 
lean_dec(v_h__3_918_);
lean_dec(v_h__2_917_);
lean_dec(v_h__1_916_);
v___x_929_ = lean_apply_4(v_h__4_919_, v_k_x27_915_, lean_box(0), lean_box(0), lean_box(0));
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_930_, lean_object* v_k_x27_931_, lean_object* v_h__1_932_, lean_object* v_h__2_933_, lean_object* v_h__3_934_, lean_object* v_h__4_935_){
_start:
{
switch(lean_obj_tag(v_k_x27_931_))
{
case 4:
{
lean_object* v_target_936_; lean_object* v_facet_937_; lean_object* v___x_938_; 
lean_dec(v_h__4_935_);
lean_dec(v_h__3_934_);
lean_dec(v_h__2_933_);
v_target_936_ = lean_ctor_get(v_k_x27_931_, 0);
lean_inc_ref(v_target_936_);
v_facet_937_ = lean_ctor_get(v_k_x27_931_, 1);
lean_inc(v_facet_937_);
lean_dec_ref_known(v_k_x27_931_, 2);
v___x_938_ = lean_apply_2(v_h__1_932_, v_target_936_, v_facet_937_);
return v___x_938_;
}
case 3:
{
lean_object* v_package_939_; lean_object* v_target_940_; lean_object* v___x_941_; 
lean_dec(v_h__4_935_);
lean_dec(v_h__3_934_);
lean_dec(v_h__1_932_);
v_package_939_ = lean_ctor_get(v_k_x27_931_, 0);
lean_inc(v_package_939_);
v_target_940_ = lean_ctor_get(v_k_x27_931_, 1);
lean_inc(v_target_940_);
lean_dec_ref_known(v_k_x27_931_, 2);
v___x_941_ = lean_apply_2(v_h__2_933_, v_package_939_, v_target_940_);
return v___x_941_;
}
case 2:
{
lean_object* v_package_942_; lean_object* v_module_943_; lean_object* v___x_944_; 
lean_dec(v_h__4_935_);
lean_dec(v_h__2_933_);
lean_dec(v_h__1_932_);
v_package_942_ = lean_ctor_get(v_k_x27_931_, 0);
lean_inc(v_package_942_);
v_module_943_ = lean_ctor_get(v_k_x27_931_, 1);
lean_inc(v_module_943_);
lean_dec_ref_known(v_k_x27_931_, 2);
v___x_944_ = lean_apply_2(v_h__3_934_, v_package_942_, v_module_943_);
return v___x_944_;
}
default: 
{
lean_object* v___x_945_; 
lean_dec(v_h__3_934_);
lean_dec(v_h__2_933_);
lean_dec(v_h__1_932_);
v___x_945_ = lean_apply_4(v_h__4_935_, v_k_x27_931_, lean_box(0), lean_box(0), lean_box(0));
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_946_, lean_object* v_h__1_947_, lean_object* v_h__2_948_){
_start:
{
if (v_x_946_ == 1)
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_h__2_948_);
v___x_949_ = lean_box(0);
v___x_950_ = lean_apply_1(v_h__1_947_, v___x_949_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_h__1_947_);
v___x_951_ = lean_box(v_x_946_);
v___x_952_ = lean_apply_2(v_h__2_948_, v___x_951_, lean_box(0));
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_){
_start:
{
uint8_t v_x_13__boxed_956_; lean_object* v_res_957_; 
v_x_13__boxed_956_ = lean_unbox(v_x_953_);
v_res_957_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_13__boxed_956_, v_h__1_954_, v_h__2_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_958_, uint8_t v_x_959_, lean_object* v_h__1_960_, lean_object* v_h__2_961_){
_start:
{
if (v_x_959_ == 1)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_h__2_961_);
v___x_962_ = lean_box(0);
v___x_963_ = lean_apply_1(v_h__1_960_, v___x_962_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_h__1_960_);
v___x_964_ = lean_box(v_x_959_);
v___x_965_ = lean_apply_2(v_h__2_961_, v___x_964_, lean_box(0));
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_966_, lean_object* v_x_967_, lean_object* v_h__1_968_, lean_object* v_h__2_969_){
_start:
{
uint8_t v_x_24__boxed_970_; lean_object* v_res_971_; 
v_x_24__boxed_970_ = lean_unbox(v_x_967_);
v_res_971_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_966_, v_x_24__boxed_970_, v_h__1_968_, v_h__2_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_){
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_983_, lean_object* v_k_x27_984_, lean_object* v_h__1_985_, lean_object* v_h__2_986_, lean_object* v_h__3_987_){
_start:
{
switch(lean_obj_tag(v_k_x27_984_))
{
case 4:
{
lean_object* v_target_988_; lean_object* v_facet_989_; lean_object* v___x_990_; 
lean_dec(v_h__3_987_);
lean_dec(v_h__2_986_);
v_target_988_ = lean_ctor_get(v_k_x27_984_, 0);
lean_inc_ref(v_target_988_);
v_facet_989_ = lean_ctor_get(v_k_x27_984_, 1);
lean_inc(v_facet_989_);
lean_dec_ref_known(v_k_x27_984_, 2);
v___x_990_ = lean_apply_2(v_h__1_985_, v_target_988_, v_facet_989_);
return v___x_990_;
}
case 3:
{
lean_object* v_package_991_; lean_object* v_target_992_; lean_object* v___x_993_; 
lean_dec(v_h__3_987_);
lean_dec(v_h__1_985_);
v_package_991_ = lean_ctor_get(v_k_x27_984_, 0);
lean_inc(v_package_991_);
v_target_992_ = lean_ctor_get(v_k_x27_984_, 1);
lean_inc(v_target_992_);
lean_dec_ref_known(v_k_x27_984_, 2);
v___x_993_ = lean_apply_2(v_h__2_986_, v_package_991_, v_target_992_);
return v___x_993_;
}
default: 
{
lean_object* v___x_994_; 
lean_dec(v_h__2_986_);
lean_dec(v_h__1_985_);
v___x_994_ = lean_apply_3(v_h__3_987_, v_k_x27_984_, lean_box(0), lean_box(0));
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_995_, lean_object* v_h__1_996_, lean_object* v_h__2_997_){
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_1002_, lean_object* v_k_x27_1003_, lean_object* v_h__1_1004_, lean_object* v_h__2_1005_){
_start:
{
if (lean_obj_tag(v_k_x27_1003_) == 4)
{
lean_object* v_target_1006_; lean_object* v_facet_1007_; lean_object* v___x_1008_; 
lean_dec(v_h__2_1005_);
v_target_1006_ = lean_ctor_get(v_k_x27_1003_, 0);
lean_inc_ref(v_target_1006_);
v_facet_1007_ = lean_ctor_get(v_k_x27_1003_, 1);
lean_inc(v_facet_1007_);
lean_dec_ref_known(v_k_x27_1003_, 2);
v___x_1008_ = lean_apply_2(v_h__1_1004_, v_target_1006_, v_facet_1007_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; 
lean_dec(v_h__1_1004_);
v___x_1009_ = lean_apply_2(v_h__2_1005_, v_k_x27_1003_, lean_box(0));
return v___x_1009_;
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
