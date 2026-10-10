// Lean compiler output
// Module: Lake.Reservoir
// Imports: import Init.Control.Do public import Lake.Util.JsonObject public import Lake.Util.Version public import Lake.Config.Env public import Lake.Util.Reservoir import Lake.Util.Url
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* l_Lake_getUrl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_StdVer_parse(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedRegistrySrc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedRegistrySrc_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedRegistrySrc_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedRegistrySrc_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedRegistrySrc_default = (const lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedRegistrySrc = (const lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lake_RegistrySrc_isGit(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_isGit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object*);
static const lean_closure_object l_Lake_RegistrySrc_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RegistrySrc_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RegistrySrc_instToJson___closed__0 = (const lean_object*)&l_Lake_RegistrySrc_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_RegistrySrc_instToJson = (const lean_object*)&l_Lake_RegistrySrc_instToJson___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object*);
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "invalid registry source: "};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "gitUrl"};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "gitUrl: "};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "subDir"};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subDir: "};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "defaultBranch"};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "defaultBranch: "};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__6_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__7_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "host: "};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__8 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__8_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "github"};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__9 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__9_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repoUrl"};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__10 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__10_value;
static const lean_string_object l_Lake_RegistrySrc_fromJson_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "repoUrl: "};
static const lean_object* l_Lake_RegistrySrc_fromJson_x3f___closed__11 = (const lean_object*)&l_Lake_RegistrySrc_fromJson_x3f___closed__11_value;
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_RegistrySrc_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RegistrySrc_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RegistrySrc_instFromJson___closed__0 = (const lean_object*)&l_Lake_RegistrySrc_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_RegistrySrc_instFromJson = (const lean_object*)&l_Lake_RegistrySrc_instFromJson___closed__0_value;
static const lean_array_object l_Lake_instInhabitedRegistryPkg_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedRegistryPkg_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedRegistryPkg_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedRegistryPkg_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedRegistrySrc_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedRegistryPkg_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedRegistryPkg_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedRegistryPkg_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedRegistryPkg_default = (const lean_object*)&l_Lake_instInhabitedRegistryPkg_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedRegistryPkg = (const lean_object*)&l_Lake_instInhabitedRegistryPkg_default___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RegistryPkg_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0 = (const lean_object*)&l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson = (const lean_object*)&l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid registry package: "};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "property not found: name"};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "name: "};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fullName"};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "property not found: fullName"};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fullName: "};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__6_value;
static const lean_array_object l_Lake_RegistryPkg_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__7_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sources"};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__8 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__8_value;
static const lean_string_object l_Lake_RegistryPkg_fromJson_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sources: "};
static const lean_object* l_Lake_RegistryPkg_fromJson_x3f___closed__9 = (const lean_object*)&l_Lake_RegistryPkg_fromJson_x3f___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_RegistryPkg_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RegistryPkg_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RegistryPkg_instFromJson___closed__0 = (const lean_object*)&l_Lake_RegistryPkg_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_RegistryPkg_instFromJson = (const lean_object*)&l_Lake_RegistryPkg_instFromJson___closed__0_value;
static const lean_string_object l_Lake_Reservoir_pkgApiUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "/packages/"};
static const lean_object* l_Lake_Reservoir_pkgApiUrl___closed__0 = (const lean_object*)&l_Lake_Reservoir_pkgApiUrl___closed__0_value;
static const lean_string_object l_Lake_Reservoir_pkgApiUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_Reservoir_pkgApiUrl___closed__1 = (const lean_object*)&l_Lake_Reservoir_pkgApiUrl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object*);
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "property not found: status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "status: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "message: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object*);
static const lean_string_object l_Lake_Reservoir_fetchPkg_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = ": Reservoir lookup failed; server returned invalid JSON: "};
static const lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__0 = (const lean_object*)&l_Lake_Reservoir_fetchPkg_x3f___closed__0_value;
static const lean_string_object l_Lake_Reservoir_fetchPkg_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": Reservoir responded with:\n"};
static const lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__1 = (const lean_object*)&l_Lake_Reservoir_fetchPkg_x3f___closed__1_value;
static const lean_string_object l_Lake_Reservoir_fetchPkg_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = ": Reservoir lookup failed; server returned unsupported JSON: "};
static const lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__2 = (const lean_object*)&l_Lake_Reservoir_fetchPkg_x3f___closed__2_value;
static const lean_string_object l_Lake_Reservoir_fetchPkg_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ": Reservoir lookup failed: "};
static const lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__3 = (const lean_object*)&l_Lake_Reservoir_fetchPkg_x3f___closed__3_value;
static const lean_string_object l_Lake_Reservoir_fetchPkg_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ": Reservoir lookup failed"};
static const lean_object* l_Lake_Reservoir_fetchPkg_x3f___closed__4 = (const lean_object*)&l_Lake_Reservoir_fetchPkg_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid registry version: "};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "version: "};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: version"};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "revision"};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "property not found: revision"};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "revision: "};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_instFromJsonRegistryVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_RegistryVer_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonRegistryVer___closed__0 = (const lean_object*)&l_Lake_instFromJsonRegistryVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonRegistryVer = (const lean_object*)&l_Lake_instFromJsonRegistryVer___closed__0_value;
static const lean_string_object l_Lake_Reservoir_pkgVersionsApiUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "/versions"};
static const lean_object* l_Lake_Reservoir_pkgVersionsApiUrl___closed__0 = (const lean_object*)&l_Lake_Reservoir_pkgVersionsApiUrl___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object*);
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object*);
static const lean_string_object l_Lake_Reservoir_fetchPkgVersions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ": Reservoir lookup failed (code: "};
static const lean_object* l_Lake_Reservoir_fetchPkgVersions___closed__0 = (const lean_object*)&l_Lake_Reservoir_fetchPkgVersions___closed__0_value;
static const lean_string_object l_Lake_Reservoir_fetchPkgVersions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "): "};
static const lean_object* l_Lake_Reservoir_fetchPkgVersions___closed__1 = (const lean_object*)&l_Lake_Reservoir_fetchPkgVersions___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_RegistrySrc_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_data_7_; lean_object* v_url_8_; lean_object* v_githubUrl_x3f_9_; lean_object* v_defaultBranch_x3f_10_; lean_object* v_subDir_x3f_11_; lean_object* v___x_12_; 
v_data_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_data_7_);
v_url_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_url_8_);
v_githubUrl_x3f_9_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_githubUrl_x3f_9_);
v_defaultBranch_x3f_10_ = lean_ctor_get(v_t_5_, 3);
lean_inc(v_defaultBranch_x3f_10_);
v_subDir_x3f_11_ = lean_ctor_get(v_t_5_, 4);
lean_inc(v_subDir_x3f_11_);
lean_dec_ref_known(v_t_5_, 5);
v___x_12_ = lean_apply_5(v_k_6_, v_data_7_, v_url_8_, v_githubUrl_x3f_9_, v_defaultBranch_x3f_10_, v_subDir_x3f_11_);
return v___x_12_;
}
else
{
lean_object* v_data_13_; lean_object* v___x_14_; 
v_data_13_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_data_13_);
lean_dec_ref_known(v_t_5_, 1);
v___x_14_ = lean_apply_1(v_k_6_, v_data_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_RegistrySrc_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_git_elim___redArg(lean_object* v_t_27_, lean_object* v_git_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_27_, v_git_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_git_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_git_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_31_, v_git_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_other_elim___redArg(lean_object* v_t_35_, lean_object* v_other_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_35_, v_other_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_other_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_other_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_39_, v_other_41_);
return v___x_42_;
}
}
uint8_t l_Lake_RegistrySrc_isGit(lean_object* v_src_50_){
_start:
{
if (lean_obj_tag(v_src_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT void l_Lake_RegistrySrc_isGit_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_50_ = stack[0].m_obj;
uint8_t v_res_53_;
v_res_53_ = l_Lake_RegistrySrc_isGit(v_src_50_);
stack->m_num = v_res_53_;
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_isGit___boxed(lean_object* v_src_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lake_RegistrySrc_isGit(v_src_54_);
lean_dec_ref(v_src_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data(lean_object* v_src_57_){
_start:
{
lean_object* v_data_58_; 
v_data_58_ = lean_ctor_get(v_src_57_, 0);
lean_inc(v_data_58_);
return v_data_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data___boxed(lean_object* v_src_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lake_RegistrySrc_data(v_src_59_);
lean_dec_ref(v_src_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object* v_src_61_){
_start:
{
if (lean_obj_tag(v_src_61_) == 0)
{
lean_object* v_data_62_; lean_object* v___x_63_; 
v_data_62_ = lean_ctor_get(v_src_61_, 0);
lean_inc(v_data_62_);
lean_dec_ref_known(v_src_61_, 5);
v___x_63_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_63_, 0, v_data_62_);
return v___x_63_;
}
else
{
lean_object* v_data_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_data_64_ = lean_ctor_get(v_src_61_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v_src_61_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v_src_61_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_data_64_);
lean_dec(v_src_61_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 5);
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_data_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_77_; 
v___x_77_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0));
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Json_getStr_x3f(v_x_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_a_87_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0));
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Json_getStr_x3f(v_x_96_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_a_107_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_98_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_98_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_a_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object* v_val_128_){
_start:
{
lean_object* v_a_130_; lean_object* v___x_134_; 
v___x_134_ = l_Lean_Json_getObj_x3f(v_val_128_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
v_a_130_ = v_a_135_;
goto v___jp_129_;
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_216_; 
v_a_136_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_216_ == 0)
{
v___x_138_ = v___x_134_;
v_isShared_139_ = v_isSharedCheck_216_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_216_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__1));
v___x_146_ = l_Lake_JsonObject_getJson_x3f(v_a_136_, v___x_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
goto v___jp_140_;
}
else
{
lean_object* v_val_147_; lean_object* v___x_148_; 
v_val_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v___x_146_, 1);
v___x_148_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_del_object(v___x_138_);
lean_dec(v_a_136_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__2));
v___x_151_ = lean_string_append(v___x_150_, v_a_149_);
lean_dec(v_a_149_);
v_a_130_ = v___x_151_;
goto v___jp_129_;
}
else
{
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_152_; 
lean_del_object(v___x_138_);
lean_dec(v_a_136_);
v_a_152_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_148_, 1);
v_a_130_ = v_a_152_;
goto v___jp_129_;
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_215_; 
v_a_153_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_215_ == 0)
{
v___x_155_ = v___x_148_;
v_isShared_156_ = v_isSharedCheck_215_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_148_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_215_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
if (lean_obj_tag(v_a_153_) == 1)
{
lean_object* v_val_157_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v_a_161_; lean_object* v___y_167_; lean_object* v_a_168_; lean_object* v_a_180_; lean_object* v___x_191_; lean_object* v___x_192_; 
lean_del_object(v___x_138_);
v_val_157_ = lean_ctor_get(v_a_153_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v_a_153_, 1);
v___x_191_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__7));
v___x_192_ = l_Lake_JsonObject_getJson_x3f(v_a_136_, v___x_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
v_a_180_ = v___x_193_;
goto v___jp_179_;
}
else
{
lean_object* v_val_194_; lean_object* v___x_195_; 
v_val_194_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_192_, 1);
v___x_195_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_195_, 1);
v___x_197_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__8));
v___x_198_ = lean_string_append(v___x_197_, v_a_196_);
lean_dec(v_a_196_);
v_a_130_ = v___x_198_;
goto v___jp_129_;
}
else
{
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_199_; 
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_199_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_195_, 1);
v_a_130_ = v_a_199_;
goto v___jp_129_;
}
else
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_195_, 1);
if (lean_obj_tag(v_a_200_) == 0)
{
v_a_180_ = v_a_200_;
goto v___jp_179_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_val_201_ = lean_ctor_get(v_a_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v_a_200_, 1);
v___x_202_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__9));
v___x_203_ = lean_string_dec_eq(v_val_201_, v___x_202_);
lean_dec(v_val_201_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
v_a_180_ = v___x_204_;
goto v___jp_179_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__10));
v___x_206_ = l_Lake_JsonObject_getJson_x3f(v_a_136_, v___x_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
v_a_180_ = v___x_207_;
goto v___jp_179_;
}
else
{
lean_object* v_val_208_; lean_object* v___x_209_; 
v_val_208_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_206_, 1);
v___x_209_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__11));
v___x_212_ = lean_string_append(v___x_211_, v_a_210_);
lean_dec(v_a_210_);
v_a_130_ = v___x_212_;
goto v___jp_129_;
}
else
{
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_213_; 
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_213_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_209_, 1);
v_a_130_ = v_a_213_;
goto v___jp_129_;
}
else
{
lean_object* v_a_214_; 
v_a_214_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_209_, 1);
v_a_180_ = v_a_214_;
goto v___jp_179_;
}
}
}
}
}
}
}
}
v___jp_158_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_162_, 0, v_a_136_);
lean_ctor_set(v___x_162_, 1, v_val_157_);
lean_ctor_set(v___x_162_, 2, v___y_160_);
lean_ctor_set(v___x_162_, 3, v___y_159_);
lean_ctor_set(v___x_162_, 4, v_a_161_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
v___jp_166_:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__3));
v___x_170_ = l_Lake_JsonObject_getJson_x3f(v_a_136_, v___x_169_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
v___y_159_ = v_a_168_;
v___y_160_ = v___y_167_;
v_a_161_ = v___x_171_;
goto v___jp_158_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v___x_170_, 1);
v___x_173_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(v_val_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_a_168_);
lean_dec(v___y_167_);
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__4));
v___x_176_ = lean_string_append(v___x_175_, v_a_174_);
lean_dec(v_a_174_);
v_a_130_ = v___x_176_;
goto v___jp_129_;
}
else
{
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_177_; 
lean_dec(v_a_168_);
lean_dec(v___y_167_);
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_177_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_173_, 1);
v_a_130_ = v_a_177_;
goto v___jp_129_;
}
else
{
lean_object* v_a_178_; 
v_a_178_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_173_, 1);
v___y_159_ = v_a_168_;
v___y_160_ = v___y_167_;
v_a_161_ = v_a_178_;
goto v___jp_158_;
}
}
}
}
v___jp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__5));
v___x_182_ = l_Lake_JsonObject_getJson_x3f(v_a_136_, v___x_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_box(0);
v___y_167_ = v_a_180_;
v_a_168_ = v___x_183_;
goto v___jp_166_;
}
else
{
lean_object* v_val_184_; lean_object* v___x_185_; 
v_val_184_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v___x_182_, 1);
v___x_185_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_a_180_);
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__6));
v___x_188_ = lean_string_append(v___x_187_, v_a_186_);
lean_dec(v_a_186_);
v_a_130_ = v___x_188_;
goto v___jp_129_;
}
else
{
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_189_; 
lean_dec(v_a_180_);
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_189_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_185_, 1);
v_a_130_ = v_a_189_;
goto v___jp_129_;
}
else
{
lean_object* v_a_190_; 
v_a_190_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_185_, 1);
v___y_167_ = v_a_180_;
v_a_168_ = v_a_190_;
goto v___jp_166_;
}
}
}
}
}
else
{
lean_del_object(v___x_155_);
lean_dec(v_a_153_);
goto v___jp_140_;
}
}
}
}
}
v___jp_140_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_a_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__0));
v___x_132_ = lean_string_append(v___x_131_, v_a_130_);
lean_dec_ref(v_a_130_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object* v_as_230_, size_t v_sz_231_, size_t v_i_232_, lean_object* v_b_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_lt(v_i_232_, v_sz_231_);
if (v___x_234_ == 0)
{
lean_inc_ref(v_b_233_);
return v_b_233_;
}
else
{
lean_object* v___x_235_; lean_object* v_a_236_; uint8_t v___x_237_; 
v___x_235_ = lean_box(0);
v_a_236_ = lean_array_uget_borrowed(v_as_230_, v_i_232_);
v___x_237_ = l_Lake_RegistrySrc_isGit(v_a_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; size_t v___x_239_; size_t v___x_240_; 
v___x_238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_232_, v___x_239_);
v_i_232_ = v___x_240_;
v_b_233_ = v___x_238_;
goto _start;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_inc(v_a_236_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_a_236_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_235_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_230_ = stack[0].m_obj;
size_t v_sz_231_ = stack[1].m_num;
size_t v_i_232_ = stack[2].m_num;
lean_object* v_b_233_ = stack[3].m_obj;
lean_object* v_res_245_;
v_res_245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_as_230_, v_sz_231_, v_i_232_, v_b_233_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object* v_as_246_, lean_object* v_sz_247_, lean_object* v_i_248_, lean_object* v_b_249_){
_start:
{
size_t v_sz_boxed_250_; size_t v_i_boxed_251_; lean_object* v_res_252_; 
v_sz_boxed_250_ = lean_unbox_usize(v_sz_247_);
lean_dec(v_sz_247_);
v_i_boxed_251_ = lean_unbox_usize(v_i_248_);
lean_dec(v_i_248_);
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_as_246_, v_sz_boxed_250_, v_i_boxed_251_, v_b_249_);
lean_dec_ref(v_b_249_);
lean_dec_ref(v_as_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object* v_pkg_253_){
_start:
{
lean_object* v_sources_254_; lean_object* v___x_255_; lean_object* v___x_256_; size_t v_sz_257_; size_t v___x_258_; lean_object* v___x_259_; lean_object* v_fst_260_; 
v_sources_254_ = lean_ctor_get(v_pkg_253_, 2);
v___x_255_ = lean_box(0);
v___x_256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v_sz_257_ = lean_array_size(v_sources_254_);
v___x_258_ = ((size_t)0ULL);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_sources_254_, v_sz_257_, v___x_258_, v___x_256_);
v_fst_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_fst_260_);
lean_dec_ref(v___x_259_);
if (lean_obj_tag(v_fst_260_) == 0)
{
return v___x_255_;
}
else
{
lean_object* v_val_261_; 
v_val_261_ = lean_ctor_get(v_fst_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_fst_260_, 1);
return v_val_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object* v_pkg_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lake_RegistryPkg_gitSrc_x3f(v_pkg_262_);
lean_dec_ref(v_pkg_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object* v_src_264_){
_start:
{
lean_object* v_data_265_; 
v_data_265_ = lean_ctor_get(v_src_264_, 3);
lean_inc(v_data_265_);
return v_data_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object* v_src_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lake_RegistryPkg_toJson(v_src_266_);
lean_dec_ref(v_src_266_);
return v_res_267_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t v_sz_270_, size_t v_i_271_, lean_object* v_bs_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_usize_dec_lt(v_i_271_, v_sz_270_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_bs_272_);
return v___x_274_;
}
else
{
lean_object* v_v_275_; lean_object* v___x_276_; lean_object* v_bs_x27_277_; size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v_v_275_ = lean_array_uget(v_bs_272_, v_i_271_);
v___x_276_ = lean_unsigned_to_nat(0u);
v_bs_x27_277_ = lean_array_uset(v_bs_272_, v_i_271_, v___x_276_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_add(v_i_271_, v___x_278_);
v___x_280_ = lean_array_uset(v_bs_x27_277_, v_i_271_, v_v_275_);
v_i_271_ = v___x_279_;
v_bs_272_ = v___x_280_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_270_ = stack[0].m_num;
size_t v_i_271_ = stack[1].m_num;
lean_object* v_bs_272_ = stack[2].m_obj;
lean_object* v_res_282_;
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_270_, v_i_271_, v_bs_272_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_283_, lean_object* v_i_284_, lean_object* v_bs_285_){
_start:
{
size_t v_sz_boxed_286_; size_t v_i_boxed_287_; lean_object* v_res_288_; 
v_sz_boxed_286_ = lean_unbox_usize(v_sz_283_);
lean_dec(v_sz_283_);
v_i_boxed_287_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_boxed_286_, v_i_boxed_287_, v_bs_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 4)
{
lean_object* v_elems_292_; size_t v_sz_293_; size_t v___x_294_; lean_object* v___x_295_; 
v_elems_292_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_elems_292_);
lean_dec_ref_known(v_x_291_, 1);
v_sz_293_ = lean_array_size(v_elems_292_);
v___x_294_ = ((size_t)0ULL);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_293_, v___x_294_, v_elems_292_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_297_ = lean_unsigned_to_nat(80u);
v___x_298_ = l_Lean_Json_pretty(v_x_291_, v___x_297_);
v___x_299_ = lean_string_append(v___x_296_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0));
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(v_x_305_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_307_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_307_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(size_t v_sz_325_, size_t v_i_326_, lean_object* v_bs_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_bs_327_);
return v___x_329_;
}
else
{
lean_object* v_v_330_; lean_object* v___x_331_; 
v_v_330_ = lean_array_uget_borrowed(v_bs_327_, v_i_326_);
lean_inc(v_v_330_);
v___x_331_ = l_Lake_RegistrySrc_fromJson_x3f(v_v_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_bs_327_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v_bs_x27_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_a_340_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_331_, 1);
v___x_341_ = lean_unsigned_to_nat(0u);
v_bs_x27_342_ = lean_array_uset(v_bs_327_, v_i_326_, v___x_341_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_326_, v___x_343_);
v___x_345_ = lean_array_uset(v_bs_x27_342_, v_i_326_, v_a_340_);
v_i_326_ = v___x_344_;
v_bs_327_ = v___x_345_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_325_ = stack[0].m_num;
size_t v_i_326_ = stack[1].m_num;
lean_object* v_bs_327_ = stack[2].m_obj;
lean_object* v_res_347_;
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_325_, v_i_326_, v_bs_327_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object* v_sz_348_, lean_object* v_i_349_, lean_object* v_bs_350_){
_start:
{
size_t v_sz_boxed_351_; size_t v_i_boxed_352_; lean_object* v_res_353_; 
v_sz_boxed_351_ = lean_unbox_usize(v_sz_348_);
lean_dec(v_sz_348_);
v_i_boxed_352_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_boxed_351_, v_i_boxed_352_, v_bs_350_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object* v_val_365_){
_start:
{
lean_object* v_a_367_; lean_object* v___x_371_; 
v___x_371_ = l_Lean_Json_getObj_x3f(v_val_365_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v_a_367_ = v_a_372_;
goto v___jp_366_;
}
else
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_371_, 1);
v___x_374_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__1));
v___x_375_ = l_Lake_JsonObject_getJson_x3f(v_a_373_, v___x_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v___x_376_; 
lean_dec(v_a_373_);
v___x_376_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__2));
v_a_367_ = v___x_376_;
goto v___jp_366_;
}
else
{
lean_object* v_val_377_; lean_object* v___x_378_; 
v_val_377_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_val_377_);
lean_dec_ref_known(v___x_375_, 1);
v___x_378_ = l_Lean_Json_getStr_x3f(v_val_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_a_373_);
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
v___x_380_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__3));
v___x_381_ = lean_string_append(v___x_380_, v_a_379_);
lean_dec(v_a_379_);
v_a_367_ = v___x_381_;
goto v___jp_366_;
}
else
{
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_382_; 
lean_dec(v_a_373_);
v_a_382_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_378_, 1);
v_a_367_ = v_a_382_;
goto v___jp_366_;
}
else
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_378_, 1);
v___x_384_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__4));
v___x_385_ = l_Lake_JsonObject_getJson_x3f(v_a_373_, v___x_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
lean_dec(v_a_383_);
lean_dec(v_a_373_);
v___x_386_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__5));
v_a_367_ = v___x_386_;
goto v___jp_366_;
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; 
v_val_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_385_, 1);
v___x_388_ = l_Lean_Json_getStr_x3f(v_val_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_a_383_);
lean_dec(v_a_373_);
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__6));
v___x_391_ = lean_string_append(v___x_390_, v_a_389_);
lean_dec(v_a_389_);
v_a_367_ = v___x_391_;
goto v___jp_366_;
}
else
{
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_392_; 
lean_dec(v_a_383_);
lean_dec(v_a_373_);
v_a_392_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_388_, 1);
v_a_367_ = v_a_392_;
goto v___jp_366_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_427_; 
v_a_393_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_427_ == 0)
{
v___x_395_ = v___x_388_;
v_isShared_396_ = v_isSharedCheck_427_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_427_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_a_398_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__8));
v___x_418_ = l_Lake_JsonObject_getJson_x3f(v_a_373_, v___x_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_420_; 
v_val_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(v_val_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_del_object(v___x_395_);
lean_dec(v_a_393_);
lean_dec(v_a_383_);
lean_dec(v_a_373_);
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__9));
v___x_423_ = lean_string_append(v___x_422_, v_a_421_);
lean_dec(v_a_421_);
v_a_367_ = v___x_423_;
goto v___jp_366_;
}
else
{
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_424_; 
lean_del_object(v___x_395_);
lean_dec(v_a_393_);
lean_dec(v_a_383_);
lean_dec(v_a_373_);
v_a_424_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_420_, 1);
v_a_367_ = v_a_424_;
goto v___jp_366_;
}
else
{
lean_object* v_a_425_; 
v_a_425_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_420_, 1);
if (lean_obj_tag(v_a_425_) == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v_val_426_; 
v_val_426_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_a_425_, 1);
v_a_398_ = v_val_426_;
goto v___jp_397_;
}
}
}
}
v___jp_397_:
{
size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_sz_399_ = lean_array_size(v_a_398_);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_399_, v___x_400_, v_a_398_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; 
lean_del_object(v___x_395_);
lean_dec(v_a_393_);
lean_dec(v_a_383_);
lean_dec(v_a_373_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v_a_367_ = v_a_402_;
goto v___jp_366_;
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v_a_403_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_414_ == 0)
{
v___x_405_ = v___x_401_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_401_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 5);
lean_ctor_set(v___x_395_, 0, v_a_373_);
v___x_408_ = v___x_395_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_373_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_409_, 0, v_a_383_);
lean_ctor_set(v___x_409_, 1, v_a_393_);
lean_ctor_set(v___x_409_, 2, v_a_403_);
lean_ctor_set(v___x_409_, 3, v___x_408_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_409_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
v___jp_415_:
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__7));
v_a_398_ = v___x_416_;
goto v___jp_397_;
}
}
}
}
}
}
}
}
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__0));
v___x_369_ = lean_string_append(v___x_368_, v_a_367_);
lean_dec_ref(v_a_367_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object* v_lakeEnv_432_, lean_object* v_owner_433_, lean_object* v_pkg_434_){
_start:
{
lean_object* v_reservoirApiUrl_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_reservoirApiUrl_435_ = lean_ctor_get(v_lakeEnv_432_, 3);
lean_inc_ref(v_reservoirApiUrl_435_);
lean_dec_ref(v_lakeEnv_432_);
v___x_436_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_437_ = lean_string_append(v_reservoirApiUrl_435_, v___x_436_);
v___x_438_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_439_ = l_Lake_uriEncode(v_owner_433_, v___x_438_);
v___x_440_ = lean_string_append(v___x_437_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
v___x_443_ = l_Lake_uriEncode(v_pkg_434_, v___x_438_);
v___x_444_ = lean_string_append(v___x_442_, v___x_443_);
lean_dec_ref(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object* v_lakeEnv_445_, lean_object* v_owner_446_, lean_object* v_pkg_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_445_, v_owner_446_, v_pkg_447_);
lean_dec_ref(v_pkg_447_);
lean_dec_ref(v_owner_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0));
return v___x_452_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Json_getObj_x3f(v_x_451_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_a_462_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v___x_453_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_453_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_a_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0));
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_x_473_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* v_val_490_){
_start:
{
lean_object* v_a_492_; lean_object* v___x_536_; 
lean_inc(v_val_490_);
v___x_536_ = l_Lean_Json_getObj_x3f(v_val_490_);
if (lean_obj_tag(v___x_536_) == 1)
{
lean_object* v_a_537_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_544_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_545_ = l_Lake_JsonObject_getJson_x3f(v_a_537_, v___x_544_);
if (lean_obj_tag(v___x_545_) == 0)
{
goto v___jp_538_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_546_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_537_);
lean_dec(v_val_490_);
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_557_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_553_ = lean_string_append(v___x_552_, v_a_548_);
lean_dec(v_a_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_553_);
v___x_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
else
{
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_a_537_);
lean_dec(v_val_490_);
v_a_558_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_547_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_547_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 0);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v_a_566_; 
v_a_566_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_547_, 1);
if (lean_obj_tag(v_a_566_) == 1)
{
lean_object* v_val_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_a_537_);
lean_dec(v_val_490_);
v_val_567_ = lean_ctor_get(v_a_566_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_a_566_, 1);
v___x_568_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_569_ = l_Lake_JsonObject_getJson_x3f(v_val_567_, v___x_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
lean_dec(v_val_567_);
v___x_570_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5));
return v___x_570_;
}
else
{
lean_object* v_val_571_; lean_object* v___x_572_; 
v_val_571_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v___x_569_, 1);
v___x_572_ = l_Lean_Json_getNat_x3f(v_val_571_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_val_567_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_578_ = lean_string_append(v___x_577_, v_a_573_);
lean_dec(v_a_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_val_567_);
v_a_583_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_572_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_572_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_591_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_572_, 1);
v___x_592_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_593_ = l_Lake_JsonObject_getJson_x3f(v_val_567_, v___x_592_);
lean_dec(v_val_567_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; 
lean_dec(v_a_591_);
v___x_594_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9));
return v___x_594_;
}
else
{
lean_object* v_val_595_; lean_object* v___x_596_; 
v_val_595_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v___x_593_, 1);
v___x_596_ = l_Lean_Json_getStr_x3f(v_val_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_a_591_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_606_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_601_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_602_ = lean_string_append(v___x_601_, v_a_597_);
lean_dec(v_a_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v_a_591_);
v_a_607_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_596_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_596_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
v_a_615_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v___x_596_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_596_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v_a_591_);
lean_ctor_set(v___x_619_, 1, v_a_615_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_619_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
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
lean_dec(v_a_566_);
goto v___jp_538_;
}
}
}
}
v___jp_538_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_540_ = l_Lake_JsonObject_getJson_x3f(v_a_537_, v___x_539_);
lean_dec(v_a_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
v_a_492_ = v___x_540_;
goto v___jp_491_;
}
else
{
lean_object* v_val_541_; lean_object* v___x_542_; lean_object* v_a_543_; 
v_val_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_541_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
v_a_492_ = v_a_543_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec_ref(v___x_536_);
v___x_624_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_490_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_a_633_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v___x_624_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_624_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_a_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
v___jp_491_:
{
if (lean_obj_tag(v_a_492_) == 1)
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_val_490_);
v_val_493_ = lean_ctor_get(v_a_492_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_517_ == 0)
{
v___x_495_ = v_a_492_;
v_isShared_496_ = v_isSharedCheck_517_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v_a_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_517_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_493_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_del_object(v___x_495_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_a_506_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_516_ == 0)
{
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set_tag(v___x_495_, 0);
lean_ctor_set(v___x_495_, 0, v_a_506_);
v___x_511_ = v___x_495_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_a_492_);
v___x_518_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_490_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_535_; 
v_a_527_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_535_ == 0)
{
v___x_529_ = v___x_518_;
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_a_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
}
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* v_lakeEnv_647_, lean_object* v_owner_648_, lean_object* v_pkg_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_url_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_url_652_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_647_, v_owner_648_, v_pkg_649_);
v___x_653_ = l_Lake_Reservoir_lakeHeaders;
v___x_654_ = l_Lake_getUrl(v_url_652_, v___x_653_, v_a_650_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_746_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_a_656_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_746_ == 0)
{
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_746_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_746_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; 
lean_inc(v_a_655_);
v___x_660_ = l_Lean_Json_parse(v_a_655_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_663_ = lean_string_append(v_owner_648_, v___x_662_);
v___x_664_ = lean_string_append(v___x_663_, v_pkg_649_);
v___x_665_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_664_);
v___x_666_ = lean_string_append(v___x_664_, v___x_665_);
v___x_667_ = lean_string_append(v___x_666_, v_a_661_);
lean_dec(v_a_661_);
v___x_668_ = 3;
v___x_669_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_668_);
v___x_670_ = lean_array_get_size(v_a_656_);
v___x_671_ = lean_array_push(v_a_656_, v___x_669_);
v___x_672_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_673_ = lean_string_append(v___x_664_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_string_utf8_byte_size(v_a_655_);
v___x_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_676_, 0, v_a_655_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
lean_ctor_set(v___x_676_, 2, v___x_675_);
v___x_677_ = l_String_Slice_trimAscii(v___x_676_);
v___x_678_ = l_String_Slice_toString(v___x_677_);
lean_dec_ref(v___x_677_);
v___x_679_ = lean_string_append(v___x_673_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = 0;
v___x_681_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v___x_680_);
v___x_682_ = lean_array_push(v___x_671_, v___x_681_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 1, v___x_682_);
lean_ctor_set(v___x_658_, 0, v___x_670_);
v___x_684_ = v___x_658_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_687_; 
v_a_686_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_660_, 1);
v___x_687_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_690_ = lean_string_append(v_owner_648_, v___x_689_);
v___x_691_ = lean_string_append(v___x_690_, v_pkg_649_);
v___x_692_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_691_);
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
v___x_694_ = lean_string_append(v___x_693_, v_a_688_);
lean_dec(v_a_688_);
v___x_695_ = 3;
v___x_696_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*1, v___x_695_);
v___x_697_ = lean_array_get_size(v_a_656_);
v___x_698_ = lean_array_push(v_a_656_, v___x_696_);
v___x_699_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_700_ = lean_string_append(v___x_691_, v___x_699_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_string_utf8_byte_size(v_a_655_);
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v_a_655_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
v___x_704_ = l_String_Slice_trimAscii(v___x_703_);
v___x_705_ = l_String_Slice_toString(v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = lean_string_append(v___x_700_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = 0;
v___x_708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*1, v___x_707_);
v___x_709_ = lean_array_push(v___x_698_, v___x_708_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 1, v___x_709_);
lean_ctor_set(v___x_658_, 0, v___x_697_);
v___x_711_ = v___x_658_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v_a_713_; 
lean_dec(v_a_655_);
v_a_713_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_687_, 1);
if (lean_obj_tag(v_a_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v_owner_648_);
v_a_714_ = lean_ctor_get(v_a_713_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_724_ == 0)
{
v___x_716_ = v_a_713_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v_a_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 1);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_719_);
v___x_721_ = v___x_658_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_a_656_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_status_725_; lean_object* v_message_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_status_725_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_status_725_);
v_message_726_ = lean_ctor_get(v_a_713_, 1);
lean_inc_ref(v_message_726_);
lean_dec_ref_known(v_a_713_, 2);
v___x_727_ = lean_unsigned_to_nat(404u);
v___x_728_ = lean_nat_dec_eq(v_status_725_, v___x_727_);
lean_dec(v_status_725_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_729_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_730_ = lean_string_append(v_owner_648_, v___x_729_);
v___x_731_ = lean_string_append(v___x_730_, v_pkg_649_);
v___x_732_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__3));
v___x_733_ = lean_string_append(v___x_731_, v___x_732_);
v___x_734_ = lean_string_append(v___x_733_, v_message_726_);
lean_dec_ref(v_message_726_);
v___x_735_ = 3;
v___x_736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*1, v___x_735_);
v___x_737_ = lean_array_get_size(v_a_656_);
v___x_738_ = lean_array_push(v_a_656_, v___x_736_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 1, v___x_738_);
lean_ctor_set(v___x_658_, 0, v___x_737_);
v___x_740_ = v___x_658_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_dec_ref(v_message_726_);
lean_dec_ref(v_owner_648_);
v___x_742_ = lean_box(0);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_742_);
v___x_744_ = v___x_658_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_656_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_763_; 
v_a_747_ = lean_ctor_get(v___x_654_, 0);
v_a_748_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_763_ == 0)
{
v___x_750_ = v___x_654_;
v_isShared_751_ = v_isSharedCheck_763_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_inc(v_a_747_);
lean_dec(v___x_654_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_763_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_752_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_753_ = lean_string_append(v_owner_648_, v___x_752_);
v___x_754_ = lean_string_append(v___x_753_, v_pkg_649_);
v___x_755_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
v___x_757_ = 3;
v___x_758_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*1, v___x_757_);
v___x_759_ = lean_array_push(v_a_748_, v___x_758_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_759_);
v___x_761_ = v___x_750_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_747_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Reservoir_fetchPkg_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lakeEnv_647_ = stack[0].m_obj;
lean_object* v_owner_648_ = stack[1].m_obj;
lean_object* v_pkg_649_ = stack[2].m_obj;
lean_object* v_a_650_ = stack[3].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_647_, v_owner_648_, v_pkg_649_, v_a_650_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* v_lakeEnv_765_, lean_object* v_owner_766_, lean_object* v_pkg_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_765_, v_owner_766_, v_pkg_767_, v_a_768_);
lean_dec_ref(v_pkg_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object* v_val_778_){
_start:
{
lean_object* v_a_780_; lean_object* v_a_785_; lean_object* v___x_788_; 
v___x_788_ = l_Lean_Json_getObj_x3f(v_val_778_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v_a_780_ = v_a_789_;
goto v___jp_779_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_788_, 1);
v___x_791_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__2));
v___x_792_ = l_Lake_JsonObject_getJson_x3f(v_a_790_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; 
lean_dec(v_a_790_);
v___x_793_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__3));
v_a_780_ = v___x_793_;
goto v___jp_779_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_795_; 
v_val_794_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v___x_792_, 1);
v___x_795_ = l_Lean_Json_getStr_x3f(v_val_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; 
lean_dec(v_a_790_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v_a_785_ = v_a_796_;
goto v___jp_784_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_795_, 1);
v___x_798_ = l_Lake_StdVer_parse(v_a_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
lean_dec(v_a_790_);
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v_a_785_ = v_a_799_;
goto v___jp_784_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_798_, 1);
v___x_801_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__4));
v___x_802_ = l_Lake_JsonObject_getJson_x3f(v_a_790_, v___x_801_);
lean_dec(v_a_790_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_803_; 
lean_dec(v_a_800_);
v___x_803_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__5));
v_a_780_ = v___x_803_;
goto v___jp_779_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v___x_802_, 1);
v___x_805_ = l_Lean_Json_getStr_x3f(v_val_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v_a_800_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__6));
v___x_808_ = lean_string_append(v___x_807_, v_a_806_);
lean_dec(v_a_806_);
v_a_780_ = v___x_808_;
goto v___jp_779_;
}
else
{
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_809_; 
lean_dec(v_a_800_);
v_a_809_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_805_, 1);
v_a_780_ = v_a_809_;
goto v___jp_779_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_818_; 
v_a_810_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_818_ == 0)
{
v___x_812_ = v___x_805_;
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_805_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_800_);
lean_ctor_set(v___x_814_, 1, v_a_810_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
}
}
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__0));
v___x_782_ = lean_string_append(v___x_781_, v_a_780_);
lean_dec_ref(v_a_780_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__1));
v___x_787_ = lean_string_append(v___x_786_, v_a_785_);
lean_dec_ref(v_a_785_);
v_a_780_ = v___x_787_;
goto v___jp_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object* v_lakeEnv_822_, lean_object* v_owner_823_, lean_object* v_pkg_824_){
_start:
{
lean_object* v_reservoirApiUrl_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_reservoirApiUrl_825_ = lean_ctor_get(v_lakeEnv_822_, 3);
lean_inc_ref(v_reservoirApiUrl_825_);
lean_dec_ref(v_lakeEnv_822_);
v___x_826_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_827_ = lean_string_append(v_reservoirApiUrl_825_, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_829_ = l_Lake_uriEncode(v_owner_823_, v___x_828_);
v___x_830_ = lean_string_append(v___x_827_, v___x_829_);
lean_dec_ref(v___x_829_);
v___x_831_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_832_ = lean_string_append(v___x_830_, v___x_831_);
v___x_833_ = l_Lake_uriEncode(v_pkg_824_, v___x_828_);
v___x_834_ = lean_string_append(v___x_832_, v___x_833_);
lean_dec_ref(v___x_833_);
v___x_835_ = ((lean_object*)(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0));
v___x_836_ = lean_string_append(v___x_834_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl___boxed(lean_object* v_lakeEnv_837_, lean_object* v_owner_838_, lean_object* v_pkg_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_837_, v_owner_838_, v_pkg_839_);
lean_dec_ref(v_pkg_839_);
lean_dec_ref(v_owner_838_);
return v_res_840_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t v_sz_841_, size_t v_i_842_, lean_object* v_bs_843_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_lt(v_i_842_, v_sz_841_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v_bs_843_);
return v___x_845_;
}
else
{
lean_object* v_v_846_; lean_object* v___x_847_; 
v_v_846_ = lean_array_uget_borrowed(v_bs_843_, v_i_842_);
lean_inc(v_v_846_);
v___x_847_ = l_Lake_RegistryVer_fromJson_x3f(v_v_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_bs_843_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v_bs_x27_858_; size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v_a_856_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_847_, 1);
v___x_857_ = lean_unsigned_to_nat(0u);
v_bs_x27_858_ = lean_array_uset(v_bs_843_, v_i_842_, v___x_857_);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_add(v_i_842_, v___x_859_);
v___x_861_ = lean_array_uset(v_bs_x27_858_, v_i_842_, v_a_856_);
v_i_842_ = v___x_860_;
v_bs_843_ = v___x_861_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_841_ = stack[0].m_num;
size_t v_i_842_ = stack[1].m_num;
lean_object* v_bs_843_ = stack[2].m_obj;
lean_object* v_res_863_;
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_841_, v_i_842_, v_bs_843_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_bs_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_868_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_867_, v_i_boxed_868_, v_bs_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 4)
{
lean_object* v_elems_871_; size_t v_sz_872_; size_t v___x_873_; lean_object* v___x_874_; 
v_elems_871_ = lean_ctor_get(v_x_870_, 0);
lean_inc_ref(v_elems_871_);
lean_dec_ref_known(v_x_870_, 1);
v_sz_872_ = lean_array_size(v_elems_871_);
v___x_873_ = ((size_t)0ULL);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_872_, v___x_873_, v_elems_871_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_875_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_876_ = lean_unsigned_to_nat(80u);
v___x_877_ = l_Lean_Json_pretty(v_x_870_, v___x_876_);
v___x_878_ = lean_string_append(v___x_875_, v___x_877_);
lean_dec_ref(v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_880_ = lean_string_append(v___x_878_, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object* v_val_886_){
_start:
{
lean_object* v_a_888_; lean_object* v___x_932_; 
lean_inc(v_val_886_);
v___x_932_ = l_Lean_Json_getObj_x3f(v_val_886_);
if (lean_obj_tag(v___x_932_) == 1)
{
lean_object* v_a_933_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_940_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_941_ = l_Lake_JsonObject_getJson_x3f(v_a_933_, v___x_940_);
if (lean_obj_tag(v___x_941_) == 0)
{
goto v___jp_934_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_943_; 
v_val_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_val_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_a_933_);
lean_dec(v_val_886_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_953_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_949_ = lean_string_append(v___x_948_, v_a_944_);
lean_dec(v_a_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_933_);
lean_dec(v_val_886_);
v_a_954_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_943_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_943_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 0);
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v_a_962_; 
v_a_962_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_943_, 1);
if (lean_obj_tag(v_a_962_) == 1)
{
lean_object* v_val_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_a_933_);
lean_dec(v_val_886_);
v_val_963_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v_a_962_, 1);
v___x_964_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_965_ = l_Lake_JsonObject_getJson_x3f(v_val_963_, v___x_964_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v___x_966_; 
lean_dec(v_val_963_);
v___x_966_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0));
return v___x_966_;
}
else
{
lean_object* v_val_967_; lean_object* v___x_968_; 
v_val_967_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v___x_965_, 1);
v___x_968_ = l_Lean_Json_getNat_x3f(v_val_967_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_val_963_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_974_ = lean_string_append(v___x_973_, v_a_969_);
lean_dec(v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_val_963_);
v_a_979_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_968_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_968_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_968_, 1);
v___x_988_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_989_ = l_Lake_JsonObject_getJson_x3f(v_val_963_, v___x_988_);
lean_dec(v_val_963_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_990_; 
lean_dec(v_a_987_);
v___x_990_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1));
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; 
v_val_991_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_989_, 1);
v___x_992_ = l_Lean_Json_getStr_x3f(v_val_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_a_987_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_998_ = lean_string_append(v___x_997_, v_a_993_);
lean_dec(v_a_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_a_987_);
v_a_1003_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_992_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_992_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 0);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
v_a_1011_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1013_ = v___x_992_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_992_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_a_987_);
lean_ctor_set(v___x_1015_, 1, v_a_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1017_ = v___x_1013_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
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
lean_dec(v_a_962_);
goto v___jp_934_;
}
}
}
}
v___jp_934_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_936_ = l_Lake_JsonObject_getJson_x3f(v_a_933_, v___x_935_);
lean_dec(v_a_933_);
if (lean_obj_tag(v___x_936_) == 0)
{
v_a_888_ = v___x_936_;
goto v___jp_887_;
}
else
{
lean_object* v_val_937_; lean_object* v___x_938_; lean_object* v_a_939_; 
v_val_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_937_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v___x_938_);
v_a_888_ = v_a_939_;
goto v___jp_887_;
}
}
}
else
{
lean_object* v___x_1020_; 
lean_dec_ref(v___x_932_);
v___x_1020_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_886_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
v_a_1029_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1031_ = v___x_1020_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1020_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
v___jp_887_:
{
if (lean_obj_tag(v_a_888_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_val_886_);
v_val_889_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_913_ == 0)
{
v___x_891_ = v_a_888_;
v_isShared_892_ = v_isSharedCheck_913_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v_a_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_913_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_889_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_del_object(v___x_891_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_a_902_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v___x_893_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_893_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v_a_902_);
v___x_907_ = v___x_891_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v_a_888_);
v___x_914_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_886_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_931_; 
v_a_923_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_931_ == 0)
{
v___x_925_ = v___x_914_;
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_914_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_a_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
}
lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object* v_lakeEnv_1040_, lean_object* v_owner_1041_, lean_object* v_pkg_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_url_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_url_1045_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_1040_, v_owner_1041_, v_pkg_1042_);
v___x_1046_ = l_Lake_Reservoir_lakeHeaders;
v___x_1047_ = l_Lake_getUrl(v_url_1045_, v___x_1046_, v_a_1043_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1130_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_a_1049_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1130_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1130_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; 
lean_inc(v_a_1048_);
v___x_1053_ = l_Lean_Json_parse(v_a_1048_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1056_ = lean_string_append(v_owner_1041_, v___x_1055_);
v___x_1057_ = lean_string_append(v___x_1056_, v_pkg_1042_);
v___x_1058_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_1057_);
v___x_1059_ = lean_string_append(v___x_1057_, v___x_1058_);
v___x_1060_ = lean_string_append(v___x_1059_, v_a_1054_);
lean_dec(v_a_1054_);
v___x_1061_ = 3;
v___x_1062_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*1, v___x_1061_);
v___x_1063_ = lean_array_get_size(v_a_1049_);
v___x_1064_ = lean_array_push(v_a_1049_, v___x_1062_);
v___x_1065_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1066_ = lean_string_append(v___x_1057_, v___x_1065_);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_string_utf8_byte_size(v_a_1048_);
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v_a_1048_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
v___x_1070_ = l_String_Slice_trimAscii(v___x_1069_);
v___x_1071_ = l_String_Slice_toString(v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = lean_string_append(v___x_1066_, v___x_1071_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = 0;
v___x_1074_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_1073_);
v___x_1075_ = lean_array_push(v___x_1064_, v___x_1074_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 1, v___x_1075_);
lean_ctor_set(v___x_1051_, 0, v___x_1063_);
v___x_1077_ = v___x_1051_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1079_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1080_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1083_ = lean_string_append(v_owner_1041_, v___x_1082_);
v___x_1084_ = lean_string_append(v___x_1083_, v_pkg_1042_);
v___x_1085_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_1084_);
v___x_1086_ = lean_string_append(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_string_append(v___x_1086_, v_a_1081_);
lean_dec(v_a_1081_);
v___x_1088_ = 3;
v___x_1089_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1, v___x_1088_);
v___x_1090_ = lean_array_get_size(v_a_1049_);
v___x_1091_ = lean_array_push(v_a_1049_, v___x_1089_);
v___x_1092_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1093_ = lean_string_append(v___x_1084_, v___x_1092_);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_string_utf8_byte_size(v_a_1048_);
v___x_1096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1096_, 0, v_a_1048_);
lean_ctor_set(v___x_1096_, 1, v___x_1094_);
lean_ctor_set(v___x_1096_, 2, v___x_1095_);
v___x_1097_ = l_String_Slice_trimAscii(v___x_1096_);
v___x_1098_ = l_String_Slice_toString(v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = lean_string_append(v___x_1093_, v___x_1098_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = 0;
v___x_1101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*1, v___x_1100_);
v___x_1102_ = lean_array_push(v___x_1091_, v___x_1101_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 1, v___x_1102_);
lean_ctor_set(v___x_1051_, 0, v___x_1090_);
v___x_1104_ = v___x_1051_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
else
{
lean_object* v_a_1106_; 
lean_dec(v_a_1048_);
v_a_1106_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1080_, 1);
if (lean_obj_tag(v_a_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; 
lean_dec_ref(v_owner_1041_);
v_a_1107_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v_a_1106_, 1);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_a_1107_);
v___x_1109_ = v___x_1051_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1107_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_a_1049_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
else
{
lean_object* v_status_1111_; lean_object* v_message_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v_status_1111_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_status_1111_);
v_message_1112_ = lean_ctor_get(v_a_1106_, 1);
lean_inc_ref(v_message_1112_);
lean_dec_ref_known(v_a_1106_, 2);
v___x_1113_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1114_ = lean_string_append(v_owner_1041_, v___x_1113_);
v___x_1115_ = lean_string_append(v___x_1114_, v_pkg_1042_);
v___x_1116_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__0));
v___x_1117_ = lean_string_append(v___x_1115_, v___x_1116_);
v___x_1118_ = l_Nat_reprFast(v_status_1111_);
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__1));
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
v___x_1122_ = lean_string_append(v___x_1121_, v_message_1112_);
lean_dec_ref(v_message_1112_);
v___x_1123_ = 3;
v___x_1124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*1, v___x_1123_);
v___x_1125_ = lean_array_get_size(v_a_1049_);
v___x_1126_ = lean_array_push(v_a_1049_, v___x_1124_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 1, v___x_1126_);
lean_ctor_set(v___x_1051_, 0, v___x_1125_);
v___x_1128_ = v___x_1051_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1147_; 
v_a_1131_ = lean_ctor_get(v___x_1047_, 0);
v_a_1132_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1134_ = v___x_1047_;
v_isShared_1135_ = v_isSharedCheck_1147_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_inc(v_a_1131_);
lean_dec(v___x_1047_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1147_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1136_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1137_ = lean_string_append(v_owner_1041_, v___x_1136_);
v___x_1138_ = lean_string_append(v___x_1137_, v_pkg_1042_);
v___x_1139_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_1140_ = lean_string_append(v___x_1138_, v___x_1139_);
v___x_1141_ = 3;
v___x_1142_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*1, v___x_1141_);
v___x_1143_ = lean_array_push(v_a_1132_, v___x_1142_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1143_);
v___x_1145_ = v___x_1134_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Reservoir_fetchPkgVersions_0interp(lean_interpreter_value* stack)
{
lean_object* v_lakeEnv_1040_ = stack[0].m_obj;
lean_object* v_owner_1041_ = stack[1].m_obj;
lean_object* v_pkg_1042_ = stack[2].m_obj;
lean_object* v_a_1043_ = stack[3].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1040_, v_owner_1041_, v_pkg_1042_, v_a_1043_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object* v_lakeEnv_1149_, lean_object* v_owner_1150_, lean_object* v_pkg_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1149_, v_owner_1150_, v_pkg_1151_, v_a_1152_);
lean_dec_ref(v_pkg_1151_);
return v_res_1154_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Reservoir(builtin);
}
#ifdef __cplusplus
}
#endif
