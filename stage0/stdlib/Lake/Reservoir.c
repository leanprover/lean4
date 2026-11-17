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
LEAN_EXPORT uint8_t l_Lake_RegistrySrc_isGit(lean_object* v_src_50_){
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
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_isGit___boxed(lean_object* v_src_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Lake_RegistrySrc_isGit(v_src_53_);
lean_dec_ref(v_src_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data(lean_object* v_src_56_){
_start:
{
lean_object* v_data_57_; 
v_data_57_ = lean_ctor_get(v_src_56_, 0);
lean_inc(v_data_57_);
return v_data_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_data___boxed(lean_object* v_src_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_RegistrySrc_data(v_src_58_);
lean_dec_ref(v_src_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_toJson(lean_object* v_src_60_){
_start:
{
if (lean_obj_tag(v_src_60_) == 0)
{
lean_object* v_data_61_; lean_object* v___x_62_; 
v_data_61_ = lean_ctor_get(v_src_60_, 0);
lean_inc(v_data_61_);
lean_dec_ref_known(v_src_60_, 5);
v___x_62_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_62_, 0, v_data_61_);
return v___x_62_;
}
else
{
lean_object* v_data_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_data_63_ = lean_ctor_get(v_src_60_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_src_60_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v_src_60_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_data_63_);
lean_dec(v_src_60_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 5);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_data_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0));
return v___x_76_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Json_getStr_x3f(v_x_75_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_a_86_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v___x_77_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_77_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v_a_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0));
return v___x_96_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Json_getStr_x3f(v_x_95_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_114_; 
v_a_106_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_114_ == 0)
{
v___x_108_ = v___x_97_;
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_97_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_a_106_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_fromJson_x3f(lean_object* v_val_127_){
_start:
{
lean_object* v_a_129_; lean_object* v___x_133_; 
v___x_133_ = l_Lean_Json_getObj_x3f(v_val_127_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v_a_129_ = v_a_134_;
goto v___jp_128_;
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_210_; 
v_a_135_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_210_ == 0)
{
v___x_137_ = v___x_133_;
v_isShared_138_ = v_isSharedCheck_210_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_210_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__1));
v___x_145_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_144_);
if (lean_obj_tag(v___x_145_) == 0)
{
goto v___jp_139_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_147_; 
v_val_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_146_);
lean_dec_ref_known(v___x_145_, 1);
v___x_147_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_146_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_del_object(v___x_137_);
lean_dec(v_a_135_);
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__2));
v___x_150_ = lean_string_append(v___x_149_, v_a_148_);
lean_dec(v_a_148_);
v_a_129_ = v___x_150_;
goto v___jp_128_;
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_209_; 
v_a_151_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_209_ == 0)
{
v___x_153_ = v___x_147_;
v_isShared_154_ = v_isSharedCheck_209_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_147_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_209_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
if (lean_obj_tag(v_a_151_) == 1)
{
lean_object* v_val_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v_a_159_; lean_object* v___y_165_; lean_object* v_a_166_; lean_object* v_a_177_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_del_object(v___x_137_);
v_val_155_ = lean_ctor_get(v_a_151_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v_a_151_, 1);
v___x_187_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__7));
v___x_188_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
v_a_177_ = v___x_189_;
goto v___jp_176_;
}
else
{
lean_object* v_val_190_; lean_object* v___x_191_; 
v_val_190_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v___x_188_, 1);
v___x_191_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_val_155_);
lean_del_object(v___x_153_);
lean_dec(v_a_135_);
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__8));
v___x_194_ = lean_string_append(v___x_193_, v_a_192_);
lean_dec(v_a_192_);
v_a_129_ = v___x_194_;
goto v___jp_128_;
}
else
{
lean_object* v_a_195_; 
v_a_195_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_191_, 1);
if (lean_obj_tag(v_a_195_) == 0)
{
v_a_177_ = v_a_195_;
goto v___jp_176_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_val_196_ = lean_ctor_get(v_a_195_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v_a_195_, 1);
v___x_197_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__9));
v___x_198_ = lean_string_dec_eq(v_val_196_, v___x_197_);
lean_dec(v_val_196_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
v_a_177_ = v___x_199_;
goto v___jp_176_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__10));
v___x_201_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
v_a_177_ = v___x_202_;
goto v___jp_176_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_204_; 
v_val_203_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_201_, 1);
v___x_204_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_val_155_);
lean_del_object(v___x_153_);
lean_dec(v_a_135_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_204_, 1);
v___x_206_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__11));
v___x_207_ = lean_string_append(v___x_206_, v_a_205_);
lean_dec(v_a_205_);
v_a_129_ = v___x_207_;
goto v___jp_128_;
}
else
{
lean_object* v_a_208_; 
v_a_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_204_, 1);
v_a_177_ = v_a_208_;
goto v___jp_176_;
}
}
}
}
}
}
v___jp_156_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_160_, 0, v_a_135_);
lean_ctor_set(v___x_160_, 1, v_val_155_);
lean_ctor_set(v___x_160_, 2, v___y_158_);
lean_ctor_set(v___x_160_, 3, v___y_157_);
lean_ctor_set(v___x_160_, 4, v_a_159_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_160_);
v___x_162_ = v___x_153_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
v___jp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__3));
v___x_168_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
v___y_157_ = v_a_166_;
v___y_158_ = v___y_165_;
v_a_159_ = v___x_169_;
goto v___jp_156_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_171_; 
v_val_170_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v___x_168_, 1);
v___x_171_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(v_val_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_a_166_);
lean_dec(v___y_165_);
lean_dec(v_val_155_);
lean_del_object(v___x_153_);
lean_dec(v_a_135_);
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
v___x_173_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__4));
v___x_174_ = lean_string_append(v___x_173_, v_a_172_);
lean_dec(v_a_172_);
v_a_129_ = v___x_174_;
goto v___jp_128_;
}
else
{
lean_object* v_a_175_; 
v_a_175_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_171_, 1);
v___y_157_ = v_a_166_;
v___y_158_ = v___y_165_;
v_a_159_ = v_a_175_;
goto v___jp_156_;
}
}
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__5));
v___x_179_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
v___y_165_ = v_a_177_;
v_a_166_ = v___x_180_;
goto v___jp_164_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; 
v_val_181_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v___x_179_, 1);
v___x_182_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_a_177_);
lean_dec(v_val_155_);
lean_del_object(v___x_153_);
lean_dec(v_a_135_);
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v___x_184_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__6));
v___x_185_ = lean_string_append(v___x_184_, v_a_183_);
lean_dec(v_a_183_);
v_a_129_ = v___x_185_;
goto v___jp_128_;
}
else
{
lean_object* v_a_186_; 
v_a_186_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_182_, 1);
v___y_165_ = v_a_177_;
v_a_166_ = v_a_186_;
goto v___jp_164_;
}
}
}
}
else
{
lean_del_object(v___x_153_);
lean_dec(v_a_151_);
goto v___jp_139_;
}
}
}
}
v___jp_139_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_a_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
v___jp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__0));
v___x_131_ = lean_string_append(v___x_130_, v_a_129_);
lean_dec_ref(v_a_129_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object* v_as_224_, size_t v_sz_225_, size_t v_i_226_, lean_object* v_b_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_lt(v_i_226_, v_sz_225_);
if (v___x_228_ == 0)
{
lean_inc_ref(v_b_227_);
return v_b_227_;
}
else
{
lean_object* v___x_229_; lean_object* v_a_230_; uint8_t v___x_231_; 
v___x_229_ = lean_box(0);
v_a_230_ = lean_array_uget_borrowed(v_as_224_, v_i_226_);
v___x_231_ = l_Lake_RegistrySrc_isGit(v_a_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; size_t v___x_233_; size_t v___x_234_; 
v___x_232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_226_, v___x_233_);
v_i_226_ = v___x_234_;
v_b_227_ = v___x_232_;
goto _start;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_inc(v_a_230_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_a_230_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_229_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object* v_as_239_, lean_object* v_sz_240_, lean_object* v_i_241_, lean_object* v_b_242_){
_start:
{
size_t v_sz_boxed_243_; size_t v_i_boxed_244_; lean_object* v_res_245_; 
v_sz_boxed_243_ = lean_unbox_usize(v_sz_240_);
lean_dec(v_sz_240_);
v_i_boxed_244_ = lean_unbox_usize(v_i_241_);
lean_dec(v_i_241_);
v_res_245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_as_239_, v_sz_boxed_243_, v_i_boxed_244_, v_b_242_);
lean_dec_ref(v_b_242_);
lean_dec_ref(v_as_239_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object* v_pkg_246_){
_start:
{
lean_object* v_sources_247_; lean_object* v___x_248_; lean_object* v___x_249_; size_t v_sz_250_; size_t v___x_251_; lean_object* v___x_252_; lean_object* v_fst_253_; 
v_sources_247_ = lean_ctor_get(v_pkg_246_, 2);
v___x_248_ = lean_box(0);
v___x_249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v_sz_250_ = lean_array_size(v_sources_247_);
v___x_251_ = ((size_t)0ULL);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_sources_247_, v_sz_250_, v___x_251_, v___x_249_);
v_fst_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_fst_253_);
lean_dec_ref(v___x_252_);
if (lean_obj_tag(v_fst_253_) == 0)
{
return v___x_248_;
}
else
{
lean_object* v_val_254_; 
v_val_254_ = lean_ctor_get(v_fst_253_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v_fst_253_, 1);
return v_val_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object* v_pkg_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lake_RegistryPkg_gitSrc_x3f(v_pkg_255_);
lean_dec_ref(v_pkg_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object* v_src_257_){
_start:
{
lean_object* v_data_258_; 
v_data_258_ = lean_ctor_get(v_src_257_, 3);
lean_inc(v_data_258_);
return v_data_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object* v_src_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lake_RegistryPkg_toJson(v_src_259_);
lean_dec_ref(v_src_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t v_sz_263_, size_t v_i_264_, lean_object* v_bs_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_264_, v_sz_263_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_bs_265_);
return v___x_267_;
}
else
{
lean_object* v_v_268_; lean_object* v___x_269_; lean_object* v_bs_x27_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v_v_268_ = lean_array_uget(v_bs_265_, v_i_264_);
v___x_269_ = lean_unsigned_to_nat(0u);
v_bs_x27_270_ = lean_array_uset(v_bs_265_, v_i_264_, v___x_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_264_, v___x_271_);
v___x_273_ = lean_array_uset(v_bs_x27_270_, v_i_264_, v_v_268_);
v_i_264_ = v___x_272_;
v_bs_265_ = v___x_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_bs_277_){
_start:
{
size_t v_sz_boxed_278_; size_t v_i_boxed_279_; lean_object* v_res_280_; 
v_sz_boxed_278_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_279_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_boxed_278_, v_i_boxed_279_, v_bs_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 4)
{
lean_object* v_elems_284_; size_t v_sz_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_elems_284_ = lean_ctor_get(v_x_283_, 0);
lean_inc_ref(v_elems_284_);
lean_dec_ref_known(v_x_283_, 1);
v_sz_285_ = lean_array_size(v_elems_284_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_285_, v___x_286_, v_elems_284_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_288_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_289_ = lean_unsigned_to_nat(80u);
v___x_290_ = l_Lean_Json_pretty(v_x_283_, v___x_289_);
v___x_291_ = lean_string_append(v___x_288_, v___x_290_);
lean_dec_ref(v___x_290_);
v___x_292_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0));
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(v_x_297_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_a_308_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v___x_299_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_299_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(size_t v_sz_317_, size_t v_i_318_, lean_object* v_bs_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_lt(v_i_318_, v_sz_317_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_bs_319_);
return v___x_321_;
}
else
{
lean_object* v_v_322_; lean_object* v___x_323_; 
v_v_322_ = lean_array_uget_borrowed(v_bs_319_, v_i_318_);
lean_inc(v_v_322_);
v___x_323_ = l_Lake_RegistrySrc_fromJson_x3f(v_v_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_bs_319_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_a_332_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_323_, 1);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_319_, v_i_318_, v___x_333_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_318_, v___x_335_);
v___x_337_ = lean_array_uset(v_bs_x27_334_, v_i_318_, v_a_332_);
v_i_318_ = v___x_336_;
v_bs_319_ = v___x_337_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object* v_sz_339_, lean_object* v_i_340_, lean_object* v_bs_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_339_);
lean_dec(v_sz_339_);
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_boxed_342_, v_i_boxed_343_, v_bs_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object* v_val_356_){
_start:
{
lean_object* v_a_358_; lean_object* v___x_362_; 
v___x_362_ = l_Lean_Json_getObj_x3f(v_val_356_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v_a_358_ = v_a_363_;
goto v___jp_357_;
}
else
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_364_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_362_, 1);
v___x_365_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__1));
v___x_366_ = l_Lake_JsonObject_getJson_x3f(v_a_364_, v___x_365_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_367_; 
lean_dec(v_a_364_);
v___x_367_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__2));
v_a_358_ = v___x_367_;
goto v___jp_357_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_369_; 
v_val_368_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v___x_366_, 1);
v___x_369_ = l_Lean_Json_getStr_x3f(v_val_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_a_364_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__3));
v___x_372_ = lean_string_append(v___x_371_, v_a_370_);
lean_dec(v_a_370_);
v_a_358_ = v___x_372_;
goto v___jp_357_;
}
else
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_373_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_369_, 1);
v___x_374_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__4));
v___x_375_ = l_Lake_JsonObject_getJson_x3f(v_a_364_, v___x_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v___x_376_; 
lean_dec(v_a_373_);
lean_dec(v_a_364_);
v___x_376_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__5));
v_a_358_ = v___x_376_;
goto v___jp_357_;
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
lean_dec(v_a_364_);
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
v___x_380_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__6));
v___x_381_ = lean_string_append(v___x_380_, v_a_379_);
lean_dec(v_a_379_);
v_a_358_ = v___x_381_;
goto v___jp_357_;
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_415_; 
v_a_382_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_415_ == 0)
{
v___x_384_ = v___x_378_;
v_isShared_385_ = v_isSharedCheck_415_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_415_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_a_387_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__8));
v___x_407_ = l_Lake_JsonObject_getJson_x3f(v_a_364_, v___x_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
goto v___jp_404_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; 
v_val_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(v_val_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_del_object(v___x_384_);
lean_dec(v_a_382_);
lean_dec(v_a_373_);
lean_dec(v_a_364_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__9));
v___x_412_ = lean_string_append(v___x_411_, v_a_410_);
lean_dec(v_a_410_);
v_a_358_ = v___x_412_;
goto v___jp_357_;
}
else
{
lean_object* v_a_413_; 
v_a_413_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_409_, 1);
if (lean_obj_tag(v_a_413_) == 0)
{
goto v___jp_404_;
}
else
{
lean_object* v_val_414_; 
v_val_414_ = lean_ctor_get(v_a_413_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v_a_413_, 1);
v_a_387_ = v_val_414_;
goto v___jp_386_;
}
}
}
v___jp_386_:
{
size_t v_sz_388_; size_t v___x_389_; lean_object* v___x_390_; 
v_sz_388_ = lean_array_size(v_a_387_);
v___x_389_ = ((size_t)0ULL);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_388_, v___x_389_, v_a_387_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; 
lean_del_object(v___x_384_);
lean_dec(v_a_382_);
lean_dec(v_a_373_);
lean_dec(v_a_364_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v_a_358_ = v_a_391_;
goto v___jp_357_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_403_; 
v_a_392_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_403_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_403_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_403_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 5);
lean_ctor_set(v___x_384_, 0, v_a_364_);
v___x_397_ = v___x_384_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_364_);
v___x_397_ = v_reuseFailAlloc_402_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_398_, 0, v_a_373_);
lean_ctor_set(v___x_398_, 1, v_a_382_);
lean_ctor_set(v___x_398_, 2, v_a_392_);
lean_ctor_set(v___x_398_, 3, v___x_397_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_398_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
v___jp_404_:
{
lean_object* v___x_405_; 
v___x_405_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__7));
v_a_387_ = v___x_405_;
goto v___jp_386_;
}
}
}
}
}
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__0));
v___x_360_ = lean_string_append(v___x_359_, v_a_358_);
lean_dec_ref(v_a_358_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object* v_lakeEnv_420_, lean_object* v_owner_421_, lean_object* v_pkg_422_){
_start:
{
lean_object* v_reservoirApiUrl_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_reservoirApiUrl_423_ = lean_ctor_get(v_lakeEnv_420_, 3);
lean_inc_ref(v_reservoirApiUrl_423_);
lean_dec_ref(v_lakeEnv_420_);
v___x_424_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_425_ = lean_string_append(v_reservoirApiUrl_423_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_427_ = l_Lake_uriEncode(v_owner_421_, v___x_426_);
v___x_428_ = lean_string_append(v___x_425_, v___x_427_);
lean_dec_ref(v___x_427_);
v___x_429_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_430_ = lean_string_append(v___x_428_, v___x_429_);
v___x_431_ = l_Lake_uriEncode(v_pkg_422_, v___x_426_);
v___x_432_ = lean_string_append(v___x_430_, v___x_431_);
lean_dec_ref(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object* v_lakeEnv_433_, lean_object* v_owner_434_, lean_object* v_pkg_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_433_, v_owner_434_, v_pkg_435_);
lean_dec_ref(v_pkg_435_);
lean_dec_ref(v_owner_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_440_; 
v___x_440_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0));
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Json_getObj_x3f(v_x_439_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
v_a_450_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_452_ = v___x_441_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_441_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_a_450_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0));
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_x_461_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* v_val_478_){
_start:
{
lean_object* v___x_498_; 
lean_inc(v_val_478_);
v___x_498_ = l_Lean_Json_getObj_x3f(v_val_478_);
if (lean_obj_tag(v___x_498_) == 1)
{
lean_object* v_a_499_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_531_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_532_ = l_Lake_JsonObject_getJson_x3f(v_a_499_, v___x_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
goto v___jp_500_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_534_; 
v_val_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_499_);
lean_dec(v_val_478_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_539_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_540_ = lean_string_append(v___x_539_, v_a_535_);
lean_dec(v_a_535_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_534_, 1);
if (lean_obj_tag(v_a_545_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_a_499_);
lean_dec(v_val_478_);
v_val_546_ = lean_ctor_get(v_a_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v_a_545_, 1);
v___x_547_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_548_ = l_Lake_JsonObject_getJson_x3f(v_val_546_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v___x_549_; 
lean_dec(v_val_546_);
v___x_549_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5));
return v___x_549_;
}
else
{
lean_object* v_val_550_; lean_object* v___x_551_; 
v_val_550_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v___x_548_, 1);
v___x_551_ = l_Lean_Json_getNat_x3f(v_val_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_val_546_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_557_ = lean_string_append(v___x_556_, v_a_552_);
lean_dec(v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_562_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_551_, 1);
v___x_563_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_564_ = l_Lake_JsonObject_getJson_x3f(v_val_546_, v___x_563_);
lean_dec(v_val_546_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
lean_dec(v_a_562_);
v___x_565_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9));
return v___x_565_;
}
else
{
lean_object* v_val_566_; lean_object* v___x_567_; 
v_val_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_564_, 1);
v___x_567_ = l_Lean_Json_getStr_x3f(v_val_566_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_562_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_573_ = lean_string_append(v___x_572_, v_a_568_);
lean_dec(v_a_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_a_578_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v___x_567_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_567_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v_a_562_);
lean_ctor_set(v___x_582_, 1, v_a_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_545_);
goto v___jp_500_;
}
}
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_502_ = l_Lake_JsonObject_getJson_x3f(v_a_499_, v___x_501_);
lean_dec(v_a_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
goto v___jp_479_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_504_; lean_object* v_a_505_; 
v_val_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_503_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
if (lean_obj_tag(v_a_505_) == 1)
{
lean_object* v_val_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_val_478_);
v_val_506_ = lean_ctor_get(v_a_505_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_505_);
if (v_isSharedCheck_530_ == 0)
{
v___x_508_ = v_a_505_;
v_isShared_509_ = v_isSharedCheck_530_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_val_506_);
lean_dec(v_a_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_530_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_506_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_508_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v_a_519_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_510_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 0, v_a_519_);
v___x_524_ = v___x_508_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
else
{
lean_dec(v_a_505_);
goto v___jp_479_;
}
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v___x_498_);
v___x_587_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_478_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_a_596_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v___x_587_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_a_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
v___jp_479_:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_478_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
v_a_489_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v___x_480_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_480_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v_a_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* v_lakeEnv_610_, lean_object* v_owner_611_, lean_object* v_pkg_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_url_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_url_615_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_610_, v_owner_611_, v_pkg_612_);
v___x_616_ = l_Lake_Reservoir_lakeHeaders;
v___x_617_ = l_Lake_getUrl(v_url_615_, v___x_616_, v_a_613_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_709_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_a_619_ = lean_ctor_get(v___x_617_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_709_ == 0)
{
v___x_621_ = v___x_617_;
v_isShared_622_ = v_isSharedCheck_709_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_709_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; 
lean_inc(v_a_618_);
v___x_623_ = l_Lean_Json_parse(v_a_618_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_626_ = lean_string_append(v_owner_611_, v___x_625_);
v___x_627_ = lean_string_append(v___x_626_, v_pkg_612_);
v___x_628_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_627_);
v___x_629_ = lean_string_append(v___x_627_, v___x_628_);
v___x_630_ = lean_string_append(v___x_629_, v_a_624_);
lean_dec(v_a_624_);
v___x_631_ = 3;
v___x_632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_631_);
v___x_633_ = lean_array_get_size(v_a_619_);
v___x_634_ = lean_array_push(v_a_619_, v___x_632_);
v___x_635_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_636_ = lean_string_append(v___x_627_, v___x_635_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_string_utf8_byte_size(v_a_618_);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v_a_618_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
v___x_640_ = l_String_Slice_trimAscii(v___x_639_);
v___x_641_ = l_String_Slice_toString(v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_string_append(v___x_636_, v___x_641_);
lean_dec_ref(v___x_641_);
v___x_643_ = 0;
v___x_644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*1, v___x_643_);
v___x_645_ = lean_array_push(v___x_634_, v___x_644_);
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 1);
lean_ctor_set(v___x_621_, 1, v___x_645_);
lean_ctor_set(v___x_621_, 0, v___x_633_);
v___x_647_ = v___x_621_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_623_, 1);
v___x_650_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_653_ = lean_string_append(v_owner_611_, v___x_652_);
v___x_654_ = lean_string_append(v___x_653_, v_pkg_612_);
v___x_655_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_654_);
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
v___x_657_ = lean_string_append(v___x_656_, v_a_651_);
lean_dec(v_a_651_);
v___x_658_ = 3;
v___x_659_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_658_);
v___x_660_ = lean_array_get_size(v_a_619_);
v___x_661_ = lean_array_push(v_a_619_, v___x_659_);
v___x_662_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_663_ = lean_string_append(v___x_654_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_string_utf8_byte_size(v_a_618_);
v___x_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_666_, 0, v_a_618_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
lean_ctor_set(v___x_666_, 2, v___x_665_);
v___x_667_ = l_String_Slice_trimAscii(v___x_666_);
v___x_668_ = l_String_Slice_toString(v___x_667_);
lean_dec_ref(v___x_667_);
v___x_669_ = lean_string_append(v___x_663_, v___x_668_);
lean_dec_ref(v___x_668_);
v___x_670_ = 0;
v___x_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*1, v___x_670_);
v___x_672_ = lean_array_push(v___x_661_, v___x_671_);
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 1);
lean_ctor_set(v___x_621_, 1, v___x_672_);
lean_ctor_set(v___x_621_, 0, v___x_660_);
v___x_674_ = v___x_621_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
else
{
lean_object* v_a_676_; 
lean_dec(v_a_618_);
v_a_676_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_650_, 1);
if (lean_obj_tag(v_a_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_owner_611_);
v_a_677_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_687_ == 0)
{
v___x_679_ = v_a_676_;
v_isShared_680_ = v_isSharedCheck_687_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v_a_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_687_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 1);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_682_);
v___x_684_ = v___x_621_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_619_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_status_688_; lean_object* v_message_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_status_688_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_status_688_);
v_message_689_ = lean_ctor_get(v_a_676_, 1);
lean_inc_ref(v_message_689_);
lean_dec_ref_known(v_a_676_, 2);
v___x_690_ = lean_unsigned_to_nat(404u);
v___x_691_ = lean_nat_dec_eq(v_status_688_, v___x_690_);
lean_dec(v_status_688_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_692_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_693_ = lean_string_append(v_owner_611_, v___x_692_);
v___x_694_ = lean_string_append(v___x_693_, v_pkg_612_);
v___x_695_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__3));
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
v___x_697_ = lean_string_append(v___x_696_, v_message_689_);
lean_dec_ref(v_message_689_);
v___x_698_ = 3;
v___x_699_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*1, v___x_698_);
v___x_700_ = lean_array_get_size(v_a_619_);
v___x_701_ = lean_array_push(v_a_619_, v___x_699_);
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 1);
lean_ctor_set(v___x_621_, 1, v___x_701_);
lean_ctor_set(v___x_621_, 0, v___x_700_);
v___x_703_ = v___x_621_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec_ref(v_message_689_);
lean_dec_ref(v_owner_611_);
v___x_705_ = lean_box(0);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_705_);
v___x_707_ = v___x_621_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_a_619_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_726_; 
v_a_710_ = lean_ctor_get(v___x_617_, 0);
v_a_711_ = lean_ctor_get(v___x_617_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_726_ == 0)
{
v___x_713_ = v___x_617_;
v_isShared_714_ = v_isSharedCheck_726_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_inc(v_a_710_);
lean_dec(v___x_617_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_726_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_715_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_716_ = lean_string_append(v_owner_611_, v___x_715_);
v___x_717_ = lean_string_append(v___x_716_, v_pkg_612_);
v___x_718_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
v___x_720_ = 3;
v___x_721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*1, v___x_720_);
v___x_722_ = lean_array_push(v_a_711_, v___x_721_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_722_);
v___x_724_ = v___x_713_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_710_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* v_lakeEnv_727_, lean_object* v_owner_728_, lean_object* v_pkg_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_727_, v_owner_728_, v_pkg_729_, v_a_730_);
lean_dec_ref(v_pkg_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object* v_val_740_){
_start:
{
lean_object* v_a_742_; lean_object* v_a_747_; lean_object* v___x_750_; 
v___x_750_ = l_Lean_Json_getObj_x3f(v_val_740_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v_a_742_ = v_a_751_;
goto v___jp_741_;
}
else
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_a_752_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_750_, 1);
v___x_753_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__2));
v___x_754_ = l_Lake_JsonObject_getJson_x3f(v_a_752_, v___x_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; 
lean_dec(v_a_752_);
v___x_755_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__3));
v_a_742_ = v___x_755_;
goto v___jp_741_;
}
else
{
lean_object* v_val_756_; lean_object* v___x_757_; 
v_val_756_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v___x_754_, 1);
v___x_757_ = l_Lean_Json_getStr_x3f(v_val_756_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; 
lean_dec(v_a_752_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v_a_747_ = v_a_758_;
goto v___jp_746_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_757_, 1);
v___x_760_ = l_Lake_StdVer_parse(v_a_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; 
lean_dec(v_a_752_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v_a_747_ = v_a_761_;
goto v___jp_746_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_760_, 1);
v___x_763_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__4));
v___x_764_ = l_Lake_JsonObject_getJson_x3f(v_a_752_, v___x_763_);
lean_dec(v_a_752_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_765_; 
lean_dec(v_a_762_);
v___x_765_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__5));
v_a_742_ = v___x_765_;
goto v___jp_741_;
}
else
{
lean_object* v_val_766_; lean_object* v___x_767_; 
v_val_766_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_764_, 1);
v___x_767_ = l_Lean_Json_getStr_x3f(v_val_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_a_762_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__6));
v___x_770_ = lean_string_append(v___x_769_, v_a_768_);
lean_dec(v_a_768_);
v_a_742_ = v___x_770_;
goto v___jp_741_;
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_779_; 
v_a_771_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_779_ == 0)
{
v___x_773_ = v___x_767_;
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_767_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_a_762_);
lean_ctor_set(v___x_775_, 1, v_a_771_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
}
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__0));
v___x_744_ = lean_string_append(v___x_743_, v_a_742_);
lean_dec_ref(v_a_742_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__1));
v___x_749_ = lean_string_append(v___x_748_, v_a_747_);
lean_dec_ref(v_a_747_);
v_a_742_ = v___x_749_;
goto v___jp_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object* v_lakeEnv_783_, lean_object* v_owner_784_, lean_object* v_pkg_785_){
_start:
{
lean_object* v_reservoirApiUrl_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_reservoirApiUrl_786_ = lean_ctor_get(v_lakeEnv_783_, 3);
lean_inc_ref(v_reservoirApiUrl_786_);
lean_dec_ref(v_lakeEnv_783_);
v___x_787_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_788_ = lean_string_append(v_reservoirApiUrl_786_, v___x_787_);
v___x_789_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_790_ = l_Lake_uriEncode(v_owner_784_, v___x_789_);
v___x_791_ = lean_string_append(v___x_788_, v___x_790_);
lean_dec_ref(v___x_790_);
v___x_792_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
v___x_794_ = l_Lake_uriEncode(v_pkg_785_, v___x_789_);
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
lean_dec_ref(v___x_794_);
v___x_796_ = ((lean_object*)(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0));
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl___boxed(lean_object* v_lakeEnv_798_, lean_object* v_owner_799_, lean_object* v_pkg_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_798_, v_owner_799_, v_pkg_800_);
lean_dec_ref(v_pkg_800_);
lean_dec_ref(v_owner_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t v_sz_802_, size_t v_i_803_, lean_object* v_bs_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = lean_usize_dec_lt(v_i_803_, v_sz_802_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_bs_804_);
return v___x_806_;
}
else
{
lean_object* v_v_807_; lean_object* v___x_808_; 
v_v_807_ = lean_array_uget_borrowed(v_bs_804_, v_i_803_);
lean_inc(v_v_807_);
v___x_808_ = l_Lake_RegistryVer_fromJson_x3f(v_v_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_bs_804_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v_bs_x27_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v_a_817_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_808_, 1);
v___x_818_ = lean_unsigned_to_nat(0u);
v_bs_x27_819_ = lean_array_uset(v_bs_804_, v_i_803_, v___x_818_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_803_, v___x_820_);
v___x_822_ = lean_array_uset(v_bs_x27_819_, v_i_803_, v_a_817_);
v_i_803_ = v___x_821_;
v_bs_804_ = v___x_822_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_bs_826_){
_start:
{
size_t v_sz_boxed_827_; size_t v_i_boxed_828_; lean_object* v_res_829_; 
v_sz_boxed_827_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_828_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_827_, v_i_boxed_828_, v_bs_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 4)
{
lean_object* v_elems_831_; size_t v_sz_832_; size_t v___x_833_; lean_object* v___x_834_; 
v_elems_831_ = lean_ctor_get(v_x_830_, 0);
lean_inc_ref(v_elems_831_);
lean_dec_ref_known(v_x_830_, 1);
v_sz_832_ = lean_array_size(v_elems_831_);
v___x_833_ = ((size_t)0ULL);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_832_, v___x_833_, v_elems_831_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_835_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_836_ = lean_unsigned_to_nat(80u);
v___x_837_ = l_Lean_Json_pretty(v_x_830_, v___x_836_);
v___x_838_ = lean_string_append(v___x_835_, v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_840_ = lean_string_append(v___x_838_, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object* v_val_846_){
_start:
{
lean_object* v___x_866_; 
lean_inc(v_val_846_);
v___x_866_ = l_Lean_Json_getObj_x3f(v_val_846_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v_a_867_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_899_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_900_ = l_Lake_JsonObject_getJson_x3f(v_a_867_, v___x_899_);
if (lean_obj_tag(v___x_900_) == 0)
{
goto v___jp_868_;
}
else
{
lean_object* v_val_901_; lean_object* v___x_902_; 
v_val_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_867_);
lean_dec(v_val_846_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_912_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_907_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_908_ = lean_string_append(v___x_907_, v_a_903_);
lean_dec(v_a_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
else
{
lean_object* v_a_913_; 
v_a_913_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_902_, 1);
if (lean_obj_tag(v_a_913_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec(v_a_867_);
lean_dec(v_val_846_);
v_val_914_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v_a_913_, 1);
v___x_915_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_916_ = l_Lake_JsonObject_getJson_x3f(v_val_914_, v___x_915_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; 
lean_dec(v_val_914_);
v___x_917_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0));
return v___x_917_;
}
else
{
lean_object* v_val_918_; lean_object* v___x_919_; 
v_val_918_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v___x_916_, 1);
v___x_919_ = l_Lean_Json_getNat_x3f(v_val_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_val_914_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_929_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_924_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_925_ = lean_string_append(v___x_924_, v_a_920_);
lean_dec(v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_919_, 1);
v___x_931_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_932_ = l_Lake_JsonObject_getJson_x3f(v_val_914_, v___x_931_);
lean_dec(v_val_914_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; 
lean_dec(v_a_930_);
v___x_933_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1));
return v___x_933_;
}
else
{
lean_object* v_val_934_; lean_object* v___x_935_; 
v_val_934_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v___x_932_, 1);
v___x_935_ = l_Lean_Json_getStr_x3f(v_val_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_a_930_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_945_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_941_ = lean_string_append(v___x_940_, v_a_936_);
lean_dec(v_a_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
v_a_946_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v___x_935_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_935_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v_a_930_);
lean_ctor_set(v___x_950_, 1, v_a_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_913_);
goto v___jp_868_;
}
}
}
v___jp_868_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_870_ = l_Lake_JsonObject_getJson_x3f(v_a_867_, v___x_869_);
lean_dec(v_a_867_);
if (lean_obj_tag(v___x_870_) == 0)
{
goto v___jp_847_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_872_; lean_object* v_a_873_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_871_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
if (lean_obj_tag(v_a_873_) == 1)
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_val_846_);
v_val_874_ = lean_ctor_get(v_a_873_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_898_ == 0)
{
v___x_876_ = v_a_873_;
v_isShared_877_ = v_isSharedCheck_898_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v_a_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_898_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_874_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_876_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_897_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_897_ == 0)
{
v___x_889_ = v___x_878_;
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_878_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 0);
lean_ctor_set(v___x_876_, 0, v_a_887_);
v___x_892_ = v___x_876_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
else
{
lean_dec(v_a_873_);
goto v___jp_847_;
}
}
}
}
else
{
lean_object* v___x_955_; 
lean_dec_ref(v___x_866_);
v___x_955_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_846_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_a_964_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_955_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_955_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v_a_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
v___jp_847_:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_a_857_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_865_ == 0)
{
v___x_859_ = v___x_848_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_848_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_a_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object* v_lakeEnv_975_, lean_object* v_owner_976_, lean_object* v_pkg_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_url_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_url_980_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_975_, v_owner_976_, v_pkg_977_);
v___x_981_ = l_Lake_Reservoir_lakeHeaders;
v___x_982_ = l_Lake_getUrl(v_url_980_, v___x_981_, v_a_978_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1065_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_a_984_ = lean_ctor_get(v___x_982_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_986_ = v___x_982_;
v_isShared_987_ = v_isSharedCheck_1065_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1065_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; 
lean_inc(v_a_983_);
v___x_988_ = l_Lean_Json_parse(v_a_983_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_991_ = lean_string_append(v_owner_976_, v___x_990_);
v___x_992_ = lean_string_append(v___x_991_, v_pkg_977_);
v___x_993_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_992_);
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
v___x_995_ = lean_string_append(v___x_994_, v_a_989_);
lean_dec(v_a_989_);
v___x_996_ = 3;
v___x_997_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*1, v___x_996_);
v___x_998_ = lean_array_get_size(v_a_984_);
v___x_999_ = lean_array_push(v_a_984_, v___x_997_);
v___x_1000_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1001_ = lean_string_append(v___x_992_, v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_string_utf8_byte_size(v_a_983_);
v___x_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_a_983_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
v___x_1005_ = l_String_Slice_trimAscii(v___x_1004_);
v___x_1006_ = l_String_Slice_toString(v___x_1005_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = lean_string_append(v___x_1001_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = 0;
v___x_1009_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_1008_);
v___x_1010_ = lean_array_push(v___x_999_, v___x_1009_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 1);
lean_ctor_set(v___x_986_, 1, v___x_1010_);
lean_ctor_set(v___x_986_, 0, v___x_998_);
v___x_1012_ = v___x_986_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_988_, 1);
v___x_1015_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1018_ = lean_string_append(v_owner_976_, v___x_1017_);
v___x_1019_ = lean_string_append(v___x_1018_, v_pkg_977_);
v___x_1020_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_1019_);
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_string_append(v___x_1021_, v_a_1016_);
lean_dec(v_a_1016_);
v___x_1023_ = 3;
v___x_1024_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*1, v___x_1023_);
v___x_1025_ = lean_array_get_size(v_a_984_);
v___x_1026_ = lean_array_push(v_a_984_, v___x_1024_);
v___x_1027_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1028_ = lean_string_append(v___x_1019_, v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_string_utf8_byte_size(v_a_983_);
v___x_1031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1031_, 0, v_a_983_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v___x_1032_ = l_String_Slice_trimAscii(v___x_1031_);
v___x_1033_ = l_String_Slice_toString(v___x_1032_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_string_append(v___x_1028_, v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1035_ = 0;
v___x_1036_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_1035_);
v___x_1037_ = lean_array_push(v___x_1026_, v___x_1036_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 1);
lean_ctor_set(v___x_986_, 1, v___x_1037_);
lean_ctor_set(v___x_986_, 0, v___x_1025_);
v___x_1039_ = v___x_986_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
else
{
lean_object* v_a_1041_; 
lean_dec(v_a_983_);
v_a_1041_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1015_, 1);
if (lean_obj_tag(v_a_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; 
lean_dec_ref(v_owner_976_);
v_a_1042_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v_a_1041_, 1);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v_a_1042_);
v___x_1044_ = v___x_986_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1042_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_984_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v_status_1046_; lean_object* v_message_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v_status_1046_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_status_1046_);
v_message_1047_ = lean_ctor_get(v_a_1041_, 1);
lean_inc_ref(v_message_1047_);
lean_dec_ref_known(v_a_1041_, 2);
v___x_1048_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1049_ = lean_string_append(v_owner_976_, v___x_1048_);
v___x_1050_ = lean_string_append(v___x_1049_, v_pkg_977_);
v___x_1051_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__0));
v___x_1052_ = lean_string_append(v___x_1050_, v___x_1051_);
v___x_1053_ = l_Nat_reprFast(v_status_1046_);
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__1));
v___x_1056_ = lean_string_append(v___x_1054_, v___x_1055_);
v___x_1057_ = lean_string_append(v___x_1056_, v_message_1047_);
lean_dec_ref(v_message_1047_);
v___x_1058_ = 3;
v___x_1059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*1, v___x_1058_);
v___x_1060_ = lean_array_get_size(v_a_984_);
v___x_1061_ = lean_array_push(v_a_984_, v___x_1059_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 1);
lean_ctor_set(v___x_986_, 1, v___x_1061_);
lean_ctor_set(v___x_986_, 0, v___x_1060_);
v___x_1063_ = v___x_986_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1082_; 
v_a_1066_ = lean_ctor_get(v___x_982_, 0);
v_a_1067_ = lean_ctor_get(v___x_982_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1069_ = v___x_982_;
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_inc(v_a_1066_);
lean_dec(v___x_982_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1071_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1072_ = lean_string_append(v_owner_976_, v___x_1071_);
v___x_1073_ = lean_string_append(v___x_1072_, v_pkg_977_);
v___x_1074_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_1075_ = lean_string_append(v___x_1073_, v___x_1074_);
v___x_1076_ = 3;
v___x_1077_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1, v___x_1076_);
v___x_1078_ = lean_array_push(v_a_1067_, v___x_1077_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1078_);
v___x_1080_ = v___x_1069_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1066_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object* v_lakeEnv_1083_, lean_object* v_owner_1084_, lean_object* v_pkg_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1083_, v_owner_1084_, v_pkg_1085_, v_a_1086_);
lean_dec_ref(v_pkg_1085_);
return v_res_1088_;
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
