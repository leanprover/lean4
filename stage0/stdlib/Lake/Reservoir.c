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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lake_RegistrySrc_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_data_8_; lean_object* v_url_9_; lean_object* v_githubUrl_x3f_10_; lean_object* v_defaultBranch_x3f_11_; lean_object* v_subDir_x3f_12_; lean_object* v___x_13_; 
v_data_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_data_8_);
v_url_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_url_9_);
v_githubUrl_x3f_10_ = lean_ctor_get(v_t_6_, 2);
lean_inc(v_githubUrl_x3f_10_);
v_defaultBranch_x3f_11_ = lean_ctor_get(v_t_6_, 3);
lean_inc(v_defaultBranch_x3f_11_);
v_subDir_x3f_12_ = lean_ctor_get(v_t_6_, 4);
lean_inc(v_subDir_x3f_12_);
lean_dec_ref_known(v_t_6_, 5);
v___x_13_ = lean_apply_5(v_k_7_, v_data_8_, v_url_9_, v_githubUrl_x3f_10_, v_defaultBranch_x3f_11_, v_subDir_x3f_12_);
return v___x_13_;
}
else
{
lean_object* v_data_14_; lean_object* v___x_15_; 
v_data_14_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_data_14_);
lean_dec_ref_known(v_t_6_, 1);
v___x_15_ = lean_apply_1(v_k_7_, v_data_14_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lake_RegistrySrc_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_24_, v_h_25_, v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_git_elim___redArg(lean_object* v_t_28_, lean_object* v_git_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_28_, v_git_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_git_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_git_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_32_, v_git_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_other_elim___redArg(lean_object* v_t_36_, lean_object* v_other_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_36_, v_other_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistrySrc_other_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_other_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_40_, v_other_42_);
return v___x_43_;
}
}
LEAN_EXPORT uint8_t l_Lake_RegistrySrc_isGit(lean_object* v_src_51_){
_start:
{
if (lean_obj_tag(v_src_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_77_; 
v___x_77_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0));
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0));
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
v___x_148_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_147_);
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
v___x_195_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_194_);
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
v___x_209_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_208_);
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
lean_ctor_set(v___x_162_, 2, v___y_159_);
lean_ctor_set(v___x_162_, 3, v___y_160_);
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
v___y_159_ = v___y_167_;
v___y_160_ = v_a_168_;
v_a_161_ = v___x_171_;
goto v___jp_158_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v___x_170_, 1);
v___x_173_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(v_val_172_);
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
v___y_159_ = v___y_167_;
v___y_160_ = v_a_168_;
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
v___x_185_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_184_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object* v_as_230_, size_t v_sz_231_, size_t v_i_232_, lean_object* v_b_233_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object* v_as_245_, lean_object* v_sz_246_, lean_object* v_i_247_, lean_object* v_b_248_){
_start:
{
size_t v_sz_boxed_249_; size_t v_i_boxed_250_; lean_object* v_res_251_; 
v_sz_boxed_249_ = lean_unbox_usize(v_sz_246_);
lean_dec(v_sz_246_);
v_i_boxed_250_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_as_245_, v_sz_boxed_249_, v_i_boxed_250_, v_b_248_);
lean_dec_ref(v_b_248_);
lean_dec_ref(v_as_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object* v_pkg_252_){
_start:
{
lean_object* v_sources_253_; lean_object* v___x_254_; lean_object* v___x_255_; size_t v_sz_256_; size_t v___x_257_; lean_object* v___x_258_; lean_object* v_fst_259_; 
v_sources_253_ = lean_ctor_get(v_pkg_252_, 2);
v___x_254_ = lean_box(0);
v___x_255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v_sz_256_ = lean_array_size(v_sources_253_);
v___x_257_ = ((size_t)0ULL);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_sources_253_, v_sz_256_, v___x_257_, v___x_255_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_fst_259_);
lean_dec_ref(v___x_258_);
if (lean_obj_tag(v_fst_259_) == 0)
{
return v___x_254_;
}
else
{
lean_object* v_val_260_; 
v_val_260_ = lean_ctor_get(v_fst_259_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v_fst_259_, 1);
return v_val_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object* v_pkg_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lake_RegistryPkg_gitSrc_x3f(v_pkg_261_);
lean_dec_ref(v_pkg_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object* v_src_263_){
_start:
{
lean_object* v_data_264_; 
v_data_264_ = lean_ctor_get(v_src_263_, 3);
lean_inc(v_data_264_);
return v_data_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object* v_src_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lake_RegistryPkg_toJson(v_src_265_);
lean_dec_ref(v_src_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t v_sz_269_, size_t v_i_270_, lean_object* v_bs_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_lt(v_i_270_, v_sz_269_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_bs_271_);
return v___x_273_;
}
else
{
lean_object* v_v_274_; lean_object* v___x_275_; lean_object* v_bs_x27_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v_v_274_ = lean_array_uget(v_bs_271_, v_i_270_);
v___x_275_ = lean_unsigned_to_nat(0u);
v_bs_x27_276_ = lean_array_uset(v_bs_271_, v_i_270_, v___x_275_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_270_, v___x_277_);
v___x_279_ = lean_array_uset(v_bs_x27_276_, v_i_270_, v_v_274_);
v_i_270_ = v___x_278_;
v_bs_271_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_281_, lean_object* v_i_282_, lean_object* v_bs_283_){
_start:
{
size_t v_sz_boxed_284_; size_t v_i_boxed_285_; lean_object* v_res_286_; 
v_sz_boxed_284_ = lean_unbox_usize(v_sz_281_);
lean_dec(v_sz_281_);
v_i_boxed_285_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_boxed_284_, v_i_boxed_285_, v_bs_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_289_) == 4)
{
lean_object* v_elems_290_; size_t v_sz_291_; size_t v___x_292_; lean_object* v___x_293_; 
v_elems_290_ = lean_ctor_get(v_x_289_, 0);
lean_inc_ref(v_elems_290_);
lean_dec_ref_known(v_x_289_, 1);
v_sz_291_ = lean_array_size(v_elems_290_);
v___x_292_ = ((size_t)0ULL);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_291_, v___x_292_, v_elems_290_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_295_ = lean_unsigned_to_nat(80u);
v___x_296_ = l_Lean_Json_pretty(v_x_289_, v___x_295_);
v___x_297_ = lean_string_append(v___x_294_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0));
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(v_x_303_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_a_314_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_305_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_305_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v_a_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(size_t v_sz_323_, size_t v_i_324_, lean_object* v_bs_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_bs_325_);
return v___x_327_;
}
else
{
lean_object* v_v_328_; lean_object* v___x_329_; 
v_v_328_ = lean_array_uget_borrowed(v_bs_325_, v_i_324_);
lean_inc(v_v_328_);
v___x_329_ = l_Lake_RegistrySrc_fromJson_x3f(v_v_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_bs_325_);
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v_bs_x27_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
v_a_338_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_329_, 1);
v___x_339_ = lean_unsigned_to_nat(0u);
v_bs_x27_340_ = lean_array_uset(v_bs_325_, v_i_324_, v___x_339_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_324_, v___x_341_);
v___x_343_ = lean_array_uset(v_bs_x27_340_, v_i_324_, v_a_338_);
v_i_324_ = v___x_342_;
v_bs_325_ = v___x_343_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object* v_sz_345_, lean_object* v_i_346_, lean_object* v_bs_347_){
_start:
{
size_t v_sz_boxed_348_; size_t v_i_boxed_349_; lean_object* v_res_350_; 
v_sz_boxed_348_ = lean_unbox_usize(v_sz_345_);
lean_dec(v_sz_345_);
v_i_boxed_349_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_boxed_348_, v_i_boxed_349_, v_bs_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object* v_val_362_){
_start:
{
lean_object* v_a_364_; lean_object* v___x_368_; 
v___x_368_ = l_Lean_Json_getObj_x3f(v_val_362_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v_a_364_ = v_a_369_;
goto v___jp_363_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_a_370_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_368_, 1);
v___x_371_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__1));
v___x_372_ = l_Lake_JsonObject_getJson_x3f(v_a_370_, v___x_371_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec(v_a_370_);
v___x_373_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__2));
v_a_364_ = v___x_373_;
goto v___jp_363_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_375_; 
v_val_374_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___x_372_, 1);
v___x_375_ = l_Lean_Json_getStr_x3f(v_val_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_a_370_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
v___x_377_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__3));
v___x_378_ = lean_string_append(v___x_377_, v_a_376_);
lean_dec(v_a_376_);
v_a_364_ = v___x_378_;
goto v___jp_363_;
}
else
{
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_379_; 
lean_dec(v_a_370_);
v_a_379_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_375_, 1);
v_a_364_ = v_a_379_;
goto v___jp_363_;
}
else
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_a_380_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_375_, 1);
v___x_381_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__4));
v___x_382_ = l_Lake_JsonObject_getJson_x3f(v_a_370_, v___x_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; 
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v___x_383_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__5));
v_a_364_ = v___x_383_;
goto v___jp_363_;
}
else
{
lean_object* v_val_384_; lean_object* v___x_385_; 
v_val_384_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v___x_382_, 1);
v___x_385_ = l_Lean_Json_getStr_x3f(v_val_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__6));
v___x_388_ = lean_string_append(v___x_387_, v_a_386_);
lean_dec(v_a_386_);
v_a_364_ = v___x_388_;
goto v___jp_363_;
}
else
{
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_389_; 
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v_a_389_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_385_, 1);
v_a_364_ = v_a_389_;
goto v___jp_363_;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_424_; 
v_a_390_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_424_ == 0)
{
v___x_392_ = v___x_385_;
v_isShared_393_ = v_isSharedCheck_424_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_385_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_424_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_a_395_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__8));
v___x_415_ = l_Lake_JsonObject_getJson_x3f(v_a_370_, v___x_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
goto v___jp_412_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_417_; 
v_val_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_val_416_);
lean_dec_ref_known(v___x_415_, 1);
v___x_417_ = l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(v_val_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_del_object(v___x_392_);
lean_dec(v_a_390_);
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
v___x_419_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__9));
v___x_420_ = lean_string_append(v___x_419_, v_a_418_);
lean_dec(v_a_418_);
v_a_364_ = v___x_420_;
goto v___jp_363_;
}
else
{
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_421_; 
lean_del_object(v___x_392_);
lean_dec(v_a_390_);
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v_a_421_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_417_, 1);
v_a_364_ = v_a_421_;
goto v___jp_363_;
}
else
{
lean_object* v_a_422_; 
v_a_422_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_417_, 1);
if (lean_obj_tag(v_a_422_) == 0)
{
goto v___jp_412_;
}
else
{
lean_object* v_val_423_; 
v_val_423_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v_a_422_, 1);
v_a_395_ = v_val_423_;
goto v___jp_394_;
}
}
}
}
v___jp_394_:
{
size_t v_sz_396_; size_t v___x_397_; lean_object* v___x_398_; 
v_sz_396_ = lean_array_size(v_a_395_);
v___x_397_ = ((size_t)0ULL);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_396_, v___x_397_, v_a_395_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; 
lean_del_object(v___x_392_);
lean_dec(v_a_390_);
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v_a_364_ = v_a_399_;
goto v___jp_363_;
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v_a_400_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 5);
lean_ctor_set(v___x_392_, 0, v_a_370_);
v___x_405_ = v___x_392_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_370_);
v___x_405_ = v_reuseFailAlloc_410_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_406_, 0, v_a_380_);
lean_ctor_set(v___x_406_, 1, v_a_390_);
lean_ctor_set(v___x_406_, 2, v_a_400_);
lean_ctor_set(v___x_406_, 3, v___x_405_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_406_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
v___jp_412_:
{
lean_object* v___x_413_; 
v___x_413_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__7));
v_a_395_ = v___x_413_;
goto v___jp_394_;
}
}
}
}
}
}
}
}
}
v___jp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__0));
v___x_366_ = lean_string_append(v___x_365_, v_a_364_);
lean_dec_ref(v_a_364_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object* v_lakeEnv_429_, lean_object* v_owner_430_, lean_object* v_pkg_431_){
_start:
{
lean_object* v_reservoirApiUrl_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_reservoirApiUrl_432_ = lean_ctor_get(v_lakeEnv_429_, 3);
lean_inc_ref(v_reservoirApiUrl_432_);
lean_dec_ref(v_lakeEnv_429_);
v___x_433_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_434_ = lean_string_append(v_reservoirApiUrl_432_, v___x_433_);
v___x_435_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_436_ = l_Lake_uriEncode(v_owner_430_, v___x_435_);
v___x_437_ = lean_string_append(v___x_434_, v___x_436_);
lean_dec_ref(v___x_436_);
v___x_438_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_439_ = lean_string_append(v___x_437_, v___x_438_);
v___x_440_ = l_Lake_uriEncode(v_pkg_431_, v___x_435_);
v___x_441_ = lean_string_append(v___x_439_, v___x_440_);
lean_dec_ref(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_object* v___x_445_; 
v___x_445_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0));
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Json_getObj_x3f(v_x_444_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_a_455_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_463_ == 0)
{
v___x_457_ = v___x_446_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_446_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_a_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0));
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_x_466_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* v_val_483_){
_start:
{
lean_object* v_a_485_; lean_object* v___x_529_; 
lean_inc(v_val_483_);
v___x_529_ = l_Lean_Json_getObj_x3f(v_val_483_);
if (lean_obj_tag(v___x_529_) == 1)
{
lean_object* v_a_530_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_537_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_538_ = l_Lake_JsonObject_getJson_x3f(v_a_530_, v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
goto v___jp_531_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_540_; 
v_val_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_539_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_530_);
lean_dec(v_val_483_);
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_550_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_545_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_546_ = lean_string_append(v___x_545_, v_a_541_);
lean_dec(v_a_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_546_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_a_530_);
lean_dec(v_val_483_);
v_a_551_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_540_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_540_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 0);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_540_, 1);
if (lean_obj_tag(v_a_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_a_530_);
lean_dec(v_val_483_);
v_val_560_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v_a_559_, 1);
v___x_561_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_562_ = l_Lake_JsonObject_getJson_x3f(v_val_560_, v___x_561_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
lean_dec(v_val_560_);
v___x_563_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5));
return v___x_563_;
}
else
{
lean_object* v_val_564_; lean_object* v___x_565_; 
v_val_564_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v___x_562_, 1);
v___x_565_ = l_Lean_Json_getNat_x3f(v_val_564_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_val_560_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_575_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_575_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_575_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_570_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_571_ = lean_string_append(v___x_570_, v_a_566_);
lean_dec(v_a_566_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_571_);
v___x_573_ = v___x_568_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_val_560_);
v_a_576_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_565_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_565_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 0);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_565_, 1);
v___x_585_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_586_ = l_Lake_JsonObject_getJson_x3f(v_val_560_, v___x_585_);
lean_dec(v_val_560_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
lean_dec(v_a_584_);
v___x_587_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9));
return v___x_587_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_589_; 
v_val_588_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v___x_586_, 1);
v___x_589_ = l_Lean_Json_getStr_x3f(v_val_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_584_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_599_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_594_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_595_ = lean_string_append(v___x_594_, v_a_590_);
lean_dec(v_a_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_595_);
v___x_597_ = v___x_592_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_a_584_);
v_a_600_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_589_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_589_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 0);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_a_608_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_616_ == 0)
{
v___x_610_ = v___x_589_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_589_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v_a_584_);
lean_ctor_set(v___x_612_, 1, v_a_608_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
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
lean_dec(v_a_559_);
goto v___jp_531_;
}
}
}
}
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_533_ = l_Lake_JsonObject_getJson_x3f(v_a_530_, v___x_532_);
lean_dec(v_a_530_);
if (lean_obj_tag(v___x_533_) == 0)
{
v_a_485_ = v___x_533_;
goto v___jp_484_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_535_; lean_object* v_a_536_; 
v_val_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_534_);
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v_a_485_ = v_a_536_;
goto v___jp_484_;
}
}
}
else
{
lean_object* v___x_617_; 
lean_dec_ref(v___x_529_);
v___x_617_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_483_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_a_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
v___jp_484_:
{
if (lean_obj_tag(v_a_485_) == 1)
{
lean_object* v_val_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_val_483_);
v_val_486_ = lean_ctor_get(v_a_485_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_510_ == 0)
{
v___x_488_ = v_a_485_;
v_isShared_489_ = v_isSharedCheck_510_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_val_486_);
lean_dec(v_a_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_510_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_486_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_del_object(v___x_488_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_509_; 
v_a_499_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_509_ == 0)
{
v___x_501_ = v___x_490_;
v_isShared_502_ = v_isSharedCheck_509_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_509_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 0);
lean_ctor_set(v___x_488_, 0, v_a_499_);
v___x_504_ = v___x_488_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v_a_485_);
v___x_511_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_483_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_a_520_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_528_ == 0)
{
v___x_522_ = v___x_511_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_511_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_a_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_526_ = v___x_522_;
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
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* v_lakeEnv_640_, lean_object* v_owner_641_, lean_object* v_pkg_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_url_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc_ref(v_pkg_642_);
lean_inc_ref(v_owner_641_);
v_url_645_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_640_, v_owner_641_, v_pkg_642_);
v___x_646_ = l_Lake_Reservoir_lakeHeaders;
v___x_647_ = l_Lake_getUrl(v_url_645_, v___x_646_, v_a_643_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_739_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_a_649_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_739_ == 0)
{
v___x_651_ = v___x_647_;
v_isShared_652_ = v_isSharedCheck_739_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_739_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; 
lean_inc(v_a_648_);
v___x_653_ = l_Lean_Json_parse(v_a_648_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_656_ = lean_string_append(v_owner_641_, v___x_655_);
v___x_657_ = lean_string_append(v___x_656_, v_pkg_642_);
lean_dec_ref(v_pkg_642_);
v___x_658_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_657_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
v___x_660_ = lean_string_append(v___x_659_, v_a_654_);
lean_dec(v_a_654_);
v___x_661_ = 3;
v___x_662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*1, v___x_661_);
v___x_663_ = lean_array_get_size(v_a_649_);
v___x_664_ = lean_array_push(v_a_649_, v___x_662_);
v___x_665_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_666_ = lean_string_append(v___x_657_, v___x_665_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_string_utf8_byte_size(v_a_648_);
v___x_669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_669_, 0, v_a_648_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
v___x_670_ = l_String_Slice_trimAscii(v___x_669_);
v___x_671_ = l_String_Slice_toString(v___x_670_);
lean_dec_ref(v___x_670_);
v___x_672_ = lean_string_append(v___x_666_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = 0;
v___x_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*1, v___x_673_);
v___x_675_ = lean_array_push(v___x_664_, v___x_674_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 1, v___x_675_);
lean_ctor_set(v___x_651_, 0, v___x_663_);
v___x_677_ = v___x_651_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_653_, 1);
v___x_680_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_683_ = lean_string_append(v_owner_641_, v___x_682_);
v___x_684_ = lean_string_append(v___x_683_, v_pkg_642_);
lean_dec_ref(v_pkg_642_);
v___x_685_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_684_);
v___x_686_ = lean_string_append(v___x_684_, v___x_685_);
v___x_687_ = lean_string_append(v___x_686_, v_a_681_);
lean_dec(v_a_681_);
v___x_688_ = 3;
v___x_689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*1, v___x_688_);
v___x_690_ = lean_array_get_size(v_a_649_);
v___x_691_ = lean_array_push(v_a_649_, v___x_689_);
v___x_692_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_693_ = lean_string_append(v___x_684_, v___x_692_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_string_utf8_byte_size(v_a_648_);
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v_a_648_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
v___x_697_ = l_String_Slice_trimAscii(v___x_696_);
v___x_698_ = l_String_Slice_toString(v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = lean_string_append(v___x_693_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = 0;
v___x_701_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1, v___x_700_);
v___x_702_ = lean_array_push(v___x_691_, v___x_701_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 1, v___x_702_);
lean_ctor_set(v___x_651_, 0, v___x_690_);
v___x_704_ = v___x_651_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v_a_706_; 
lean_dec(v_a_648_);
v_a_706_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_680_, 1);
if (lean_obj_tag(v_a_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_pkg_642_);
lean_dec_ref(v_owner_641_);
v_a_707_ = lean_ctor_get(v_a_706_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_717_ == 0)
{
v___x_709_ = v_a_706_;
v_isShared_710_ = v_isSharedCheck_717_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v_a_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_717_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_712_);
v___x_714_ = v___x_651_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_a_649_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_status_718_; lean_object* v_message_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_status_718_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_status_718_);
v_message_719_ = lean_ctor_get(v_a_706_, 1);
lean_inc_ref(v_message_719_);
lean_dec_ref_known(v_a_706_, 2);
v___x_720_ = lean_unsigned_to_nat(404u);
v___x_721_ = lean_nat_dec_eq(v_status_718_, v___x_720_);
lean_dec(v_status_718_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_722_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_723_ = lean_string_append(v_owner_641_, v___x_722_);
v___x_724_ = lean_string_append(v___x_723_, v_pkg_642_);
lean_dec_ref(v_pkg_642_);
v___x_725_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__3));
v___x_726_ = lean_string_append(v___x_724_, v___x_725_);
v___x_727_ = lean_string_append(v___x_726_, v_message_719_);
lean_dec_ref(v_message_719_);
v___x_728_ = 3;
v___x_729_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*1, v___x_728_);
v___x_730_ = lean_array_get_size(v_a_649_);
v___x_731_ = lean_array_push(v_a_649_, v___x_729_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 1);
lean_ctor_set(v___x_651_, 1, v___x_731_);
lean_ctor_set(v___x_651_, 0, v___x_730_);
v___x_733_ = v___x_651_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec_ref(v_message_719_);
lean_dec_ref(v_pkg_642_);
lean_dec_ref(v_owner_641_);
v___x_735_ = lean_box(0);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_735_);
v___x_737_ = v___x_651_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_649_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_756_; 
v_a_740_ = lean_ctor_get(v___x_647_, 0);
v_a_741_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_756_ == 0)
{
v___x_743_ = v___x_647_;
v_isShared_744_ = v_isSharedCheck_756_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_inc(v_a_740_);
lean_dec(v___x_647_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_756_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_745_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_746_ = lean_string_append(v_owner_641_, v___x_745_);
v___x_747_ = lean_string_append(v___x_746_, v_pkg_642_);
lean_dec_ref(v_pkg_642_);
v___x_748_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
v___x_750_ = 3;
v___x_751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*1, v___x_750_);
v___x_752_ = lean_array_push(v_a_741_, v___x_751_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_752_);
v___x_754_ = v___x_743_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* v_lakeEnv_757_, lean_object* v_owner_758_, lean_object* v_pkg_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_757_, v_owner_758_, v_pkg_759_, v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object* v_val_770_){
_start:
{
lean_object* v_a_772_; lean_object* v_a_777_; lean_object* v___x_780_; 
v___x_780_ = l_Lean_Json_getObj_x3f(v_val_770_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v_a_772_ = v_a_781_;
goto v___jp_771_;
}
else
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_a_782_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_780_, 1);
v___x_783_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__2));
v___x_784_ = l_Lake_JsonObject_getJson_x3f(v_a_782_, v___x_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; 
lean_dec(v_a_782_);
v___x_785_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__3));
v_a_772_ = v___x_785_;
goto v___jp_771_;
}
else
{
lean_object* v_val_786_; lean_object* v___x_787_; 
v_val_786_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v___x_784_, 1);
v___x_787_ = l_Lean_Json_getStr_x3f(v_val_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; 
lean_dec(v_a_782_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v_a_777_ = v_a_788_;
goto v___jp_776_;
}
else
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_787_, 1);
v___x_790_ = l_Lake_StdVer_parse(v_a_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; 
lean_dec(v_a_782_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v_a_777_ = v_a_791_;
goto v___jp_776_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_a_792_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_790_, 1);
v___x_793_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__4));
v___x_794_ = l_Lake_JsonObject_getJson_x3f(v_a_782_, v___x_793_);
lean_dec(v_a_782_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
lean_dec(v_a_792_);
v___x_795_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__5));
v_a_772_ = v___x_795_;
goto v___jp_771_;
}
else
{
lean_object* v_val_796_; lean_object* v___x_797_; 
v_val_796_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v___x_794_, 1);
v___x_797_ = l_Lean_Json_getStr_x3f(v_val_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_a_792_);
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__6));
v___x_800_ = lean_string_append(v___x_799_, v_a_798_);
lean_dec(v_a_798_);
v_a_772_ = v___x_800_;
goto v___jp_771_;
}
else
{
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_801_; 
lean_dec(v_a_792_);
v_a_801_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_797_, 1);
v_a_772_ = v_a_801_;
goto v___jp_771_;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_a_802_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_810_ == 0)
{
v___x_804_ = v___x_797_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_797_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_a_792_);
lean_ctor_set(v___x_806_, 1, v_a_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
}
}
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__0));
v___x_774_ = lean_string_append(v___x_773_, v_a_772_);
lean_dec_ref(v_a_772_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__1));
v___x_779_ = lean_string_append(v___x_778_, v_a_777_);
lean_dec_ref(v_a_777_);
v_a_772_ = v___x_779_;
goto v___jp_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object* v_lakeEnv_814_, lean_object* v_owner_815_, lean_object* v_pkg_816_){
_start:
{
lean_object* v_reservoirApiUrl_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_reservoirApiUrl_817_ = lean_ctor_get(v_lakeEnv_814_, 3);
lean_inc_ref(v_reservoirApiUrl_817_);
lean_dec_ref(v_lakeEnv_814_);
v___x_818_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_819_ = lean_string_append(v_reservoirApiUrl_817_, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_821_ = l_Lake_uriEncode(v_owner_815_, v___x_820_);
v___x_822_ = lean_string_append(v___x_819_, v___x_821_);
lean_dec_ref(v___x_821_);
v___x_823_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_824_ = lean_string_append(v___x_822_, v___x_823_);
v___x_825_ = l_Lake_uriEncode(v_pkg_816_, v___x_820_);
v___x_826_ = lean_string_append(v___x_824_, v___x_825_);
lean_dec_ref(v___x_825_);
v___x_827_ = ((lean_object*)(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0));
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t v_sz_829_, size_t v_i_830_, lean_object* v_bs_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_lt(v_i_830_, v_sz_829_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_bs_831_);
return v___x_833_;
}
else
{
lean_object* v_v_834_; lean_object* v___x_835_; 
v_v_834_ = lean_array_uget_borrowed(v_bs_831_, v_i_830_);
lean_inc(v_v_834_);
v___x_835_ = l_Lake_RegistryVer_fromJson_x3f(v_v_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref(v_bs_831_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v_bs_x27_846_; size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
v_a_844_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_835_, 1);
v___x_845_ = lean_unsigned_to_nat(0u);
v_bs_x27_846_ = lean_array_uset(v_bs_831_, v_i_830_, v___x_845_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_830_, v___x_847_);
v___x_849_ = lean_array_uset(v_bs_x27_846_, v_i_830_, v_a_844_);
v_i_830_ = v___x_848_;
v_bs_831_ = v___x_849_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_851_, lean_object* v_i_852_, lean_object* v_bs_853_){
_start:
{
size_t v_sz_boxed_854_; size_t v_i_boxed_855_; lean_object* v_res_856_; 
v_sz_boxed_854_ = lean_unbox_usize(v_sz_851_);
lean_dec(v_sz_851_);
v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_854_, v_i_boxed_855_, v_bs_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object* v_x_857_){
_start:
{
if (lean_obj_tag(v_x_857_) == 4)
{
lean_object* v_elems_858_; size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; 
v_elems_858_ = lean_ctor_get(v_x_857_, 0);
lean_inc_ref(v_elems_858_);
lean_dec_ref_known(v_x_857_, 1);
v_sz_859_ = lean_array_size(v_elems_858_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_859_, v___x_860_, v_elems_858_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_862_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_863_ = lean_unsigned_to_nat(80u);
v___x_864_ = l_Lean_Json_pretty(v_x_857_, v___x_863_);
v___x_865_ = lean_string_append(v___x_862_, v___x_864_);
lean_dec_ref(v___x_864_);
v___x_866_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_867_ = lean_string_append(v___x_865_, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object* v_val_873_){
_start:
{
lean_object* v_a_875_; lean_object* v___x_919_; 
lean_inc(v_val_873_);
v___x_919_ = l_Lean_Json_getObj_x3f(v_val_873_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v_a_920_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_927_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_928_ = l_Lake_JsonObject_getJson_x3f(v_a_920_, v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
goto v___jp_921_;
}
else
{
lean_object* v_val_929_; lean_object* v___x_930_; 
v_val_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_920_);
lean_dec(v_val_873_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_940_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_940_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_940_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_936_ = lean_string_append(v___x_935_, v_a_931_);
lean_dec(v_a_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_920_);
lean_dec(v_val_873_);
v_a_941_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_930_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_930_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 0);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_930_, 1);
if (lean_obj_tag(v_a_949_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_a_920_);
lean_dec(v_val_873_);
v_val_950_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_val_950_);
lean_dec_ref_known(v_a_949_, 1);
v___x_951_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_952_ = l_Lake_JsonObject_getJson_x3f(v_val_950_, v___x_951_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v___x_953_; 
lean_dec(v_val_950_);
v___x_953_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0));
return v___x_953_;
}
else
{
lean_object* v_val_954_; lean_object* v___x_955_; 
v_val_954_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v___x_952_, 1);
v___x_955_ = l_Lean_Json_getNat_x3f(v_val_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_val_950_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_961_ = lean_string_append(v___x_960_, v_a_956_);
lean_dec(v_a_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_val_950_);
v_a_966_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_955_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_955_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 0);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_955_, 1);
v___x_975_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_976_ = l_Lake_JsonObject_getJson_x3f(v_val_950_, v___x_975_);
lean_dec(v_val_950_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v___x_977_; 
lean_dec(v_a_974_);
v___x_977_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1));
return v___x_977_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_976_, 1);
v___x_979_ = l_Lean_Json_getStr_x3f(v_val_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_974_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_989_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_984_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_985_ = lean_string_append(v___x_984_, v_a_980_);
lean_dec(v_a_980_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_974_);
v_a_990_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_979_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_979_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1006_; 
v_a_998_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1000_ = v___x_979_;
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_979_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_974_);
lean_ctor_set(v___x_1002_, 1, v_a_998_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1002_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
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
lean_dec(v_a_949_);
goto v___jp_921_;
}
}
}
}
v___jp_921_:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_923_ = l_Lake_JsonObject_getJson_x3f(v_a_920_, v___x_922_);
lean_dec(v_a_920_);
if (lean_obj_tag(v___x_923_) == 0)
{
v_a_875_ = v___x_923_;
goto v___jp_874_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_925_; lean_object* v_a_926_; 
v_val_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_925_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_924_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_925_);
v_a_875_ = v_a_926_;
goto v___jp_874_;
}
}
}
else
{
lean_object* v___x_1007_; 
lean_dec_ref(v___x_919_);
v___x_1007_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_873_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
v_a_1016_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1018_ = v___x_1007_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1007_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_a_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
v___jp_874_:
{
if (lean_obj_tag(v_a_875_) == 1)
{
lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_val_873_);
v_val_876_ = lean_ctor_get(v_a_875_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_900_ == 0)
{
v___x_878_ = v_a_875_;
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_dec(v_a_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_900_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; 
v___x_880_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_876_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_del_object(v___x_878_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v_a_889_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_899_ == 0)
{
v___x_891_ = v___x_880_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_880_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 0);
lean_ctor_set(v___x_878_, 0, v_a_889_);
v___x_894_ = v___x_878_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
else
{
lean_object* v___x_901_; 
lean_dec(v_a_875_);
v___x_901_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_873_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_a_910_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v___x_901_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_901_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_a_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object* v_lakeEnv_1027_, lean_object* v_owner_1028_, lean_object* v_pkg_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_url_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v_pkg_1029_);
lean_inc_ref(v_owner_1028_);
v_url_1032_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_1027_, v_owner_1028_, v_pkg_1029_);
v___x_1033_ = l_Lake_Reservoir_lakeHeaders;
v___x_1034_ = l_Lake_getUrl(v_url_1032_, v___x_1033_, v_a_1030_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1117_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_a_1036_ = lean_ctor_get(v___x_1034_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1038_ = v___x_1034_;
v_isShared_1039_ = v_isSharedCheck_1117_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1117_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; 
lean_inc(v_a_1035_);
v___x_1040_ = l_Lean_Json_parse(v_a_1035_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1043_ = lean_string_append(v_owner_1028_, v___x_1042_);
v___x_1044_ = lean_string_append(v___x_1043_, v_pkg_1029_);
lean_dec_ref(v_pkg_1029_);
v___x_1045_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_1044_);
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
v___x_1047_ = lean_string_append(v___x_1046_, v_a_1041_);
lean_dec(v_a_1041_);
v___x_1048_ = 3;
v___x_1049_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*1, v___x_1048_);
v___x_1050_ = lean_array_get_size(v_a_1036_);
v___x_1051_ = lean_array_push(v_a_1036_, v___x_1049_);
v___x_1052_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1053_ = lean_string_append(v___x_1044_, v___x_1052_);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_string_utf8_byte_size(v_a_1035_);
v___x_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1035_);
lean_ctor_set(v___x_1056_, 1, v___x_1054_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
v___x_1057_ = l_String_Slice_trimAscii(v___x_1056_);
v___x_1058_ = l_String_Slice_toString(v___x_1057_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = lean_string_append(v___x_1053_, v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = 0;
v___x_1061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v___x_1060_);
v___x_1062_ = lean_array_push(v___x_1051_, v___x_1061_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 1, v___x_1062_);
lean_ctor_set(v___x_1038_, 0, v___x_1050_);
v___x_1064_ = v___x_1038_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1066_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1067_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1070_ = lean_string_append(v_owner_1028_, v___x_1069_);
v___x_1071_ = lean_string_append(v___x_1070_, v_pkg_1029_);
lean_dec_ref(v_pkg_1029_);
v___x_1072_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_1071_);
v___x_1073_ = lean_string_append(v___x_1071_, v___x_1072_);
v___x_1074_ = lean_string_append(v___x_1073_, v_a_1068_);
lean_dec(v_a_1068_);
v___x_1075_ = 3;
v___x_1076_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*1, v___x_1075_);
v___x_1077_ = lean_array_get_size(v_a_1036_);
v___x_1078_ = lean_array_push(v_a_1036_, v___x_1076_);
v___x_1079_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1080_ = lean_string_append(v___x_1071_, v___x_1079_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_string_utf8_byte_size(v_a_1035_);
v___x_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1083_, 0, v_a_1035_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v___x_1082_);
v___x_1084_ = l_String_Slice_trimAscii(v___x_1083_);
v___x_1085_ = l_String_Slice_toString(v___x_1084_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_string_append(v___x_1080_, v___x_1085_);
lean_dec_ref(v___x_1085_);
v___x_1087_ = 0;
v___x_1088_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*1, v___x_1087_);
v___x_1089_ = lean_array_push(v___x_1078_, v___x_1088_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 1, v___x_1089_);
lean_ctor_set(v___x_1038_, 0, v___x_1077_);
v___x_1091_ = v___x_1038_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
lean_object* v_a_1093_; 
lean_dec(v_a_1035_);
v_a_1093_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1067_, 1);
if (lean_obj_tag(v_a_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; 
lean_dec_ref(v_pkg_1029_);
lean_dec_ref(v_owner_1028_);
v_a_1094_ = lean_ctor_get(v_a_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v_a_1093_, 1);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_a_1094_);
v___x_1096_ = v___x_1038_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1094_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_a_1036_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
else
{
lean_object* v_status_1098_; lean_object* v_message_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_status_1098_ = lean_ctor_get(v_a_1093_, 0);
lean_inc(v_status_1098_);
v_message_1099_ = lean_ctor_get(v_a_1093_, 1);
lean_inc_ref(v_message_1099_);
lean_dec_ref_known(v_a_1093_, 2);
v___x_1100_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1101_ = lean_string_append(v_owner_1028_, v___x_1100_);
v___x_1102_ = lean_string_append(v___x_1101_, v_pkg_1029_);
lean_dec_ref(v_pkg_1029_);
v___x_1103_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__0));
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
v___x_1105_ = l_Nat_reprFast(v_status_1098_);
v___x_1106_ = lean_string_append(v___x_1104_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__1));
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
v___x_1109_ = lean_string_append(v___x_1108_, v_message_1099_);
lean_dec_ref(v_message_1099_);
v___x_1110_ = 3;
v___x_1111_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*1, v___x_1110_);
v___x_1112_ = lean_array_get_size(v_a_1036_);
v___x_1113_ = lean_array_push(v_a_1036_, v___x_1111_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
lean_ctor_set(v___x_1038_, 1, v___x_1113_);
lean_ctor_set(v___x_1038_, 0, v___x_1112_);
v___x_1115_ = v___x_1038_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1134_; 
v_a_1118_ = lean_ctor_get(v___x_1034_, 0);
v_a_1119_ = lean_ctor_get(v___x_1034_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1121_ = v___x_1034_;
v_isShared_1122_ = v_isSharedCheck_1134_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_inc(v_a_1118_);
lean_dec(v___x_1034_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1134_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1123_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1124_ = lean_string_append(v_owner_1028_, v___x_1123_);
v___x_1125_ = lean_string_append(v___x_1124_, v_pkg_1029_);
lean_dec_ref(v_pkg_1029_);
v___x_1126_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_1127_ = lean_string_append(v___x_1125_, v___x_1126_);
v___x_1128_ = 3;
v___x_1129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*1, v___x_1128_);
v___x_1130_ = lean_array_push(v_a_1119_, v___x_1129_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1130_);
v___x_1132_ = v___x_1121_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object* v_lakeEnv_1135_, lean_object* v_owner_1136_, lean_object* v_pkg_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1135_, v_owner_1136_, v_pkg_1137_, v_a_1138_);
return v_res_1140_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
