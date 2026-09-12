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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t v_sz_269_, size_t v_i_270_, lean_object* v_bs_271_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_281_, lean_object* v_i_282_, lean_object* v_bs_283_){
_start:
{
size_t v_sz_boxed_284_; size_t v_i_boxed_285_; lean_object* v_res_286_; 
v_sz_boxed_284_ = lean_unbox_usize(v_sz_281_);
lean_dec(v_sz_281_);
v_i_boxed_285_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_boxed_284_, v_i_boxed_285_, v_bs_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object* v_x_289_){
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
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_291_, v___x_292_, v_elems_290_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_295_ = lean_unsigned_to_nat(80u);
v___x_296_ = l_Lean_Json_pretty(v_x_289_, v___x_295_);
v___x_297_ = lean_string_append(v___x_294_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0));
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(v_x_303_);
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
v___x_417_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(v_val_416_);
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
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object* v_lakeEnv_442_, lean_object* v_owner_443_, lean_object* v_pkg_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_442_, v_owner_443_, v_pkg_444_);
lean_dec_ref(v_pkg_444_);
lean_dec_ref(v_owner_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0));
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Json_getObj_x3f(v_x_448_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_a_459_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v___x_450_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_450_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_a_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0));
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_x_470_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* v_val_487_){
_start:
{
lean_object* v_a_489_; lean_object* v___x_533_; 
lean_inc(v_val_487_);
v___x_533_ = l_Lean_Json_getObj_x3f(v_val_487_);
if (lean_obj_tag(v___x_533_) == 1)
{
lean_object* v_a_534_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_541_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_542_ = l_Lake_JsonObject_getJson_x3f(v_a_534_, v___x_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
goto v___jp_535_;
}
else
{
lean_object* v_val_543_; lean_object* v___x_544_; 
v_val_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_534_);
lean_dec(v_val_487_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_554_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_550_ = lean_string_append(v___x_549_, v_a_545_);
lean_dec(v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_550_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_534_);
lean_dec(v_val_487_);
v_a_555_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_544_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_544_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; 
v_a_563_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_544_, 1);
if (lean_obj_tag(v_a_563_) == 1)
{
lean_object* v_val_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_a_534_);
lean_dec(v_val_487_);
v_val_564_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v_a_563_, 1);
v___x_565_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_566_ = l_Lake_JsonObject_getJson_x3f(v_val_564_, v___x_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; 
lean_dec(v_val_564_);
v___x_567_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5));
return v___x_567_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; 
v_val_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v___x_566_, 1);
v___x_569_ = l_Lean_Json_getNat_x3f(v_val_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_val_564_);
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_575_ = lean_string_append(v___x_574_, v_a_570_);
lean_dec(v_a_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_575_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_val_564_);
v_a_580_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_569_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_569_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_a_588_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_569_, 1);
v___x_589_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_590_ = l_Lake_JsonObject_getJson_x3f(v_val_564_, v___x_589_);
lean_dec(v_val_564_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v___x_591_; 
lean_dec(v_a_588_);
v___x_591_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9));
return v___x_591_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_593_; 
v_val_592_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v___x_590_, 1);
v___x_593_ = l_Lean_Json_getStr_x3f(v_val_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_a_588_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_599_ = lean_string_append(v___x_598_, v_a_594_);
lean_dec(v_a_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_599_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_a_588_);
v_a_604_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_593_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_593_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set_tag(v___x_606_, 0);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v_a_612_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_620_ == 0)
{
v___x_614_ = v___x_593_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_593_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v_a_588_);
lean_ctor_set(v___x_616_, 1, v_a_612_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
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
lean_dec(v_a_563_);
goto v___jp_535_;
}
}
}
}
v___jp_535_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_537_ = l_Lake_JsonObject_getJson_x3f(v_a_534_, v___x_536_);
lean_dec(v_a_534_);
if (lean_obj_tag(v___x_537_) == 0)
{
v_a_489_ = v___x_537_;
goto v___jp_488_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_539_; lean_object* v_a_540_; 
v_val_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_538_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
v_a_489_ = v_a_540_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref(v___x_533_);
v___x_621_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_487_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_a_630_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v___x_621_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_621_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_a_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
v___jp_488_:
{
if (lean_obj_tag(v_a_489_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_val_487_);
v_val_490_ = lean_ctor_get(v_a_489_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_489_);
if (v_isSharedCheck_514_ == 0)
{
v___x_492_ = v_a_489_;
v_isShared_493_ = v_isSharedCheck_514_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v_a_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_514_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_490_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_del_object(v___x_492_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_513_; 
v_a_503_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_513_ == 0)
{
v___x_505_ = v___x_494_;
v_isShared_506_ = v_isSharedCheck_513_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_494_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_513_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 0);
lean_ctor_set(v___x_492_, 0, v_a_503_);
v___x_508_ = v___x_492_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
else
{
lean_object* v___x_515_; 
lean_dec(v_a_489_);
v___x_515_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_487_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_a_524_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v___x_515_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* v_lakeEnv_644_, lean_object* v_owner_645_, lean_object* v_pkg_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_url_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_url_649_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_644_, v_owner_645_, v_pkg_646_);
v___x_650_ = l_Lake_Reservoir_lakeHeaders;
v___x_651_ = l_Lake_getUrl(v_url_649_, v___x_650_, v_a_647_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_743_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_a_653_ = lean_ctor_get(v___x_651_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_743_ == 0)
{
v___x_655_ = v___x_651_;
v_isShared_656_ = v_isSharedCheck_743_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_743_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; 
lean_inc(v_a_652_);
v___x_657_ = l_Lean_Json_parse(v_a_652_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_660_ = lean_string_append(v_owner_645_, v___x_659_);
v___x_661_ = lean_string_append(v___x_660_, v_pkg_646_);
v___x_662_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_661_);
v___x_663_ = lean_string_append(v___x_661_, v___x_662_);
v___x_664_ = lean_string_append(v___x_663_, v_a_658_);
lean_dec(v_a_658_);
v___x_665_ = 3;
v___x_666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*1, v___x_665_);
v___x_667_ = lean_array_get_size(v_a_653_);
v___x_668_ = lean_array_push(v_a_653_, v___x_666_);
v___x_669_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_670_ = lean_string_append(v___x_661_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_string_utf8_byte_size(v_a_652_);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v_a_652_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = l_String_Slice_trimAscii(v___x_673_);
v___x_675_ = l_String_Slice_toString(v___x_674_);
lean_dec_ref(v___x_674_);
v___x_676_ = lean_string_append(v___x_670_, v___x_675_);
lean_dec_ref(v___x_675_);
v___x_677_ = 0;
v___x_678_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*1, v___x_677_);
v___x_679_ = lean_array_push(v___x_668_, v___x_678_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 1);
lean_ctor_set(v___x_655_, 1, v___x_679_);
lean_ctor_set(v___x_655_, 0, v___x_667_);
v___x_681_ = v___x_655_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_657_, 1);
v___x_684_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_687_ = lean_string_append(v_owner_645_, v___x_686_);
v___x_688_ = lean_string_append(v___x_687_, v_pkg_646_);
v___x_689_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_688_);
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
v___x_691_ = lean_string_append(v___x_690_, v_a_685_);
lean_dec(v_a_685_);
v___x_692_ = 3;
v___x_693_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*1, v___x_692_);
v___x_694_ = lean_array_get_size(v_a_653_);
v___x_695_ = lean_array_push(v_a_653_, v___x_693_);
v___x_696_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_697_ = lean_string_append(v___x_688_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_string_utf8_byte_size(v_a_652_);
v___x_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_700_, 0, v_a_652_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
lean_ctor_set(v___x_700_, 2, v___x_699_);
v___x_701_ = l_String_Slice_trimAscii(v___x_700_);
v___x_702_ = l_String_Slice_toString(v___x_701_);
lean_dec_ref(v___x_701_);
v___x_703_ = lean_string_append(v___x_697_, v___x_702_);
lean_dec_ref(v___x_702_);
v___x_704_ = 0;
v___x_705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_704_);
v___x_706_ = lean_array_push(v___x_695_, v___x_705_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 1);
lean_ctor_set(v___x_655_, 1, v___x_706_);
lean_ctor_set(v___x_655_, 0, v___x_694_);
v___x_708_ = v___x_655_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_a_710_; 
lean_dec(v_a_652_);
v_a_710_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_684_, 1);
if (lean_obj_tag(v_a_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_owner_645_);
v_a_711_ = lean_ctor_get(v_a_710_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_a_710_);
if (v_isSharedCheck_721_ == 0)
{
v___x_713_ = v_a_710_;
v_isShared_714_ = v_isSharedCheck_721_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v_a_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_721_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 1);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_716_);
v___x_718_ = v___x_655_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_a_653_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_status_722_; lean_object* v_message_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_status_722_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_status_722_);
v_message_723_ = lean_ctor_get(v_a_710_, 1);
lean_inc_ref(v_message_723_);
lean_dec_ref_known(v_a_710_, 2);
v___x_724_ = lean_unsigned_to_nat(404u);
v___x_725_ = lean_nat_dec_eq(v_status_722_, v___x_724_);
lean_dec(v_status_722_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_726_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_727_ = lean_string_append(v_owner_645_, v___x_726_);
v___x_728_ = lean_string_append(v___x_727_, v_pkg_646_);
v___x_729_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__3));
v___x_730_ = lean_string_append(v___x_728_, v___x_729_);
v___x_731_ = lean_string_append(v___x_730_, v_message_723_);
lean_dec_ref(v_message_723_);
v___x_732_ = 3;
v___x_733_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*1, v___x_732_);
v___x_734_ = lean_array_get_size(v_a_653_);
v___x_735_ = lean_array_push(v_a_653_, v___x_733_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 1);
lean_ctor_set(v___x_655_, 1, v___x_735_);
lean_ctor_set(v___x_655_, 0, v___x_734_);
v___x_737_ = v___x_655_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec_ref(v_message_723_);
lean_dec_ref(v_owner_645_);
v___x_739_ = lean_box(0);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_739_);
v___x_741_ = v___x_655_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_653_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_760_; 
v_a_744_ = lean_ctor_get(v___x_651_, 0);
v_a_745_ = lean_ctor_get(v___x_651_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_760_ == 0)
{
v___x_747_ = v___x_651_;
v_isShared_748_ = v_isSharedCheck_760_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_inc(v_a_744_);
lean_dec(v___x_651_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_760_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_749_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_750_ = lean_string_append(v_owner_645_, v___x_749_);
v___x_751_ = lean_string_append(v___x_750_, v_pkg_646_);
v___x_752_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = 3;
v___x_755_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*1, v___x_754_);
v___x_756_ = lean_array_push(v_a_745_, v___x_755_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_756_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_744_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* v_lakeEnv_761_, lean_object* v_owner_762_, lean_object* v_pkg_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_761_, v_owner_762_, v_pkg_763_, v_a_764_);
lean_dec_ref(v_pkg_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object* v_val_774_){
_start:
{
lean_object* v_a_776_; lean_object* v_a_781_; lean_object* v___x_784_; 
v___x_784_ = l_Lean_Json_getObj_x3f(v_val_774_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v_a_776_ = v_a_785_;
goto v___jp_775_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_a_786_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_784_, 1);
v___x_787_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__2));
v___x_788_ = l_Lake_JsonObject_getJson_x3f(v_a_786_, v___x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; 
lean_dec(v_a_786_);
v___x_789_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__3));
v_a_776_ = v___x_789_;
goto v___jp_775_;
}
else
{
lean_object* v_val_790_; lean_object* v___x_791_; 
v_val_790_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v___x_788_, 1);
v___x_791_ = l_Lean_Json_getStr_x3f(v_val_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
lean_dec(v_a_786_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_a_781_ = v_a_792_;
goto v___jp_780_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_791_, 1);
v___x_794_ = l_Lake_StdVer_parse(v_a_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; 
lean_dec(v_a_786_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v_a_781_ = v_a_795_;
goto v___jp_780_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_796_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_794_, 1);
v___x_797_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__4));
v___x_798_ = l_Lake_JsonObject_getJson_x3f(v_a_786_, v___x_797_);
lean_dec(v_a_786_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; 
lean_dec(v_a_796_);
v___x_799_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__5));
v_a_776_ = v___x_799_;
goto v___jp_775_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_801_; 
v_val_800_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v___x_798_, 1);
v___x_801_ = l_Lean_Json_getStr_x3f(v_val_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_a_796_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v___x_803_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__6));
v___x_804_ = lean_string_append(v___x_803_, v_a_802_);
lean_dec(v_a_802_);
v_a_776_ = v___x_804_;
goto v___jp_775_;
}
else
{
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_805_; 
lean_dec(v_a_796_);
v_a_805_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_801_, 1);
v_a_776_ = v_a_805_;
goto v___jp_775_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_a_806_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v___x_801_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_801_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_a_796_);
lean_ctor_set(v___x_810_, 1, v_a_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
}
}
}
v___jp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__0));
v___x_778_ = lean_string_append(v___x_777_, v_a_776_);
lean_dec_ref(v_a_776_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__1));
v___x_783_ = lean_string_append(v___x_782_, v_a_781_);
lean_dec_ref(v_a_781_);
v_a_776_ = v___x_783_;
goto v___jp_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object* v_lakeEnv_818_, lean_object* v_owner_819_, lean_object* v_pkg_820_){
_start:
{
lean_object* v_reservoirApiUrl_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_reservoirApiUrl_821_ = lean_ctor_get(v_lakeEnv_818_, 3);
lean_inc_ref(v_reservoirApiUrl_821_);
lean_dec_ref(v_lakeEnv_818_);
v___x_822_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_823_ = lean_string_append(v_reservoirApiUrl_821_, v___x_822_);
v___x_824_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_825_ = l_Lake_uriEncode(v_owner_819_, v___x_824_);
v___x_826_ = lean_string_append(v___x_823_, v___x_825_);
lean_dec_ref(v___x_825_);
v___x_827_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
v___x_829_ = l_Lake_uriEncode(v_pkg_820_, v___x_824_);
v___x_830_ = lean_string_append(v___x_828_, v___x_829_);
lean_dec_ref(v___x_829_);
v___x_831_ = ((lean_object*)(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0));
v___x_832_ = lean_string_append(v___x_830_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl___boxed(lean_object* v_lakeEnv_833_, lean_object* v_owner_834_, lean_object* v_pkg_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_833_, v_owner_834_, v_pkg_835_);
lean_dec_ref(v_pkg_835_);
lean_dec_ref(v_owner_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t v_sz_837_, size_t v_i_838_, lean_object* v_bs_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_bs_839_);
return v___x_841_;
}
else
{
lean_object* v_v_842_; lean_object* v___x_843_; 
v_v_842_ = lean_array_uget_borrowed(v_bs_839_, v_i_838_);
lean_inc(v_v_842_);
v___x_843_ = l_Lake_RegistryVer_fromJson_x3f(v_v_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_bs_839_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v_bs_x27_854_; size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
v_a_852_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_843_, 1);
v___x_853_ = lean_unsigned_to_nat(0u);
v_bs_x27_854_ = lean_array_uset(v_bs_839_, v_i_838_, v___x_853_);
v___x_855_ = ((size_t)1ULL);
v___x_856_ = lean_usize_add(v_i_838_, v___x_855_);
v___x_857_ = lean_array_uset(v_bs_x27_854_, v_i_838_, v_a_852_);
v_i_838_ = v___x_856_;
v_bs_839_ = v___x_857_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_bs_861_){
_start:
{
size_t v_sz_boxed_862_; size_t v_i_boxed_863_; lean_object* v_res_864_; 
v_sz_boxed_862_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_863_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_862_, v_i_boxed_863_, v_bs_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 4)
{
lean_object* v_elems_866_; size_t v_sz_867_; size_t v___x_868_; lean_object* v___x_869_; 
v_elems_866_ = lean_ctor_get(v_x_865_, 0);
lean_inc_ref(v_elems_866_);
lean_dec_ref_known(v_x_865_, 1);
v_sz_867_ = lean_array_size(v_elems_866_);
v___x_868_ = ((size_t)0ULL);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_867_, v___x_868_, v_elems_866_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_870_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_871_ = lean_unsigned_to_nat(80u);
v___x_872_ = l_Lean_Json_pretty(v_x_865_, v___x_871_);
v___x_873_ = lean_string_append(v___x_870_, v___x_872_);
lean_dec_ref(v___x_872_);
v___x_874_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_875_ = lean_string_append(v___x_873_, v___x_874_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object* v_val_881_){
_start:
{
lean_object* v_a_883_; lean_object* v___x_927_; 
lean_inc(v_val_881_);
v___x_927_ = l_Lean_Json_getObj_x3f(v_val_881_);
if (lean_obj_tag(v___x_927_) == 1)
{
lean_object* v_a_928_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_935_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_936_ = l_Lake_JsonObject_getJson_x3f(v_a_928_, v___x_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
goto v___jp_929_;
}
else
{
lean_object* v_val_937_; lean_object* v___x_938_; 
v_val_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_928_);
lean_dec(v_val_881_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_944_ = lean_string_append(v___x_943_, v_a_939_);
lean_dec(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
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
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_928_);
lean_dec(v_val_881_);
v_a_949_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_938_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_938_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 0);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_938_, 1);
if (lean_obj_tag(v_a_957_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_a_928_);
lean_dec(v_val_881_);
v_val_958_ = lean_ctor_get(v_a_957_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v_a_957_, 1);
v___x_959_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_960_ = l_Lake_JsonObject_getJson_x3f(v_val_958_, v___x_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_961_; 
lean_dec(v_val_958_);
v___x_961_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0));
return v___x_961_;
}
else
{
lean_object* v_val_962_; lean_object* v___x_963_; 
v_val_962_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v___x_960_, 1);
v___x_963_ = l_Lean_Json_getNat_x3f(v_val_962_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_val_958_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_973_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_969_ = lean_string_append(v___x_968_, v_a_964_);
lean_dec(v_a_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
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
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_val_958_);
v_a_974_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_963_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_963_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 0);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_963_, 1);
v___x_983_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_984_ = l_Lake_JsonObject_getJson_x3f(v_val_958_, v___x_983_);
lean_dec(v_val_958_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_985_; 
lean_dec(v_a_982_);
v___x_985_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1));
return v___x_985_;
}
else
{
lean_object* v_val_986_; lean_object* v___x_987_; 
v_val_986_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v___x_984_, 1);
v___x_987_ = l_Lean_Json_getStr_x3f(v_val_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_982_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_997_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_993_ = lean_string_append(v___x_992_, v_a_988_);
lean_dec(v_a_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
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
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_982_);
v_a_998_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_987_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_987_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 0);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
v_a_1006_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v___x_987_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_987_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_a_982_);
lean_ctor_set(v___x_1010_, 1, v_a_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
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
lean_dec(v_a_957_);
goto v___jp_929_;
}
}
}
}
v___jp_929_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_931_ = l_Lake_JsonObject_getJson_x3f(v_a_928_, v___x_930_);
lean_dec(v_a_928_);
if (lean_obj_tag(v___x_931_) == 0)
{
v_a_883_ = v___x_931_;
goto v___jp_882_;
}
else
{
lean_object* v_val_932_; lean_object* v___x_933_; lean_object* v_a_934_; 
v_val_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_932_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v_a_883_ = v_a_934_;
goto v___jp_882_;
}
}
}
else
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_927_);
v___x_1015_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_881_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1032_; 
v_a_1024_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1026_ = v___x_1015_;
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1015_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_a_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
v___jp_882_:
{
if (lean_obj_tag(v_a_883_) == 1)
{
lean_object* v_val_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_val_881_);
v_val_884_ = lean_ctor_get(v_a_883_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_883_);
if (v_isSharedCheck_908_ == 0)
{
v___x_886_ = v_a_883_;
v_isShared_887_ = v_isSharedCheck_908_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_val_884_);
lean_dec(v_a_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_908_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_884_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_886_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
v_a_897_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_907_ == 0)
{
v___x_899_ = v___x_888_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_888_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 0);
lean_ctor_set(v___x_886_, 0, v_a_897_);
v___x_902_ = v___x_886_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
else
{
lean_object* v___x_909_; 
lean_dec(v_a_883_);
v___x_909_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_881_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_a_918_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v___x_909_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_909_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_a_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object* v_lakeEnv_1035_, lean_object* v_owner_1036_, lean_object* v_pkg_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_url_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_url_1040_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_1035_, v_owner_1036_, v_pkg_1037_);
v___x_1041_ = l_Lake_Reservoir_lakeHeaders;
v___x_1042_ = l_Lake_getUrl(v_url_1040_, v___x_1041_, v_a_1038_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1125_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_a_1044_ = lean_ctor_get(v___x_1042_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1046_ = v___x_1042_;
v_isShared_1047_ = v_isSharedCheck_1125_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1125_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; 
lean_inc(v_a_1043_);
v___x_1048_ = l_Lean_Json_parse(v_a_1043_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1051_ = lean_string_append(v_owner_1036_, v___x_1050_);
v___x_1052_ = lean_string_append(v___x_1051_, v_pkg_1037_);
v___x_1053_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_1052_);
v___x_1054_ = lean_string_append(v___x_1052_, v___x_1053_);
v___x_1055_ = lean_string_append(v___x_1054_, v_a_1049_);
lean_dec(v_a_1049_);
v___x_1056_ = 3;
v___x_1057_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*1, v___x_1056_);
v___x_1058_ = lean_array_get_size(v_a_1044_);
v___x_1059_ = lean_array_push(v_a_1044_, v___x_1057_);
v___x_1060_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1061_ = lean_string_append(v___x_1052_, v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_string_utf8_byte_size(v_a_1043_);
v___x_1064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1064_, 0, v_a_1043_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
v___x_1065_ = l_String_Slice_trimAscii(v___x_1064_);
v___x_1066_ = l_String_Slice_toString(v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1061_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = 0;
v___x_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1068_);
v___x_1070_ = lean_array_push(v___x_1059_, v___x_1069_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
lean_ctor_set(v___x_1046_, 1, v___x_1070_);
lean_ctor_set(v___x_1046_, 0, v___x_1058_);
v___x_1072_ = v___x_1046_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1075_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1078_ = lean_string_append(v_owner_1036_, v___x_1077_);
v___x_1079_ = lean_string_append(v___x_1078_, v_pkg_1037_);
v___x_1080_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_1079_);
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
v___x_1082_ = lean_string_append(v___x_1081_, v_a_1076_);
lean_dec(v_a_1076_);
v___x_1083_ = 3;
v___x_1084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v___x_1083_);
v___x_1085_ = lean_array_get_size(v_a_1044_);
v___x_1086_ = lean_array_push(v_a_1044_, v___x_1084_);
v___x_1087_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1088_ = lean_string_append(v___x_1079_, v___x_1087_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_string_utf8_byte_size(v_a_1043_);
v___x_1091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1091_, 0, v_a_1043_);
lean_ctor_set(v___x_1091_, 1, v___x_1089_);
lean_ctor_set(v___x_1091_, 2, v___x_1090_);
v___x_1092_ = l_String_Slice_trimAscii(v___x_1091_);
v___x_1093_ = l_String_Slice_toString(v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = lean_string_append(v___x_1088_, v___x_1093_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = 0;
v___x_1096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*1, v___x_1095_);
v___x_1097_ = lean_array_push(v___x_1086_, v___x_1096_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
lean_ctor_set(v___x_1046_, 1, v___x_1097_);
lean_ctor_set(v___x_1046_, 0, v___x_1085_);
v___x_1099_ = v___x_1046_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v_a_1101_; 
lean_dec(v_a_1043_);
v_a_1101_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1075_, 1);
if (lean_obj_tag(v_a_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; 
lean_dec_ref(v_owner_1036_);
v_a_1102_ = lean_ctor_get(v_a_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v_a_1101_, 1);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_a_1102_);
v___x_1104_ = v___x_1046_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_a_1044_);
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
lean_object* v_status_1106_; lean_object* v_message_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v_status_1106_ = lean_ctor_get(v_a_1101_, 0);
lean_inc(v_status_1106_);
v_message_1107_ = lean_ctor_get(v_a_1101_, 1);
lean_inc_ref(v_message_1107_);
lean_dec_ref_known(v_a_1101_, 2);
v___x_1108_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1109_ = lean_string_append(v_owner_1036_, v___x_1108_);
v___x_1110_ = lean_string_append(v___x_1109_, v_pkg_1037_);
v___x_1111_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__0));
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
v___x_1113_ = l_Nat_reprFast(v_status_1106_);
v___x_1114_ = lean_string_append(v___x_1112_, v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__1));
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
v___x_1117_ = lean_string_append(v___x_1116_, v_message_1107_);
lean_dec_ref(v_message_1107_);
v___x_1118_ = 3;
v___x_1119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*1, v___x_1118_);
v___x_1120_ = lean_array_get_size(v_a_1044_);
v___x_1121_ = lean_array_push(v_a_1044_, v___x_1119_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
lean_ctor_set(v___x_1046_, 1, v___x_1121_);
lean_ctor_set(v___x_1046_, 0, v___x_1120_);
v___x_1123_ = v___x_1046_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1142_; 
v_a_1126_ = lean_ctor_get(v___x_1042_, 0);
v_a_1127_ = lean_ctor_get(v___x_1042_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1129_ = v___x_1042_;
v_isShared_1130_ = v_isSharedCheck_1142_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_inc(v_a_1126_);
lean_dec(v___x_1042_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1142_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1131_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1132_ = lean_string_append(v_owner_1036_, v___x_1131_);
v___x_1133_ = lean_string_append(v___x_1132_, v_pkg_1037_);
v___x_1134_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_1135_ = lean_string_append(v___x_1133_, v___x_1134_);
v___x_1136_ = 3;
v___x_1137_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*1, v___x_1136_);
v___x_1138_ = lean_array_push(v_a_1127_, v___x_1137_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 1, v___x_1138_);
v___x_1140_ = v___x_1129_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object* v_lakeEnv_1143_, lean_object* v_owner_1144_, lean_object* v_pkg_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1143_, v_owner_1144_, v_pkg_1145_, v_a_1146_);
lean_dec_ref(v_pkg_1145_);
return v_res_1148_;
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
