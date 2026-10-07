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
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_215_; 
v_a_135_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_215_ == 0)
{
v___x_137_ = v___x_133_;
v_isShared_138_ = v_isSharedCheck_215_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_215_;
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
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_151_; 
lean_del_object(v___x_137_);
lean_dec(v_a_135_);
v_a_151_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_147_, 1);
v_a_129_ = v_a_151_;
goto v___jp_128_;
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_214_; 
v_a_152_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_214_ == 0)
{
v___x_154_ = v___x_147_;
v_isShared_155_ = v_isSharedCheck_214_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_147_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_214_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
if (lean_obj_tag(v_a_152_) == 1)
{
lean_object* v_val_156_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v_a_160_; lean_object* v___y_166_; lean_object* v_a_167_; lean_object* v_a_179_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_del_object(v___x_137_);
v_val_156_ = lean_ctor_get(v_a_152_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v_a_152_, 1);
v___x_190_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__7));
v___x_191_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_box(0);
v_a_179_ = v___x_192_;
goto v___jp_178_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; 
v_val_193_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_191_, 1);
v___x_194_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__8));
v___x_197_ = lean_string_append(v___x_196_, v_a_195_);
lean_dec(v_a_195_);
v_a_129_ = v___x_197_;
goto v___jp_128_;
}
else
{
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_198_; 
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_198_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_194_, 1);
v_a_129_ = v_a_198_;
goto v___jp_128_;
}
else
{
lean_object* v_a_199_; 
v_a_199_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_194_, 1);
if (lean_obj_tag(v_a_199_) == 0)
{
v_a_179_ = v_a_199_;
goto v___jp_178_;
}
else
{
lean_object* v_val_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_val_200_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v_a_199_, 1);
v___x_201_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__9));
v___x_202_ = lean_string_dec_eq(v_val_200_, v___x_201_);
lean_dec(v_val_200_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
v_a_179_ = v___x_203_;
goto v___jp_178_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__10));
v___x_205_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
v_a_179_ = v___x_206_;
goto v___jp_178_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_208_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_205_, 1);
v___x_208_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__11));
v___x_211_ = lean_string_append(v___x_210_, v_a_209_);
lean_dec(v_a_209_);
v_a_129_ = v___x_211_;
goto v___jp_128_;
}
else
{
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_212_; 
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_212_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_208_, 1);
v_a_129_ = v_a_212_;
goto v___jp_128_;
}
else
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_208_, 1);
v_a_179_ = v_a_213_;
goto v___jp_178_;
}
}
}
}
}
}
}
}
v___jp_157_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_161_, 0, v_a_135_);
lean_ctor_set(v___x_161_, 1, v_val_156_);
lean_ctor_set(v___x_161_, 2, v___y_159_);
lean_ctor_set(v___x_161_, 3, v___y_158_);
lean_ctor_set(v___x_161_, 4, v_a_160_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_161_);
v___x_163_ = v___x_154_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
v___jp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__3));
v___x_169_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
v___y_158_ = v_a_167_;
v___y_159_ = v___y_166_;
v_a_160_ = v___x_170_;
goto v___jp_157_;
}
else
{
lean_object* v_val_171_; lean_object* v___x_172_; 
v_val_171_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v___x_169_, 1);
v___x_172_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(v_val_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_a_167_);
lean_dec(v___y_166_);
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__4));
v___x_175_ = lean_string_append(v___x_174_, v_a_173_);
lean_dec(v_a_173_);
v_a_129_ = v___x_175_;
goto v___jp_128_;
}
else
{
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_176_; 
lean_dec(v_a_167_);
lean_dec(v___y_166_);
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_176_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_172_, 1);
v_a_129_ = v_a_176_;
goto v___jp_128_;
}
else
{
lean_object* v_a_177_; 
v_a_177_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_172_, 1);
v___y_158_ = v_a_167_;
v___y_159_ = v___y_166_;
v_a_160_ = v_a_177_;
goto v___jp_157_;
}
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__5));
v___x_181_ = l_Lake_JsonObject_getJson_x3f(v_a_135_, v___x_180_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
v___y_166_ = v_a_179_;
v_a_167_ = v___x_182_;
goto v___jp_165_;
}
else
{
lean_object* v_val_183_; lean_object* v___x_184_; 
v_val_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v___x_181_, 1);
v___x_184_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_a_179_);
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v___x_186_ = ((lean_object*)(l_Lake_RegistrySrc_fromJson_x3f___closed__6));
v___x_187_ = lean_string_append(v___x_186_, v_a_185_);
lean_dec(v_a_185_);
v_a_129_ = v___x_187_;
goto v___jp_128_;
}
else
{
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_188_; 
lean_dec(v_a_179_);
lean_dec(v_val_156_);
lean_del_object(v___x_154_);
lean_dec(v_a_135_);
v_a_188_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_184_, 1);
v_a_129_ = v_a_188_;
goto v___jp_128_;
}
else
{
lean_object* v_a_189_; 
v_a_189_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_184_, 1);
v___y_166_ = v_a_179_;
v_a_167_ = v_a_189_;
goto v___jp_165_;
}
}
}
}
}
else
{
lean_del_object(v___x_154_);
lean_dec(v_a_152_);
goto v___jp_139_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object* v_as_229_, size_t v_sz_230_, size_t v_i_231_, lean_object* v_b_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_lt(v_i_231_, v_sz_230_);
if (v___x_233_ == 0)
{
lean_inc_ref(v_b_232_);
return v_b_232_;
}
else
{
lean_object* v___x_234_; lean_object* v_a_235_; uint8_t v___x_236_; 
v___x_234_ = lean_box(0);
v_a_235_ = lean_array_uget_borrowed(v_as_229_, v_i_231_);
v___x_236_ = l_Lake_RegistrySrc_isGit(v_a_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; size_t v___x_238_; size_t v___x_239_; 
v___x_237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_231_, v___x_238_);
v_i_231_ = v___x_239_;
v_b_232_ = v___x_237_;
goto _start;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_inc(v_a_235_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v_a_235_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_234_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(lean_object* v_as_244_, lean_object* v_sz_245_, lean_object* v_i_246_, lean_object* v_b_247_){
_start:
{
size_t v_sz_boxed_248_; size_t v_i_boxed_249_; lean_object* v_res_250_; 
v_sz_boxed_248_ = lean_unbox_usize(v_sz_245_);
lean_dec(v_sz_245_);
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_res_250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_as_244_, v_sz_boxed_248_, v_i_boxed_249_, v_b_247_);
lean_dec_ref(v_b_247_);
lean_dec_ref(v_as_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object* v_pkg_251_){
_start:
{
lean_object* v_sources_252_; lean_object* v___x_253_; lean_object* v___x_254_; size_t v_sz_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v_fst_258_; 
v_sources_252_ = lean_ctor_get(v_pkg_251_, 2);
v___x_253_ = lean_box(0);
v___x_254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0));
v_sz_255_ = lean_array_size(v_sources_252_);
v___x_256_ = ((size_t)0ULL);
v___x_257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_sources_252_, v_sz_255_, v___x_256_, v___x_254_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_fst_258_);
lean_dec_ref(v___x_257_);
if (lean_obj_tag(v_fst_258_) == 0)
{
return v___x_253_;
}
else
{
lean_object* v_val_259_; 
v_val_259_ = lean_ctor_get(v_fst_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v_fst_258_, 1);
return v_val_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_gitSrc_x3f___boxed(lean_object* v_pkg_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lake_RegistryPkg_gitSrc_x3f(v_pkg_260_);
lean_dec_ref(v_pkg_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson(lean_object* v_src_262_){
_start:
{
lean_object* v_data_263_; 
v_data_263_ = lean_ctor_get(v_src_262_, 3);
lean_inc(v_data_263_);
return v_data_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_toJson___boxed(lean_object* v_src_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lake_RegistryPkg_toJson(v_src_264_);
lean_dec_ref(v_src_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(size_t v_sz_268_, size_t v_i_269_, lean_object* v_bs_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_lt(v_i_269_, v_sz_268_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_bs_270_);
return v___x_272_;
}
else
{
lean_object* v_v_273_; lean_object* v___x_274_; lean_object* v_bs_x27_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v_v_273_ = lean_array_uget(v_bs_270_, v_i_269_);
v___x_274_ = lean_unsigned_to_nat(0u);
v_bs_x27_275_ = lean_array_uset(v_bs_270_, v_i_269_, v___x_274_);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_269_, v___x_276_);
v___x_278_ = lean_array_uset(v_bs_x27_275_, v_i_269_, v_v_273_);
v_i_269_ = v___x_277_;
v_bs_270_ = v___x_278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_280_, lean_object* v_i_281_, lean_object* v_bs_282_){
_start:
{
size_t v_sz_boxed_283_; size_t v_i_boxed_284_; lean_object* v_res_285_; 
v_sz_boxed_283_ = lean_unbox_usize(v_sz_280_);
lean_dec(v_sz_280_);
v_i_boxed_284_ = lean_unbox_usize(v_i_281_);
lean_dec(v_i_281_);
v_res_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_boxed_283_, v_i_boxed_284_, v_bs_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 4)
{
lean_object* v_elems_289_; size_t v_sz_290_; size_t v___x_291_; lean_object* v___x_292_; 
v_elems_289_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_elems_289_);
lean_dec_ref_known(v_x_288_, 1);
v_sz_290_ = lean_array_size(v_elems_289_);
v___x_291_ = ((size_t)0ULL);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_290_, v___x_291_, v_elems_289_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_293_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_294_ = lean_unsigned_to_nat(80u);
v___x_295_ = l_Lean_Json_pretty(v_x_288_, v___x_294_);
v___x_296_ = lean_string_append(v___x_293_, v___x_295_);
lean_dec_ref(v___x_295_);
v___x_297_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v___x_303_; 
v___x_303_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0));
return v___x_303_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(v_x_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_a_313_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v___x_304_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_304_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_a_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(size_t v_sz_322_, size_t v_i_323_, lean_object* v_bs_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_bs_324_);
return v___x_326_;
}
else
{
lean_object* v_v_327_; lean_object* v___x_328_; 
v_v_327_ = lean_array_uget_borrowed(v_bs_324_, v_i_323_);
lean_inc(v_v_327_);
v___x_328_ = l_Lake_RegistrySrc_fromJson_x3f(v_v_327_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_bs_324_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_338_; lean_object* v_bs_x27_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v_a_337_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_328_, 1);
v___x_338_ = lean_unsigned_to_nat(0u);
v_bs_x27_339_ = lean_array_uset(v_bs_324_, v_i_323_, v___x_338_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_323_, v___x_340_);
v___x_342_ = lean_array_uset(v_bs_x27_339_, v_i_323_, v_a_337_);
v_i_323_ = v___x_341_;
v_bs_324_ = v___x_342_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(lean_object* v_sz_344_, lean_object* v_i_345_, lean_object* v_bs_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v_i_boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_344_);
lean_dec(v_sz_344_);
v_i_boxed_348_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_boxed_347_, v_i_boxed_348_, v_bs_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryPkg_fromJson_x3f(lean_object* v_val_361_){
_start:
{
lean_object* v_a_363_; lean_object* v___x_367_; 
v___x_367_ = l_Lean_Json_getObj_x3f(v_val_361_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v_a_363_ = v_a_368_;
goto v___jp_362_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_a_369_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_367_, 1);
v___x_370_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__1));
v___x_371_ = l_Lake_JsonObject_getJson_x3f(v_a_369_, v___x_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; 
lean_dec(v_a_369_);
v___x_372_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__2));
v_a_363_ = v___x_372_;
goto v___jp_362_;
}
else
{
lean_object* v_val_373_; lean_object* v___x_374_; 
v_val_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_371_, 1);
v___x_374_ = l_Lean_Json_getStr_x3f(v_val_373_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_a_369_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v___x_376_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__3));
v___x_377_ = lean_string_append(v___x_376_, v_a_375_);
lean_dec(v_a_375_);
v_a_363_ = v___x_377_;
goto v___jp_362_;
}
else
{
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_378_; 
lean_dec(v_a_369_);
v_a_378_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v___x_374_, 1);
v_a_363_ = v_a_378_;
goto v___jp_362_;
}
else
{
lean_object* v_a_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_374_, 1);
v___x_380_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__4));
v___x_381_ = l_Lake_JsonObject_getJson_x3f(v_a_369_, v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; 
lean_dec(v_a_379_);
lean_dec(v_a_369_);
v___x_382_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__5));
v_a_363_ = v___x_382_;
goto v___jp_362_;
}
else
{
lean_object* v_val_383_; lean_object* v___x_384_; 
v_val_383_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_381_, 1);
v___x_384_ = l_Lean_Json_getStr_x3f(v_val_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_a_379_);
lean_dec(v_a_369_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__6));
v___x_387_ = lean_string_append(v___x_386_, v_a_385_);
lean_dec(v_a_385_);
v_a_363_ = v___x_387_;
goto v___jp_362_;
}
else
{
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_388_; 
lean_dec(v_a_379_);
lean_dec(v_a_369_);
v_a_388_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_384_, 1);
v_a_363_ = v_a_388_;
goto v___jp_362_;
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_423_; 
v_a_389_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_423_ == 0)
{
v___x_391_ = v___x_384_;
v_isShared_392_ = v_isSharedCheck_423_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_384_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_423_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_a_394_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__8));
v___x_414_ = l_Lake_JsonObject_getJson_x3f(v_a_369_, v___x_413_);
if (lean_obj_tag(v___x_414_) == 0)
{
goto v___jp_411_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_416_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = l_Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(v_val_415_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_del_object(v___x_391_);
lean_dec(v_a_389_);
lean_dec(v_a_379_);
lean_dec(v_a_369_);
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__9));
v___x_419_ = lean_string_append(v___x_418_, v_a_417_);
lean_dec(v_a_417_);
v_a_363_ = v___x_419_;
goto v___jp_362_;
}
else
{
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_420_; 
lean_del_object(v___x_391_);
lean_dec(v_a_389_);
lean_dec(v_a_379_);
lean_dec(v_a_369_);
v_a_420_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_416_, 1);
v_a_363_ = v_a_420_;
goto v___jp_362_;
}
else
{
lean_object* v_a_421_; 
v_a_421_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_416_, 1);
if (lean_obj_tag(v_a_421_) == 0)
{
goto v___jp_411_;
}
else
{
lean_object* v_val_422_; 
v_val_422_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_a_421_, 1);
v_a_394_ = v_val_422_;
goto v___jp_393_;
}
}
}
}
v___jp_393_:
{
size_t v_sz_395_; size_t v___x_396_; lean_object* v___x_397_; 
v_sz_395_ = lean_array_size(v_a_394_);
v___x_396_ = ((size_t)0ULL);
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_395_, v___x_396_, v_a_394_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; 
lean_del_object(v___x_391_);
lean_dec(v_a_389_);
lean_dec(v_a_379_);
lean_dec(v_a_369_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v_a_363_ = v_a_398_;
goto v___jp_362_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_410_; 
v_a_399_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_410_ == 0)
{
v___x_401_ = v___x_397_;
v_isShared_402_ = v_isSharedCheck_410_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_397_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_410_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 5);
lean_ctor_set(v___x_391_, 0, v_a_369_);
v___x_404_ = v___x_391_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_369_);
v___x_404_ = v_reuseFailAlloc_409_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_405_, 0, v_a_379_);
lean_ctor_set(v___x_405_, 1, v_a_389_);
lean_ctor_set(v___x_405_, 2, v_a_399_);
lean_ctor_set(v___x_405_, 3, v___x_404_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_405_);
v___x_407_ = v___x_401_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
v___jp_411_:
{
lean_object* v___x_412_; 
v___x_412_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__7));
v_a_394_ = v___x_412_;
goto v___jp_393_;
}
}
}
}
}
}
}
}
}
v___jp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = ((lean_object*)(l_Lake_RegistryPkg_fromJson_x3f___closed__0));
v___x_365_ = lean_string_append(v___x_364_, v_a_363_);
lean_dec_ref(v_a_363_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object* v_lakeEnv_428_, lean_object* v_owner_429_, lean_object* v_pkg_430_){
_start:
{
lean_object* v_reservoirApiUrl_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_reservoirApiUrl_431_ = lean_ctor_get(v_lakeEnv_428_, 3);
lean_inc_ref(v_reservoirApiUrl_431_);
lean_dec_ref(v_lakeEnv_428_);
v___x_432_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_433_ = lean_string_append(v_reservoirApiUrl_431_, v___x_432_);
v___x_434_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_435_ = l_Lake_uriEncode(v_owner_429_, v___x_434_);
v___x_436_ = lean_string_append(v___x_433_, v___x_435_);
lean_dec_ref(v___x_435_);
v___x_437_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
v___x_439_ = l_Lake_uriEncode(v_pkg_430_, v___x_434_);
v___x_440_ = lean_string_append(v___x_438_, v___x_439_);
lean_dec_ref(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl___boxed(lean_object* v_lakeEnv_441_, lean_object* v_owner_442_, lean_object* v_pkg_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_441_, v_owner_442_, v_pkg_443_);
lean_dec_ref(v_pkg_443_);
lean_dec_ref(v_owner_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0));
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Json_getObj_x3f(v_x_447_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_458_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_449_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_449_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0));
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_x_469_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* v_val_486_){
_start:
{
lean_object* v_a_488_; lean_object* v___x_532_; 
lean_inc(v_val_486_);
v___x_532_ = l_Lean_Json_getObj_x3f(v_val_486_);
if (lean_obj_tag(v___x_532_) == 1)
{
lean_object* v_a_533_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_540_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_541_ = l_Lake_JsonObject_getJson_x3f(v_a_533_, v___x_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
goto v___jp_534_;
}
else
{
lean_object* v_val_542_; lean_object* v___x_543_; 
v_val_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_542_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_a_533_);
lean_dec(v_val_486_);
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_553_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_549_ = lean_string_append(v___x_548_, v_a_544_);
lean_dec(v_a_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_533_);
lean_dec(v_val_486_);
v_a_554_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_543_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_543_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
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
lean_object* v_a_562_; 
v_a_562_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_543_, 1);
if (lean_obj_tag(v_a_562_) == 1)
{
lean_object* v_val_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_a_533_);
lean_dec(v_val_486_);
v_val_563_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v_a_562_, 1);
v___x_564_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_565_ = l_Lake_JsonObject_getJson_x3f(v_val_563_, v___x_564_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_566_; 
lean_dec(v_val_563_);
v___x_566_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5));
return v___x_566_;
}
else
{
lean_object* v_val_567_; lean_object* v___x_568_; 
v_val_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_565_, 1);
v___x_568_ = l_Lean_Json_getNat_x3f(v_val_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_val_563_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_574_ = lean_string_append(v___x_573_, v_a_569_);
lean_dec(v_a_569_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v_val_563_);
v_a_579_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_568_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_568_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_568_, 1);
v___x_588_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_589_ = l_Lake_JsonObject_getJson_x3f(v_val_563_, v___x_588_);
lean_dec(v_val_563_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec(v_a_587_);
v___x_590_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9));
return v___x_590_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_592_; 
v_val_591_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v___x_589_, 1);
v___x_592_ = l_Lean_Json_getStr_x3f(v_val_591_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_a_587_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_602_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_598_ = lean_string_append(v___x_597_, v_a_593_);
lean_dec(v_a_593_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_a_587_);
v_a_603_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_592_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_592_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 0);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_a_611_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v___x_592_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_592_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v_a_587_);
lean_ctor_set(v___x_615_, 1, v_a_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
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
lean_dec(v_a_562_);
goto v___jp_534_;
}
}
}
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_536_ = l_Lake_JsonObject_getJson_x3f(v_a_533_, v___x_535_);
lean_dec(v_a_533_);
if (lean_obj_tag(v___x_536_) == 0)
{
v_a_488_ = v___x_536_;
goto v___jp_487_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; lean_object* v_a_539_; 
v_val_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_537_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref(v___x_538_);
v_a_488_ = v_a_539_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v___x_532_);
v___x_620_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_486_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_a_629_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v___x_620_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_620_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
v___jp_487_:
{
if (lean_obj_tag(v_a_488_) == 1)
{
lean_object* v_val_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_val_486_);
v_val_489_ = lean_ctor_get(v_a_488_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_a_488_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_val_489_);
lean_dec(v_a_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_489_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_491_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_512_; 
v_a_502_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_512_ == 0)
{
v___x_504_ = v___x_493_;
v_isShared_505_ = v_isSharedCheck_512_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_493_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_512_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set_tag(v___x_491_, 0);
lean_ctor_set(v___x_491_, 0, v_a_502_);
v___x_507_ = v___x_491_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_a_488_);
v___x_514_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_486_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_a_523_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_531_ == 0)
{
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v_a_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* v_lakeEnv_643_, lean_object* v_owner_644_, lean_object* v_pkg_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_url_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_url_648_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_643_, v_owner_644_, v_pkg_645_);
v___x_649_ = l_Lake_Reservoir_lakeHeaders;
v___x_650_ = l_Lake_getUrl(v_url_648_, v___x_649_, v_a_646_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_742_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_a_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_742_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_742_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_742_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; 
lean_inc(v_a_651_);
v___x_656_ = l_Lean_Json_parse(v_a_651_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_659_ = lean_string_append(v_owner_644_, v___x_658_);
v___x_660_ = lean_string_append(v___x_659_, v_pkg_645_);
v___x_661_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_660_);
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
v___x_663_ = lean_string_append(v___x_662_, v_a_657_);
lean_dec(v_a_657_);
v___x_664_ = 3;
v___x_665_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*1, v___x_664_);
v___x_666_ = lean_array_get_size(v_a_652_);
v___x_667_ = lean_array_push(v_a_652_, v___x_665_);
v___x_668_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_669_ = lean_string_append(v___x_660_, v___x_668_);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_string_utf8_byte_size(v_a_651_);
v___x_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_672_, 0, v_a_651_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
lean_ctor_set(v___x_672_, 2, v___x_671_);
v___x_673_ = l_String_Slice_trimAscii(v___x_672_);
v___x_674_ = l_String_Slice_toString(v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = lean_string_append(v___x_669_, v___x_674_);
lean_dec_ref(v___x_674_);
v___x_676_ = 0;
v___x_677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*1, v___x_676_);
v___x_678_ = lean_array_push(v___x_667_, v___x_677_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 1, v___x_678_);
lean_ctor_set(v___x_654_, 0, v___x_666_);
v___x_680_ = v___x_654_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_656_, 1);
v___x_683_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_686_ = lean_string_append(v_owner_644_, v___x_685_);
v___x_687_ = lean_string_append(v___x_686_, v_pkg_645_);
v___x_688_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_687_);
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
v___x_690_ = lean_string_append(v___x_689_, v_a_684_);
lean_dec(v_a_684_);
v___x_691_ = 3;
v___x_692_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*1, v___x_691_);
v___x_693_ = lean_array_get_size(v_a_652_);
v___x_694_ = lean_array_push(v_a_652_, v___x_692_);
v___x_695_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_696_ = lean_string_append(v___x_687_, v___x_695_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_string_utf8_byte_size(v_a_651_);
v___x_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_699_, 0, v_a_651_);
lean_ctor_set(v___x_699_, 1, v___x_697_);
lean_ctor_set(v___x_699_, 2, v___x_698_);
v___x_700_ = l_String_Slice_trimAscii(v___x_699_);
v___x_701_ = l_String_Slice_toString(v___x_700_);
lean_dec_ref(v___x_700_);
v___x_702_ = lean_string_append(v___x_696_, v___x_701_);
lean_dec_ref(v___x_701_);
v___x_703_ = 0;
v___x_704_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*1, v___x_703_);
v___x_705_ = lean_array_push(v___x_694_, v___x_704_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 1, v___x_705_);
lean_ctor_set(v___x_654_, 0, v___x_693_);
v___x_707_ = v___x_654_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
lean_object* v_a_709_; 
lean_dec(v_a_651_);
v_a_709_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_683_, 1);
if (lean_obj_tag(v_a_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_owner_644_);
v_a_710_ = lean_ctor_get(v_a_709_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_720_ == 0)
{
v___x_712_ = v_a_709_;
v_isShared_713_ = v_isSharedCheck_720_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v_a_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_720_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_719_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_715_);
v___x_717_ = v___x_654_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_a_652_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_status_721_; lean_object* v_message_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_status_721_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_status_721_);
v_message_722_ = lean_ctor_get(v_a_709_, 1);
lean_inc_ref(v_message_722_);
lean_dec_ref_known(v_a_709_, 2);
v___x_723_ = lean_unsigned_to_nat(404u);
v___x_724_ = lean_nat_dec_eq(v_status_721_, v___x_723_);
lean_dec(v_status_721_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_725_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_726_ = lean_string_append(v_owner_644_, v___x_725_);
v___x_727_ = lean_string_append(v___x_726_, v_pkg_645_);
v___x_728_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__3));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = lean_string_append(v___x_729_, v_message_722_);
lean_dec_ref(v_message_722_);
v___x_731_ = 3;
v___x_732_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*1, v___x_731_);
v___x_733_ = lean_array_get_size(v_a_652_);
v___x_734_ = lean_array_push(v_a_652_, v___x_732_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 1, v___x_734_);
lean_ctor_set(v___x_654_, 0, v___x_733_);
v___x_736_ = v___x_654_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec_ref(v_message_722_);
lean_dec_ref(v_owner_644_);
v___x_738_ = lean_box(0);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_738_);
v___x_740_ = v___x_654_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_a_652_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_759_; 
v_a_743_ = lean_ctor_get(v___x_650_, 0);
v_a_744_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_759_ == 0)
{
v___x_746_ = v___x_650_;
v_isShared_747_ = v_isSharedCheck_759_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_inc(v_a_743_);
lean_dec(v___x_650_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_759_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_748_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_749_ = lean_string_append(v_owner_644_, v___x_748_);
v___x_750_ = lean_string_append(v___x_749_, v_pkg_645_);
v___x_751_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = 3;
v___x_754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_753_);
v___x_755_ = lean_array_push(v_a_744_, v___x_754_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_755_);
v___x_757_ = v___x_746_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_743_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* v_lakeEnv_760_, lean_object* v_owner_761_, lean_object* v_pkg_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_760_, v_owner_761_, v_pkg_762_, v_a_763_);
lean_dec_ref(v_pkg_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object* v_val_773_){
_start:
{
lean_object* v_a_775_; lean_object* v_a_780_; lean_object* v___x_783_; 
v___x_783_ = l_Lean_Json_getObj_x3f(v_val_773_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v_a_775_ = v_a_784_;
goto v___jp_774_;
}
else
{
lean_object* v_a_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_785_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_783_, 1);
v___x_786_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__2));
v___x_787_ = l_Lake_JsonObject_getJson_x3f(v_a_785_, v___x_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_788_; 
lean_dec(v_a_785_);
v___x_788_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__3));
v_a_775_ = v___x_788_;
goto v___jp_774_;
}
else
{
lean_object* v_val_789_; lean_object* v___x_790_; 
v_val_789_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v___x_787_, 1);
v___x_790_ = l_Lean_Json_getStr_x3f(v_val_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; 
lean_dec(v_a_785_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v_a_780_ = v_a_791_;
goto v___jp_779_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_790_, 1);
v___x_793_ = l_Lake_StdVer_parse(v_a_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; 
lean_dec(v_a_785_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v_a_780_ = v_a_794_;
goto v___jp_779_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_a_795_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_793_, 1);
v___x_796_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__4));
v___x_797_ = l_Lake_JsonObject_getJson_x3f(v_a_785_, v___x_796_);
lean_dec(v_a_785_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; 
lean_dec(v_a_795_);
v___x_798_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__5));
v_a_775_ = v___x_798_;
goto v___jp_774_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; 
v_val_799_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_797_, 1);
v___x_800_ = l_Lean_Json_getStr_x3f(v_val_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v_a_795_);
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__6));
v___x_803_ = lean_string_append(v___x_802_, v_a_801_);
lean_dec(v_a_801_);
v_a_775_ = v___x_803_;
goto v___jp_774_;
}
else
{
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_804_; 
lean_dec(v_a_795_);
v_a_804_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_800_, 1);
v_a_775_ = v_a_804_;
goto v___jp_774_;
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_a_805_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v___x_800_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_800_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_a_795_);
lean_ctor_set(v___x_809_, 1, v_a_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
}
}
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__0));
v___x_777_ = lean_string_append(v___x_776_, v_a_775_);
lean_dec_ref(v_a_775_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__1));
v___x_782_ = lean_string_append(v___x_781_, v_a_780_);
lean_dec_ref(v_a_780_);
v_a_775_ = v___x_782_;
goto v___jp_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object* v_lakeEnv_817_, lean_object* v_owner_818_, lean_object* v_pkg_819_){
_start:
{
lean_object* v_reservoirApiUrl_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_reservoirApiUrl_820_ = lean_ctor_get(v_lakeEnv_817_, 3);
lean_inc_ref(v_reservoirApiUrl_820_);
lean_dec_ref(v_lakeEnv_817_);
v___x_821_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_822_ = lean_string_append(v_reservoirApiUrl_820_, v___x_821_);
v___x_823_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_824_ = l_Lake_uriEncode(v_owner_818_, v___x_823_);
v___x_825_ = lean_string_append(v___x_822_, v___x_824_);
lean_dec_ref(v___x_824_);
v___x_826_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v___x_828_ = l_Lake_uriEncode(v_pkg_819_, v___x_823_);
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
lean_dec_ref(v___x_828_);
v___x_830_ = ((lean_object*)(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0));
v___x_831_ = lean_string_append(v___x_829_, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl___boxed(lean_object* v_lakeEnv_832_, lean_object* v_owner_833_, lean_object* v_pkg_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_832_, v_owner_833_, v_pkg_834_);
lean_dec_ref(v_pkg_834_);
lean_dec_ref(v_owner_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t v_sz_836_, size_t v_i_837_, lean_object* v_bs_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = lean_usize_dec_lt(v_i_837_, v_sz_836_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_bs_838_);
return v___x_840_;
}
else
{
lean_object* v_v_841_; lean_object* v___x_842_; 
v_v_841_ = lean_array_uget_borrowed(v_bs_838_, v_i_837_);
lean_inc(v_v_841_);
v___x_842_ = l_Lake_RegistryVer_fromJson_x3f(v_v_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_bs_838_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v_bs_x27_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v_a_851_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_842_, 1);
v___x_852_ = lean_unsigned_to_nat(0u);
v_bs_x27_853_ = lean_array_uset(v_bs_838_, v_i_837_, v___x_852_);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_837_, v___x_854_);
v___x_856_ = lean_array_uset(v_bs_x27_853_, v_i_837_, v_a_851_);
v_i_837_ = v___x_855_;
v_bs_838_ = v___x_856_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_858_, lean_object* v_i_859_, lean_object* v_bs_860_){
_start:
{
size_t v_sz_boxed_861_; size_t v_i_boxed_862_; lean_object* v_res_863_; 
v_sz_boxed_861_ = lean_unbox_usize(v_sz_858_);
lean_dec(v_sz_858_);
v_i_boxed_862_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_861_, v_i_boxed_862_, v_bs_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 4)
{
lean_object* v_elems_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; 
v_elems_865_ = lean_ctor_get(v_x_864_, 0);
lean_inc_ref(v_elems_865_);
lean_dec_ref_known(v_x_864_, 1);
v_sz_866_ = lean_array_size(v_elems_865_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_866_, v___x_867_, v_elems_865_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_869_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_870_ = lean_unsigned_to_nat(80u);
v___x_871_ = l_Lean_Json_pretty(v_x_864_, v___x_870_);
v___x_872_ = lean_string_append(v___x_869_, v___x_871_);
lean_dec_ref(v___x_871_);
v___x_873_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_874_ = lean_string_append(v___x_872_, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object* v_val_880_){
_start:
{
lean_object* v_a_882_; lean_object* v___x_926_; 
lean_inc(v_val_880_);
v___x_926_ = l_Lean_Json_getObj_x3f(v_val_880_);
if (lean_obj_tag(v___x_926_) == 1)
{
lean_object* v_a_927_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_934_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
v___x_935_ = l_Lake_JsonObject_getJson_x3f(v_a_927_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
goto v___jp_928_;
}
else
{
lean_object* v_val_936_; lean_object* v___x_937_; 
v_val_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_936_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_927_);
lean_dec(v_val_880_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_947_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_942_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2));
v___x_943_ = lean_string_append(v___x_942_, v_a_938_);
lean_dec(v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_943_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_a_927_);
lean_dec(v_val_880_);
v_a_948_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_937_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_937_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_a_956_; 
v_a_956_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_937_, 1);
if (lean_obj_tag(v_a_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_a_927_);
lean_dec(v_val_880_);
v_val_957_ = lean_ctor_get(v_a_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_a_956_, 1);
v___x_958_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3));
v___x_959_ = l_Lake_JsonObject_getJson_x3f(v_val_957_, v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_960_; 
lean_dec(v_val_957_);
v___x_960_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0));
return v___x_960_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_962_; 
v_val_961_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v___x_959_, 1);
v___x_962_ = l_Lean_Json_getNat_x3f(v_val_961_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
lean_dec(v_val_957_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6));
v___x_968_ = lean_string_append(v___x_967_, v_a_963_);
lean_dec(v_a_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_val_957_);
v_a_973_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_962_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_962_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_962_, 1);
v___x_982_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7));
v___x_983_ = l_Lake_JsonObject_getJson_x3f(v_val_957_, v___x_982_);
lean_dec(v_val_957_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v___x_984_; 
lean_dec(v_a_981_);
v___x_984_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1));
return v___x_984_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_986_; 
v_val_985_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v___x_983_, 1);
v___x_986_ = l_Lean_Json_getStr_x3f(v_val_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_a_981_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_996_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_991_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10));
v___x_992_ = lean_string_append(v___x_991_, v_a_987_);
lean_dec(v_a_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_992_);
v___x_994_ = v___x_989_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_a_981_);
v_a_997_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_986_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_986_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1013_; 
v_a_1005_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1007_ = v___x_986_;
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_986_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_a_981_);
lean_ctor_set(v___x_1009_, 1, v_a_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1009_);
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
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
lean_dec(v_a_956_);
goto v___jp_928_;
}
}
}
}
v___jp_928_:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
v___x_930_ = l_Lake_JsonObject_getJson_x3f(v_a_927_, v___x_929_);
lean_dec(v_a_927_);
if (lean_obj_tag(v___x_930_) == 0)
{
v_a_882_ = v___x_930_;
goto v___jp_881_;
}
else
{
lean_object* v_val_931_; lean_object* v___x_932_; lean_object* v_a_933_; 
v_val_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_931_);
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v___x_932_);
v_a_882_ = v_a_933_;
goto v___jp_881_;
}
}
}
else
{
lean_object* v___x_1014_; 
lean_dec_ref(v___x_926_);
v___x_1014_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_880_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_a_1023_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v___x_1014_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1014_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
v___jp_881_:
{
if (lean_obj_tag(v_a_882_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_val_880_);
v_val_883_ = lean_ctor_get(v_a_882_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_907_ == 0)
{
v___x_885_ = v_a_882_;
v_isShared_886_ = v_isSharedCheck_907_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_val_883_);
lean_dec(v_a_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_907_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_883_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_del_object(v___x_885_);
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
v_a_896_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_906_ == 0)
{
v___x_898_ = v___x_887_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_887_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 0);
lean_ctor_set(v___x_885_, 0, v_a_896_);
v___x_901_ = v___x_885_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_901_);
v___x_903_ = v___x_898_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v_a_882_);
v___x_908_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_880_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_a_917_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_908_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_908_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v_a_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object* v_lakeEnv_1034_, lean_object* v_owner_1035_, lean_object* v_pkg_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_url_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_url_1039_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_1034_, v_owner_1035_, v_pkg_1036_);
v___x_1040_ = l_Lake_Reservoir_lakeHeaders;
v___x_1041_ = l_Lake_getUrl(v_url_1039_, v___x_1040_, v_a_1037_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1124_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_a_1043_ = lean_ctor_get(v___x_1041_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1045_ = v___x_1041_;
v_isShared_1046_ = v_isSharedCheck_1124_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1124_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; 
lean_inc(v_a_1042_);
v___x_1047_ = l_Lean_Json_parse(v_a_1042_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1050_ = lean_string_append(v_owner_1035_, v___x_1049_);
v___x_1051_ = lean_string_append(v___x_1050_, v_pkg_1036_);
v___x_1052_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_1051_);
v___x_1053_ = lean_string_append(v___x_1051_, v___x_1052_);
v___x_1054_ = lean_string_append(v___x_1053_, v_a_1048_);
lean_dec(v_a_1048_);
v___x_1055_ = 3;
v___x_1056_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*1, v___x_1055_);
v___x_1057_ = lean_array_get_size(v_a_1043_);
v___x_1058_ = lean_array_push(v_a_1043_, v___x_1056_);
v___x_1059_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1060_ = lean_string_append(v___x_1051_, v___x_1059_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_string_utf8_byte_size(v_a_1042_);
v___x_1063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1063_, 0, v_a_1042_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
lean_ctor_set(v___x_1063_, 2, v___x_1062_);
v___x_1064_ = l_String_Slice_trimAscii(v___x_1063_);
v___x_1065_ = l_String_Slice_toString(v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = lean_string_append(v___x_1060_, v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = 0;
v___x_1068_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*1, v___x_1067_);
v___x_1069_ = lean_array_push(v___x_1058_, v___x_1068_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 1, v___x_1069_);
lean_ctor_set(v___x_1045_, 0, v___x_1057_);
v___x_1071_ = v___x_1045_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1074_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1077_ = lean_string_append(v_owner_1035_, v___x_1076_);
v___x_1078_ = lean_string_append(v___x_1077_, v_pkg_1036_);
v___x_1079_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_1078_);
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_string_append(v___x_1080_, v_a_1075_);
lean_dec(v_a_1075_);
v___x_1082_ = 3;
v___x_1083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
v___x_1084_ = lean_array_get_size(v_a_1043_);
v___x_1085_ = lean_array_push(v_a_1043_, v___x_1083_);
v___x_1086_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1087_ = lean_string_append(v___x_1078_, v___x_1086_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_string_utf8_byte_size(v_a_1042_);
v___x_1090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1090_, 0, v_a_1042_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
lean_ctor_set(v___x_1090_, 2, v___x_1089_);
v___x_1091_ = l_String_Slice_trimAscii(v___x_1090_);
v___x_1092_ = l_String_Slice_toString(v___x_1091_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = lean_string_append(v___x_1087_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = 0;
v___x_1095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1094_);
v___x_1096_ = lean_array_push(v___x_1085_, v___x_1095_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 1, v___x_1096_);
lean_ctor_set(v___x_1045_, 0, v___x_1084_);
v___x_1098_ = v___x_1045_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_object* v_a_1100_; 
lean_dec(v_a_1042_);
v_a_1100_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1074_, 1);
if (lean_obj_tag(v_a_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; 
lean_dec_ref(v_owner_1035_);
v_a_1101_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v_a_1100_, 1);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v_a_1101_);
v___x_1103_ = v___x_1045_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1101_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_a_1043_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
else
{
lean_object* v_status_1105_; lean_object* v_message_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_status_1105_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_status_1105_);
v_message_1106_ = lean_ctor_get(v_a_1100_, 1);
lean_inc_ref(v_message_1106_);
lean_dec_ref_known(v_a_1100_, 2);
v___x_1107_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1108_ = lean_string_append(v_owner_1035_, v___x_1107_);
v___x_1109_ = lean_string_append(v___x_1108_, v_pkg_1036_);
v___x_1110_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__0));
v___x_1111_ = lean_string_append(v___x_1109_, v___x_1110_);
v___x_1112_ = l_Nat_reprFast(v_status_1105_);
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__1));
v___x_1115_ = lean_string_append(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_string_append(v___x_1115_, v_message_1106_);
lean_dec_ref(v_message_1106_);
v___x_1117_ = 3;
v___x_1118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*1, v___x_1117_);
v___x_1119_ = lean_array_get_size(v_a_1043_);
v___x_1120_ = lean_array_push(v_a_1043_, v___x_1118_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 1, v___x_1120_);
lean_ctor_set(v___x_1045_, 0, v___x_1119_);
v___x_1122_ = v___x_1045_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1141_; 
v_a_1125_ = lean_ctor_get(v___x_1041_, 0);
v_a_1126_ = lean_ctor_get(v___x_1041_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1128_ = v___x_1041_;
v_isShared_1129_ = v_isSharedCheck_1141_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_inc(v_a_1125_);
lean_dec(v___x_1041_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1141_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1130_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1131_ = lean_string_append(v_owner_1035_, v___x_1130_);
v___x_1132_ = lean_string_append(v___x_1131_, v_pkg_1036_);
v___x_1133_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
v___x_1135_ = 3;
v___x_1136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*1, v___x_1135_);
v___x_1137_ = lean_array_push(v_a_1126_, v___x_1136_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1137_);
v___x_1139_ = v___x_1128_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object* v_lakeEnv_1142_, lean_object* v_owner_1143_, lean_object* v_pkg_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1142_, v_owner_1143_, v_pkg_1144_, v_a_1145_);
lean_dec_ref(v_pkg_1144_);
return v_res_1147_;
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
