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
lean_object* l_Lake_StdVer_parseM(lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object*);
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
static lean_once_cell_t l_Lake_instInhabitedRegistryPkg_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedRegistryPkg_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedRegistryPkg_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedRegistryPkg;
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
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "data: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_JsonObject_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "property not found: status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "status: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "message: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1_value;
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
static const lean_closure_object l_Lake_RegistryVer_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "revision"};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "property not found: revision"};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__6_value;
static const lean_string_object l_Lake_RegistryVer_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "revision: "};
static const lean_object* l_Lake_RegistryVer_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_RegistryVer_fromJson_x3f___closed__7_value;
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
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)}};
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
lean_dec_ref(v_t_6_);
v___x_13_ = lean_apply_5(v_k_7_, v_data_8_, v_url_9_, v_githubUrl_x3f_10_, v_defaultBranch_x3f_11_, v_subDir_x3f_12_);
return v___x_13_;
}
else
{
lean_object* v_data_14_; lean_object* v___x_15_; 
v_data_14_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_data_14_);
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_src_61_);
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
lean_dec_ref(v___x_134_);
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
lean_dec_ref(v___x_146_);
v___x_148_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_del_object(v___x_138_);
lean_dec(v_a_136_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref(v___x_148_);
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
lean_dec_ref(v___x_148_);
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
lean_dec_ref(v_a_153_);
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
lean_dec_ref(v___x_192_);
v___x_195_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v___x_195_);
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
lean_dec_ref(v___x_195_);
v_a_130_ = v_a_199_;
goto v___jp_129_;
}
else
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v___x_195_);
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
lean_dec_ref(v_a_200_);
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
lean_dec_ref(v___x_206_);
v___x_209_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_val_157_);
lean_del_object(v___x_155_);
lean_dec(v_a_136_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref(v___x_209_);
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
lean_dec_ref(v___x_209_);
v_a_130_ = v_a_213_;
goto v___jp_129_;
}
else
{
lean_object* v_a_214_; 
v_a_214_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_209_);
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
lean_dec_ref(v___x_170_);
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
lean_dec_ref(v___x_173_);
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
lean_dec_ref(v___x_173_);
v_a_130_ = v_a_177_;
goto v___jp_129_;
}
else
{
lean_object* v_a_178_; 
v_a_178_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v___x_173_);
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
lean_dec_ref(v___x_182_);
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
lean_dec_ref(v___x_185_);
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
lean_dec_ref(v___x_185_);
v_a_130_ = v_a_189_;
goto v___jp_129_;
}
else
{
lean_object* v_a_190_; 
v_a_190_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_185_);
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
static lean_object* _init_l_Lake_instInhabitedRegistryPkg_default___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_box(0);
v___x_222_ = ((lean_object*)(l_Lake_instInhabitedRegistryPkg_default___closed__0));
v___x_223_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_224_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_ctor_set(v___x_224_, 2, v___x_222_);
lean_ctor_set(v___x_224_, 3, v___x_221_);
return v___x_224_;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg_default(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_obj_once(&l_Lake_instInhabitedRegistryPkg_default___closed__1, &l_Lake_instInhabitedRegistryPkg_default___closed__1_once, _init_l_Lake_instInhabitedRegistryPkg_default___closed__1);
return v___x_225_;
}
}
static lean_object* _init_l_Lake_instInhabitedRegistryPkg(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lake_instInhabitedRegistryPkg_default;
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(lean_object* v_as_230_, size_t v_sz_231_, size_t v_i_232_, lean_object* v_b_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_lt(v_i_232_, v_sz_231_);
if (v___x_234_ == 0)
{
return v_b_233_;
}
else
{
lean_object* v___x_235_; lean_object* v_a_236_; uint8_t v___x_237_; 
lean_dec_ref(v_b_233_);
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
lean_dec_ref(v_fst_259_);
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
lean_dec_ref(v_x_289_);
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
lean_dec_ref(v___x_329_);
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
lean_dec_ref(v___x_368_);
v_a_364_ = v_a_369_;
goto v___jp_363_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_a_370_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_368_);
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
lean_dec_ref(v___x_372_);
v___x_375_ = l_Lean_Json_getStr_x3f(v_val_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_a_370_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
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
lean_dec_ref(v___x_375_);
v_a_364_ = v_a_379_;
goto v___jp_363_;
}
else
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_a_380_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v___x_375_);
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
lean_dec_ref(v___x_382_);
v___x_385_ = l_Lean_Json_getStr_x3f(v_val_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_a_380_);
lean_dec(v_a_370_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
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
lean_dec_ref(v___x_385_);
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
lean_dec_ref(v___x_415_);
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
lean_dec_ref(v___x_417_);
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
lean_dec_ref(v___x_417_);
v_a_364_ = v_a_421_;
goto v___jp_363_;
}
else
{
lean_object* v_a_422_; 
v_a_422_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_422_);
lean_dec_ref(v___x_417_);
if (lean_obj_tag(v_a_422_) == 0)
{
goto v___jp_412_;
}
else
{
lean_object* v_val_423_; 
v_val_423_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref(v_a_422_);
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
lean_dec_ref(v___x_398_);
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
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg(lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(1u);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg___boxed(lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_430_);
lean_dec_ref(v_x_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx(lean_object* v_00_u03b1_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___boxed(lean_object* v_00_u03b1_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lake_ReservoirResp_ctorIdx(v_00_u03b1_435_, v_x_436_);
lean_dec_ref(v_x_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___redArg(lean_object* v_t_438_, lean_object* v_k_439_){
_start:
{
if (lean_obj_tag(v_t_438_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; 
v_a_440_ = lean_ctor_get(v_t_438_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v_t_438_);
v___x_441_ = lean_apply_1(v_k_439_, v_a_440_);
return v___x_441_;
}
else
{
lean_object* v_status_442_; lean_object* v_message_443_; lean_object* v___x_444_; 
v_status_442_ = lean_ctor_get(v_t_438_, 0);
lean_inc(v_status_442_);
v_message_443_ = lean_ctor_get(v_t_438_, 1);
lean_inc_ref(v_message_443_);
lean_dec_ref(v_t_438_);
v___x_444_ = lean_apply_2(v_k_439_, v_status_442_, v_message_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim(lean_object* v_00_u03b1_445_, lean_object* v_motive_446_, lean_object* v_ctorIdx_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_k_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_448_, v_k_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___boxed(lean_object* v_00_u03b1_452_, lean_object* v_motive_453_, lean_object* v_ctorIdx_454_, lean_object* v_t_455_, lean_object* v_h_456_, lean_object* v_k_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lake_ReservoirResp_ctorElim(v_00_u03b1_452_, v_motive_453_, v_ctorIdx_454_, v_t_455_, v_h_456_, v_k_457_);
lean_dec(v_ctorIdx_454_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim___redArg(lean_object* v_t_459_, lean_object* v_data_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_459_, v_data_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim(lean_object* v_00_u03b1_462_, lean_object* v_motive_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_data_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_464_, v_data_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim___redArg(lean_object* v_t_468_, lean_object* v_error_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_468_, v_error_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim(lean_object* v_00_u03b1_471_, lean_object* v_motive_472_, lean_object* v_t_473_, lean_object* v_h_474_, lean_object* v_error_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_473_, v_error_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object* v_inst_493_, lean_object* v_val_494_){
_start:
{
lean_object* v_a_496_; lean_object* v___x_540_; 
lean_inc(v_val_494_);
v___x_540_ = l_Lean_Json_getObj_x3f(v_val_494_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_val_494_);
lean_dec_ref(v_inst_493_);
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___f_550_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_549_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_540_);
v___f_550_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0));
v___x_575_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3));
v___x_576_ = l_Lake_JsonObject_getJson_x3f(v_a_549_, v___x_575_);
if (lean_obj_tag(v___x_576_) == 0)
{
goto v___jp_551_;
}
else
{
lean_object* v_val_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref(v___x_576_);
v___x_578_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4));
v___x_579_ = l_Option_fromJson_x3f___redArg(v___x_578_, v_val_577_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_549_);
lean_dec(v_val_494_);
lean_dec_ref(v_inst_493_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5));
v___x_585_ = lean_string_append(v___x_584_, v_a_580_);
lean_dec(v_a_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_585_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_549_);
lean_dec(v_val_494_);
lean_dec_ref(v_inst_493_);
v_a_590_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_579_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; 
v_a_598_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_579_);
if (lean_obj_tag(v_a_598_) == 1)
{
lean_object* v_val_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_a_549_);
lean_dec(v_val_494_);
lean_dec_ref(v_inst_493_);
v_val_599_ = lean_ctor_get(v_a_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref(v_a_598_);
v___x_600_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6));
v___x_601_ = l_Lake_JsonObject_getJson_x3f(v_val_599_, v___x_600_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_602_; 
lean_dec(v_val_599_);
v___x_602_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8));
return v___x_602_;
}
else
{
lean_object* v_val_603_; lean_object* v___x_604_; 
v_val_603_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_val_603_);
lean_dec_ref(v___x_601_);
v___x_604_ = l_Lean_Json_getNat_x3f(v_val_603_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
lean_dec(v_val_599_);
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_614_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_609_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9));
v___x_610_ = lean_string_append(v___x_609_, v_a_605_);
lean_dec(v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
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
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v_val_599_);
v_a_615_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_604_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_604_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set_tag(v___x_617_, 0);
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_a_623_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_604_);
v___x_624_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10));
v___x_625_ = l_Lake_JsonObject_getJson_x3f(v_val_599_, v___x_624_);
lean_dec(v_val_599_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v___x_626_; 
lean_dec(v_a_623_);
v___x_626_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12));
return v___x_626_;
}
else
{
lean_object* v_val_627_; lean_object* v___x_628_; 
v_val_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v___x_625_);
v___x_628_ = l_Lean_Json_getStr_x3f(v_val_627_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_623_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13));
v___x_634_ = lean_string_append(v___x_633_, v_a_629_);
lean_dec(v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_a_623_);
v_a_639_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_628_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_628_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 0);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
v_a_647_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_655_ == 0)
{
v___x_649_ = v___x_628_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_628_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_a_623_);
lean_ctor_set(v___x_651_, 1, v_a_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
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
lean_dec(v_a_598_);
goto v___jp_551_;
}
}
}
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1));
v___x_553_ = l_Lake_JsonObject_getJson_x3f(v_a_549_, v___x_552_);
lean_dec(v_a_549_);
if (lean_obj_tag(v___x_553_) == 0)
{
v_a_496_ = v___x_553_;
goto v___jp_495_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_555_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = l_Option_fromJson_x3f___redArg(v___f_550_, v_val_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_val_494_);
lean_dec_ref(v_inst_493_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_565_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_560_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2));
v___x_561_ = lean_string_append(v___x_560_, v_a_556_);
lean_dec(v_a_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_561_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
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
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_val_494_);
lean_dec_ref(v_inst_493_);
v_a_566_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_555_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_555_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 0);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; 
v_a_574_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_555_);
v_a_496_ = v_a_574_;
goto v___jp_495_;
}
}
}
}
}
v___jp_495_:
{
if (lean_obj_tag(v_a_496_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_val_494_);
v_val_497_ = lean_ctor_get(v_a_496_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_521_ == 0)
{
v___x_499_ = v_a_496_;
v_isShared_500_ = v_isSharedCheck_521_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v_a_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_521_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_1(v_inst_493_, v_val_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_499_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_520_; 
v_a_510_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_520_ == 0)
{
v___x_512_ = v___x_501_;
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_501_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 0);
lean_ctor_set(v___x_499_, 0, v_a_510_);
v___x_515_ = v___x_499_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
else
{
lean_object* v___x_522_; 
lean_dec(v_a_496_);
v___x_522_ = lean_apply_1(v_inst_493_, v_val_494_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_a_531_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_539_ == 0)
{
v___x_533_ = v___x_522_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_522_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object* v_00_u03b1_656_, lean_object* v_inst_657_, lean_object* v_val_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lake_ReservoirResp_fromJson_x3f___redArg(v_inst_657_, v_val_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object* v_inst_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_661_, 0, lean_box(0));
lean_closure_set(v___x_661_, 1, v_inst_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object* v_00_u03b1_662_, lean_object* v_inst_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_664_, 0, lean_box(0));
lean_closure_set(v___x_664_, 1, v_inst_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object* v_lakeEnv_667_, lean_object* v_owner_668_, lean_object* v_pkg_669_){
_start:
{
lean_object* v_reservoirApiUrl_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_reservoirApiUrl_670_ = lean_ctor_get(v_lakeEnv_667_, 3);
lean_inc_ref(v_reservoirApiUrl_670_);
lean_dec_ref(v_lakeEnv_667_);
v___x_671_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_672_ = lean_string_append(v_reservoirApiUrl_670_, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_674_ = l_Lake_uriEncode(v_owner_668_, v___x_673_);
v___x_675_ = lean_string_append(v___x_672_, v___x_674_);
lean_dec_ref(v___x_674_);
v___x_676_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_677_ = lean_string_append(v___x_675_, v___x_676_);
v___x_678_ = l_Lake_uriEncode(v_pkg_669_, v___x_673_);
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
lean_dec_ref(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0));
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Json_getObj_x3f(v_x_682_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_a_693_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v___x_684_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_684_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_a_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v___x_705_; 
v___x_705_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0));
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_x_704_);
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(lean_object* v_val_712_){
_start:
{
lean_object* v_a_714_; lean_object* v___x_758_; 
lean_inc(v_val_712_);
v___x_758_ = l_Lean_Json_getObj_x3f(v_val_712_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_val_712_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_767_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_758_);
v___x_774_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3));
v___x_775_ = l_Lake_JsonObject_getJson_x3f(v_a_767_, v___x_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
goto v___jp_768_;
}
else
{
lean_object* v_val_776_; lean_object* v___x_777_; 
v_val_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_val_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_767_);
lean_dec(v_val_712_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5));
v___x_783_ = lean_string_append(v___x_782_, v_a_778_);
lean_dec(v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_767_);
lean_dec(v_val_712_);
v_a_788_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_777_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_777_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 0);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_a_796_; 
v_a_796_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_777_);
if (lean_obj_tag(v_a_796_) == 1)
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v_a_767_);
lean_dec(v_val_712_);
v_val_797_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_797_);
lean_dec_ref(v_a_796_);
v___x_798_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6));
v___x_799_ = l_Lake_JsonObject_getJson_x3f(v_val_797_, v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; 
lean_dec(v_val_797_);
v___x_800_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0));
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_802_; 
v_val_801_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_val_801_);
lean_dec_ref(v___x_799_);
v___x_802_ = l_Lean_Json_getNat_x3f(v_val_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_val_797_);
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9));
v___x_808_ = lean_string_append(v___x_807_, v_a_803_);
lean_dec(v_a_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_val_797_);
v_a_813_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_802_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_802_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 0);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_a_821_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_802_);
v___x_822_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10));
v___x_823_ = l_Lake_JsonObject_getJson_x3f(v_val_797_, v___x_822_);
lean_dec(v_val_797_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; 
lean_dec(v_a_821_);
v___x_824_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1));
return v___x_824_;
}
else
{
lean_object* v_val_825_; lean_object* v___x_826_; 
v_val_825_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v___x_823_);
v___x_826_ = l_Lean_Json_getStr_x3f(v_val_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_a_821_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13));
v___x_832_ = lean_string_append(v___x_831_, v_a_827_);
lean_dec(v_a_827_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_a_821_);
v_a_837_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_826_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_a_845_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_853_ == 0)
{
v___x_847_ = v___x_826_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_826_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v_a_821_);
lean_ctor_set(v___x_849_, 1, v_a_845_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
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
lean_dec(v_a_796_);
goto v___jp_768_;
}
}
}
}
v___jp_768_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1));
v___x_770_ = l_Lake_JsonObject_getJson_x3f(v_a_767_, v___x_769_);
lean_dec(v_a_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
v_a_714_ = v___x_770_;
goto v___jp_713_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_772_; lean_object* v_a_773_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_771_);
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v_a_714_ = v_a_773_;
goto v___jp_713_;
}
}
}
v___jp_713_:
{
if (lean_obj_tag(v_a_714_) == 1)
{
lean_object* v_val_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_val_712_);
v_val_715_ = lean_ctor_get(v_a_714_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_739_ == 0)
{
v___x_717_ = v_a_714_;
v_isShared_718_ = v_isSharedCheck_739_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_val_715_);
lean_dec(v_a_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_739_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_715_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_del_object(v___x_717_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_738_; 
v_a_728_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_738_ == 0)
{
v___x_730_ = v___x_719_;
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_719_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 0);
lean_ctor_set(v___x_717_, 0, v_a_728_);
v___x_733_ = v___x_717_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_733_);
v___x_735_ = v___x_730_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
else
{
lean_object* v___x_740_; 
lean_dec(v_a_714_);
v___x_740_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_712_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_757_; 
v_a_749_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_757_ == 0)
{
v___x_751_ = v___x_740_;
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_740_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v_a_749_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object* v_lakeEnv_859_, lean_object* v_owner_860_, lean_object* v_pkg_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_url_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_inc_ref(v_pkg_861_);
lean_inc_ref(v_owner_860_);
v_url_864_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_859_, v_owner_860_, v_pkg_861_);
v___x_865_ = l_Lake_Reservoir_lakeHeaders;
v___x_866_ = l_Lake_getUrl(v_url_864_, v___x_865_, v_a_862_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_958_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_a_868_ = lean_ctor_get(v___x_866_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_958_ == 0)
{
v___x_870_ = v___x_866_;
v_isShared_871_ = v_isSharedCheck_958_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_958_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; 
lean_inc(v_a_867_);
v___x_872_ = l_Lean_Json_parse(v_a_867_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
v___x_874_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_875_ = lean_string_append(v_owner_860_, v___x_874_);
v___x_876_ = lean_string_append(v___x_875_, v_pkg_861_);
lean_dec_ref(v_pkg_861_);
v___x_877_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_876_);
v___x_878_ = lean_string_append(v___x_876_, v___x_877_);
v___x_879_ = lean_string_append(v___x_878_, v_a_873_);
lean_dec(v_a_873_);
v___x_880_ = 3;
v___x_881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_880_);
v___x_882_ = lean_array_get_size(v_a_868_);
v___x_883_ = lean_array_push(v_a_868_, v___x_881_);
v___x_884_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_885_ = lean_string_append(v___x_876_, v___x_884_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_string_utf8_byte_size(v_a_867_);
v___x_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_888_, 0, v_a_867_);
lean_ctor_set(v___x_888_, 1, v___x_886_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
v___x_889_ = l_String_Slice_trimAscii(v___x_888_);
lean_dec_ref(v___x_888_);
v___x_890_ = l_String_Slice_toString(v___x_889_);
lean_dec_ref(v___x_889_);
v___x_891_ = lean_string_append(v___x_885_, v___x_890_);
lean_dec_ref(v___x_890_);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = lean_array_push(v___x_883_, v___x_893_);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
lean_ctor_set(v___x_870_, 1, v___x_894_);
lean_ctor_set(v___x_870_, 0, v___x_882_);
v___x_896_ = v___x_870_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_872_);
v___x_899_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
v___x_901_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_902_ = lean_string_append(v_owner_860_, v___x_901_);
v___x_903_ = lean_string_append(v___x_902_, v_pkg_861_);
lean_dec_ref(v_pkg_861_);
v___x_904_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_903_);
v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
v___x_906_ = lean_string_append(v___x_905_, v_a_900_);
lean_dec(v_a_900_);
v___x_907_ = 3;
v___x_908_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1, v___x_907_);
v___x_909_ = lean_array_get_size(v_a_868_);
v___x_910_ = lean_array_push(v_a_868_, v___x_908_);
v___x_911_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_912_ = lean_string_append(v___x_903_, v___x_911_);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_string_utf8_byte_size(v_a_867_);
v___x_915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_915_, 0, v_a_867_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
v___x_916_ = l_String_Slice_trimAscii(v___x_915_);
lean_dec_ref(v___x_915_);
v___x_917_ = l_String_Slice_toString(v___x_916_);
lean_dec_ref(v___x_916_);
v___x_918_ = lean_string_append(v___x_912_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = 0;
v___x_920_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_919_);
v___x_921_ = lean_array_push(v___x_910_, v___x_920_);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
lean_ctor_set(v___x_870_, 1, v___x_921_);
lean_ctor_set(v___x_870_, 0, v___x_909_);
v___x_923_ = v___x_870_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_object* v_a_925_; 
lean_dec(v_a_867_);
v_a_925_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_899_);
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_pkg_861_);
lean_dec_ref(v_owner_860_);
v_a_926_ = lean_ctor_get(v_a_925_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_936_ == 0)
{
v___x_928_ = v_a_925_;
v_isShared_929_ = v_isSharedCheck_936_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v_a_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_936_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 1);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_935_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_931_);
v___x_933_ = v___x_870_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_a_868_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_status_937_; lean_object* v_message_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_status_937_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_status_937_);
v_message_938_ = lean_ctor_get(v_a_925_, 1);
lean_inc_ref(v_message_938_);
lean_dec_ref(v_a_925_);
v___x_939_ = lean_unsigned_to_nat(404u);
v___x_940_ = lean_nat_dec_eq(v_status_937_, v___x_939_);
lean_dec(v_status_937_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_941_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_942_ = lean_string_append(v_owner_860_, v___x_941_);
v___x_943_ = lean_string_append(v___x_942_, v_pkg_861_);
lean_dec_ref(v_pkg_861_);
v___x_944_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__3));
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
v___x_946_ = lean_string_append(v___x_945_, v_message_938_);
lean_dec_ref(v_message_938_);
v___x_947_ = 3;
v___x_948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*1, v___x_947_);
v___x_949_ = lean_array_get_size(v_a_868_);
v___x_950_ = lean_array_push(v_a_868_, v___x_948_);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
lean_ctor_set(v___x_870_, 1, v___x_950_);
lean_ctor_set(v___x_870_, 0, v___x_949_);
v___x_952_ = v___x_870_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v___x_954_; lean_object* v___x_956_; 
lean_dec_ref(v_message_938_);
lean_dec_ref(v_pkg_861_);
lean_dec_ref(v_owner_860_);
v___x_954_ = lean_box(0);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_954_);
v___x_956_ = v___x_870_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_a_868_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_975_; 
v_a_959_ = lean_ctor_get(v___x_866_, 0);
v_a_960_ = lean_ctor_get(v___x_866_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_975_ == 0)
{
v___x_962_ = v___x_866_;
v_isShared_963_ = v_isSharedCheck_975_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_inc(v_a_959_);
lean_dec(v___x_866_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_975_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_964_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_965_ = lean_string_append(v_owner_860_, v___x_964_);
v___x_966_ = lean_string_append(v___x_965_, v_pkg_861_);
lean_dec_ref(v_pkg_861_);
v___x_967_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_968_ = lean_string_append(v___x_966_, v___x_967_);
v___x_969_ = 3;
v___x_970_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_969_);
v___x_971_ = lean_array_push(v_a_960_, v___x_970_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_971_);
v___x_973_ = v___x_962_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkg_x3f___boxed(lean_object* v_lakeEnv_976_, lean_object* v_owner_977_, lean_object* v_pkg_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_976_, v_owner_977_, v_pkg_978_, v_a_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_RegistryVer_fromJson_x3f(lean_object* v_val_990_){
_start:
{
lean_object* v_a_992_; lean_object* v_a_997_; lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Json_getObj_x3f(v_val_990_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
v_a_992_ = v_a_1001_;
goto v___jp_991_;
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1000_);
v___x_1003_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__2));
v___x_1004_ = l_Lake_JsonObject_getJson_x3f(v_a_1002_, v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; 
lean_dec(v_a_1002_);
v___x_1005_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__3));
v_a_992_ = v___x_1005_;
goto v___jp_991_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; 
v_val_1006_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v___x_1004_);
v___x_1007_ = l_Lean_Json_getStr_x3f(v_val_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
lean_dec(v_a_1002_);
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
v_a_997_ = v_a_1008_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1009_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1007_);
v___x_1010_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__4));
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_string_utf8_byte_size(v_a_1009_);
v___x_1013_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_a_1009_, v___x_1010_, v___x_1011_, v___x_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; 
lean_dec(v_a_1002_);
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref(v___x_1013_);
v_a_997_ = v_a_1014_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1013_);
v___x_1016_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__5));
v___x_1017_ = l_Lake_JsonObject_getJson_x3f(v_a_1002_, v___x_1016_);
lean_dec(v_a_1002_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_a_1015_);
v___x_1018_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__6));
v_a_992_ = v___x_1018_;
goto v___jp_991_;
}
else
{
lean_object* v_val_1019_; lean_object* v___x_1020_; 
v_val_1019_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_val_1019_);
lean_dec_ref(v___x_1017_);
v___x_1020_ = l_Lean_Json_getStr_x3f(v_val_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v_a_1015_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__7));
v___x_1023_ = lean_string_append(v___x_1022_, v_a_1021_);
lean_dec(v_a_1021_);
v_a_992_ = v___x_1023_;
goto v___jp_991_;
}
else
{
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1024_; 
lean_dec(v_a_1015_);
v_a_1024_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1020_);
v_a_992_ = v_a_1024_;
goto v___jp_991_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
v_a_1025_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1027_ = v___x_1020_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1020_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_a_1015_);
lean_ctor_set(v___x_1029_, 1, v_a_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
}
}
}
v___jp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__0));
v___x_994_ = lean_string_append(v___x_993_, v_a_992_);
lean_dec_ref(v_a_992_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lake_RegistryVer_fromJson_x3f___closed__1));
v___x_999_ = lean_string_append(v___x_998_, v_a_997_);
lean_dec_ref(v_a_997_);
v_a_992_ = v___x_999_;
goto v___jp_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_pkgVersionsApiUrl(lean_object* v_lakeEnv_1037_, lean_object* v_owner_1038_, lean_object* v_pkg_1039_){
_start:
{
lean_object* v_reservoirApiUrl_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_reservoirApiUrl_1040_ = lean_ctor_get(v_lakeEnv_1037_, 3);
lean_inc_ref(v_reservoirApiUrl_1040_);
lean_dec_ref(v_lakeEnv_1037_);
v___x_1041_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__0));
v___x_1042_ = lean_string_append(v_reservoirApiUrl_1040_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lake_instInhabitedRegistrySrc_default___closed__0));
v___x_1044_ = l_Lake_uriEncode(v_owner_1038_, v___x_1043_);
v___x_1045_ = lean_string_append(v___x_1042_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = l_Lake_uriEncode(v_pkg_1039_, v___x_1043_);
v___x_1049_ = lean_string_append(v___x_1047_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(size_t v_sz_1052_, size_t v_i_1053_, lean_object* v_bs_1054_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_lt(v_i_1053_, v_sz_1052_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_bs_1054_);
return v___x_1056_;
}
else
{
lean_object* v_v_1057_; lean_object* v___x_1058_; 
v_v_1057_ = lean_array_uget_borrowed(v_bs_1054_, v_i_1053_);
lean_inc(v_v_1057_);
v___x_1058_ = l_Lake_RegistryVer_fromJson_x3f(v_v_1057_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_bs_1054_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v_bs_x27_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_a_1067_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1058_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v_bs_x27_1069_ = lean_array_uset(v_bs_1054_, v_i_1053_, v___x_1068_);
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1053_, v___x_1070_);
v___x_1072_ = lean_array_uset(v_bs_x27_1069_, v_i_1053_, v_a_1067_);
v_i_1053_ = v___x_1071_;
v_bs_1054_ = v___x_1072_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_bs_1076_){
_start:
{
size_t v_sz_boxed_1077_; size_t v_i_boxed_1078_; lean_object* v_res_1079_; 
v_sz_boxed_1077_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1078_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_1077_, v_i_boxed_1078_, v_bs_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 4)
{
lean_object* v_elems_1081_; size_t v_sz_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_elems_1081_ = lean_ctor_get(v_x_1080_, 0);
lean_inc_ref(v_elems_1081_);
lean_dec_ref(v_x_1080_);
v_sz_1082_ = lean_array_size(v_elems_1081_);
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_1082_, v___x_1083_, v_elems_1081_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1085_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0));
v___x_1086_ = lean_unsigned_to_nat(80u);
v___x_1087_ = l_Lean_Json_pretty(v_x_1080_, v___x_1086_);
v___x_1088_ = lean_string_append(v___x_1085_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1));
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(lean_object* v_val_1096_){
_start:
{
lean_object* v_a_1098_; lean_object* v___x_1142_; 
lean_inc(v_val_1096_);
v___x_1142_ = l_Lean_Json_getObj_x3f(v_val_1096_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_val_1096_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1151_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1142_);
v___x_1158_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3));
v___x_1159_ = l_Lake_JsonObject_getJson_x3f(v_a_1151_, v___x_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
goto v___jp_1152_;
}
else
{
lean_object* v_val_1160_; lean_object* v___x_1161_; 
v_val_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_val_1160_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_a_1151_);
lean_dec(v_val_1096_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5));
v___x_1167_ = lean_string_append(v___x_1166_, v_a_1162_);
lean_dec(v_a_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1151_);
lean_dec(v_val_1096_);
v_a_1172_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1161_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1161_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 0);
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; 
v_a_1180_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1161_);
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_a_1151_);
lean_dec(v_val_1096_);
v_val_1181_ = lean_ctor_get(v_a_1180_, 0);
lean_inc(v_val_1181_);
lean_dec_ref(v_a_1180_);
v___x_1182_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6));
v___x_1183_ = l_Lake_JsonObject_getJson_x3f(v_val_1181_, v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
lean_dec(v_val_1181_);
v___x_1184_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0));
return v___x_1184_;
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1186_; 
v_val_1185_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1185_);
lean_dec_ref(v___x_1183_);
v___x_1186_ = l_Lean_Json_getNat_x3f(v_val_1185_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_val_1181_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9));
v___x_1192_ = lean_string_append(v___x_1191_, v_a_1187_);
lean_dec(v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_val_1181_);
v_a_1197_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1186_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1186_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set_tag(v___x_1199_, 0);
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_a_1205_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1205_);
lean_dec_ref(v___x_1186_);
v___x_1206_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10));
v___x_1207_ = l_Lake_JsonObject_getJson_x3f(v_val_1181_, v___x_1206_);
lean_dec(v_val_1181_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1208_; 
lean_dec(v_a_1205_);
v___x_1208_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1));
return v___x_1208_;
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1210_; 
v_val_1209_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_val_1209_);
lean_dec_ref(v___x_1207_);
v___x_1210_ = l_Lean_Json_getStr_x3f(v_val_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_a_1205_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1215_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13));
v___x_1216_ = lean_string_append(v___x_1215_, v_a_1211_);
lean_dec(v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1218_ = v___x_1213_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_a_1205_);
v_a_1221_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1210_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1210_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 0);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_a_1229_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v___x_1210_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1210_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_a_1205_);
lean_ctor_set(v___x_1233_, 1, v_a_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
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
lean_dec(v_a_1180_);
goto v___jp_1152_;
}
}
}
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1));
v___x_1154_ = l_Lake_JsonObject_getJson_x3f(v_a_1151_, v___x_1153_);
lean_dec(v_a_1151_);
if (lean_obj_tag(v___x_1154_) == 0)
{
v_a_1098_ = v___x_1154_;
goto v___jp_1097_;
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1156_; lean_object* v_a_1157_; 
v_val_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_val_1155_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_1155_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v_a_1098_ = v_a_1157_;
goto v___jp_1097_;
}
}
}
v___jp_1097_:
{
if (lean_obj_tag(v_a_1098_) == 1)
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_val_1096_);
v_val_1099_ = lean_ctor_get(v_a_1098_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_a_1098_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1101_ = v_a_1098_;
v_isShared_1102_ = v_isSharedCheck_1123_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v_a_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1123_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_1099_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_del_object(v___x_1101_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1122_; 
v_a_1112_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1114_ = v___x_1103_;
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1103_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 0, v_a_1112_);
v___x_1117_ = v___x_1101_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1117_);
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_a_1098_);
v___x_1124_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_1096_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1133_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1124_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1124_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions(lean_object* v_lakeEnv_1240_, lean_object* v_owner_1241_, lean_object* v_pkg_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_url_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_inc_ref(v_pkg_1242_);
lean_inc_ref(v_owner_1241_);
v_url_1245_ = l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_1240_, v_owner_1241_, v_pkg_1242_);
v___x_1246_ = l_Lake_Reservoir_lakeHeaders;
v___x_1247_ = l_Lake_getUrl(v_url_1245_, v___x_1246_, v_a_1243_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1330_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_a_1249_ = lean_ctor_get(v___x_1247_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1251_ = v___x_1247_;
v_isShared_1252_ = v_isSharedCheck_1330_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1330_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; 
lean_inc(v_a_1248_);
v___x_1253_ = l_Lean_Json_parse(v_a_1248_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1256_ = lean_string_append(v_owner_1241_, v___x_1255_);
v___x_1257_ = lean_string_append(v___x_1256_, v_pkg_1242_);
lean_dec_ref(v_pkg_1242_);
v___x_1258_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__0));
lean_inc_ref(v___x_1257_);
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
v___x_1260_ = lean_string_append(v___x_1259_, v_a_1254_);
lean_dec(v_a_1254_);
v___x_1261_ = 3;
v___x_1262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*1, v___x_1261_);
v___x_1263_ = lean_array_get_size(v_a_1249_);
v___x_1264_ = lean_array_push(v_a_1249_, v___x_1262_);
v___x_1265_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1266_ = lean_string_append(v___x_1257_, v___x_1265_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_string_utf8_byte_size(v_a_1248_);
v___x_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1248_);
lean_ctor_set(v___x_1269_, 1, v___x_1267_);
lean_ctor_set(v___x_1269_, 2, v___x_1268_);
v___x_1270_ = l_String_Slice_trimAscii(v___x_1269_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = l_String_Slice_toString(v___x_1270_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_string_append(v___x_1266_, v___x_1271_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = 0;
v___x_1274_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*1, v___x_1273_);
v___x_1275_ = lean_array_push(v___x_1264_, v___x_1274_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 1);
lean_ctor_set(v___x_1251_, 1, v___x_1275_);
lean_ctor_set(v___x_1251_, 0, v___x_1263_);
v___x_1277_ = v___x_1251_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1253_);
v___x_1280_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1283_ = lean_string_append(v_owner_1241_, v___x_1282_);
v___x_1284_ = lean_string_append(v___x_1283_, v_pkg_1242_);
lean_dec_ref(v_pkg_1242_);
v___x_1285_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__2));
lean_inc_ref(v___x_1284_);
v___x_1286_ = lean_string_append(v___x_1284_, v___x_1285_);
v___x_1287_ = lean_string_append(v___x_1286_, v_a_1281_);
lean_dec(v_a_1281_);
v___x_1288_ = 3;
v___x_1289_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*1, v___x_1288_);
v___x_1290_ = lean_array_get_size(v_a_1249_);
v___x_1291_ = lean_array_push(v_a_1249_, v___x_1289_);
v___x_1292_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__1));
v___x_1293_ = lean_string_append(v___x_1284_, v___x_1292_);
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = lean_string_utf8_byte_size(v_a_1248_);
v___x_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1296_, 0, v_a_1248_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
lean_ctor_set(v___x_1296_, 2, v___x_1295_);
v___x_1297_ = l_String_Slice_trimAscii(v___x_1296_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = l_String_Slice_toString(v___x_1297_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = lean_string_append(v___x_1293_, v___x_1298_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = 0;
v___x_1301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*1, v___x_1300_);
v___x_1302_ = lean_array_push(v___x_1291_, v___x_1301_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 1);
lean_ctor_set(v___x_1251_, 1, v___x_1302_);
lean_ctor_set(v___x_1251_, 0, v___x_1290_);
v___x_1304_ = v___x_1251_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v_a_1306_; 
lean_dec(v_a_1248_);
v_a_1306_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1280_);
if (lean_obj_tag(v_a_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; 
lean_dec_ref(v_pkg_1242_);
lean_dec_ref(v_owner_1241_);
v_a_1307_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v_a_1306_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_a_1307_);
v___x_1309_ = v___x_1251_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_a_1249_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
lean_object* v_status_1311_; lean_object* v_message_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v_status_1311_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_status_1311_);
v_message_1312_ = lean_ctor_get(v_a_1306_, 1);
lean_inc_ref(v_message_1312_);
lean_dec_ref(v_a_1306_);
v___x_1313_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1314_ = lean_string_append(v_owner_1241_, v___x_1313_);
v___x_1315_ = lean_string_append(v___x_1314_, v_pkg_1242_);
lean_dec_ref(v_pkg_1242_);
v___x_1316_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__0));
v___x_1317_ = lean_string_append(v___x_1315_, v___x_1316_);
v___x_1318_ = l_Nat_reprFast(v_status_1311_);
v___x_1319_ = lean_string_append(v___x_1317_, v___x_1318_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lake_Reservoir_fetchPkgVersions___closed__1));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_string_append(v___x_1321_, v_message_1312_);
lean_dec_ref(v_message_1312_);
v___x_1323_ = 3;
v___x_1324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*1, v___x_1323_);
v___x_1325_ = lean_array_get_size(v_a_1249_);
v___x_1326_ = lean_array_push(v_a_1249_, v___x_1324_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 1);
lean_ctor_set(v___x_1251_, 1, v___x_1326_);
lean_ctor_set(v___x_1251_, 0, v___x_1325_);
v___x_1328_ = v___x_1251_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1347_; 
v_a_1331_ = lean_ctor_get(v___x_1247_, 0);
v_a_1332_ = lean_ctor_get(v___x_1247_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1334_ = v___x_1247_;
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_inc(v_a_1331_);
lean_dec(v___x_1247_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1336_ = ((lean_object*)(l_Lake_Reservoir_pkgApiUrl___closed__1));
v___x_1337_ = lean_string_append(v_owner_1241_, v___x_1336_);
v___x_1338_ = lean_string_append(v___x_1337_, v_pkg_1242_);
lean_dec_ref(v_pkg_1242_);
v___x_1339_ = ((lean_object*)(l_Lake_Reservoir_fetchPkg_x3f___closed__4));
v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
v___x_1341_ = 3;
v___x_1342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*1, v___x_1341_);
v___x_1343_ = lean_array_push(v_a_1332_, v___x_1342_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1343_);
v___x_1345_ = v___x_1334_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1331_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Reservoir_fetchPkgVersions___boxed(lean_object* v_lakeEnv_1348_, lean_object* v_owner_1349_, lean_object* v_pkg_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_1348_, v_owner_1349_, v_pkg_1350_, v_a_1351_);
return v_res_1353_;
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
l_Lake_instInhabitedRegistryPkg_default = _init_l_Lake_instInhabitedRegistryPkg_default();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg_default);
l_Lake_instInhabitedRegistryPkg = _init_l_Lake_instInhabitedRegistryPkg();
lean_mark_persistent(l_Lake_instInhabitedRegistryPkg);
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
