// Lean compiler output
// Module: Lake.Config.Cache
// Imports: import Init.Control.Do public import Lake.Util.Log public import Lake.Util.Version public import Lake.Config.Artifact import Lake.Config.InstallPath import Lake.Build.Actions import Lake.Util.Url import Lake.Util.Proc import Lake.Util.Reservoir import Lake.Util.JsonObject import Lake.Util.IO import Init.System.Platform import Init.Data.String.Lemmas
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_Hash_hex(uint64_t);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lake_Date_fromJson_x3f(lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_get_line(lean_object*);
extern lean_object* l_System_instInhabitedFilePath_default;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lake_normalizeToolchain(lean_object*);
static const lean_ctor_object l_Lake_CacheMap_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2026) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lake_CacheMap_schemaVersion___closed__0 = (const lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheMap_schemaVersion = (const lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": invalid header on line 1: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ": unknown schema version '"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "'; may not parse correctly"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": expected schema version on line 1"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected array of size > 0"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected array of size > 1"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": invalid JSON on line "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheMap_parse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_parse___closed__0;
static const lean_array_object l_Lake_CacheMap_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheMap_parse___closed__1 = (const lean_object*)&l_Lake_CacheMap_parse___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheMap_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": failed to open file: "};
static const lean_object* l_Lake_CacheMap_load___closed__0 = (const lean_object*)&l_Lake_CacheMap_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__0;
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__1;
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__2;
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unsupported output; "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unsupported output: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_CacheMap_collectOutputDescrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheMap_collectOutputDescrs___closed__0 = (const lean_object*)&l_Lake_CacheMap_collectOutputDescrs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheServiceName_reservoir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_CacheServiceName_reservoir___closed__0 = (const lean_object*)&l_Lake_CacheServiceName_reservoir___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceName_reservoir = (const lean_object*)&l_Lake_CacheServiceName_reservoir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheServiceName_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceName_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceName_instToString___closed__0 = (const lean_object*)&l_Lake_CacheServiceName_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceName_instToString = (const lean_object*)&l_Lake_CacheServiceName_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object*);
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheServiceScope_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceScope_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceScope_instToString___closed__0 = (const lean_object*)&l_Lake_CacheServiceScope_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceScope_instToString = (const lean_object*)&l_Lake_CacheServiceScope_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0_value;
static const lean_string_object l_Lake_CacheOutput_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2026-02-25"};
static const lean_object* l_Lake_CacheOutput_schemaVersion___closed__0 = (const lean_object*)&l_Lake_CacheOutput_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheOutput_schemaVersion = (const lean_object*)&l_Lake_CacheOutput_schemaVersion___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedCacheOutput_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedCacheOutput_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedCacheOutput_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheOutput_default = (const lean_object*)&l_Lake_instInhabitedCacheOutput_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheOutput = (const lean_object*)&l_Lake_instInhabitedCacheOutput_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object*);
static const lean_string_object l_Lake_CacheOutput_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__0 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__0_value;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__1 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__1_value;
static const lean_ctor_object l_Lake_CacheOutput_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_CacheOutput_schemaVersion___closed__0_value)}};
static const lean_object* l_Lake_CacheOutput_toJson___closed__2 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__2_value;
static lean_once_cell_t l_Lake_CacheOutput_toJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheOutput_toJson___closed__3;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "service"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__4 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__4_value;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__5 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__5_value;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repo"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__6 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object*);
static const lean_closure_object l_Lake_CacheOutput_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheOutput_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheOutput_instToJson___closed__0 = (const lean_object*)&l_Lake_CacheOutput_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheOutput_instToJson = (const lean_object*)&l_Lake_CacheOutput_instToJson___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "property not found: data"};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lake_CacheOutput_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scope: "};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repo: "};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "service: "};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_CacheOutput_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheOutput_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheOutput_instFromJson___closed__0 = (const lean_object*)&l_Lake_CacheOutput_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheOutput_instFromJson = (const lean_object*)&l_Lake_CacheOutput_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache;
static const lean_string_object l_Lake_Cache_artifactDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "artifacts"};
static const lean_object* l_Lake_Cache_artifactDir___closed__0 = (const lean_object*)&l_Lake_Cache_artifactDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object*);
static const lean_string_object l_Lake_Cache_artifactPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Cache_artifactPath___closed__0 = (const lean_object*)&l_Lake_Cache_artifactPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_getArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "artifact not found in cache: "};
static const lean_object* l_Lake_Cache_getArtifact___closed__0 = (const lean_object*)&l_Lake_Cache_getArtifact___closed__0_value;
static const lean_string_object l_Lake_Cache_getArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve artifact from cache: "};
static const lean_object* l_Lake_Cache_getArtifact___closed__1 = (const lean_object*)&l_Lake_Cache_getArtifact___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Cache_getArtifactPaths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Cache_getArtifactPaths___closed__0 = (const lean_object*)&l_Lake_Cache_getArtifactPaths___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_outputsDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "outputs"};
static const lean_object* l_Lake_Cache_outputsDir___closed__0 = (const lean_object*)&l_Lake_Cache_outputsDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object*);
static const lean_string_object l_Lake_Cache_outputsFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".json"};
static const lean_object* l_Lake_Cache_outputsFile___closed__0 = (const lean_object*)&l_Lake_Cache_outputsFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object*);
static const lean_string_object l_Lake_Cache_readOutputs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ": invalid JSON: "};
static const lean_object* l_Lake_Cache_readOutputs_x3f___closed__0 = (const lean_object*)&l_Lake_Cache_readOutputs_x3f___closed__0_value;
static const lean_string_object l_Lake_Cache_readOutputs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ": read failed: "};
static const lean_object* l_Lake_Cache_readOutputs_x3f___closed__1 = (const lean_object*)&l_Lake_Cache_readOutputs_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_revisionDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "revisions"};
static const lean_object* l_Lake_Cache_revisionDir___closed__0 = (const lean_object*)&l_Lake_Cache_revisionDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object*);
static const lean_string_object l_Lake_Cache_revisionPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".jsonl"};
static const lean_object* l_Lake_Cache_revisionPath___closed__0 = (const lean_object*)&l_Lake_Cache_revisionPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CachePlatform_none___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_CachePlatform_none___closed__0 = (const lean_object*)&l_Lake_CachePlatform_none___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CachePlatform_none = (const lean_object*)&l_Lake_CachePlatform_none___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_system;
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object*);
static const lean_string_object l_Lake_CachePlatform_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lake_CachePlatform_toString___closed__0 = (const lean_object*)&l_Lake_CachePlatform_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CachePlatform_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheToolchain_none = (const lean_object*)&l_Lake_CachePlatform_none___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheToolchain_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value;
static const lean_string_object l_Lake_downloadArtifactCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = ": downloaded artifact does not have the expected hash"};
static const lean_object* l_Lake_downloadArtifactCore___closed__0 = (const lean_object*)&l_Lake_downloadArtifactCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "curl's JSON output contained an invalid JSON response code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "; JSON received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "curl's JSON output did not contain a response code; JSON received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "failed to upload artifact, error "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "http_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "http_code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "curl produced invalid JSON output: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-w"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "%{stderr}%{json}\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--aws-sigv4"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "aws:amz:auto:s3"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--user"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-X"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-T"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Content-Type: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26;
static const lean_array_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "response_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_artifactContentType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "application/vnd.reservoir.artifact"};
static const lean_object* l_Lake_CacheService_artifactContentType___closed__0 = (const lean_object*)&l_Lake_CacheService_artifactContentType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheService_artifactContentType = (const lean_object*)&l_Lake_CacheService_artifactContentType___closed__0_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".art"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_artifactUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "/artifacts/"};
static const lean_object* l_Lake_CacheService_artifactUrl___closed__0 = (const lean_object*)&l_Lake_CacheService_artifactUrl___closed__0_value;
static const lean_string_object l_Lake_CacheService_artifactUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "/packages"};
static const lean_object* l_Lake_CacheService_artifactUrl___closed__1 = (const lean_object*)&l_Lake_CacheService_artifactUrl___closed__1_value;
static const lean_string_object l_Lake_CacheService_artifactUrl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/repositories"};
static const lean_object* l_Lake_CacheService_artifactUrl___closed__2 = (const lean_object*)&l_Lake_CacheService_artifactUrl___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_downloadArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": downloading artifact "};
static const lean_object* l_Lake_CacheService_downloadArtifact___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadArtifact___closed__0_value;
static const lean_string_object l_Lake_CacheService_downloadArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  local path: "};
static const lean_object* l_Lake_CacheService_downloadArtifact___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadArtifact___closed__1_value;
static const lean_string_object l_Lake_CacheService_downloadArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  remote URL: "};
static const lean_object* l_Lake_CacheService_downloadArtifact___closed__2 = (const lean_object*)&l_Lake_CacheService_downloadArtifact___closed__2_value;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheService_downloadArtifact___closed__3;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_CacheService_downloadArtifact___closed__4;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_CacheService_downloadArtifact___closed__5;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_CacheService_downloadArtifact___closed__6;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_downloadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": failed to download some artifacts"};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ": uploading artifact "};
static const lean_object* l_Lake_CacheService_uploadArtifact___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_mapContentType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "application/vnd.reservoir.outputs+json-lines"};
static const lean_object* l_Lake_CacheService_mapContentType___closed__0 = (const lean_object*)&l_Lake_CacheService_mapContentType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheService_mapContentType = (const lean_object*)&l_Lake_CacheService_mapContentType___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/tc/"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/pt/"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_revisionUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "&toolchain="};
static const lean_object* l_Lake_CacheService_revisionUrl___closed__0 = (const lean_object*)&l_Lake_CacheService_revisionUrl___closed__0_value;
static const lean_string_object l_Lake_CacheService_revisionUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/build-outputs\?rev="};
static const lean_object* l_Lake_CacheService_revisionUrl___closed__1 = (const lean_object*)&l_Lake_CacheService_revisionUrl___closed__1_value;
static const lean_string_object l_Lake_CacheService_revisionUrl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "&platform="};
static const lean_object* l_Lake_CacheService_revisionUrl___closed__2 = (const lean_object*)&l_Lake_CacheService_revisionUrl___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": output lookup failed"};
static const lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0_value;
static const lean_string_object l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": downloading build outputs for revision "};
static const lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1_value;
static const lean_array_object l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2 = (const lean_object*)&l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadRevisionOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = ": uploading build outputs for revision "};
static const lean_object* l_Lake_CacheService_uploadRevisionOutputs___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadRevisionOutputs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object* v_inputName_10_, lean_object* v_line_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_a_15_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_24_ = lean_string_utf8_byte_size(v_line_11_);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_nat_dec_eq(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Json_parse(v_line_11_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref(v___x_27_);
v_a_15_ = v_a_28_;
goto v___jp_14_;
}
else
{
lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_29_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v___x_27_);
v___x_30_ = l_Lake_Date_fromJson_x3f(v_a_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v___x_30_);
v_a_15_ = v_a_31_;
goto v___jp_14_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_a_32_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_32_);
lean_dec_ref(v___x_30_);
v___x_45_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_46_ = l_Lake_instOrdDate_ord(v_a_32_, v___x_45_);
if (v___x_46_ == 0)
{
goto v___jp_33_;
}
else
{
if (v___x_26_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_a_32_);
lean_dec_ref(v_inputName_10_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_a_12_);
return v___x_48_;
}
else
{
goto v___jp_33_;
}
}
v___jp_33_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_34_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1));
v___x_35_ = lean_string_append(v_inputName_10_, v___x_34_);
v___x_36_ = l_Lake_Date_toString(v_a_32_);
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
lean_dec_ref(v___x_36_);
v___x_38_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2));
v___x_39_ = lean_string_append(v___x_37_, v___x_38_);
v___x_40_ = 2;
v___x_41_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_41_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_41_, sizeof(void*)*1, v___x_40_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_array_push(v_a_12_, v___x_41_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
}
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v_line_11_);
v___x_49_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3));
v___x_50_ = lean_string_append(v_inputName_10_, v___x_49_);
v___x_51_ = 3;
v___x_52_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v___x_51_);
v___x_53_ = lean_array_get_size(v_a_12_);
v___x_54_ = lean_array_push(v_a_12_, v___x_52_);
v___x_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
v___jp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_16_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0));
v___x_17_ = lean_string_append(v_inputName_10_, v___x_16_);
v___x_18_ = lean_string_append(v___x_17_, v_a_15_);
lean_dec_ref(v_a_15_);
v___x_19_ = 2;
v___x_20_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_20_, 0, v___x_18_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*1, v___x_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_array_push(v_a_12_, v___x_20_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object* v_inputName_56_, lean_object* v_line_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_56_, v_line_57_, v_a_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(uint64_t v_a_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
else
{
lean_object* v_key_64_; lean_object* v_tail_65_; uint64_t v___x_66_; uint8_t v___x_67_; 
v_key_64_ = lean_ctor_get(v_x_62_, 0);
v_tail_65_ = lean_ctor_get(v_x_62_, 2);
v___x_66_ = lean_unbox_uint64(v_key_64_);
v___x_67_ = lean_uint64_dec_eq(v___x_66_, v_a_61_);
if (v___x_67_ == 0)
{
v_x_62_ = v_tail_65_;
goto _start;
}
else
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_69_, lean_object* v_x_70_){
_start:
{
uint64_t v_a_boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_a_boxed_71_ = lean_unbox_uint64(v_a_69_);
lean_dec_ref(v_a_69_);
v_res_72_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_boxed_71_, v_x_70_);
lean_dec(v_x_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
return v_x_74_;
}
else
{
lean_object* v_key_76_; lean_object* v_value_77_; lean_object* v_tail_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_102_; 
v_key_76_ = lean_ctor_get(v_x_75_, 0);
v_value_77_ = lean_ctor_get(v_x_75_, 1);
v_tail_78_ = lean_ctor_get(v_x_75_, 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_102_ == 0)
{
v___x_80_ = v_x_75_;
v_isShared_81_ = v_isSharedCheck_102_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_tail_78_);
lean_inc(v_value_77_);
lean_inc(v_key_76_);
lean_dec(v_x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_102_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v_fold_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_82_ = lean_array_get_size(v_x_74_);
v___x_83_ = 32ULL;
v___x_84_ = lean_unbox_uint64(v_key_76_);
v___x_85_ = lean_uint64_shift_right(v___x_84_, v___x_83_);
v___x_86_ = lean_unbox_uint64(v_key_76_);
v_fold_87_ = lean_uint64_xor(v___x_86_, v___x_85_);
v___x_88_ = 16ULL;
v___x_89_ = lean_uint64_shift_right(v_fold_87_, v___x_88_);
v___x_90_ = lean_uint64_xor(v_fold_87_, v___x_89_);
v___x_91_ = lean_uint64_to_usize(v___x_90_);
v___x_92_ = lean_usize_of_nat(v___x_82_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_sub(v___x_92_, v___x_93_);
v___x_95_ = lean_usize_land(v___x_91_, v___x_94_);
v___x_96_ = lean_array_uget_borrowed(v_x_74_, v___x_95_);
lean_inc(v___x_96_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 2, v___x_96_);
v___x_98_ = v___x_80_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_key_76_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_value_77_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v___x_96_);
v___x_98_ = v_reuseFailAlloc_101_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_array_uset(v_x_74_, v___x_95_, v___x_98_);
v_x_74_ = v___x_99_;
v_x_75_ = v_tail_78_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(lean_object* v_i_103_, lean_object* v_source_104_, lean_object* v_target_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_array_get_size(v_source_104_);
v___x_107_ = lean_nat_dec_lt(v_i_103_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_source_104_);
lean_dec(v_i_103_);
return v_target_105_;
}
else
{
lean_object* v_es_108_; lean_object* v___x_109_; lean_object* v_source_110_; lean_object* v_target_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_es_108_ = lean_array_fget(v_source_104_, v_i_103_);
v___x_109_ = lean_box(0);
v_source_110_ = lean_array_fset(v_source_104_, v_i_103_, v___x_109_);
v_target_111_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(v_target_105_, v_es_108_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_i_103_, v___x_112_);
lean_dec(v_i_103_);
v_i_103_ = v___x_113_;
v_source_104_ = v_source_110_;
v_target_105_ = v_target_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(lean_object* v_data_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_nbuckets_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_116_ = lean_array_get_size(v_data_115_);
v___x_117_ = lean_unsigned_to_nat(2u);
v_nbuckets_118_ = lean_nat_mul(v___x_116_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_box(0);
v___x_121_ = lean_mk_array(v_nbuckets_118_, v___x_120_);
v___x_122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(v___x_119_, v_data_115_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(uint64_t v_a_123_, lean_object* v_b_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_dec(v_b_124_);
return v_x_125_;
}
else
{
lean_object* v_key_126_; lean_object* v_value_127_; lean_object* v_tail_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_142_; 
v_key_126_ = lean_ctor_get(v_x_125_, 0);
v_value_127_ = lean_ctor_get(v_x_125_, 1);
v_tail_128_ = lean_ctor_get(v_x_125_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_142_ == 0)
{
v___x_130_ = v_x_125_;
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_tail_128_);
lean_inc(v_value_127_);
lean_inc(v_key_126_);
lean_dec(v_x_125_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
uint64_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unbox_uint64(v_key_126_);
v___x_133_ = lean_uint64_dec_eq(v___x_132_, v_a_123_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_123_, v_b_124_, v_tail_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 2, v___x_134_);
v___x_136_ = v___x_130_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_key_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_value_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec(v_value_127_);
lean_dec(v_key_126_);
v___x_138_ = lean_box_uint64(v_a_123_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_b_124_);
lean_ctor_set(v___x_130_, 0, v___x_138_);
v___x_140_ = v___x_130_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_b_124_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_tail_128_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg___boxed(lean_object* v_a_143_, lean_object* v_b_144_, lean_object* v_x_145_){
_start:
{
uint64_t v_a_boxed_146_; lean_object* v_res_147_; 
v_a_boxed_146_ = lean_unbox_uint64(v_a_143_);
lean_dec_ref(v_a_143_);
v_res_147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_boxed_146_, v_b_144_, v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(lean_object* v_m_148_, uint64_t v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v_size_151_; lean_object* v_buckets_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_195_; 
v_size_151_ = lean_ctor_get(v_m_148_, 0);
v_buckets_152_ = lean_ctor_get(v_m_148_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_m_148_);
if (v_isSharedCheck_195_ == 0)
{
v___x_154_ = v_m_148_;
v_isShared_155_ = v_isSharedCheck_195_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_buckets_152_);
lean_inc(v_size_151_);
lean_dec(v_m_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_195_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v_fold_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v_bkt_168_; uint8_t v___x_169_; 
v___x_156_ = lean_array_get_size(v_buckets_152_);
v___x_157_ = 32ULL;
v___x_158_ = lean_uint64_shift_right(v_a_149_, v___x_157_);
v_fold_159_ = lean_uint64_xor(v_a_149_, v___x_158_);
v___x_160_ = 16ULL;
v___x_161_ = lean_uint64_shift_right(v_fold_159_, v___x_160_);
v___x_162_ = lean_uint64_xor(v_fold_159_, v___x_161_);
v___x_163_ = lean_uint64_to_usize(v___x_162_);
v___x_164_ = lean_usize_of_nat(v___x_156_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = lean_usize_sub(v___x_164_, v___x_165_);
v___x_167_ = lean_usize_land(v___x_163_, v___x_166_);
v_bkt_168_ = lean_array_uget_borrowed(v_buckets_152_, v___x_167_);
v___x_169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_149_, v_bkt_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v_size_x27_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_buckets_x27_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v_size_x27_171_ = lean_nat_add(v_size_151_, v___x_170_);
lean_dec(v_size_151_);
v___x_172_ = lean_box_uint64(v_a_149_);
lean_inc(v_bkt_168_);
v___x_173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_b_150_);
lean_ctor_set(v___x_173_, 2, v_bkt_168_);
v_buckets_x27_174_ = lean_array_uset(v_buckets_152_, v___x_167_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(4u);
v___x_176_ = lean_nat_mul(v_size_x27_171_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(3u);
v___x_178_ = lean_nat_div(v___x_176_, v___x_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_array_get_size(v_buckets_x27_174_);
v___x_180_ = lean_nat_dec_le(v___x_178_, v___x_179_);
lean_dec(v___x_178_);
if (v___x_180_ == 0)
{
lean_object* v_val_181_; lean_object* v___x_183_; 
v_val_181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(v_buckets_x27_174_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_val_181_);
lean_ctor_set(v___x_154_, 0, v_size_x27_171_);
v___x_183_ = v___x_154_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_size_x27_171_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_val_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v___x_186_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_buckets_x27_174_);
lean_ctor_set(v___x_154_, 0, v_size_x27_171_);
v___x_186_ = v___x_154_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_size_x27_171_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_buckets_x27_174_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v___x_188_; lean_object* v_buckets_x27_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
lean_inc(v_bkt_168_);
v___x_188_ = lean_box(0);
v_buckets_x27_189_ = lean_array_uset(v_buckets_152_, v___x_167_, v___x_188_);
v___x_190_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_149_, v_b_150_, v_bkt_168_);
v___x_191_ = lean_array_uset(v_buckets_x27_189_, v___x_167_, v___x_190_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_191_);
v___x_193_ = v___x_154_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_size_151_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg___boxed(lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
uint64_t v_a_boxed_199_; lean_object* v_res_200_; 
v_a_boxed_199_ = lean_unbox_uint64(v_a_197_);
lean_dec_ref(v_a_197_);
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_m_196_, v_a_boxed_199_, v_b_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(size_t v_sz_201_, size_t v_i_202_, lean_object* v_bs_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_bs_203_);
return v___x_205_;
}
else
{
lean_object* v_v_206_; lean_object* v___x_207_; lean_object* v_bs_x27_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; 
v_v_206_ = lean_array_uget(v_bs_203_, v_i_202_);
v___x_207_ = lean_unsigned_to_nat(0u);
v_bs_x27_208_ = lean_array_uset(v_bs_203_, v_i_202_, v___x_207_);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_202_, v___x_209_);
v___x_211_ = lean_array_uset(v_bs_x27_208_, v_i_202_, v_v_206_);
v_i_202_ = v___x_210_;
v_bs_203_ = v___x_211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0___boxed(lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_bs_215_){
_start:
{
size_t v_sz_boxed_216_; size_t v_i_boxed_217_; lean_object* v_res_218_; 
v_sz_boxed_216_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_217_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(v_sz_boxed_216_, v_i_boxed_217_, v_bs_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 4)
{
lean_object* v_elems_222_; size_t v_sz_223_; size_t v___x_224_; lean_object* v___x_225_; 
v_elems_222_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_elems_222_);
lean_dec_ref(v_x_221_);
v_sz_223_ = lean_array_size(v_elems_222_);
v___x_224_ = ((size_t)0ULL);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(v_sz_223_, v___x_224_, v_elems_222_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_226_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_227_ = lean_unsigned_to_nat(80u);
v___x_228_ = l_Lean_Json_pretty(v_x_221_, v___x_227_);
v___x_229_ = lean_string_append(v___x_226_, v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(lean_object* v_cache_239_, lean_object* v_line_240_, uint8_t v_platformIndependent_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Json_parse(v_line_240_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_cache_239_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_242_);
v___x_252_ = l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(v_a_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_cache_239_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_252_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_array_get_size(v_a_261_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_a_261_);
lean_dec_ref(v_cache_239_);
v___x_265_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1));
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_array_fget_borrowed(v_a_261_, v___x_262_);
lean_inc(v___x_266_);
v___x_267_ = l_Lake_Hash_fromJson_x3f(v___x_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec(v_a_261_);
lean_dec_ref(v_cache_239_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_290_; 
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_290_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_dec_lt(v___x_280_, v___x_263_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_del_object(v___x_278_);
lean_dec(v_a_276_);
lean_dec(v_a_261_);
lean_dec_ref(v_cache_239_);
v___x_282_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3));
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint64_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_283_ = lean_array_fget(v_a_261_, v___x_280_);
lean_dec(v_a_261_);
v___x_284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1, v_platformIndependent_241_);
v___x_285_ = lean_unbox_uint64(v_a_276_);
lean_dec(v_a_276_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_cache_239_, v___x_285_, v___x_284_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_286_);
v___x_288_ = v___x_278_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___boxed(lean_object* v_cache_291_, lean_object* v_line_292_, lean_object* v_platformIndependent_293_){
_start:
{
uint8_t v_platformIndependent_boxed_294_; lean_object* v_res_295_; 
v_platformIndependent_boxed_294_ = lean_unbox(v_platformIndependent_293_);
v_res_295_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_291_, v_line_292_, v_platformIndependent_boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1(lean_object* v_00_u03b2_296_, lean_object* v_m_297_, uint64_t v_a_298_, lean_object* v_b_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_m_297_, v_a_298_, v_b_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
uint64_t v_a_boxed_305_; lean_object* v_res_306_; 
v_a_boxed_305_ = lean_unbox_uint64(v_a_303_);
lean_dec_ref(v_a_303_);
v_res_306_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1(v_00_u03b2_301_, v_m_302_, v_a_boxed_305_, v_b_304_);
return v_res_306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2(lean_object* v_00_u03b2_307_, uint64_t v_a_308_, lean_object* v_x_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_308_, v_x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
uint64_t v_a_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_a_boxed_314_ = lean_unbox_uint64(v_a_312_);
lean_dec_ref(v_a_312_);
v_res_315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2(v_00_u03b2_311_, v_a_boxed_314_, v_x_313_);
lean_dec(v_x_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3(lean_object* v_00_u03b2_317_, lean_object* v_data_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(v_data_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4(lean_object* v_00_u03b2_320_, uint64_t v_a_321_, lean_object* v_b_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_321_, v_b_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___boxed(lean_object* v_00_u03b2_325_, lean_object* v_a_326_, lean_object* v_b_327_, lean_object* v_x_328_){
_start:
{
uint64_t v_a_boxed_329_; lean_object* v_res_330_; 
v_a_boxed_329_ = lean_unbox_uint64(v_a_326_);
lean_dec_ref(v_a_326_);
v_res_330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4(v_00_u03b2_325_, v_a_boxed_329_, v_b_327_, v_x_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_331_, lean_object* v_i_332_, lean_object* v_source_333_, lean_object* v_target_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(v_i_332_, v_source_333_, v_target_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(v_x_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___lam__0(lean_object* v_toPure_340_, lean_object* v_cache_341_, lean_object* v_____r_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_apply_2(v_toPure_340_, lean_box(0), v_cache_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inputName_348_, lean_object* v_lineNo_349_, lean_object* v_cache_350_, lean_object* v_line_351_, uint8_t v_platformIndependent_352_){
_start:
{
lean_object* v_toApplicative_353_; lean_object* v_toBind_354_; lean_object* v_toPure_355_; lean_object* v___x_356_; 
v_toApplicative_353_ = lean_ctor_get(v_inst_346_, 0);
lean_inc_ref(v_toApplicative_353_);
v_toBind_354_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_toBind_354_);
lean_dec_ref(v_inst_346_);
v_toPure_355_ = lean_ctor_get(v_toApplicative_353_, 1);
lean_inc(v_toPure_355_);
lean_dec_ref(v_toApplicative_353_);
lean_inc_ref(v_cache_350_);
v___x_356_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_350_, v_line_351_, v_platformIndependent_352_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_356_);
v___f_358_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_358_, 0, v_toPure_355_);
lean_closure_set(v___f_358_, 1, v_cache_350_);
v___x_359_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_360_ = lean_string_append(v_inputName_348_, v___x_359_);
v___x_361_ = l_Nat_reprFast(v_lineNo_349_);
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
lean_dec_ref(v___x_361_);
v___x_363_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
v___x_365_ = lean_string_append(v___x_364_, v_a_357_);
lean_dec(v_a_357_);
v___x_366_ = 2;
v___x_367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_366_);
v___x_368_ = lean_apply_1(v_inst_347_, v___x_367_);
v___x_369_ = lean_apply_4(v_toBind_354_, lean_box(0), lean_box(0), v___x_368_, v___f_358_);
return v___x_369_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_371_; 
lean_dec(v_toBind_354_);
lean_dec_ref(v_cache_350_);
lean_dec(v_lineNo_349_);
lean_dec_ref(v_inputName_348_);
lean_dec(v_inst_347_);
v_a_370_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_356_);
v___x_371_ = lean_apply_2(v_toPure_355_, lean_box(0), v_a_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___boxed(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inputName_374_, lean_object* v_lineNo_375_, lean_object* v_cache_376_, lean_object* v_line_377_, lean_object* v_platformIndependent_378_){
_start:
{
uint8_t v_platformIndependent_boxed_379_; lean_object* v_res_380_; 
v_platformIndependent_boxed_379_ = lean_unbox(v_platformIndependent_378_);
v_res_380_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(v_inst_372_, v_inst_373_, v_inputName_374_, v_lineNo_375_, v_cache_376_, v_line_377_, v_platformIndependent_boxed_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry(lean_object* v_m_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inputName_384_, lean_object* v_lineNo_385_, lean_object* v_cache_386_, lean_object* v_line_387_, uint8_t v_platformIndependent_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(v_inst_382_, v_inst_383_, v_inputName_384_, v_lineNo_385_, v_cache_386_, v_line_387_, v_platformIndependent_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___boxed(lean_object* v_m_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inputName_393_, lean_object* v_lineNo_394_, lean_object* v_cache_395_, lean_object* v_line_396_, lean_object* v_platformIndependent_397_){
_start:
{
uint8_t v_platformIndependent_boxed_398_; lean_object* v_res_399_; 
v_platformIndependent_boxed_398_ = lean_unbox(v_platformIndependent_397_);
v_res_399_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry(v_m_390_, v_inst_391_, v_inst_392_, v_inputName_393_, v_lineNo_394_, v_cache_395_, v_line_396_, v_platformIndependent_boxed_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object* v_inputName_400_, lean_object* v_lineNo_401_, lean_object* v_cache_402_, lean_object* v_line_403_, uint8_t v_platformIndependent_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
lean_inc_ref(v_cache_402_);
v___x_407_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_402_, v_line_403_, v_platformIndependent_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_425_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_425_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_425_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_425_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_412_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_413_ = lean_string_append(v_inputName_400_, v___x_412_);
v___x_414_ = l_Nat_reprFast(v_lineNo_401_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = lean_string_append(v___x_417_, v_a_408_);
lean_dec(v_a_408_);
v___x_419_ = 2;
v___x_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
v___x_421_ = lean_apply_2(v___y_405_, v___x_420_, lean_box(0));
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_cache_402_);
v___x_423_ = v___x_410_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_cache_402_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v___y_405_);
lean_dec_ref(v_cache_402_);
lean_dec(v_lineNo_401_);
lean_dec_ref(v_inputName_400_);
v_a_426_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_407_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_407_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 0);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object* v_inputName_434_, lean_object* v_lineNo_435_, lean_object* v_cache_436_, lean_object* v_line_437_, lean_object* v_platformIndependent_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_platformIndependent_boxed_441_; lean_object* v_res_442_; 
v_platformIndependent_boxed_441_ = lean_unbox(v_platformIndependent_438_);
v_res_442_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_434_, v_lineNo_435_, v_cache_436_, v_line_437_, v_platformIndependent_boxed_441_, v___y_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v_contents_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_startInclusive_448_; lean_object* v_endExclusive_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_startInclusive_448_ = lean_ctor_get(v___x_443_, 1);
v_endExclusive_449_ = lean_ctor_get(v___x_443_, 2);
v___x_450_ = lean_nat_sub(v_endExclusive_449_, v_startInclusive_448_);
v___x_451_ = lean_nat_dec_eq(v_a_446_, v___x_450_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint32_t v___x_453_; uint32_t v___x_454_; uint8_t v___x_455_; 
lean_dec(v_b_447_);
v___x_452_ = lean_nat_add(v___x_444_, v_a_446_);
v___x_453_ = lean_string_utf8_get_fast(v_contents_445_, v___x_452_);
v___x_454_ = 10;
v___x_455_ = lean_uint32_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_a_446_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_string_utf8_next_fast(v_contents_445_, v___x_452_);
lean_dec(v___x_452_);
v___x_458_ = lean_nat_sub(v___x_457_, v___x_444_);
v_a_446_ = v___x_458_;
v_b_447_ = v___x_456_;
goto _start;
}
else
{
lean_object* v___x_460_; 
lean_dec(v___x_452_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v_a_446_);
return v___x_460_;
}
}
else
{
lean_dec(v_a_446_);
return v_b_447_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg___boxed(lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_contents_463_, lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_461_, v___x_462_, v_contents_463_, v_a_464_, v_b_465_);
lean_dec_ref(v_contents_463_);
lean_dec(v___x_462_);
lean_dec_ref(v___x_461_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object* v_a_467_, lean_object* v_inputName_468_, uint8_t v_platformIndependent_469_, lean_object* v_i_470_, lean_object* v_cache_471_, lean_object* v_contents_472_, lean_object* v_pos_473_){
_start:
{
lean_object* v___y_476_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_searcher_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = lean_string_utf8_byte_size(v_contents_472_);
lean_inc(v_pos_473_);
lean_inc_ref(v_contents_472_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v_contents_472_);
lean_ctor_set(v___x_496_, 1, v_pos_473_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v_searcher_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_box(0);
v___x_499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_496_, v_pos_473_, v_contents_472_, v_searcher_497_, v___x_498_);
lean_dec_ref(v___x_496_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_nat_sub(v___x_495_, v_pos_473_);
v___y_476_ = v___x_500_;
goto v___jp_475_;
}
else
{
lean_object* v_val_501_; 
v_val_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_501_);
lean_dec_ref(v___x_499_);
v___y_476_ = v_val_501_;
goto v___jp_475_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v_line_478_; lean_object* v___x_479_; lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_477_ = lean_nat_add(v_pos_473_, v___y_476_);
lean_dec(v___y_476_);
lean_inc(v___x_477_);
lean_inc(v_pos_473_);
lean_inc_ref(v_contents_472_);
v_line_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_478_, 0, v_contents_472_);
lean_ctor_set(v_line_478_, 1, v_pos_473_);
lean_ctor_set(v_line_478_, 2, v___x_477_);
v___x_479_ = l_String_Slice_trimAscii(v_line_478_);
lean_dec_ref(v_line_478_);
v_startInclusive_480_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_startInclusive_480_);
v_endExclusive_481_ = lean_ctor_get(v___x_479_, 2);
lean_inc(v_endExclusive_481_);
lean_dec_ref(v___x_479_);
v___x_482_ = lean_nat_sub(v_endExclusive_481_, v_startInclusive_480_);
lean_dec(v_startInclusive_480_);
lean_dec(v_endExclusive_481_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
lean_dec(v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_string_utf8_extract(v_contents_472_, v_pos_473_, v___x_477_);
lean_dec(v_pos_473_);
lean_inc_ref(v_a_467_);
lean_inc(v_i_470_);
lean_inc_ref(v_inputName_468_);
v___x_486_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_468_, v_i_470_, v_cache_471_, v___x_485_, v_platformIndependent_469_, v_a_467_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
v___x_488_ = lean_string_utf8_byte_size(v_contents_472_);
v___x_489_ = lean_nat_dec_eq(v___x_477_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___x_486_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_470_, v___x_490_);
lean_dec(v_i_470_);
v___x_492_ = lean_string_utf8_next_fast(v_contents_472_, v___x_477_);
lean_dec(v___x_477_);
v_i_470_ = v___x_491_;
v_cache_471_ = v_a_487_;
v_pos_473_ = v___x_492_;
goto _start;
}
else
{
lean_dec(v_a_487_);
lean_dec(v___x_477_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
lean_dec_ref(v_a_467_);
return v___x_486_;
}
}
else
{
lean_dec(v___x_477_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
lean_dec_ref(v_a_467_);
return v___x_486_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v___x_477_);
lean_dec(v_pos_473_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
lean_dec_ref(v_a_467_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_cache_471_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___boxed(lean_object* v_a_502_, lean_object* v_inputName_503_, lean_object* v_platformIndependent_504_, lean_object* v_i_505_, lean_object* v_cache_506_, lean_object* v_contents_507_, lean_object* v_pos_508_, lean_object* v_a_509_){
_start:
{
uint8_t v_platformIndependent_boxed_510_; lean_object* v_res_511_; 
v_platformIndependent_boxed_510_ = lean_unbox(v_platformIndependent_504_);
v_res_511_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_502_, v_inputName_503_, v_platformIndependent_boxed_510_, v_i_505_, v_cache_506_, v_contents_507_, v_pos_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_contents_514_, lean_object* v_a_515_, lean_object* v_b_516_){
_start:
{
lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_startInclusive_517_ = lean_ctor_get(v___x_512_, 1);
v_endExclusive_518_ = lean_ctor_get(v___x_512_, 2);
v___x_519_ = lean_nat_sub(v_endExclusive_518_, v_startInclusive_517_);
v___x_520_ = lean_nat_dec_eq(v_a_515_, v___x_519_);
lean_dec(v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint8_t v___x_524_; 
lean_dec(v_b_516_);
v___x_521_ = lean_nat_add(v___x_513_, v_a_515_);
v___x_522_ = lean_string_utf8_get_fast(v_contents_514_, v___x_521_);
v___x_523_ = 10;
v___x_524_ = lean_uint32_dec_eq(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_a_515_);
v___x_525_ = lean_box(0);
v___x_526_ = lean_string_utf8_next_fast(v_contents_514_, v___x_521_);
lean_dec(v___x_521_);
v___x_527_ = lean_nat_sub(v___x_526_, v___x_513_);
v_a_515_ = v___x_527_;
v_b_516_ = v___x_525_;
goto _start;
}
else
{
lean_object* v___x_529_; 
lean_dec(v___x_521_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_a_515_);
return v___x_529_;
}
}
else
{
lean_dec(v_a_515_);
return v_b_516_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_contents_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_530_, v___x_531_, v_contents_532_, v_a_533_, v_b_534_);
lean_dec_ref(v_contents_532_);
lean_dec(v___x_531_);
lean_dec_ref(v___x_530_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object* v_inputName_536_, uint8_t v_platformIndependent_537_, lean_object* v_i_538_, lean_object* v_cache_539_, lean_object* v_contents_540_, lean_object* v_pos_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___y_545_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_searcher_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_564_ = lean_string_utf8_byte_size(v_contents_540_);
lean_inc(v_pos_541_);
lean_inc_ref(v_contents_540_);
v___x_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_565_, 0, v_contents_540_);
lean_ctor_set(v___x_565_, 1, v_pos_541_);
lean_ctor_set(v___x_565_, 2, v___x_564_);
v_searcher_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_box(0);
v___x_568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_565_, v_pos_541_, v_contents_540_, v_searcher_566_, v___x_567_);
lean_dec_ref(v___x_565_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_nat_sub(v___x_564_, v_pos_541_);
v___y_545_ = v___x_569_;
goto v___jp_544_;
}
else
{
lean_object* v_val_570_; 
v_val_570_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_570_);
lean_dec_ref(v___x_568_);
v___y_545_ = v_val_570_;
goto v___jp_544_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v_line_547_; lean_object* v___x_548_; lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_546_ = lean_nat_add(v_pos_541_, v___y_545_);
lean_dec(v___y_545_);
lean_inc(v___x_546_);
lean_inc(v_pos_541_);
lean_inc_ref(v_contents_540_);
v_line_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_547_, 0, v_contents_540_);
lean_ctor_set(v_line_547_, 1, v_pos_541_);
lean_ctor_set(v_line_547_, 2, v___x_546_);
v___x_548_ = l_String_Slice_trimAscii(v_line_547_);
lean_dec_ref(v_line_547_);
v_startInclusive_549_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_startInclusive_549_);
v_endExclusive_550_ = lean_ctor_get(v___x_548_, 2);
lean_inc(v_endExclusive_550_);
lean_dec_ref(v___x_548_);
v___x_551_ = lean_nat_sub(v_endExclusive_550_, v_startInclusive_549_);
lean_dec(v_startInclusive_549_);
lean_dec(v_endExclusive_550_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_string_utf8_extract(v_contents_540_, v_pos_541_, v___x_546_);
lean_dec(v_pos_541_);
lean_inc_ref(v_a_542_);
lean_inc(v_i_538_);
lean_inc_ref(v_inputName_536_);
v___x_555_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_536_, v_i_538_, v_cache_539_, v___x_554_, v_platformIndependent_537_, v_a_542_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
v___x_557_ = lean_string_utf8_byte_size(v_contents_540_);
v___x_558_ = lean_nat_dec_eq(v___x_546_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v___x_555_);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_i_538_, v___x_559_);
lean_dec(v_i_538_);
v___x_561_ = lean_string_utf8_next_fast(v_contents_540_, v___x_546_);
lean_dec(v___x_546_);
v___x_562_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_542_, v_inputName_536_, v_platformIndependent_537_, v___x_560_, v_a_556_, v_contents_540_, v___x_561_);
return v___x_562_;
}
else
{
lean_dec(v_a_556_);
lean_dec(v___x_546_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
return v___x_555_;
}
}
else
{
lean_dec(v___x_546_);
lean_dec_ref(v_a_542_);
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
return v___x_555_;
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v___x_546_);
lean_dec_ref(v_a_542_);
lean_dec(v_pos_541_);
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_cache_539_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object* v_inputName_571_, lean_object* v_platformIndependent_572_, lean_object* v_i_573_, lean_object* v_cache_574_, lean_object* v_contents_575_, lean_object* v_pos_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
uint8_t v_platformIndependent_boxed_579_; lean_object* v_res_580_; 
v_platformIndependent_boxed_579_ = lean_unbox(v_platformIndependent_572_);
v_res_580_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(v_inputName_571_, v_platformIndependent_boxed_579_, v_i_573_, v_cache_574_, v_contents_575_, v_pos_576_, v_a_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v_contents_583_, lean_object* v_inst_584_, lean_object* v_R_585_, lean_object* v_a_586_, lean_object* v_b_587_, lean_object* v_c_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_581_, v___x_582_, v_contents_583_, v_a_586_, v_b_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v_contents_592_, lean_object* v_inst_593_, lean_object* v_R_594_, lean_object* v_a_595_, lean_object* v_b_596_, lean_object* v_c_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(v___x_590_, v___x_591_, v_contents_592_, v_inst_593_, v_R_594_, v_a_595_, v_b_596_, v_c_597_);
lean_dec_ref(v_contents_592_);
lean_dec(v___x_591_);
lean_dec_ref(v___x_590_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_contents_601_, lean_object* v_inst_602_, lean_object* v_R_603_, lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v_c_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_599_, v___x_600_, v_contents_601_, v_a_604_, v_b_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___boxed(lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v_contents_610_, lean_object* v_inst_611_, lean_object* v_R_612_, lean_object* v_a_613_, lean_object* v_b_614_, lean_object* v_c_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(v___x_608_, v___x_609_, v_contents_610_, v_inst_611_, v_R_612_, v_a_613_, v_b_614_, v_c_615_);
lean_dec_ref(v_contents_610_);
lean_dec(v___x_609_);
lean_dec_ref(v___x_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_apply_2(v___y_618_, v___y_617_, lean_box(0));
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg___boxed(lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lake_CacheMap_parse___elam__0___redArg(v___y_622_, v___y_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object* v_x_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lake_CacheMap_parse___elam__0___redArg(v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___boxed(lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lake_CacheMap_parse___elam__0(v_x_631_, v___y_632_, v___y_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(lean_object* v___x_636_, lean_object* v_contents_637_, lean_object* v_a_638_, lean_object* v_b_639_){
_start:
{
lean_object* v_startInclusive_640_; lean_object* v_endExclusive_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_startInclusive_640_ = lean_ctor_get(v___x_636_, 1);
v_endExclusive_641_ = lean_ctor_get(v___x_636_, 2);
v___x_642_ = lean_nat_sub(v_endExclusive_641_, v_startInclusive_640_);
v___x_643_ = lean_nat_dec_eq(v_a_638_, v___x_642_);
lean_dec(v___x_642_);
if (v___x_643_ == 0)
{
uint32_t v___x_644_; uint32_t v___x_645_; uint8_t v___x_646_; 
lean_dec(v_b_639_);
v___x_644_ = lean_string_utf8_get_fast(v_contents_637_, v_a_638_);
v___x_645_ = 10;
v___x_646_ = lean_uint32_dec_eq(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box(0);
v___x_648_ = lean_string_utf8_next_fast(v_contents_637_, v_a_638_);
lean_dec(v_a_638_);
v_a_638_ = v___x_648_;
v_b_639_ = v___x_647_;
goto _start;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v_a_638_);
return v___x_650_;
}
}
else
{
lean_dec(v_a_638_);
return v_b_639_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg___boxed(lean_object* v___x_651_, lean_object* v_contents_652_, lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(v___x_651_, v_contents_652_, v_a_653_, v_b_654_);
lean_dec_ref(v_contents_652_);
lean_dec_ref(v___x_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_apply_2(v___y_656_, v___y_657_, lean_box(0));
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg___boxed(lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(v___y_661_, v___y_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(lean_object* v_as_665_, size_t v_i_666_, size_t v_stop_667_, lean_object* v_b_668_, lean_object* v___y_669_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_eq(v_i_666_, v_stop_667_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_array_uget_borrowed(v_as_665_, v_i_666_);
lean_inc(v___x_672_);
lean_inc_ref(v___y_669_);
v___x_673_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(v___y_669_, v___x_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; size_t v___x_675_; size_t v___x_676_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_666_, v___x_675_);
v_i_666_ = v___x_676_;
v_b_668_ = v_a_674_;
goto _start;
}
else
{
lean_dec_ref(v___y_669_);
return v___x_673_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v___y_669_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_b_668_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
size_t v_i_boxed_685_; size_t v_stop_boxed_686_; lean_object* v_res_687_; 
v_i_boxed_685_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_686_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_as_679_, v_i_boxed_685_, v_stop_boxed_686_, v_b_682_, v___y_683_);
lean_dec_ref(v_as_679_);
return v_res_687_;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__0(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_box(0);
v___x_689_ = lean_unsigned_to_nat(16u);
v___x_690_ = lean_mk_array(v___x_689_, v___x_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* v_inputName_693_, lean_object* v_contents_694_, uint8_t v_platformIndependent_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_727_; lean_object* v_searcher_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_searcher_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_string_utf8_byte_size(v_contents_694_);
lean_inc_ref(v_contents_694_);
v___x_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_765_, 0, v_contents_694_);
lean_ctor_set(v___x_765_, 1, v_searcher_763_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
v___x_766_ = lean_box(0);
v___x_767_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(v___x_765_, v_contents_694_, v_searcher_763_, v___x_766_);
lean_dec_ref(v___x_765_);
if (lean_obj_tag(v___x_767_) == 0)
{
v___y_727_ = v___x_764_;
goto v___jp_726_;
}
else
{
lean_object* v_val_768_; 
v_val_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_val_768_);
lean_dec_ref(v___x_767_);
v___y_727_ = v_val_768_;
goto v___jp_726_;
}
v___jp_698_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
v___jp_701_:
{
if (v___y_703_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_705_ = lean_unsigned_to_nat(2u);
v___x_706_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_702_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_string_utf8_next_fast(v_contents_694_, v___y_704_);
lean_dec(v___y_704_);
v___x_709_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_696_, v_inputName_693_, v_platformIndependent_695_, v___x_705_, v___x_707_, v_contents_694_, v___x_708_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v___y_704_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_contents_694_);
lean_dec_ref(v_inputName_693_);
v___x_710_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___y_702_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
v___jp_713_:
{
if (lean_obj_tag(v___y_717_) == 0)
{
lean_dec_ref(v___y_717_);
v___y_702_ = v___y_714_;
v___y_703_ = v___y_715_;
v___y_704_ = v___y_716_;
goto v___jp_701_;
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_contents_694_);
lean_dec_ref(v_inputName_693_);
v_a_718_ = lean_ctor_get(v___y_717_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___y_717_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___y_717_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___y_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_728_; lean_object* v_line_729_; lean_object* v___x_730_; lean_object* v_str_731_; lean_object* v_startInclusive_732_; lean_object* v_endExclusive_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_728_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_727_);
lean_inc_ref(v_contents_694_);
v_line_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_729_, 0, v_contents_694_);
lean_ctor_set(v_line_729_, 1, v___x_728_);
lean_ctor_set(v_line_729_, 2, v___y_727_);
v___x_730_ = l_String_Slice_trimAscii(v_line_729_);
lean_dec_ref(v_line_729_);
v_str_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_str_731_);
v_startInclusive_732_ = lean_ctor_get(v___x_730_, 1);
lean_inc(v_startInclusive_732_);
v_endExclusive_733_ = lean_ctor_get(v___x_730_, 2);
lean_inc(v_endExclusive_733_);
lean_dec_ref(v___x_730_);
v___x_734_ = lean_string_utf8_extract(v_str_731_, v_startInclusive_732_, v_endExclusive_733_);
lean_dec(v_endExclusive_733_);
lean_dec(v_startInclusive_732_);
lean_dec_ref(v_str_731_);
v___x_735_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
lean_inc_ref(v_inputName_693_);
v___x_736_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_693_, v___x_734_, v___x_735_);
v___x_737_ = lean_string_utf8_byte_size(v_contents_694_);
v___x_738_ = lean_nat_dec_eq(v___y_727_, v___x_737_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_a_739_);
lean_dec_ref(v___x_736_);
v___x_740_ = lean_array_get_size(v_a_739_);
v___x_741_ = lean_nat_dec_lt(v___x_728_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec(v_a_739_);
v___y_702_ = v___x_728_;
v___y_703_ = v___x_738_;
v___y_704_ = v___y_727_;
goto v___jp_701_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_box(0);
v___x_743_ = lean_nat_dec_le(v___x_740_, v___x_740_);
if (v___x_743_ == 0)
{
if (v___x_741_ == 0)
{
lean_dec(v_a_739_);
v___y_702_ = v___x_728_;
v___y_703_ = v___x_738_;
v___y_704_ = v___y_727_;
goto v___jp_701_;
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_740_);
lean_inc_ref(v_a_696_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_739_, v___x_744_, v___x_745_, v___x_742_, v_a_696_);
lean_dec(v_a_739_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref(v___x_746_);
v___y_702_ = v___x_728_;
v___y_703_ = v___x_738_;
v___y_704_ = v___y_727_;
goto v___jp_701_;
}
else
{
v___y_714_ = v___x_728_;
v___y_715_ = v___x_738_;
v___y_716_ = v___y_727_;
v___y_717_ = v___x_746_;
goto v___jp_713_;
}
}
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_740_);
lean_inc_ref(v_a_696_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_739_, v___x_747_, v___x_748_, v___x_742_, v_a_696_);
lean_dec(v_a_739_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec_ref(v___x_749_);
v___y_702_ = v___x_728_;
v___y_703_ = v___x_738_;
v___y_704_ = v___y_727_;
goto v___jp_701_;
}
else
{
v___y_714_ = v___x_728_;
v___y_715_ = v___x_738_;
v___y_716_ = v___y_727_;
v___y_717_ = v___x_749_;
goto v___jp_713_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_a_750_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_a_750_);
lean_dec_ref(v___x_736_);
v___x_751_ = lean_array_get_size(v_a_750_);
v___x_752_ = lean_nat_dec_lt(v___x_728_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_a_750_);
lean_dec(v___y_727_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_contents_694_);
lean_dec_ref(v_inputName_693_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_box(0);
v___x_756_ = lean_nat_dec_le(v___x_751_, v___x_751_);
if (v___x_756_ == 0)
{
if (v___x_752_ == 0)
{
lean_dec(v_a_750_);
lean_dec(v___y_727_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_contents_694_);
lean_dec_ref(v_inputName_693_);
goto v___jp_698_;
}
else
{
size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((size_t)0ULL);
v___x_758_ = lean_usize_of_nat(v___x_751_);
lean_inc_ref(v_a_696_);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_750_, v___x_757_, v___x_758_, v___x_755_, v_a_696_);
lean_dec(v_a_750_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_dec_ref(v___x_759_);
lean_dec(v___y_727_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_contents_694_);
lean_dec_ref(v_inputName_693_);
goto v___jp_698_;
}
else
{
v___y_714_ = v___x_728_;
v___y_715_ = v___x_738_;
v___y_716_ = v___y_727_;
v___y_717_ = v___x_759_;
goto v___jp_713_;
}
}
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_751_);
lean_inc_ref(v_a_696_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_750_, v___x_760_, v___x_761_, v___x_755_, v_a_696_);
lean_dec(v_a_750_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_dec_ref(v___x_762_);
lean_dec(v___y_727_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_contents_694_);
lean_dec_ref(v_inputName_693_);
goto v___jp_698_;
}
else
{
v___y_714_ = v___x_728_;
v___y_715_ = v___x_738_;
v___y_716_ = v___y_727_;
v___y_717_ = v___x_762_;
goto v___jp_713_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* v_inputName_769_, lean_object* v_contents_770_, lean_object* v_platformIndependent_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v_platformIndependent_boxed_774_; lean_object* v_res_775_; 
v_platformIndependent_boxed_774_ = lean_unbox(v_platformIndependent_771_);
v_res_775_ = l_Lake_CacheMap_parse(v_inputName_769_, v_contents_770_, v_platformIndependent_boxed_774_, v_a_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1(lean_object* v___y_776_, lean_object* v_x_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(v___y_776_, v___y_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___boxed(lean_object* v___y_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1(v___y_781_, v_x_782_, v___y_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2(lean_object* v___x_786_, lean_object* v_contents_787_, lean_object* v_inst_788_, lean_object* v_R_789_, lean_object* v_a_790_, lean_object* v_b_791_, lean_object* v_c_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(v___x_786_, v_contents_787_, v_a_790_, v_b_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___boxed(lean_object* v___x_794_, lean_object* v_contents_795_, lean_object* v_inst_796_, lean_object* v_R_797_, lean_object* v_a_798_, lean_object* v_b_799_, lean_object* v_c_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2(v___x_794_, v_contents_795_, v_inst_796_, v_R_797_, v_a_798_, v_b_799_, v_c_800_);
lean_dec_ref(v_contents_795_);
lean_dec_ref(v___x_794_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object* v_inputName_802_, lean_object* v_lineNo_803_, lean_object* v_cache_804_, lean_object* v_line_805_, uint8_t v_platformIndependent_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
lean_inc_ref(v_cache_804_);
v___x_809_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_804_, v_line_805_, v_platformIndependent_806_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref(v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_812_ = lean_string_append(v_inputName_802_, v___x_811_);
v___x_813_ = l_Nat_reprFast(v_lineNo_803_);
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
v___x_817_ = lean_string_append(v___x_816_, v_a_810_);
lean_dec(v_a_810_);
v___x_818_ = 2;
v___x_819_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*1, v___x_818_);
v___x_820_ = lean_array_push(v___y_807_, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_cache_804_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_823_; 
lean_dec_ref(v_cache_804_);
lean_dec(v_lineNo_803_);
lean_dec_ref(v_inputName_802_);
v_a_822_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v___x_809_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_a_822_);
lean_ctor_set(v___x_823_, 1, v___y_807_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object* v_inputName_824_, lean_object* v_lineNo_825_, lean_object* v_cache_826_, lean_object* v_line_827_, lean_object* v_platformIndependent_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v_platformIndependent_boxed_831_; lean_object* v_res_832_; 
v_platformIndependent_boxed_831_ = lean_unbox(v_platformIndependent_828_);
v_res_832_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_inputName_824_, v_lineNo_825_, v_cache_826_, v_line_827_, v_platformIndependent_boxed_831_, v___y_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* v_h_833_, lean_object* v_fileName_834_, uint8_t v_platformIndependent_835_, lean_object* v_i_836_, lean_object* v_cache_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_io_prim_handle_get_line(v_h_833_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref(v___x_840_);
v___x_842_ = lean_string_utf8_byte_size(v_a_841_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_nat_dec_eq(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_inc(v_i_836_);
lean_inc_ref(v_fileName_834_);
v___x_845_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_fileName_834_, v_i_836_, v_cache_837_, v_a_841_, v_platformIndependent_835_, v_a_838_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
v_a_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_a_847_);
lean_dec_ref(v___x_845_);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_i_836_, v___x_848_);
lean_dec(v_i_836_);
v_i_836_ = v___x_849_;
v_cache_837_ = v_a_846_;
v_a_838_ = v_a_847_;
goto _start;
}
else
{
lean_dec(v_i_836_);
lean_dec_ref(v_fileName_834_);
return v___x_845_;
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v_a_841_);
lean_dec(v_i_836_);
lean_dec_ref(v_fileName_834_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_cache_837_);
lean_ctor_set(v___x_851_, 1, v_a_838_);
return v___x_851_;
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_cache_837_);
lean_dec(v_i_836_);
lean_dec_ref(v_fileName_834_);
v_a_852_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_840_);
v___x_853_ = lean_io_error_to_string(v_a_852_);
v___x_854_ = 3;
v___x_855_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*1, v___x_854_);
v___x_856_ = lean_array_get_size(v_a_838_);
v___x_857_ = lean_array_push(v_a_838_, v___x_855_);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* v_h_859_, lean_object* v_fileName_860_, lean_object* v_platformIndependent_861_, lean_object* v_i_862_, lean_object* v_cache_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_platformIndependent_boxed_866_; lean_object* v_res_867_; 
v_platformIndependent_boxed_866_ = lean_unbox(v_platformIndependent_861_);
v_res_867_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_859_, v_fileName_860_, v_platformIndependent_boxed_866_, v_i_862_, v_cache_863_, v_a_864_);
lean_dec(v_h_859_);
return v_res_867_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* v_h_871_, lean_object* v_fileName_872_, uint8_t v_platformIndependent_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = lean_io_prim_handle_get_line(v_h_871_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_876_);
lean_inc_ref(v_fileName_872_);
v___x_878_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_fileName_872_, v_a_877_, v_a_874_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_a_879_ = lean_ctor_get(v___x_878_, 1);
lean_inc(v_a_879_);
lean_dec_ref(v___x_878_);
v___x_880_ = lean_unsigned_to_nat(2u);
v___x_881_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_882_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_871_, v_fileName_872_, v_platformIndependent_873_, v___x_880_, v___x_881_, v_a_879_);
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_fileName_872_);
v_a_883_ = lean_ctor_get(v___x_878_, 0);
v_a_884_ = lean_ctor_get(v___x_878_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_878_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_inc(v_a_883_);
lean_dec(v___x_878_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v_fileName_872_);
v_a_892_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_876_);
v___x_893_ = lean_io_error_to_string(v_a_892_);
v___x_894_ = 3;
v___x_895_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_894_);
v___x_896_ = lean_array_get_size(v_a_874_);
v___x_897_ = lean_array_push(v_a_874_, v___x_895_);
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* v_h_899_, lean_object* v_fileName_900_, lean_object* v_platformIndependent_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
uint8_t v_platformIndependent_boxed_904_; lean_object* v_res_905_; 
v_platformIndependent_boxed_904_ = lean_unbox(v_platformIndependent_901_);
v_res_905_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(v_h_899_, v_fileName_900_, v_platformIndependent_boxed_904_, v_a_902_);
lean_dec(v_h_899_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* v_file_907_, uint8_t v_platformIndependent_908_, lean_object* v_a_909_){
_start:
{
uint8_t v___x_911_; lean_object* v___x_912_; 
v___x_911_ = 0;
v___x_912_ = lean_io_prim_handle_mk(v_file_907_, v___x_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; lean_object* v___x_915_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref(v___x_912_);
v___x_914_ = 0;
v___x_915_ = lean_io_prim_handle_lock(v_a_913_, v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; 
lean_dec_ref(v___x_915_);
v___x_916_ = lean_io_prim_handle_get_line(v_a_913_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref(v___x_916_);
lean_inc_ref(v_file_907_);
v___x_918_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_907_, v_a_917_, v_a_909_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_a_919_ = lean_ctor_get(v___x_918_, 1);
lean_inc(v_a_919_);
lean_dec_ref(v___x_918_);
v___x_920_ = lean_unsigned_to_nat(2u);
v___x_921_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_922_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_913_, v_file_907_, v_platformIndependent_908_, v___x_920_, v___x_921_, v_a_919_);
lean_dec(v_a_913_);
return v___x_922_;
}
else
{
lean_object* v_a_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_913_);
lean_dec_ref(v_file_907_);
v_a_923_ = lean_ctor_get(v___x_918_, 0);
v_a_924_ = lean_ctor_get(v___x_918_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_918_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_inc(v_a_923_);
lean_dec(v___x_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_923_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_a_924_);
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
else
{
lean_object* v_a_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_a_913_);
lean_dec_ref(v_file_907_);
v_a_932_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_932_);
lean_dec_ref(v___x_916_);
v___x_933_ = lean_io_error_to_string(v_a_932_);
v___x_934_ = 3;
v___x_935_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_934_);
v___x_936_ = lean_array_get_size(v_a_909_);
v___x_937_ = lean_array_push(v_a_909_, v___x_935_);
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
return v___x_938_;
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_a_913_);
lean_dec_ref(v_file_907_);
v_a_939_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v___x_915_);
v___x_940_ = lean_io_error_to_string(v_a_939_);
v___x_941_ = 3;
v___x_942_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_941_);
v___x_943_ = lean_array_get_size(v_a_909_);
v___x_944_ = lean_array_push(v_a_909_, v___x_942_);
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
return v___x_945_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_946_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_912_);
v___x_947_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_948_ = lean_string_append(v_file_907_, v___x_947_);
v___x_949_ = lean_io_error_to_string(v_a_946_);
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = 3;
v___x_952_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_951_);
v___x_953_ = lean_array_get_size(v_a_909_);
v___x_954_ = lean_array_push(v_a_909_, v___x_952_);
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object* v_file_956_, lean_object* v_platformIndependent_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
uint8_t v_platformIndependent_boxed_960_; lean_object* v_res_961_; 
v_platformIndependent_boxed_960_ = lean_unbox(v_platformIndependent_957_);
v_res_961_ = l_Lake_CacheMap_load(v_file_956_, v_platformIndependent_boxed_960_, v_a_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* v_file_962_, uint8_t v_platformIndependent_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_a_967_; lean_object* v_a_968_; uint8_t v___x_970_; lean_object* v___x_971_; 
v___x_970_ = 0;
v___x_971_ = lean_io_prim_handle_mk(v_file_962_, v___x_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = 0;
v___x_974_ = lean_io_prim_handle_lock(v_a_972_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_974_);
v___x_975_ = lean_io_prim_handle_get_line(v_a_972_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1001_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1001_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1001_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; 
lean_inc_ref(v_file_962_);
v___x_980_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_962_, v_a_976_, v_a_964_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_981_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = lean_unsigned_to_nat(2u);
v___x_983_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_984_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_972_, v_file_962_, v_platformIndependent_963_, v___x_982_, v___x_983_, v_a_981_);
lean_dec(v_a_972_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_996_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_a_986_ = lean_ctor_get(v___x_984_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_996_ == 0)
{
v___x_988_ = v___x_984_;
v_isShared_989_ = v_isSharedCheck_996_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_996_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 1);
lean_ctor_set(v___x_978_, 0, v_a_985_);
v___x_991_ = v___x_978_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_985_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_986_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v_a_998_; 
lean_del_object(v___x_978_);
v_a_997_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_997_);
v_a_998_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_a_998_);
lean_dec_ref(v___x_984_);
v_a_967_ = v_a_997_;
v_a_968_ = v_a_998_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_999_; lean_object* v_a_1000_; 
lean_del_object(v___x_978_);
lean_dec(v_a_972_);
lean_dec_ref(v_file_962_);
v_a_999_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_999_);
v_a_1000_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_980_);
v_a_967_ = v_a_999_;
v_a_968_ = v_a_1000_;
goto v___jp_966_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_a_972_);
lean_dec_ref(v_file_962_);
v_a_1002_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_975_);
v___x_1003_ = lean_io_error_to_string(v_a_1002_);
v___x_1004_ = 3;
v___x_1005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*1, v___x_1004_);
v___x_1006_ = lean_array_get_size(v_a_964_);
v___x_1007_ = lean_array_push(v_a_964_, v___x_1005_);
v_a_967_ = v___x_1006_;
v_a_968_ = v___x_1007_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v_a_972_);
lean_dec_ref(v_file_962_);
v_a_1008_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_974_);
v___x_1009_ = lean_io_error_to_string(v_a_1008_);
v___x_1010_ = 3;
v___x_1011_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*1, v___x_1010_);
v___x_1012_ = lean_array_get_size(v_a_964_);
v___x_1013_ = lean_array_push(v_a_964_, v___x_1011_);
v___x_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
return v___x_1014_;
}
}
else
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_971_);
if (lean_obj_tag(v_a_1015_) == 11)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_file_962_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_a_964_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1018_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1019_ = lean_string_append(v_file_962_, v___x_1018_);
v___x_1020_ = lean_io_error_to_string(v_a_1015_);
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = 3;
v___x_1023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*1, v___x_1022_);
v___x_1024_ = lean_array_get_size(v_a_964_);
v___x_1025_ = lean_array_push(v_a_964_, v___x_1023_);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
return v___x_1026_;
}
}
v___jp_966_:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v_a_967_);
lean_ctor_set(v___x_969_, 1, v_a_968_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object* v_file_1027_, lean_object* v_platformIndependent_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
uint8_t v_platformIndependent_boxed_1031_; lean_object* v_res_1032_; 
v_platformIndependent_boxed_1031_ = lean_unbox(v_platformIndependent_1028_);
v_res_1032_ = l_Lake_CacheMap_load_x3f(v_file_1027_, v_platformIndependent_boxed_1031_, v_a_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object* v_h_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_x_1034_);
lean_ctor_set(v___x_1038_, 1, v___y_1036_);
return v___x_1038_;
}
else
{
lean_object* v_value_1039_; lean_object* v_key_1040_; lean_object* v_tail_1041_; lean_object* v_out_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1067_; 
v_value_1039_ = lean_ctor_get(v_x_1035_, 1);
lean_inc(v_value_1039_);
v_key_1040_ = lean_ctor_get(v_x_1035_, 0);
lean_inc(v_key_1040_);
v_tail_1041_ = lean_ctor_get(v_x_1035_, 2);
lean_inc(v_tail_1041_);
lean_dec_ref(v_x_1035_);
v_out_1042_ = lean_ctor_get(v_value_1039_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_value_1039_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1044_ = v_value_1039_;
v_isShared_1045_ = v_isSharedCheck_1067_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_out_1042_);
lean_dec(v_value_1039_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1067_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
uint64_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1046_ = lean_unbox_uint64(v_key_1040_);
lean_dec(v_key_1040_);
v___x_1047_ = l_Lake_Hash_hex(v___x_1046_);
v___x_1048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(2u);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_1048_);
v___x_1052_ = lean_array_push(v___x_1051_, v_out_1042_);
v___x_1053_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = l_Lean_Json_compress(v___x_1053_);
v___x_1055_ = l_IO_FS_Handle_putStrLn(v_h_1033_, v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; 
lean_del_object(v___x_1044_);
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
v_x_1034_ = v_a_1056_;
v_x_1035_ = v_tail_1041_;
goto _start;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1062_; 
lean_dec(v_tail_1041_);
v_a_1058_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1055_);
v___x_1059_ = lean_io_error_to_string(v_a_1058_);
v___x_1060_ = 3;
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1059_);
v___x_1062_ = v___x_1044_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1059_);
v___x_1062_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*1, v___x_1060_);
v___x_1063_ = lean_array_get_size(v___y_1036_);
v___x_1064_ = lean_array_push(v___y_1036_, v___x_1062_);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object* v_h_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1068_, v_x_1069_, v_x_1070_, v___y_1071_);
lean_dec(v_h_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object* v_h_1074_, lean_object* v_as_1075_, size_t v_i_1076_, size_t v_stop_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_usize_dec_eq(v_i_1076_, v_stop_1077_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_array_uget_borrowed(v_as_1075_, v_i_1076_);
v___x_1083_ = lean_box(0);
lean_inc(v___x_1082_);
v___x_1084_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1074_, v___x_1083_, v___x_1082_, v___y_1079_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v_a_1086_; size_t v___x_1087_; size_t v___x_1088_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
v_a_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1084_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_add(v_i_1076_, v___x_1087_);
v_i_1076_ = v___x_1088_;
v_b_1078_ = v_a_1085_;
v___y_1079_ = v_a_1086_;
goto _start;
}
else
{
return v___x_1084_;
}
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_b_1078_);
lean_ctor_set(v___x_1090_, 1, v___y_1079_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object* v_h_1091_, lean_object* v_as_1092_, lean_object* v_i_1093_, lean_object* v_stop_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
size_t v_i_boxed_1098_; size_t v_stop_boxed_1099_; lean_object* v_res_1100_; 
v_i_boxed_1098_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_stop_boxed_1099_ = lean_unbox_usize(v_stop_1094_);
lean_dec(v_stop_1094_);
v_res_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1091_, v_as_1092_, v_i_boxed_1098_, v_stop_boxed_1099_, v_b_1095_, v___y_1096_);
lean_dec_ref(v_as_1092_);
lean_dec(v_h_1091_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object* v_h_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_x_1102_);
lean_ctor_set(v___x_1106_, 1, v___y_1104_);
return v___x_1106_;
}
else
{
lean_object* v_value_1107_; uint8_t v_platformIndependent_1108_; 
v_value_1107_ = lean_ctor_get(v_x_1103_, 1);
lean_inc(v_value_1107_);
v_platformIndependent_1108_ = lean_ctor_get_uint8(v_value_1107_, sizeof(void*)*1);
if (v_platformIndependent_1108_ == 0)
{
lean_object* v_tail_1109_; lean_object* v___x_1110_; 
lean_dec(v_value_1107_);
v_tail_1109_ = lean_ctor_get(v_x_1103_, 2);
lean_inc(v_tail_1109_);
lean_dec_ref(v_x_1103_);
v___x_1110_ = lean_box(0);
v_x_1102_ = v___x_1110_;
v_x_1103_ = v_tail_1109_;
goto _start;
}
else
{
lean_object* v_key_1112_; lean_object* v_tail_1113_; lean_object* v_out_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1139_; 
v_key_1112_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_key_1112_);
v_tail_1113_ = lean_ctor_get(v_x_1103_, 2);
lean_inc(v_tail_1113_);
lean_dec_ref(v_x_1103_);
v_out_1114_ = lean_ctor_get(v_value_1107_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_value_1107_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1116_ = v_value_1107_;
v_isShared_1117_ = v_isSharedCheck_1139_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_out_1114_);
lean_dec(v_value_1107_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1139_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
uint64_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1118_ = lean_unbox_uint64(v_key_1112_);
lean_dec(v_key_1112_);
v___x_1119_ = l_Lake_Hash_hex(v___x_1118_);
v___x_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
v___x_1121_ = lean_unsigned_to_nat(2u);
v___x_1122_ = lean_mk_empty_array_with_capacity(v___x_1121_);
v___x_1123_ = lean_array_push(v___x_1122_, v___x_1120_);
v___x_1124_ = lean_array_push(v___x_1123_, v_out_1114_);
v___x_1125_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
v___x_1126_ = l_Lean_Json_compress(v___x_1125_);
v___x_1127_ = l_IO_FS_Handle_putStrLn(v_h_1101_, v___x_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; 
lean_del_object(v___x_1116_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v_x_1102_ = v_a_1128_;
v_x_1103_ = v_tail_1113_;
goto _start;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1134_; 
lean_dec(v_tail_1113_);
v_a_1130_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1127_);
v___x_1131_ = lean_io_error_to_string(v_a_1130_);
v___x_1132_ = 3;
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1131_);
v___x_1134_ = v___x_1116_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1131_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*1, v___x_1132_);
v___x_1135_ = lean_array_get_size(v___y_1104_);
v___x_1136_ = lean_array_push(v___y_1104_, v___x_1134_);
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
return v___x_1137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object* v_h_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1140_, v_x_1141_, v_x_1142_, v___y_1143_);
lean_dec(v_h_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(lean_object* v_h_1146_, lean_object* v_as_1147_, size_t v_i_1148_, size_t v_stop_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_eq(v_i_1148_, v_stop_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_array_uget_borrowed(v_as_1147_, v_i_1148_);
v___x_1155_ = lean_box(0);
lean_inc(v___x_1154_);
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1146_, v___x_1155_, v___x_1154_, v___y_1151_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v_a_1158_; size_t v___x_1159_; size_t v___x_1160_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
v_a_1158_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_a_1158_);
lean_dec_ref(v___x_1156_);
v___x_1159_ = ((size_t)1ULL);
v___x_1160_ = lean_usize_add(v_i_1148_, v___x_1159_);
v_i_1148_ = v___x_1160_;
v_b_1150_ = v_a_1157_;
v___y_1151_ = v_a_1158_;
goto _start;
}
else
{
return v___x_1156_;
}
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1150_);
lean_ctor_set(v___x_1162_, 1, v___y_1151_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3___boxed(lean_object* v_h_1163_, lean_object* v_as_1164_, lean_object* v_i_1165_, lean_object* v_stop_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_i_boxed_1170_; size_t v_stop_boxed_1171_; lean_object* v_res_1172_; 
v_i_boxed_1170_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_stop_boxed_1171_ = lean_unbox_usize(v_stop_1166_);
lean_dec(v_stop_1166_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1163_, v_as_1164_, v_i_boxed_1170_, v_stop_boxed_1171_, v_b_1167_, v___y_1168_);
lean_dec_ref(v_as_1164_);
lean_dec(v_h_1163_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(lean_object* v_h_1173_, lean_object* v_cache_1174_, uint8_t v_platformIndependent_1175_, lean_object* v_a_1176_){
_start:
{
if (v_platformIndependent_1175_ == 0)
{
lean_object* v_buckets_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1199_; 
v_buckets_1178_ = lean_ctor_get(v_cache_1174_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_cache_1174_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_cache_1174_, 0);
lean_dec(v_unused_1200_);
v___x_1180_ = v_cache_1174_;
v_isShared_1181_ = v_isSharedCheck_1199_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_buckets_1178_);
lean_dec(v_cache_1174_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1199_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_array_get_size(v_buckets_1178_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_nat_dec_lt(v___x_1182_, v___x_1183_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_buckets_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_a_1176_);
lean_ctor_set(v___x_1180_, 0, v___x_1184_);
v___x_1187_ = v___x_1180_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_a_1176_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_nat_dec_le(v___x_1183_, v___x_1183_);
if (v___x_1189_ == 0)
{
if (v___x_1185_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_buckets_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_a_1176_);
lean_ctor_set(v___x_1180_, 0, v___x_1184_);
v___x_1191_ = v___x_1180_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1176_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
size_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
lean_del_object(v___x_1180_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = lean_usize_of_nat(v___x_1183_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1173_, v_buckets_1178_, v___x_1193_, v___x_1194_, v___x_1184_, v_a_1176_);
lean_dec_ref(v_buckets_1178_);
return v___x_1195_;
}
}
else
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
lean_del_object(v___x_1180_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = lean_usize_of_nat(v___x_1183_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1173_, v_buckets_1178_, v___x_1196_, v___x_1197_, v___x_1184_, v_a_1176_);
lean_dec_ref(v_buckets_1178_);
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_buckets_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1222_; 
v_buckets_1201_ = lean_ctor_get(v_cache_1174_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_cache_1174_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_cache_1174_, 0);
lean_dec(v_unused_1223_);
v___x_1203_ = v_cache_1174_;
v_isShared_1204_ = v_isSharedCheck_1222_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_buckets_1201_);
lean_dec(v_cache_1174_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1222_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_buckets_1201_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v_buckets_1201_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_a_1176_);
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_a_1176_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_le(v___x_1206_, v___x_1206_);
if (v___x_1212_ == 0)
{
if (v___x_1208_ == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref(v_buckets_1201_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_a_1176_);
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1214_ = v___x_1203_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_a_1176_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
lean_del_object(v___x_1203_);
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1206_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1173_, v_buckets_1201_, v___x_1216_, v___x_1217_, v___x_1207_, v_a_1176_);
lean_dec_ref(v_buckets_1201_);
return v___x_1218_;
}
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1203_);
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1206_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1173_, v_buckets_1201_, v___x_1219_, v___x_1220_, v___x_1207_, v_a_1176_);
lean_dec_ref(v_buckets_1201_);
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries___boxed(lean_object* v_h_1224_, lean_object* v_cache_1225_, lean_object* v_platformIndependent_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
uint8_t v_platformIndependent_boxed_1229_; lean_object* v_res_1230_; 
v_platformIndependent_boxed_1229_ = lean_unbox(v_platformIndependent_1226_);
v_res_1230_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_h_1224_, v_cache_1225_, v_platformIndependent_boxed_1229_, v_a_1227_);
lean_dec(v_h_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
return v_x_1231_;
}
else
{
lean_object* v_key_1233_; lean_object* v_value_1234_; lean_object* v_tail_1235_; uint64_t v___x_1236_; lean_object* v___x_1237_; 
v_key_1233_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_key_1233_);
v_value_1234_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_value_1234_);
v_tail_1235_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_tail_1235_);
lean_dec_ref(v_x_1232_);
v___x_1236_ = lean_unbox_uint64(v_key_1233_);
lean_dec(v_key_1233_);
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_x_1231_, v___x_1236_, v_value_1234_);
v_x_1231_ = v___x_1237_;
v_x_1232_ = v_tail_1235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(lean_object* v_as_1239_, size_t v_i_1240_, size_t v_stop_1241_, lean_object* v_b_1242_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_usize_dec_eq(v_i_1240_, v_stop_1241_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; 
v___x_1244_ = lean_array_uget_borrowed(v_as_1239_, v_i_1240_);
lean_inc(v___x_1244_);
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(v_b_1242_, v___x_1244_);
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_add(v_i_1240_, v___x_1246_);
v_i_1240_ = v___x_1247_;
v_b_1242_ = v___x_1245_;
goto _start;
}
else
{
return v_b_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object* v_as_1249_, lean_object* v_i_1250_, lean_object* v_stop_1251_, lean_object* v_b_1252_){
_start:
{
size_t v_i_boxed_1253_; size_t v_stop_boxed_1254_; lean_object* v_res_1255_; 
v_i_boxed_1253_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_stop_boxed_1254_ = lean_unbox_usize(v_stop_1251_);
lean_dec(v_stop_1251_);
v_res_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_as_1249_, v_i_boxed_1253_, v_stop_boxed_1254_, v_b_1252_);
lean_dec_ref(v_as_1249_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* v_file_1256_, lean_object* v_cache_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_a_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; 
lean_inc_ref(v_file_1256_);
v___x_1264_ = l_Lake_createParentDirs(v_file_1256_);
if (lean_obj_tag(v___x_1264_) == 0)
{
uint8_t v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v___x_1264_);
v___x_1265_ = 4;
v___x_1266_ = lean_io_prim_handle_mk(v_file_1256_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
uint8_t v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v___x_1266_);
v___x_1267_ = 3;
v___x_1268_ = lean_io_prim_handle_mk(v_file_1256_, v___x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = 1;
v___x_1271_ = lean_io_prim_handle_lock(v_a_1269_, v___x_1270_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref(v___x_1271_);
v___x_1272_ = lean_io_prim_handle_get_line(v_a_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
lean_inc_ref(v_file_1256_);
v___x_1274_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_1256_, v_a_1273_, v_a_1258_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = 0;
v___x_1277_ = lean_unsigned_to_nat(2u);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_1280_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_1269_, v_file_1256_, v___x_1276_, v___x_1277_, v___x_1279_, v_a_1275_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1309_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1284_ = v___x_1280_;
v_isShared_1285_ = v_isSharedCheck_1309_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1309_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___y_1287_; lean_object* v_buckets_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_buckets_1299_ = lean_ctor_get(v_cache_1257_, 1);
v___x_1300_ = lean_array_get_size(v_buckets_1299_);
v___x_1301_ = lean_nat_dec_lt(v___x_1278_, v___x_1300_);
if (v___x_1301_ == 0)
{
v___y_1287_ = v_a_1281_;
goto v___jp_1286_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_le(v___x_1300_, v___x_1300_);
if (v___x_1302_ == 0)
{
if (v___x_1301_ == 0)
{
v___y_1287_ = v_a_1281_;
goto v___jp_1286_;
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = lean_usize_of_nat(v___x_1300_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1299_, v___x_1303_, v___x_1304_, v_a_1281_);
v___y_1287_ = v___x_1305_;
goto v___jp_1286_;
}
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1300_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1299_, v___x_1306_, v___x_1307_, v_a_1281_);
v___y_1287_ = v___x_1308_;
goto v___jp_1286_;
}
}
v___jp_1286_:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_io_prim_handle_rewind(v_a_1269_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v___x_1288_);
lean_del_object(v___x_1284_);
v___x_1289_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1269_, v___y_1287_, v___x_1276_, v_a_1282_);
lean_dec(v_a_1269_);
return v___x_1289_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_dec_ref(v___y_1287_);
lean_dec(v_a_1269_);
v_a_1290_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v___x_1288_);
v___x_1291_ = lean_io_error_to_string(v_a_1290_);
v___x_1292_ = 3;
v___x_1293_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*1, v___x_1292_);
v___x_1294_ = lean_array_get_size(v_a_1282_);
v___x_1295_ = lean_array_push(v_a_1282_, v___x_1293_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 1, v___x_1295_);
lean_ctor_set(v___x_1284_, 0, v___x_1294_);
v___x_1297_ = v___x_1284_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v_a_1311_; 
lean_dec(v_a_1269_);
v_a_1310_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1310_);
v_a_1311_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1280_);
v_a_1261_ = v_a_1310_;
v_a_1262_ = v_a_1311_;
goto v___jp_1260_;
}
}
else
{
lean_object* v_a_1312_; lean_object* v_a_1313_; 
lean_dec(v_a_1269_);
lean_dec_ref(v_file_1256_);
v_a_1312_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1312_);
v_a_1313_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_a_1313_);
lean_dec_ref(v___x_1274_);
v_a_1261_ = v_a_1312_;
v_a_1262_ = v_a_1313_;
goto v___jp_1260_;
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_a_1269_);
lean_dec_ref(v_file_1256_);
v_a_1314_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1272_);
v___x_1315_ = lean_io_error_to_string(v_a_1314_);
v___x_1316_ = 3;
v___x_1317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1, v___x_1316_);
v___x_1318_ = lean_array_get_size(v_a_1258_);
v___x_1319_ = lean_array_push(v_a_1258_, v___x_1317_);
v_a_1261_ = v___x_1318_;
v_a_1262_ = v___x_1319_;
goto v___jp_1260_;
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v_a_1269_);
lean_dec_ref(v_file_1256_);
v_a_1320_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1271_);
v___x_1321_ = lean_io_error_to_string(v_a_1320_);
v___x_1322_ = 3;
v___x_1323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*1, v___x_1322_);
v___x_1324_ = lean_array_get_size(v_a_1258_);
v___x_1325_ = lean_array_push(v_a_1258_, v___x_1323_);
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
return v___x_1326_;
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_a_1327_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1268_);
v___x_1328_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1329_ = lean_string_append(v_file_1256_, v___x_1328_);
v___x_1330_ = lean_io_error_to_string(v_a_1327_);
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = 3;
v___x_1333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
v___x_1334_ = lean_array_get_size(v_a_1258_);
v___x_1335_ = lean_array_push(v_a_1258_, v___x_1333_);
v___x_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
return v___x_1336_;
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v_file_1256_);
v_a_1337_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1266_);
v___x_1338_ = lean_io_error_to_string(v_a_1337_);
v___x_1339_ = 3;
v___x_1340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*1, v___x_1339_);
v___x_1341_ = lean_array_get_size(v_a_1258_);
v___x_1342_ = lean_array_push(v_a_1258_, v___x_1340_);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
return v___x_1343_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_file_1256_);
v_a_1344_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1264_);
v___x_1345_ = lean_io_error_to_string(v_a_1344_);
v___x_1346_ = 3;
v___x_1347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*1, v___x_1346_);
v___x_1348_ = lean_array_get_size(v_a_1258_);
v___x_1349_ = lean_array_push(v_a_1258_, v___x_1347_);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
return v___x_1350_;
}
v___jp_1260_:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_a_1261_);
lean_ctor_set(v___x_1263_, 1, v_a_1262_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object* v_file_1351_, lean_object* v_cache_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lake_CacheMap_updateFile(v_file_1351_, v_cache_1352_, v_a_1353_);
lean_dec_ref(v_cache_1352_);
return v_res_1355_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__0(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_1357_ = l_Lake_Date_toString(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__0, &l_Lake_CacheMap_writeFile___closed__0_once, _init_l_Lake_CacheMap_writeFile___closed__0);
v___x_1359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__2(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__1, &l_Lake_CacheMap_writeFile___closed__1_once, _init_l_Lake_CacheMap_writeFile___closed__1);
v___x_1361_ = l_Lean_Json_compress(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* v_file_1362_, lean_object* v_cache_1363_, uint8_t v_platformIndependent_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1367_; 
lean_inc_ref(v_file_1362_);
v___x_1367_ = l_Lake_createParentDirs(v_file_1362_);
if (lean_obj_tag(v___x_1367_) == 0)
{
uint8_t v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v___x_1367_);
v___x_1368_ = 1;
v___x_1369_ = lean_io_prim_handle_mk(v_file_1362_, v___x_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v_file_1362_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = 1;
v___x_1372_ = lean_io_prim_handle_lock(v_a_1370_, v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v___x_1372_);
v___x_1373_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__2, &l_Lake_CacheMap_writeFile___closed__2_once, _init_l_Lake_CacheMap_writeFile___closed__2);
v___x_1374_ = l_IO_FS_Handle_putStrLn(v_a_1370_, v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1375_; 
lean_dec_ref(v___x_1374_);
v___x_1375_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1370_, v_cache_1363_, v_platformIndependent_1364_, v_a_1365_);
lean_dec(v_a_1370_);
return v___x_1375_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v_a_1370_);
lean_dec_ref(v_cache_1363_);
v_a_1376_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1374_);
v___x_1377_ = lean_io_error_to_string(v_a_1376_);
v___x_1378_ = 3;
v___x_1379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*1, v___x_1378_);
v___x_1380_ = lean_array_get_size(v_a_1365_);
v___x_1381_ = lean_array_push(v_a_1365_, v___x_1379_);
v___x_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
return v___x_1382_;
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_a_1370_);
lean_dec_ref(v_cache_1363_);
v_a_1383_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1372_);
v___x_1384_ = lean_io_error_to_string(v_a_1383_);
v___x_1385_ = 3;
v___x_1386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*1, v___x_1385_);
v___x_1387_ = lean_array_get_size(v_a_1365_);
v___x_1388_ = lean_array_push(v_a_1365_, v___x_1386_);
v___x_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
return v___x_1389_;
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v_cache_1363_);
v_a_1390_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1390_);
lean_dec_ref(v___x_1369_);
v___x_1391_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1392_ = lean_string_append(v_file_1362_, v___x_1391_);
v___x_1393_ = lean_io_error_to_string(v_a_1390_);
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = 3;
v___x_1396_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*1, v___x_1395_);
v___x_1397_ = lean_array_get_size(v_a_1365_);
v___x_1398_ = lean_array_push(v_a_1365_, v___x_1396_);
v___x_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
return v___x_1399_;
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref(v_cache_1363_);
lean_dec_ref(v_file_1362_);
v_a_1400_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1367_);
v___x_1401_ = lean_io_error_to_string(v_a_1400_);
v___x_1402_ = 3;
v___x_1403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*1, v___x_1402_);
v___x_1404_ = lean_array_get_size(v_a_1365_);
v___x_1405_ = lean_array_push(v_a_1365_, v___x_1403_);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object* v_file_1407_, lean_object* v_cache_1408_, lean_object* v_platformIndependent_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
uint8_t v_platformIndependent_boxed_1412_; lean_object* v_res_1413_; 
v_platformIndependent_boxed_1412_ = lean_unbox(v_platformIndependent_1409_);
v_res_1413_ = l_Lake_CacheMap_writeFile(v_file_1407_, v_cache_1408_, v_platformIndependent_boxed_1412_, v_a_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t v_a_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
else
{
lean_object* v_key_1417_; lean_object* v_value_1418_; lean_object* v_tail_1419_; uint64_t v___x_1420_; uint8_t v___x_1421_; 
v_key_1417_ = lean_ctor_get(v_x_1415_, 0);
v_value_1418_ = lean_ctor_get(v_x_1415_, 1);
v_tail_1419_ = lean_ctor_get(v_x_1415_, 2);
v___x_1420_ = lean_unbox_uint64(v_key_1417_);
v___x_1421_ = lean_uint64_dec_eq(v___x_1420_, v_a_1414_);
if (v___x_1421_ == 0)
{
v_x_1415_ = v_tail_1419_;
goto _start;
}
else
{
lean_object* v___x_1423_; 
lean_inc(v_value_1418_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_value_1418_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1424_, lean_object* v_x_1425_){
_start:
{
uint64_t v_a_boxed_1426_; lean_object* v_res_1427_; 
v_a_boxed_1426_ = lean_unbox_uint64(v_a_1424_);
lean_dec_ref(v_a_1424_);
v_res_1427_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_boxed_1426_, v_x_1425_);
lean_dec(v_x_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* v_m_1428_, uint64_t v_a_1429_){
_start:
{
lean_object* v_buckets_1430_; lean_object* v___x_1431_; uint64_t v___x_1432_; uint64_t v___x_1433_; uint64_t v_fold_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_buckets_1430_ = lean_ctor_get(v_m_1428_, 1);
v___x_1431_ = lean_array_get_size(v_buckets_1430_);
v___x_1432_ = 32ULL;
v___x_1433_ = lean_uint64_shift_right(v_a_1429_, v___x_1432_);
v_fold_1434_ = lean_uint64_xor(v_a_1429_, v___x_1433_);
v___x_1435_ = 16ULL;
v___x_1436_ = lean_uint64_shift_right(v_fold_1434_, v___x_1435_);
v___x_1437_ = lean_uint64_xor(v_fold_1434_, v___x_1436_);
v___x_1438_ = lean_uint64_to_usize(v___x_1437_);
v___x_1439_ = lean_usize_of_nat(v___x_1431_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_sub(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_usize_land(v___x_1438_, v___x_1441_);
v___x_1443_ = lean_array_uget_borrowed(v_buckets_1430_, v___x_1442_);
v___x_1444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1429_, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* v_m_1445_, lean_object* v_a_1446_){
_start:
{
uint64_t v_a_boxed_1447_; lean_object* v_res_1448_; 
v_a_boxed_1447_ = lean_unbox_uint64(v_a_1446_);
lean_dec_ref(v_a_1446_);
v_res_1448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1445_, v_a_boxed_1447_);
lean_dec_ref(v_m_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t v_inputHash_1449_, lean_object* v_cache_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_cache_1450_, v_inputHash_1449_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_box(0);
return v___x_1452_;
}
else
{
lean_object* v_val_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1461_; 
v_val_1453_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1455_ = v___x_1451_;
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_val_1453_);
lean_dec(v___x_1451_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_out_1457_; lean_object* v___x_1459_; 
v_out_1457_ = lean_ctor_get(v_val_1453_, 0);
lean_inc(v_out_1457_);
lean_dec(v_val_1453_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_out_1457_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_out_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* v_inputHash_1462_, lean_object* v_cache_1463_){
_start:
{
uint64_t v_inputHash_boxed_1464_; lean_object* v_res_1465_; 
v_inputHash_boxed_1464_ = lean_unbox_uint64(v_inputHash_1462_);
lean_dec_ref(v_inputHash_1462_);
v_res_1465_ = l_Lake_CacheMap_get_x3f(v_inputHash_boxed_1464_, v_cache_1463_);
lean_dec_ref(v_cache_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, uint64_t v_a_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1467_, v_a_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* v_00_u03b2_1470_, lean_object* v_m_1471_, lean_object* v_a_1472_){
_start:
{
uint64_t v_a_boxed_1473_; lean_object* v_res_1474_; 
v_a_boxed_1473_ = lean_unbox_uint64(v_a_1472_);
lean_dec_ref(v_a_1472_);
v_res_1474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(v_00_u03b2_1470_, v_m_1471_, v_a_boxed_1473_);
lean_dec_ref(v_m_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1475_, uint64_t v_a_1476_, lean_object* v_x_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1476_, v_x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1479_, lean_object* v_a_1480_, lean_object* v_x_1481_){
_start:
{
uint64_t v_a_boxed_1482_; lean_object* v_res_1483_; 
v_a_boxed_1482_ = lean_unbox_uint64(v_a_1480_);
lean_dec_ref(v_a_1480_);
v_res_1483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(v_00_u03b2_1479_, v_a_boxed_1482_, v_x_1481_);
lean_dec(v_x_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t v_inputHash_1484_, lean_object* v_out_1485_, lean_object* v_cache_1486_, uint8_t v_platformIndependent_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1488_, 0, v_out_1485_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*1, v_platformIndependent_1487_);
v___x_1489_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_cache_1486_, v_inputHash_1484_, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore___boxed(lean_object* v_inputHash_1490_, lean_object* v_out_1491_, lean_object* v_cache_1492_, lean_object* v_platformIndependent_1493_){
_start:
{
uint64_t v_inputHash_boxed_1494_; uint8_t v_platformIndependent_boxed_1495_; lean_object* v_res_1496_; 
v_inputHash_boxed_1494_ = lean_unbox_uint64(v_inputHash_1490_);
lean_dec_ref(v_inputHash_1490_);
v_platformIndependent_boxed_1495_ = lean_unbox(v_platformIndependent_1493_);
v_res_1496_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_boxed_1494_, v_out_1491_, v_cache_1492_, v_platformIndependent_boxed_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* v_inst_1497_, uint64_t v_inputHash_1498_, lean_object* v_val_1499_, lean_object* v_cache_1500_, uint8_t v_platformIndependent_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_apply_1(v_inst_1497_, v_val_1499_);
v___x_1503_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1498_, v___x_1502_, v_cache_1500_, v_platformIndependent_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* v_inst_1504_, lean_object* v_inputHash_1505_, lean_object* v_val_1506_, lean_object* v_cache_1507_, lean_object* v_platformIndependent_1508_){
_start:
{
uint64_t v_inputHash_boxed_1509_; uint8_t v_platformIndependent_boxed_1510_; lean_object* v_res_1511_; 
v_inputHash_boxed_1509_ = lean_unbox_uint64(v_inputHash_1505_);
lean_dec_ref(v_inputHash_1505_);
v_platformIndependent_boxed_1510_ = lean_unbox(v_platformIndependent_1508_);
v_res_1511_ = l_Lake_CacheMap_insert___redArg(v_inst_1504_, v_inputHash_boxed_1509_, v_val_1506_, v_cache_1507_, v_platformIndependent_boxed_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* v_00_u03b1_1512_, lean_object* v_inst_1513_, uint64_t v_inputHash_1514_, lean_object* v_val_1515_, lean_object* v_cache_1516_, uint8_t v_platformIndependent_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_apply_1(v_inst_1513_, v_val_1515_);
v___x_1519_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1514_, v___x_1518_, v_cache_1516_, v_platformIndependent_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_inst_1521_, lean_object* v_inputHash_1522_, lean_object* v_val_1523_, lean_object* v_cache_1524_, lean_object* v_platformIndependent_1525_){
_start:
{
uint64_t v_inputHash_boxed_1526_; uint8_t v_platformIndependent_boxed_1527_; lean_object* v_res_1528_; 
v_inputHash_boxed_1526_ = lean_unbox_uint64(v_inputHash_1522_);
lean_dec_ref(v_inputHash_1522_);
v_platformIndependent_boxed_1527_ = lean_unbox(v_platformIndependent_1525_);
v_res_1528_ = l_Lake_CacheMap_insert(v_00_u03b1_1520_, v_inst_1521_, v_inputHash_boxed_1526_, v_val_1523_, v_cache_1524_, v_platformIndependent_boxed_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* v_init_1532_, lean_object* v_x_1533_, lean_object* v___y_1534_){
_start:
{
if (lean_obj_tag(v_x_1533_) == 0)
{
lean_object* v_v_1536_; lean_object* v_l_1537_; lean_object* v_r_1538_; lean_object* v___x_1539_; 
v_v_1536_ = lean_ctor_get(v_x_1533_, 2);
lean_inc(v_v_1536_);
v_l_1537_ = lean_ctor_get(v_x_1533_, 3);
lean_inc(v_l_1537_);
v_r_1538_ = lean_ctor_get(v_x_1533_, 4);
lean_inc(v_r_1538_);
lean_dec_ref(v_x_1533_);
v___x_1539_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1532_, v_l_1537_, v___y_1534_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
v_a_1541_ = lean_ctor_get(v___x_1539_, 1);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1539_);
v___x_1542_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1540_, v_v_1536_, v_a_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_a_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
v_a_1544_ = lean_ctor_get(v___x_1542_, 1);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1542_);
v_init_1532_ = v_a_1543_;
v_x_1533_ = v_r_1538_;
v___y_1534_ = v_a_1544_;
goto _start;
}
else
{
lean_dec(v_r_1538_);
return v___x_1542_;
}
}
else
{
lean_dec(v_r_1538_);
lean_dec(v_v_1536_);
return v___x_1539_;
}
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_init_1532_);
lean_ctor_set(v___x_1546_, 1, v___y_1534_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* v_as_1547_, lean_object* v_o_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___y_1552_; 
switch(lean_obj_tag(v_o_1548_))
{
case 0:
{
v___y_1552_ = v_a_1549_;
goto v___jp_1551_;
}
case 1:
{
lean_object* v___x_1554_; 
lean_dec_ref(v_o_1548_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_as_1547_);
lean_ctor_set(v___x_1554_, 1, v_a_1549_);
return v___x_1554_;
}
case 2:
{
lean_object* v_n_1555_; lean_object* v___x_1556_; 
v_n_1555_ = lean_ctor_get(v_o_1548_, 0);
lean_inc_ref(v_n_1555_);
lean_dec_ref(v_o_1548_);
v___x_1556_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
v___x_1559_ = lean_string_append(v___x_1558_, v_a_1557_);
lean_dec(v_a_1557_);
v___x_1560_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_1561_ = lean_string_append(v___x_1559_, v___x_1560_);
v___x_1562_ = l_Lean_JsonNumber_toString(v_n_1555_);
v___x_1563_ = lean_string_append(v___x_1561_, v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = 3;
v___x_1565_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*1, v___x_1564_);
v___x_1566_ = lean_array_push(v_a_1549_, v___x_1565_);
v___y_1552_ = v___x_1566_;
goto v___jp_1551_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint64_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_n_1555_);
v_a_1567_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1556_);
v___x_1568_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1));
v___x_1569_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
v___x_1570_ = lean_unbox_uint64(v_a_1567_);
lean_dec(v_a_1567_);
lean_ctor_set_uint64(v___x_1569_, sizeof(void*)*1, v___x_1570_);
v___x_1571_ = lean_array_push(v_as_1547_, v___x_1569_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1549_);
return v___x_1572_;
}
}
case 3:
{
lean_object* v_s_1573_; lean_object* v___x_1574_; 
v_s_1573_ = lean_ctor_get(v_o_1548_, 0);
lean_inc_ref(v_s_1573_);
lean_dec_ref(v_o_1548_);
v___x_1574_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1573_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2));
v___x_1577_ = lean_string_append(v___x_1576_, v_a_1575_);
lean_dec(v_a_1575_);
v___x_1578_ = 3;
v___x_1579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*1, v___x_1578_);
v___x_1580_ = lean_array_push(v_a_1549_, v___x_1579_);
v___y_1552_ = v___x_1580_;
goto v___jp_1551_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_a_1581_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1574_);
v___x_1582_ = lean_array_push(v_as_1547_, v_a_1581_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_a_1549_);
return v___x_1583_;
}
}
case 4:
{
lean_object* v_elems_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_elems_1584_ = lean_ctor_get(v_o_1548_, 0);
lean_inc_ref(v_elems_1584_);
lean_dec_ref(v_o_1548_);
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = lean_array_get_size(v_elems_1584_);
v___x_1587_ = lean_nat_dec_lt(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref(v_elems_1584_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_as_1547_);
lean_ctor_set(v___x_1588_, 1, v_a_1549_);
return v___x_1588_;
}
else
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_nat_dec_le(v___x_1586_, v___x_1586_);
if (v___x_1589_ == 0)
{
if (v___x_1587_ == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref(v_elems_1584_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_as_1547_);
lean_ctor_set(v___x_1590_, 1, v_a_1549_);
return v___x_1590_;
}
else
{
size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = lean_usize_of_nat(v___x_1586_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1584_, v___x_1591_, v___x_1592_, v_as_1547_, v_a_1549_);
lean_dec_ref(v_elems_1584_);
return v___x_1593_;
}
}
else
{
size_t v___x_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = ((size_t)0ULL);
v___x_1595_ = lean_usize_of_nat(v___x_1586_);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1584_, v___x_1594_, v___x_1595_, v_as_1547_, v_a_1549_);
lean_dec_ref(v_elems_1584_);
return v___x_1596_;
}
}
}
default: 
{
lean_object* v_kvPairs_1597_; lean_object* v___x_1598_; 
v_kvPairs_1597_ = lean_ctor_get(v_o_1548_, 0);
lean_inc(v_kvPairs_1597_);
lean_dec_ref(v_o_1548_);
v___x_1598_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_as_1547_, v_kvPairs_1597_, v_a_1549_);
return v___x_1598_;
}
}
v___jp_1551_:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_as_1547_);
lean_ctor_set(v___x_1553_, 1, v___y_1552_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* v_as_1599_, size_t v_i_1600_, size_t v_stop_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_eq(v_i_1600_, v_stop_1601_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_array_uget_borrowed(v_as_1599_, v_i_1600_);
lean_inc(v___x_1606_);
v___x_1607_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_b_1602_, v___x_1606_, v___y_1603_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v_a_1609_; size_t v___x_1610_; size_t v___x_1611_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
v_a_1609_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1607_);
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1600_, v___x_1610_);
v_i_1600_ = v___x_1611_;
v_b_1602_ = v_a_1608_;
v___y_1603_ = v_a_1609_;
goto _start;
}
else
{
return v___x_1607_;
}
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_b_1602_);
lean_ctor_set(v___x_1613_, 1, v___y_1603_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* v_as_1614_, lean_object* v_i_1615_, lean_object* v_stop_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
size_t v_i_boxed_1620_; size_t v_stop_boxed_1621_; lean_object* v_res_1622_; 
v_i_boxed_1620_ = lean_unbox_usize(v_i_1615_);
lean_dec(v_i_1615_);
v_stop_boxed_1621_ = lean_unbox_usize(v_stop_1616_);
lean_dec(v_stop_1616_);
v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_as_1614_, v_i_boxed_1620_, v_stop_boxed_1621_, v_b_1617_, v___y_1618_);
lean_dec_ref(v_as_1614_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* v_init_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1623_, v_x_1624_, v___y_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* v_as_1628_, lean_object* v_o_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_as_1628_, v_o_1629_, v_a_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v___y_1635_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_x_1633_);
lean_ctor_set(v___x_1637_, 1, v___y_1635_);
return v___x_1637_;
}
else
{
lean_object* v_value_1638_; lean_object* v_tail_1639_; lean_object* v_out_1640_; lean_object* v___x_1641_; 
v_value_1638_ = lean_ctor_get(v_x_1634_, 1);
lean_inc(v_value_1638_);
v_tail_1639_ = lean_ctor_get(v_x_1634_, 2);
lean_inc(v_tail_1639_);
lean_dec_ref(v_x_1634_);
v_out_1640_ = lean_ctor_get(v_value_1638_, 0);
lean_inc(v_out_1640_);
lean_dec(v_value_1638_);
v___x_1641_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_x_1633_, v_out_1640_, v___y_1635_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_a_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
v_a_1643_ = lean_ctor_get(v___x_1641_, 1);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1641_);
v_x_1633_ = v_a_1642_;
v_x_1634_ = v_tail_1639_;
v___y_1635_ = v_a_1643_;
goto _start;
}
else
{
lean_dec(v_tail_1639_);
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_x_1645_, v_x_1646_, v___y_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* v_as_1650_, size_t v_i_1651_, size_t v_stop_1652_, lean_object* v_b_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_usize_dec_eq(v_i_1651_, v_stop_1652_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_array_uget_borrowed(v_as_1650_, v_i_1651_);
lean_inc(v___x_1657_);
v___x_1658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_b_1653_, v___x_1657_, v___y_1654_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_a_1660_; size_t v___x_1661_; size_t v___x_1662_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
v_a_1660_ = lean_ctor_get(v___x_1658_, 1);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1658_);
v___x_1661_ = ((size_t)1ULL);
v___x_1662_ = lean_usize_add(v_i_1651_, v___x_1661_);
v_i_1651_ = v___x_1662_;
v_b_1653_ = v_a_1659_;
v___y_1654_ = v_a_1660_;
goto _start;
}
else
{
return v___x_1658_;
}
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_b_1653_);
lean_ctor_set(v___x_1664_, 1, v___y_1654_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* v_as_1665_, lean_object* v_i_1666_, lean_object* v_stop_1667_, lean_object* v_b_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
size_t v_i_boxed_1671_; size_t v_stop_boxed_1672_; lean_object* v_res_1673_; 
v_i_boxed_1671_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_stop_boxed_1672_ = lean_unbox_usize(v_stop_1667_);
lean_dec(v_stop_1667_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_as_1665_, v_i_boxed_1671_, v_stop_boxed_1672_, v_b_1668_, v___y_1669_);
lean_dec_ref(v_as_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* v_map_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_buckets_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1708_; 
v_buckets_1679_ = lean_ctor_get(v_map_1676_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_map_1676_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_map_1676_, 0);
lean_dec(v_unused_1709_);
v___x_1681_ = v_map_1676_;
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_buckets_1679_);
lean_dec(v_map_1676_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___y_1687_; lean_object* v_a_1688_; lean_object* v___y_1695_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = ((lean_object*)(l_Lake_CacheMap_collectOutputDescrs___closed__0));
v___x_1685_ = lean_array_get_size(v_a_1677_);
v___x_1697_ = lean_array_get_size(v_buckets_1679_);
v___x_1698_ = lean_nat_dec_lt(v___x_1683_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
lean_dec_ref(v_buckets_1679_);
lean_inc_ref(v_a_1677_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1684_);
lean_ctor_set(v___x_1699_, 1, v_a_1677_);
v___y_1687_ = v___x_1699_;
v_a_1688_ = v_a_1677_;
goto v___jp_1686_;
}
else
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_le(v___x_1697_, v___x_1697_);
if (v___x_1700_ == 0)
{
if (v___x_1698_ == 0)
{
lean_object* v___x_1701_; 
lean_dec_ref(v_buckets_1679_);
lean_inc_ref(v_a_1677_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1684_);
lean_ctor_set(v___x_1701_, 1, v_a_1677_);
v___y_1687_ = v___x_1701_;
v_a_1688_ = v_a_1677_;
goto v___jp_1686_;
}
else
{
size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((size_t)0ULL);
v___x_1703_ = lean_usize_of_nat(v___x_1697_);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1679_, v___x_1702_, v___x_1703_, v___x_1684_, v_a_1677_);
lean_dec_ref(v_buckets_1679_);
v___y_1695_ = v___x_1704_;
goto v___jp_1694_;
}
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1697_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1679_, v___x_1705_, v___x_1706_, v___x_1684_, v_a_1677_);
lean_dec_ref(v_buckets_1679_);
v___y_1695_ = v___x_1707_;
goto v___jp_1694_;
}
}
v___jp_1686_:
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = lean_array_get_size(v_a_1688_);
v___x_1690_ = lean_nat_dec_eq(v___x_1685_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref(v___y_1687_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 1);
lean_ctor_set(v___x_1681_, 1, v_a_1688_);
lean_ctor_set(v___x_1681_, 0, v___x_1685_);
v___x_1692_ = v___x_1681_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_a_1688_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_dec_ref(v_a_1688_);
lean_del_object(v___x_1681_);
return v___y_1687_;
}
}
v___jp_1694_:
{
if (lean_obj_tag(v___y_1695_) == 0)
{
lean_object* v_a_1696_; 
v_a_1696_ = lean_ctor_get(v___y_1695_, 1);
lean_inc(v_a_1696_);
v___y_1687_ = v___y_1695_;
v_a_1688_ = v_a_1696_;
goto v___jp_1686_;
}
else
{
lean_del_object(v___x_1681_);
return v___y_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* v_map_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lake_CacheMap_collectOutputDescrs(v_map_1710_, v_a_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* v_init_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_st_mk_ref(v_init_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* v_init_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lake_CacheRef_mk(v_init_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t v_inputHash_1720_, lean_object* v_cache_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_st_ref_take(v_cache_1721_);
v___x_1724_ = l_Lake_CacheMap_get_x3f(v_inputHash_1720_, v___x_1723_);
v___x_1725_ = lean_st_ref_set(v_cache_1721_, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* v_inputHash_1726_, lean_object* v_cache_1727_, lean_object* v_a_1728_){
_start:
{
uint64_t v_inputHash_boxed_1729_; lean_object* v_res_1730_; 
v_inputHash_boxed_1729_ = lean_unbox_uint64(v_inputHash_1726_);
lean_dec_ref(v_inputHash_1726_);
v_res_1730_ = l_Lake_CacheRef_get_x3f(v_inputHash_boxed_1729_, v_cache_1727_);
lean_dec(v_cache_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* v_inst_1731_, uint64_t v_inputHash_1732_, lean_object* v_val_1733_, lean_object* v_cache_1734_, uint8_t v_platformIndependent_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = lean_st_ref_take(v_cache_1734_);
v___x_1738_ = lean_apply_1(v_inst_1731_, v_val_1733_);
v___x_1739_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1732_, v___x_1738_, v___x_1737_, v_platformIndependent_1735_);
v___x_1740_ = lean_st_ref_set(v_cache_1734_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* v_inst_1741_, lean_object* v_inputHash_1742_, lean_object* v_val_1743_, lean_object* v_cache_1744_, lean_object* v_platformIndependent_1745_, lean_object* v_a_1746_){
_start:
{
uint64_t v_inputHash_boxed_1747_; uint8_t v_platformIndependent_boxed_1748_; lean_object* v_res_1749_; 
v_inputHash_boxed_1747_ = lean_unbox_uint64(v_inputHash_1742_);
lean_dec_ref(v_inputHash_1742_);
v_platformIndependent_boxed_1748_ = lean_unbox(v_platformIndependent_1745_);
v_res_1749_ = l_Lake_CacheRef_insert___redArg(v_inst_1741_, v_inputHash_boxed_1747_, v_val_1743_, v_cache_1744_, v_platformIndependent_boxed_1748_);
lean_dec(v_cache_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* v_00_u03b1_1750_, lean_object* v_inst_1751_, uint64_t v_inputHash_1752_, lean_object* v_val_1753_, lean_object* v_cache_1754_, uint8_t v_platformIndependent_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = lean_st_ref_take(v_cache_1754_);
v___x_1758_ = lean_apply_1(v_inst_1751_, v_val_1753_);
v___x_1759_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1752_, v___x_1758_, v___x_1757_, v_platformIndependent_1755_);
v___x_1760_ = lean_st_ref_set(v_cache_1754_, v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_inst_1762_, lean_object* v_inputHash_1763_, lean_object* v_val_1764_, lean_object* v_cache_1765_, lean_object* v_platformIndependent_1766_, lean_object* v_a_1767_){
_start:
{
uint64_t v_inputHash_boxed_1768_; uint8_t v_platformIndependent_boxed_1769_; lean_object* v_res_1770_; 
v_inputHash_boxed_1768_ = lean_unbox_uint64(v_inputHash_1763_);
lean_dec_ref(v_inputHash_1763_);
v_platformIndependent_boxed_1769_ = lean_unbox(v_platformIndependent_1766_);
v_res_1770_ = l_Lake_CacheRef_insert(v_00_u03b1_1761_, v_inst_1762_, v_inputHash_boxed_1768_, v_val_1764_, v_cache_1765_, v_platformIndependent_boxed_1769_);
lean_dec(v_cache_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object* v_s_1773_){
_start:
{
lean_inc_ref(v_s_1773_);
return v_s_1773_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object* v_s_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lake_CacheServiceName_ofString(v_s_1774_);
lean_dec_ref(v_s_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object* v_self_1776_){
_start:
{
lean_inc_ref(v_self_1776_);
return v_self_1776_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object* v_self_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lake_CacheServiceName_toString(v_self_1777_);
lean_dec_ref(v_self_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object* v_j_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Json_getStr_x3f(v_j_1781_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1782_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1782_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object* v_self_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_self_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object* v_x_1805_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_unsigned_to_nat(1u);
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object* v_x_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(v_x_1808_);
lean_dec_ref(v_x_1808_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object* v_t_1810_, lean_object* v_k_1811_){
_start:
{
lean_object* v_s_1812_; lean_object* v___x_1813_; 
v_s_1812_ = lean_ctor_get(v_t_1810_, 0);
lean_inc_ref(v_s_1812_);
lean_dec_ref(v_t_1810_);
v___x_1813_ = lean_apply_1(v_k_1811_, v_s_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object* v_motive_1814_, lean_object* v_ctorIdx_1815_, lean_object* v_t_1816_, lean_object* v_h_1817_, lean_object* v_k_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1816_, v_k_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object* v_motive_1820_, lean_object* v_ctorIdx_1821_, lean_object* v_t_1822_, lean_object* v_h_1823_, lean_object* v_k_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(v_motive_1820_, v_ctorIdx_1821_, v_t_1822_, v_h_1823_, v_k_1824_);
lean_dec(v_ctorIdx_1821_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object* v_t_1826_, lean_object* v_str_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1826_, v_str_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object* v_motive_1829_, lean_object* v_t_1830_, lean_object* v_h_1831_, lean_object* v_str_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1830_, v_str_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object* v_t_1834_, lean_object* v_repo_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1834_, v_repo_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object* v_motive_1837_, lean_object* v_t_1838_, lean_object* v_h_1839_, lean_object* v_repo_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1838_, v_repo_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object* v_s_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_s_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object* v_fullName_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_fullName_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object* v_self_1846_){
_start:
{
if (lean_obj_tag(v_self_1846_) == 1)
{
uint8_t v___x_1847_; 
v___x_1847_ = 1;
return v___x_1847_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = 0;
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object* v_self_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Lake_CacheServiceScope_isRepo(v_self_1849_);
lean_dec_ref(v_self_1849_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object* v_self_1852_){
_start:
{
lean_object* v_s_1853_; 
v_s_1853_ = lean_ctor_get(v_self_1852_, 0);
lean_inc_ref(v_s_1853_);
return v_s_1853_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object* v_self_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lake_CacheServiceScope_toString(v_self_1854_);
lean_dec_ref(v_self_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object* v_self_1858_){
_start:
{
lean_object* v_s_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_s_1859_ = lean_ctor_get(v_self_1858_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_self_1858_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v_self_1858_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_s_1859_);
lean_dec(v_self_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 3);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_s_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object* v_data_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1878_, 0, v_data_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
lean_ctor_set(v___x_1878_, 2, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_box(0);
return v___x_1880_;
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
v_val_1881_ = lean_ctor_get(v_x_1879_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v_x_1879_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v_x_1879_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 3);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_val_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
static lean_object* _init_l_Lake_CacheOutput_toJson___closed__3(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__2));
v___x_1894_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1895_ = lean_box(1);
v___x_1896_ = l_Lake_JsonObject_insertJson(v___x_1895_, v___x_1894_, v___x_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object* v_out_1900_){
_start:
{
lean_object* v_data_1901_; lean_object* v_service_x3f_1902_; lean_object* v_scope_x3f_1903_; lean_object* v_obj_1905_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_obj_1912_; 
v_data_1901_ = lean_ctor_get(v_out_1900_, 0);
lean_inc(v_data_1901_);
v_service_x3f_1902_ = lean_ctor_get(v_out_1900_, 1);
lean_inc(v_service_x3f_1902_);
v_scope_x3f_1903_ = lean_ctor_get(v_out_1900_, 2);
lean_inc(v_scope_x3f_1903_);
lean_dec_ref(v_out_1900_);
v___x_1909_ = lean_obj_once(&l_Lake_CacheOutput_toJson___closed__3, &l_Lake_CacheOutput_toJson___closed__3_once, _init_l_Lake_CacheOutput_toJson___closed__3);
v___x_1910_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1911_ = l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1902_);
v_obj_1912_ = l_Lake_JsonObject_insertJson(v___x_1909_, v___x_1910_, v___x_1911_);
if (lean_obj_tag(v_scope_x3f_1903_) == 1)
{
lean_object* v_val_1913_; lean_object* v___y_1915_; uint8_t v___x_1918_; 
v_val_1913_ = lean_ctor_get(v_scope_x3f_1903_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v_scope_x3f_1903_);
v___x_1918_ = l_Lake_CacheServiceScope_isRepo(v_val_1913_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___y_1915_ = v___x_1919_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1920_; 
v___x_1920_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___y_1915_ = v___x_1920_;
goto v___jp_1914_;
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v_obj_1917_; 
v___x_1916_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(v_val_1913_);
v_obj_1917_ = l_Lake_JsonObject_insertJson(v_obj_1912_, v___y_1915_, v___x_1916_);
v_obj_1905_ = v_obj_1917_;
goto v___jp_1904_;
}
}
else
{
lean_dec(v_scope_x3f_1903_);
v_obj_1905_ = v_obj_1912_;
goto v___jp_1904_;
}
v___jp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1907_ = l_Lake_JsonObject_insertJson(v_obj_1905_, v___x_1906_, v_data_1901_);
v___x_1908_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Json_getStr_x3f(v_x_1925_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_a_1936_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v___x_1927_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1927_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1945_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Json_getStr_x3f(v_x_1945_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1964_; 
v_a_1956_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1958_ = v___x_1947_;
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1947_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1960_, 0, v_a_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object* v_k_1965_, lean_object* v_t_1966_){
_start:
{
if (lean_obj_tag(v_t_1966_) == 0)
{
lean_object* v_k_1967_; lean_object* v_l_1968_; lean_object* v_r_1969_; uint8_t v___x_1970_; 
v_k_1967_ = lean_ctor_get(v_t_1966_, 1);
v_l_1968_ = lean_ctor_get(v_t_1966_, 3);
v_r_1969_ = lean_ctor_get(v_t_1966_, 4);
v___x_1970_ = lean_string_dec_lt(v_k_1965_, v_k_1967_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_string_dec_eq(v_k_1965_, v_k_1967_);
if (v___x_1971_ == 0)
{
v_t_1966_ = v_r_1969_;
goto _start;
}
else
{
return v___x_1971_;
}
}
else
{
v_t_1966_ = v_l_1968_;
goto _start;
}
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = 0;
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object* v_k_1975_, lean_object* v_t_1976_){
_start:
{
uint8_t v_res_1977_; lean_object* v_r_1978_; 
v_res_1977_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1975_, v_t_1976_);
lean_dec(v_t_1976_);
lean_dec_ref(v_k_1975_);
v_r_1978_ = lean_box(v_res_1977_);
return v_r_1978_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object* v_json_1985_){
_start:
{
if (lean_obj_tag(v_json_1985_) == 5)
{
lean_object* v_kvPairs_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v_kvPairs_1990_ = lean_ctor_get(v_json_1985_, 0);
v___x_1991_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1992_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v___x_1991_, v_kvPairs_1990_);
if (v___x_1992_ == 0)
{
goto v___jp_1986_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_inc(v_kvPairs_1990_);
lean_dec_ref(v_json_1985_);
v___x_1993_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1994_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1990_, v___x_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; 
lean_dec(v_kvPairs_1990_);
v___x_1995_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__1));
return v___x_1995_;
}
else
{
lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2114_; 
v_val_1996_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_1998_ = v___x_1994_;
v_isShared_1999_ = v_isSharedCheck_2114_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v___x_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2114_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___y_2001_; lean_object* v_a_2002_; lean_object* v___y_2008_; lean_object* v___y_2011_; lean_object* v_a_2051_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_2091_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1990_, v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_box(0);
v_a_2051_ = v___x_2092_;
goto v___jp_2050_;
}
else
{
lean_object* v_val_2093_; lean_object* v___x_2094_; 
v_val_2093_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_val_2093_);
lean_dec_ref(v___x_2091_);
v___x_2094_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2104_; 
lean_del_object(v___x_1998_);
lean_dec(v_val_1996_);
lean_dec(v_kvPairs_1990_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2099_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__4));
v___x_2100_ = lean_string_append(v___x_2099_, v_a_2095_);
lean_dec(v_a_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2102_ = v___x_2097_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_del_object(v___x_1998_);
lean_dec(v_val_1996_);
lean_dec(v_kvPairs_1990_);
v_a_2105_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2094_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2094_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 0);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2094_);
v_a_2051_ = v_a_2113_;
goto v___jp_2050_;
}
}
}
v___jp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2003_, 0, v_val_1996_);
lean_ctor_set(v___x_2003_, 1, v___y_2001_);
lean_ctor_set(v___x_2003_, 2, v_a_2002_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2003_);
v___x_2005_ = v___x_1998_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
v___jp_2007_:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_box(0);
v___y_2001_ = v___y_2008_;
v_a_2002_ = v___x_2009_;
goto v___jp_2000_;
}
v___jp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___x_2013_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1990_, v___x_2012_);
lean_dec(v_kvPairs_1990_);
if (lean_obj_tag(v___x_2013_) == 0)
{
v___y_2008_ = v___y_2011_;
goto v___jp_2007_;
}
else
{
lean_object* v_val_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2049_; 
v_val_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2049_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_val_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2049_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_2014_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
lean_del_object(v___x_2016_);
lean_dec(v___y_2011_);
lean_del_object(v___x_1998_);
lean_dec(v_val_1996_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__2));
v___x_2024_ = lean_string_append(v___x_2023_, v_a_2019_);
lean_dec(v_a_2019_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_del_object(v___x_2016_);
lean_dec(v___y_2011_);
lean_del_object(v___x_1998_);
lean_dec(v_val_1996_);
v_a_2029_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2018_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2018_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 0);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2018_);
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_object* v_val_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2048_; 
v_val_2038_ = lean_ctor_get(v_a_2037_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2040_ = v_a_2037_;
v_isShared_2041_ = v_isSharedCheck_2048_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_val_2038_);
lean_dec(v_a_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2048_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 0);
lean_ctor_set(v___x_2016_, 0, v_val_2038_);
v___x_2043_ = v___x_2016_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_val_2038_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2043_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v___y_2001_ = v___y_2011_;
v_a_2002_ = v___x_2045_;
goto v___jp_2000_;
}
}
}
}
else
{
lean_dec(v_a_2037_);
lean_del_object(v___x_2016_);
v___y_2008_ = v___y_2011_;
goto v___jp_2007_;
}
}
}
}
}
}
v___jp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___x_2053_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1990_, v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
v___y_2011_ = v_a_2051_;
goto v___jp_2010_;
}
else
{
lean_object* v_val_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2089_; 
v_val_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2089_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_val_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2089_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_2054_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_2056_);
lean_dec(v_a_2051_);
lean_del_object(v___x_1998_);
lean_dec(v_val_1996_);
lean_dec(v_kvPairs_1990_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2068_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2063_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__3));
v___x_2064_ = lean_string_append(v___x_2063_, v_a_2059_);
lean_dec(v_a_2059_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_2056_);
lean_dec(v_a_2051_);
lean_del_object(v___x_1998_);
lean_dec(v_val_1996_);
lean_dec(v_kvPairs_1990_);
v_a_2069_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2058_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2058_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 0);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2058_);
if (lean_obj_tag(v_a_2077_) == 1)
{
lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_kvPairs_1990_);
v_val_2078_ = lean_ctor_get(v_a_2077_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2080_ = v_a_2077_;
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_dec(v_a_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v_val_2078_);
v___x_2083_ = v___x_2056_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_val_2078_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2085_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2083_);
v___x_2085_ = v___x_2080_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v___y_2001_ = v_a_2051_;
v_a_2002_ = v___x_2085_;
goto v___jp_2000_;
}
}
}
}
else
{
lean_dec(v_a_2077_);
lean_del_object(v___x_2056_);
v___y_2011_ = v_a_2051_;
goto v___jp_2010_;
}
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
goto v___jp_1986_;
}
v___jp_1986_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1988_, 0, v_json_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
lean_ctor_set(v___x_1988_, 2, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object* v_00_u03b2_2115_, lean_object* v_k_2116_, lean_object* v_t_2117_){
_start:
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_2116_, v_t_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object* v_00_u03b2_2119_, lean_object* v_k_2120_, lean_object* v_t_2121_){
_start:
{
uint8_t v_res_2122_; lean_object* v_r_2123_; 
v_res_2122_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(v_00_u03b2_2119_, v_k_2120_, v_t_2121_);
lean_dec(v_t_2121_);
lean_dec_ref(v_k_2120_);
v_r_2123_ = lean_box(v_res_2122_);
return v_r_2123_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache_default(void){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_System_instInhabitedFilePath_default;
return v___x_2126_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache(void){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_System_instInhabitedFilePath_default;
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2131_ = l_System_FilePath_join(v_cache_2129_, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_2133_, uint64_t v_contentHash_2134_, lean_object* v_ext_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2136_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2137_ = l_System_FilePath_join(v_cache_2133_, v___x_2136_);
v___x_2138_ = lean_string_utf8_byte_size(v_ext_2135_);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = lean_nat_dec_eq(v___x_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2141_ = l_Lake_Hash_hex(v_contentHash_2134_);
v___x_2142_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2143_ = lean_string_append(v___x_2141_, v___x_2142_);
v___x_2144_ = lean_string_append(v___x_2143_, v_ext_2135_);
v___x_2145_ = l_System_FilePath_join(v___x_2137_, v___x_2144_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = l_Lake_Hash_hex(v_contentHash_2134_);
v___x_2147_ = l_System_FilePath_join(v___x_2137_, v___x_2146_);
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_2148_, lean_object* v_contentHash_2149_, lean_object* v_ext_2150_){
_start:
{
uint64_t v_contentHash_boxed_2151_; lean_object* v_res_2152_; 
v_contentHash_boxed_2151_ = lean_unbox_uint64(v_contentHash_2149_);
lean_dec_ref(v_contentHash_2149_);
v_res_2152_ = l_Lake_Cache_artifactPath(v_cache_2148_, v_contentHash_boxed_2151_, v_ext_2150_);
lean_dec_ref(v_ext_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_2153_, lean_object* v_descr_2154_){
_start:
{
uint64_t v_hash_2156_; lean_object* v_ext_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___y_2161_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_hash_2156_ = lean_ctor_get_uint64(v_descr_2154_, sizeof(void*)*1);
v_ext_2157_ = lean_ctor_get(v_descr_2154_, 0);
v___x_2158_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2159_ = l_System_FilePath_join(v_cache_2153_, v___x_2158_);
v___x_2175_ = lean_string_utf8_byte_size(v_ext_2157_);
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_nat_dec_eq(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = l_Lake_Hash_hex(v_hash_2156_);
v___x_2179_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2180_ = lean_string_append(v___x_2178_, v___x_2179_);
v___x_2181_ = lean_string_append(v___x_2180_, v_ext_2157_);
v___y_2161_ = v___x_2181_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lake_Hash_hex(v_hash_2156_);
v___y_2161_ = v___x_2182_;
goto v___jp_2160_;
}
v___jp_2160_:
{
lean_object* v_path_2162_; lean_object* v___x_2163_; 
v_path_2162_ = l_System_FilePath_join(v___x_2159_, v___y_2161_);
v___x_2163_ = lean_io_metadata(v_path_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2173_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_modified_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v_modified_2168_ = lean_ctor_get(v_a_2164_, 1);
lean_inc_ref(v_modified_2168_);
lean_dec(v_a_2164_);
lean_inc_ref(v_path_2162_);
v___x_2169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2169_, 0, v_descr_2154_);
lean_ctor_set(v___x_2169_, 1, v_path_2162_);
lean_ctor_set(v___x_2169_, 2, v_path_2162_);
lean_ctor_set(v___x_2169_, 3, v_modified_2168_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v___x_2174_; 
lean_dec_ref(v___x_2163_);
lean_dec_ref(v_path_2162_);
lean_dec_ref(v_descr_2154_);
v___x_2174_ = lean_box(0);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_2183_, lean_object* v_descr_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lake_Cache_getArtifact_x3f(v_cache_2183_, v_descr_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_2189_, lean_object* v_descr_2190_){
_start:
{
uint64_t v_hash_2192_; lean_object* v_ext_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___y_2197_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_hash_2192_ = lean_ctor_get_uint64(v_descr_2190_, sizeof(void*)*1);
v_ext_2193_ = lean_ctor_get(v_descr_2190_, 0);
v___x_2194_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2195_ = l_System_FilePath_join(v_cache_2189_, v___x_2194_);
v___x_2226_ = lean_string_utf8_byte_size(v_ext_2193_);
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_nat_dec_eq(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = l_Lake_Hash_hex(v_hash_2192_);
v___x_2230_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
v___x_2232_ = lean_string_append(v___x_2231_, v_ext_2193_);
v___y_2197_ = v___x_2232_;
goto v___jp_2196_;
}
else
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lake_Hash_hex(v_hash_2192_);
v___y_2197_ = v___x_2233_;
goto v___jp_2196_;
}
v___jp_2196_:
{
lean_object* v_path_2198_; lean_object* v___x_2199_; 
v_path_2198_ = l_System_FilePath_join(v___x_2195_, v___y_2197_);
v___x_2199_ = lean_io_metadata(v_path_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2209_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_modified_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v_modified_2204_ = lean_ctor_get(v_a_2200_, 1);
lean_inc_ref(v_modified_2204_);
lean_dec(v_a_2200_);
lean_inc_ref(v_path_2198_);
v___x_2205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2205_, 0, v_descr_2190_);
lean_ctor_set(v___x_2205_, 1, v_path_2198_);
lean_ctor_set(v___x_2205_, 2, v_path_2198_);
lean_ctor_set(v___x_2205_, 3, v_modified_2204_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_descr_2190_);
v_a_2210_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2212_ = v___x_2199_;
v_isShared_2213_ = v_isSharedCheck_2225_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2199_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2225_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
if (lean_obj_tag(v_a_2210_) == 11)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec_ref(v_a_2210_);
v___x_2214_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2215_ = lean_string_append(v___x_2214_, v_path_2198_);
lean_dec_ref(v_path_2198_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2215_);
v___x_2217_ = v___x_2212_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
lean_dec_ref(v_path_2198_);
v___x_2219_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_2220_ = lean_io_error_to_string(v_a_2210_);
v___x_2221_ = lean_string_append(v___x_2219_, v___x_2220_);
lean_dec_ref(v___x_2220_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2221_);
v___x_2223_ = v___x_2212_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_2234_, lean_object* v_descr_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lake_Cache_getArtifact(v_cache_2234_, v_descr_2235_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object* v_cache_2238_, lean_object* v_out_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___y_2243_; lean_object* v___y_2244_; uint64_t v_hash_2246_; lean_object* v_ext_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___y_2251_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_hash_2246_ = lean_ctor_get_uint64(v_out_2239_, sizeof(void*)*1);
v_ext_2247_ = lean_ctor_get(v_out_2239_, 0);
v___x_2248_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2249_ = l_System_FilePath_join(v_cache_2238_, v___x_2248_);
v___x_2259_ = lean_string_utf8_byte_size(v_ext_2247_);
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = lean_nat_dec_eq(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = l_Lake_Hash_hex(v_hash_2246_);
v___x_2263_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_string_append(v___x_2264_, v_ext_2247_);
v___y_2251_ = v___x_2265_;
goto v___jp_2250_;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lake_Hash_hex(v_hash_2246_);
v___y_2251_ = v___x_2266_;
goto v___jp_2250_;
}
v___jp_2242_:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___y_2243_);
lean_ctor_set(v___x_2245_, 1, v___y_2244_);
return v___x_2245_;
}
v___jp_2250_:
{
lean_object* v_art_2252_; uint8_t v___x_2253_; 
v_art_2252_ = l_System_FilePath_join(v___x_2249_, v___y_2251_);
v___x_2253_ = l_System_FilePath_pathExists(v_art_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2254_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2255_ = lean_string_append(v___x_2254_, v_art_2252_);
v___x_2256_ = 3;
v___x_2257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1, v___x_2256_);
v___x_2258_ = lean_array_push(v___y_2240_, v___x_2257_);
v___y_2243_ = v_art_2252_;
v___y_2244_ = v___x_2258_;
goto v___jp_2242_;
}
else
{
v___y_2243_ = v_art_2252_;
v___y_2244_ = v___y_2240_;
goto v___jp_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object* v_cache_2267_, lean_object* v_out_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lake_Cache_getArtifactPaths___lam__0(v_cache_2267_, v_out_2268_, v___y_2269_);
lean_dec_ref(v_out_2268_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object* v_n_2272_, lean_object* v_f_2273_, lean_object* v_xs_2274_, lean_object* v_k_2275_, lean_object* v_acc_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v___x_2279_; 
v___x_2279_ = lean_nat_dec_lt(v_k_2275_, v_n_2272_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; 
lean_dec(v_k_2275_);
lean_dec_ref(v_f_2273_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v_acc_2276_);
lean_ctor_set(v___x_2280_, 1, v___y_2277_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_array_fget_borrowed(v_xs_2274_, v_k_2275_);
lean_inc_ref(v_f_2273_);
lean_inc(v___x_2281_);
v___x_2282_ = lean_apply_3(v_f_2273_, v___x_2281_, v___y_2277_, lean_box(0));
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
v_a_2284_ = lean_ctor_get(v___x_2282_, 1);
lean_inc(v_a_2284_);
lean_dec_ref(v___x_2282_);
v___x_2285_ = lean_unsigned_to_nat(1u);
v___x_2286_ = lean_nat_add(v_k_2275_, v___x_2285_);
lean_dec(v_k_2275_);
v___x_2287_ = lean_array_push(v_acc_2276_, v_a_2283_);
v_k_2275_ = v___x_2286_;
v_acc_2276_ = v___x_2287_;
v___y_2277_ = v_a_2284_;
goto _start;
}
else
{
lean_object* v_a_2289_; lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v_acc_2276_);
lean_dec(v_k_2275_);
lean_dec_ref(v_f_2273_);
v_a_2289_ = lean_ctor_get(v___x_2282_, 0);
v_a_2290_ = lean_ctor_get(v___x_2282_, 1);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2282_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_inc(v_a_2289_);
lean_dec(v___x_2282_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2289_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object* v_n_2298_, lean_object* v_f_2299_, lean_object* v_xs_2300_, lean_object* v_k_2301_, lean_object* v_acc_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2298_, v_f_2299_, v_xs_2300_, v_k_2301_, v_acc_2302_, v___y_2303_);
lean_dec_ref(v_xs_2300_);
lean_dec(v_n_2298_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object* v_cache_2308_, lean_object* v_descrs_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___f_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___f_2312_ = lean_alloc_closure((void*)(l_Lake_Cache_getArtifactPaths___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2312_, 0, v_cache_2308_);
v___x_2313_ = lean_array_get_size(v_descrs_2309_);
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_a_2310_);
v___x_2316_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v___x_2313_, v___f_2312_, v_descrs_2309_, v___x_2314_, v___x_2315_, v_a_2310_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 1);
lean_inc(v_a_2317_);
v___x_2318_ = lean_array_get_size(v_a_2310_);
lean_dec_ref(v_a_2310_);
v___x_2319_ = lean_array_get_size(v_a_2317_);
v___x_2320_ = lean_nat_dec_eq(v___x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; lean_object* v_unused_2329_; 
v_unused_2328_ = lean_ctor_get(v___x_2316_, 1);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v___x_2316_, 0);
lean_dec(v_unused_2329_);
v___x_2322_ = v___x_2316_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_dec(v___x_2316_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set_tag(v___x_2322_, 1);
lean_ctor_set(v___x_2322_, 0, v___x_2318_);
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_a_2317_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
else
{
lean_dec(v_a_2317_);
return v___x_2316_;
}
}
else
{
lean_dec_ref(v_a_2310_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object* v_cache_2330_, lean_object* v_descrs_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lake_Cache_getArtifactPaths(v_cache_2330_, v_descrs_2331_, v_a_2332_);
lean_dec_ref(v_descrs_2331_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object* v_00_u03b1_2335_, lean_object* v_00_u03b2_2336_, lean_object* v_n_2337_, lean_object* v_f_2338_, lean_object* v_xs_2339_, lean_object* v_k_2340_, lean_object* v_h_2341_, lean_object* v_acc_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2337_, v_f_2338_, v_xs_2339_, v_k_2340_, v_acc_2342_, v___y_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_00_u03b2_2347_, lean_object* v_n_2348_, lean_object* v_f_2349_, lean_object* v_xs_2350_, lean_object* v_k_2351_, lean_object* v_h_2352_, lean_object* v_acc_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(v_00_u03b1_2346_, v_00_u03b2_2347_, v_n_2348_, v_f_2349_, v_xs_2350_, v_k_2351_, v_h_2352_, v_acc_2353_, v___y_2354_);
lean_dec_ref(v_xs_2350_);
lean_dec(v_n_2348_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2360_ = l_System_FilePath_join(v_cache_2358_, v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2362_, lean_object* v_scope_2363_, uint64_t v_inputHash_2364_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2365_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2366_ = l_System_FilePath_join(v_cache_2362_, v___x_2365_);
v___x_2367_ = l_System_FilePath_join(v___x_2366_, v_scope_2363_);
v___x_2368_ = l_Lake_Hash_hex(v_inputHash_2364_);
v___x_2369_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
v___x_2371_ = l_System_FilePath_join(v___x_2367_, v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2372_, lean_object* v_scope_2373_, lean_object* v_inputHash_2374_){
_start:
{
uint64_t v_inputHash_boxed_2375_; lean_object* v_res_2376_; 
v_inputHash_boxed_2375_ = lean_unbox_uint64(v_inputHash_2374_);
lean_dec_ref(v_inputHash_2374_);
v_res_2376_ = l_Lake_Cache_outputsFile(v_cache_2372_, v_scope_2373_, v_inputHash_boxed_2375_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2377_, lean_object* v_scope_2378_, uint64_t v_inputHash_2379_, lean_object* v_out_2380_, lean_object* v_service_x3f_2381_, lean_object* v_remoteScope_x3f_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_file_2390_; lean_object* v___x_2391_; 
v___x_2384_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2385_ = l_System_FilePath_join(v_cache_2377_, v___x_2384_);
v___x_2386_ = l_System_FilePath_join(v___x_2385_, v_scope_2378_);
v___x_2387_ = l_Lake_Hash_hex(v_inputHash_2379_);
v___x_2388_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2389_ = lean_string_append(v___x_2387_, v___x_2388_);
v_file_2390_ = l_System_FilePath_join(v___x_2386_, v___x_2389_);
lean_inc_ref(v_file_2390_);
v___x_2391_ = l_Lake_createParentDirs(v_file_2390_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec_ref(v___x_2391_);
v___x_2392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2392_, 0, v_out_2380_);
lean_ctor_set(v___x_2392_, 1, v_service_x3f_2381_);
lean_ctor_set(v___x_2392_, 2, v_remoteScope_x3f_2382_);
v___x_2393_ = l_Lake_CacheOutput_toJson(v___x_2392_);
v___x_2394_ = lean_unsigned_to_nat(80u);
v___x_2395_ = l_Lean_Json_pretty(v___x_2393_, v___x_2394_);
v___x_2396_ = l_IO_FS_writeFile(v_file_2390_, v___x_2395_);
lean_dec_ref(v___x_2395_);
lean_dec_ref(v_file_2390_);
return v___x_2396_;
}
else
{
lean_dec_ref(v_file_2390_);
lean_dec(v_remoteScope_x3f_2382_);
lean_dec(v_service_x3f_2381_);
lean_dec(v_out_2380_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2397_, lean_object* v_scope_2398_, lean_object* v_inputHash_2399_, lean_object* v_out_2400_, lean_object* v_service_x3f_2401_, lean_object* v_remoteScope_x3f_2402_, lean_object* v_a_2403_){
_start:
{
uint64_t v_inputHash_boxed_2404_; lean_object* v_res_2405_; 
v_inputHash_boxed_2404_ = lean_unbox_uint64(v_inputHash_2399_);
lean_dec_ref(v_inputHash_2399_);
v_res_2405_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2397_, v_scope_2398_, v_inputHash_boxed_2404_, v_out_2400_, v_service_x3f_2401_, v_remoteScope_x3f_2402_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2406_, lean_object* v_cache_2407_, lean_object* v_scope_2408_, uint64_t v_inputHash_2409_, lean_object* v_outputs_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_apply_1(v_inst_2406_, v_outputs_2410_);
v___x_2413_ = lean_box(0);
v___x_2414_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2407_, v_scope_2408_, v_inputHash_2409_, v___x_2412_, v___x_2413_, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2415_, lean_object* v_cache_2416_, lean_object* v_scope_2417_, lean_object* v_inputHash_2418_, lean_object* v_outputs_2419_, lean_object* v_a_2420_){
_start:
{
uint64_t v_inputHash_boxed_2421_; lean_object* v_res_2422_; 
v_inputHash_boxed_2421_ = lean_unbox_uint64(v_inputHash_2418_);
lean_dec_ref(v_inputHash_2418_);
v_res_2422_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2415_, v_cache_2416_, v_scope_2417_, v_inputHash_boxed_2421_, v_outputs_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2423_, lean_object* v_inst_2424_, lean_object* v_cache_2425_, lean_object* v_scope_2426_, uint64_t v_inputHash_2427_, lean_object* v_outputs_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_apply_1(v_inst_2424_, v_outputs_2428_);
v___x_2431_ = lean_box(0);
v___x_2432_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2425_, v_scope_2426_, v_inputHash_2427_, v___x_2430_, v___x_2431_, v___x_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2433_, lean_object* v_inst_2434_, lean_object* v_cache_2435_, lean_object* v_scope_2436_, lean_object* v_inputHash_2437_, lean_object* v_outputs_2438_, lean_object* v_a_2439_){
_start:
{
uint64_t v_inputHash_boxed_2440_; lean_object* v_res_2441_; 
v_inputHash_boxed_2440_ = lean_unbox_uint64(v_inputHash_2437_);
lean_dec_ref(v_inputHash_2437_);
v_res_2441_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2433_, v_inst_2434_, v_cache_2435_, v_scope_2436_, v_inputHash_boxed_2440_, v_outputs_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2442_, lean_object* v_scope_2443_, lean_object* v_service_x3f_2444_, lean_object* v_remoteScope_x3f_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
if (lean_obj_tag(v_x_2447_) == 0)
{
lean_object* v___x_2449_; 
lean_dec(v_remoteScope_x3f_2445_);
lean_dec(v_service_x3f_2444_);
lean_dec_ref(v_scope_2443_);
lean_dec_ref(v_cache_2442_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_x_2446_);
return v___x_2449_;
}
else
{
lean_object* v_value_2450_; lean_object* v_key_2451_; lean_object* v_tail_2452_; lean_object* v_out_2453_; uint64_t v___x_2454_; lean_object* v___x_2455_; 
v_value_2450_ = lean_ctor_get(v_x_2447_, 1);
lean_inc(v_value_2450_);
v_key_2451_ = lean_ctor_get(v_x_2447_, 0);
lean_inc(v_key_2451_);
v_tail_2452_ = lean_ctor_get(v_x_2447_, 2);
lean_inc(v_tail_2452_);
lean_dec_ref(v_x_2447_);
v_out_2453_ = lean_ctor_get(v_value_2450_, 0);
lean_inc(v_out_2453_);
lean_dec(v_value_2450_);
v___x_2454_ = lean_unbox_uint64(v_key_2451_);
lean_dec(v_key_2451_);
lean_inc(v_remoteScope_x3f_2445_);
lean_inc(v_service_x3f_2444_);
lean_inc_ref(v_scope_2443_);
lean_inc_ref(v_cache_2442_);
v___x_2455_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2442_, v_scope_2443_, v___x_2454_, v_out_2453_, v_service_x3f_2444_, v_remoteScope_x3f_2445_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v_x_2446_ = v_a_2456_;
v_x_2447_ = v_tail_2452_;
goto _start;
}
else
{
lean_dec(v_tail_2452_);
lean_dec(v_remoteScope_x3f_2445_);
lean_dec(v_service_x3f_2444_);
lean_dec_ref(v_scope_2443_);
lean_dec_ref(v_cache_2442_);
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2458_, lean_object* v_scope_2459_, lean_object* v_service_x3f_2460_, lean_object* v_remoteScope_x3f_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2458_, v_scope_2459_, v_service_x3f_2460_, v_remoteScope_x3f_2461_, v_x_2462_, v_x_2463_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2466_, lean_object* v_scope_2467_, lean_object* v_service_x3f_2468_, lean_object* v_remoteScope_x3f_2469_, lean_object* v_as_2470_, size_t v_i_2471_, size_t v_stop_2472_, lean_object* v_b_2473_){
_start:
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_usize_dec_eq(v_i_2471_, v_stop_2472_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_array_uget_borrowed(v_as_2470_, v_i_2471_);
v___x_2477_ = lean_box(0);
lean_inc(v___x_2476_);
lean_inc(v_remoteScope_x3f_2469_);
lean_inc(v_service_x3f_2468_);
lean_inc_ref(v_scope_2467_);
lean_inc_ref(v_cache_2466_);
v___x_2478_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2466_, v_scope_2467_, v_service_x3f_2468_, v_remoteScope_x3f_2469_, v___x_2477_, v___x_2476_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; size_t v___x_2480_; size_t v___x_2481_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2471_, v___x_2480_);
v_i_2471_ = v___x_2481_;
v_b_2473_ = v_a_2479_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2469_);
lean_dec(v_service_x3f_2468_);
lean_dec_ref(v_scope_2467_);
lean_dec_ref(v_cache_2466_);
return v___x_2478_;
}
}
else
{
lean_object* v___x_2483_; 
lean_dec(v_remoteScope_x3f_2469_);
lean_dec(v_service_x3f_2468_);
lean_dec_ref(v_scope_2467_);
lean_dec_ref(v_cache_2466_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_b_2473_);
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2484_, lean_object* v_scope_2485_, lean_object* v_service_x3f_2486_, lean_object* v_remoteScope_x3f_2487_, lean_object* v_as_2488_, lean_object* v_i_2489_, lean_object* v_stop_2490_, lean_object* v_b_2491_, lean_object* v___y_2492_){
_start:
{
size_t v_i_boxed_2493_; size_t v_stop_boxed_2494_; lean_object* v_res_2495_; 
v_i_boxed_2493_ = lean_unbox_usize(v_i_2489_);
lean_dec(v_i_2489_);
v_stop_boxed_2494_ = lean_unbox_usize(v_stop_2490_);
lean_dec(v_stop_2490_);
v_res_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2484_, v_scope_2485_, v_service_x3f_2486_, v_remoteScope_x3f_2487_, v_as_2488_, v_i_boxed_2493_, v_stop_boxed_2494_, v_b_2491_);
lean_dec_ref(v_as_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2496_, lean_object* v_scope_2497_, lean_object* v_map_2498_, lean_object* v_service_x3f_2499_, lean_object* v_remoteScope_x3f_2500_){
_start:
{
lean_object* v_buckets_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_buckets_2502_ = lean_ctor_get(v_map_2498_, 1);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = lean_array_get_size(v_buckets_2502_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_nat_dec_lt(v___x_2503_, v___x_2504_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
lean_dec(v_remoteScope_x3f_2500_);
lean_dec(v_service_x3f_2499_);
lean_dec_ref(v_scope_2497_);
lean_dec_ref(v_cache_2496_);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
return v___x_2507_;
}
else
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_nat_dec_le(v___x_2504_, v___x_2504_);
if (v___x_2508_ == 0)
{
if (v___x_2506_ == 0)
{
lean_object* v___x_2509_; 
lean_dec(v_remoteScope_x3f_2500_);
lean_dec(v_service_x3f_2499_);
lean_dec_ref(v_scope_2497_);
lean_dec_ref(v_cache_2496_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2505_);
return v___x_2509_;
}
else
{
size_t v___x_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = lean_usize_of_nat(v___x_2504_);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2496_, v_scope_2497_, v_service_x3f_2499_, v_remoteScope_x3f_2500_, v_buckets_2502_, v___x_2510_, v___x_2511_, v___x_2505_);
return v___x_2512_;
}
}
else
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = lean_usize_of_nat(v___x_2504_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2496_, v_scope_2497_, v_service_x3f_2499_, v_remoteScope_x3f_2500_, v_buckets_2502_, v___x_2513_, v___x_2514_, v___x_2505_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2516_, lean_object* v_scope_2517_, lean_object* v_map_2518_, lean_object* v_service_x3f_2519_, lean_object* v_remoteScope_x3f_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lake_Cache_writeMap(v_cache_2516_, v_scope_2517_, v_map_2518_, v_service_x3f_2519_, v_remoteScope_x3f_2520_);
lean_dec_ref(v_map_2518_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2525_){
_start:
{
if (lean_obj_tag(v_x_2525_) == 0)
{
lean_object* v___x_2526_; 
v___x_2526_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
return v___x_2526_;
}
else
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lake_CacheOutput_fromJson_x3f(v_x_2525_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
v_a_2536_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v___x_2527_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2527_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2547_, lean_object* v_scope_2548_, uint64_t v_inputHash_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v_path_2558_; lean_object* v___x_2559_; 
v___x_2552_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2553_ = l_System_FilePath_join(v_cache_2547_, v___x_2552_);
v___x_2554_ = l_System_FilePath_join(v___x_2553_, v_scope_2548_);
v___x_2555_ = l_Lake_Hash_hex(v_inputHash_2549_);
v___x_2556_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2557_ = lean_string_append(v___x_2555_, v___x_2556_);
v_path_2558_ = l_System_FilePath_join(v___x_2554_, v___x_2557_);
v___x_2559_ = l_IO_FS_readFile(v_path_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v_a_2562_; lean_object* v___x_2571_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2559_);
v___x_2571_ = l_Lean_Json_parse(v_a_2560_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v_a_2562_ = v_a_2572_;
goto v___jp_2561_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2574_; 
v_a_2573_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2573_);
lean_dec_ref(v___x_2571_);
v___x_2574_ = l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2573_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2574_);
v_a_2562_ = v_a_2575_;
goto v___jp_2561_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v_path_2558_);
v_a_2576_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2574_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_a_2576_);
lean_ctor_set(v___x_2577_, 1, v_a_2550_);
return v___x_2577_;
}
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2563_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2564_ = lean_string_append(v_path_2558_, v___x_2563_);
v___x_2565_ = lean_string_append(v___x_2564_, v_a_2562_);
lean_dec_ref(v_a_2562_);
v___x_2566_ = 2;
v___x_2567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*1, v___x_2566_);
v___x_2568_ = lean_array_push(v_a_2550_, v___x_2567_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v___x_2568_);
return v___x_2570_;
}
}
else
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2559_);
if (lean_obj_tag(v_a_2578_) == 11)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec_ref(v_a_2578_);
lean_dec_ref(v_path_2558_);
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v_a_2550_);
return v___x_2580_;
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2581_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2582_ = lean_string_append(v_path_2558_, v___x_2581_);
v___x_2583_ = lean_io_error_to_string(v_a_2578_);
v___x_2584_ = lean_string_append(v___x_2582_, v___x_2583_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = 3;
v___x_2586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set_uint8(v___x_2586_, sizeof(void*)*1, v___x_2585_);
v___x_2587_ = lean_array_get_size(v_a_2550_);
v___x_2588_ = lean_array_push(v_a_2550_, v___x_2586_);
v___x_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2590_, lean_object* v_scope_2591_, lean_object* v_inputHash_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
uint64_t v_inputHash_boxed_2595_; lean_object* v_res_2596_; 
v_inputHash_boxed_2595_ = lean_unbox_uint64(v_inputHash_2592_);
lean_dec_ref(v_inputHash_2592_);
v_res_2596_ = l_Lake_Cache_readOutputs_x3f(v_cache_2590_, v_scope_2591_, v_inputHash_boxed_2595_, v_a_2593_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2598_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2600_ = l_System_FilePath_join(v_cache_2598_, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2602_, lean_object* v_scope_2603_, lean_object* v_rev_2604_){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2605_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2606_ = l_System_FilePath_join(v_cache_2602_, v___x_2605_);
v___x_2607_ = l_System_FilePath_join(v___x_2606_, v_scope_2603_);
v___x_2608_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2609_ = lean_string_append(v_rev_2604_, v___x_2608_);
v___x_2610_ = l_System_FilePath_join(v___x_2607_, v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2613_){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2614_ = lean_string_utf8_byte_size(v_self_2613_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_nat_dec_eq(v___x_2614_, v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2617_){
_start:
{
uint8_t v_res_2618_; lean_object* v_r_2619_; 
v_res_2618_ = l_Lake_CachePlatform_isNone(v_self_2617_);
lean_dec_ref(v_self_2617_);
v_r_2619_ = lean_box(v_res_2618_);
return v_r_2619_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_System_Platform_target;
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2621_){
_start:
{
lean_inc_ref(v_s_2621_);
return v_s_2621_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lake_CachePlatform_ofString(v_s_2622_);
lean_dec_ref(v_s_2622_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_string_length(v_self_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object* v_self_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lake_CachePlatform_length(v_self_2626_);
lean_dec_ref(v_self_2626_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2629_){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2630_ = lean_string_utf8_byte_size(v_self_2629_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_nat_dec_eq(v___x_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_inc_ref(v_self_2629_);
return v_self_2629_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lake_CachePlatform_toString(v_self_2634_);
lean_dec_ref(v_self_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = lean_string_utf8_byte_size(v_self_2639_);
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = lean_nat_dec_eq(v___x_2640_, v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2643_){
_start:
{
uint8_t v_res_2644_; lean_object* v_r_2645_; 
v_res_2644_ = l_Lake_CacheToolchain_isNone(v_self_2643_);
lean_dec_ref(v_self_2643_);
v_r_2645_ = lean_box(v_res_2644_);
return v_r_2645_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lake_normalizeToolchain(v_s_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2648_){
_start:
{
lean_inc_ref(v_s_2648_);
return v_s_2648_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2649_);
lean_dec_ref(v_s_2649_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_string_length(v_self_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object* v_self_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lake_CacheToolchain_length(v_self_2653_);
lean_dec_ref(v_self_2653_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2656_ = lean_string_utf8_byte_size(v_self_2655_);
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = lean_nat_dec_eq(v___x_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_inc_ref(v_self_2655_);
return v_self_2655_;
}
else
{
lean_object* v___x_2659_; 
v___x_2659_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lake_CacheToolchain_toString(v_self_2660_);
lean_dec_ref(v_self_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2665_, lean_object* v_url_2666_, lean_object* v_path_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_path_2667_);
v___x_2671_ = l_Lake_download(v_url_2666_, v_path_2667_, v___x_2670_, v_a_2668_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2711_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; 
v_unused_2712_ = lean_ctor_get(v___x_2671_, 0);
lean_dec(v_unused_2712_);
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2711_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2711_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lake_computeBinFileHash(v_path_2667_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; uint64_t v___x_2678_; uint8_t v___x_2679_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = lean_unbox_uint64(v_a_2677_);
lean_dec(v_a_2677_);
v___x_2679_ = lean_uint64_dec_eq(v___x_2678_, v_hash_2665_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2680_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2667_);
v___x_2681_ = lean_string_append(v_path_2667_, v___x_2680_);
v___x_2682_ = 3;
v___x_2683_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*1, v___x_2682_);
v___x_2684_ = lean_array_push(v_a_2672_, v___x_2683_);
v___x_2685_ = lean_io_remove_file(v_path_2667_);
lean_dec_ref(v_path_2667_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
lean_dec_ref(v___x_2685_);
v___x_2686_ = lean_array_get_size(v___x_2684_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 1);
lean_ctor_set(v___x_2674_, 1, v___x_2684_);
lean_ctor_set(v___x_2674_, 0, v___x_2686_);
v___x_2688_ = v___x_2674_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2684_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v_a_2690_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2685_);
v___x_2691_ = lean_io_error_to_string(v_a_2690_);
v___x_2692_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*1, v___x_2682_);
v___x_2693_ = lean_array_get_size(v___x_2684_);
v___x_2694_ = lean_array_push(v___x_2684_, v___x_2692_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 1);
lean_ctor_set(v___x_2674_, 1, v___x_2694_);
lean_ctor_set(v___x_2674_, 0, v___x_2693_);
v___x_2696_ = v___x_2674_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec_ref(v_path_2667_);
v___x_2698_ = lean_box(0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2698_);
v___x_2700_ = v___x_2674_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_a_2672_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
lean_dec_ref(v_path_2667_);
v_a_2702_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2676_);
v___x_2703_ = lean_io_error_to_string(v_a_2702_);
v___x_2704_ = 3;
v___x_2705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set_uint8(v___x_2705_, sizeof(void*)*1, v___x_2704_);
v___x_2706_ = lean_array_get_size(v_a_2672_);
v___x_2707_ = lean_array_push(v_a_2672_, v___x_2705_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 1);
lean_ctor_set(v___x_2674_, 1, v___x_2707_);
lean_ctor_set(v___x_2674_, 0, v___x_2706_);
v___x_2709_ = v___x_2674_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_dec_ref(v_path_2667_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2713_, lean_object* v_url_2714_, lean_object* v_path_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
uint64_t v_hash_boxed_2718_; lean_object* v_res_2719_; 
v_hash_boxed_2718_ = lean_unbox_uint64(v_hash_2713_);
lean_dec_ref(v_hash_2713_);
v_res_2719_ = l_Lake_downloadArtifactCore(v_hash_boxed_2718_, v_url_2714_, v_path_2715_, v_a_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2722_){
_start:
{
if (lean_obj_tag(v_x_2722_) == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Json_getNat_x3f(v_x_2722_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2741_; 
v_a_2733_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2735_ = v___x_2724_;
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2724_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2733_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2737_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2764_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2765_ = lean_unsigned_to_nat(14u);
v___x_2766_ = lean_mk_empty_array_with_capacity(v___x_2765_);
v___x_2767_ = lean_array_push(v___x_2766_, v___x_2764_);
return v___x_2767_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2769_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2770_ = lean_array_push(v___x_2769_, v___x_2768_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2772_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2773_ = lean_array_push(v___x_2772_, v___x_2771_);
return v___x_2773_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2775_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2776_ = lean_array_push(v___x_2775_, v___x_2774_);
return v___x_2776_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2777_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2778_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2779_ = lean_array_push(v___x_2778_, v___x_2777_);
return v___x_2779_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2781_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2782_ = lean_array_push(v___x_2781_, v___x_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2786_, lean_object* v_contentType_2787_, lean_object* v_url_2788_, lean_object* v_key_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___y_2793_; lean_object* v_a_2794_; lean_object* v_stderr_2807_; lean_object* v___y_2816_; lean_object* v___y_2819_; lean_object* v_a_2820_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v_stderr_2859_; lean_object* v_a_2860_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2874_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2875_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2876_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2877_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2878_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2879_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2880_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2881_ = lean_string_append(v___x_2880_, v_contentType_2787_);
v___x_2882_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2883_ = lean_array_push(v___x_2882_, v_key_2789_);
v___x_2884_ = lean_array_push(v___x_2883_, v___x_2876_);
v___x_2885_ = lean_array_push(v___x_2884_, v___x_2877_);
v___x_2886_ = lean_array_push(v___x_2885_, v___x_2878_);
v___x_2887_ = lean_array_push(v___x_2886_, v_file_2786_);
v___x_2888_ = lean_array_push(v___x_2887_, v_url_2788_);
v___x_2889_ = lean_array_push(v___x_2888_, v___x_2879_);
v___x_2890_ = lean_array_push(v___x_2889_, v___x_2881_);
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2894_ = 1;
v___x_2895_ = 0;
v___x_2896_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2896_, 0, v___x_2874_);
lean_ctor_set(v___x_2896_, 1, v___x_2875_);
lean_ctor_set(v___x_2896_, 2, v___x_2890_);
lean_ctor_set(v___x_2896_, 3, v___x_2891_);
lean_ctor_set(v___x_2896_, 4, v___x_2893_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*5, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*5 + 1, v___x_2895_);
v___x_2897_ = l_Lake_captureProc_x27(v___x_2896_, v___x_2893_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_a_2899_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
v_a_2899_ = lean_ctor_get(v___x_2897_, 1);
lean_inc(v_a_2899_);
lean_dec_ref(v___x_2897_);
v___x_2913_ = lean_array_get_size(v_a_2899_);
v___x_2914_ = lean_nat_dec_lt(v___x_2892_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_dec(v_a_2899_);
goto v___jp_2900_;
}
else
{
lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = lean_box(0);
v___x_2916_ = lean_nat_dec_le(v___x_2913_, v___x_2913_);
if (v___x_2916_ == 0)
{
if (v___x_2914_ == 0)
{
lean_dec(v_a_2899_);
goto v___jp_2900_;
}
else
{
size_t v___x_2917_; size_t v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = ((size_t)0ULL);
v___x_2918_ = lean_usize_of_nat(v___x_2913_);
lean_inc_ref(v_a_2790_);
v___x_2919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2899_, v___x_2917_, v___x_2918_, v___x_2915_, v_a_2790_);
lean_dec(v_a_2899_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_dec_ref(v___x_2919_);
goto v___jp_2900_;
}
else
{
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2790_);
return v___x_2919_;
}
}
}
else
{
size_t v___x_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = lean_usize_of_nat(v___x_2913_);
lean_inc_ref(v_a_2790_);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2899_, v___x_2920_, v___x_2921_, v___x_2915_, v_a_2790_);
lean_dec(v_a_2899_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_dec_ref(v___x_2922_);
goto v___jp_2900_;
}
else
{
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2790_);
return v___x_2922_;
}
}
}
v___jp_2900_:
{
lean_object* v_stderr_2901_; lean_object* v___x_2902_; 
v_stderr_2901_ = lean_ctor_get(v_a_2898_, 1);
lean_inc_ref(v_stderr_2901_);
v___x_2902_ = l_Lean_Json_parse(v_stderr_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; 
lean_inc_ref(v_stderr_2901_);
lean_dec(v_a_2898_);
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref(v___x_2902_);
v_stderr_2859_ = v_stderr_2901_;
v_a_2860_ = v_a_2903_;
goto v___jp_2858_;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2902_);
v___x_2905_ = l_Lean_Json_getObj_x3f(v_a_2904_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; 
lean_inc_ref(v_stderr_2901_);
lean_dec(v_a_2898_);
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v_stderr_2859_ = v_stderr_2901_;
v_a_2860_ = v_a_2906_;
goto v___jp_2858_;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2907_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2905_);
v___x_2908_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2909_ = l_Lake_JsonObject_getJson_x3f(v_a_2907_, v___x_2908_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_inc_ref(v_stderr_2901_);
lean_dec(v_a_2907_);
lean_dec(v_a_2898_);
v_stderr_2807_ = v_stderr_2901_;
goto v___jp_2806_;
}
else
{
lean_object* v_val_2910_; lean_object* v___x_2911_; 
v_val_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2910_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_dec_ref(v___x_2911_);
v___y_2847_ = v_a_2898_;
v___y_2848_ = v_a_2907_;
goto v___jp_2846_;
}
else
{
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_dec_ref(v___x_2911_);
v___y_2847_ = v_a_2898_;
v___y_2848_ = v_a_2907_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2912_; 
lean_dec(v_a_2907_);
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___x_2911_);
v___y_2819_ = v_a_2898_;
v_a_2820_ = v_a_2912_;
goto v___jp_2818_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v_a_2923_ = lean_ctor_get(v___x_2897_, 1);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2897_);
v___x_2924_ = lean_array_get_size(v_a_2923_);
v___x_2925_ = lean_nat_dec_lt(v___x_2892_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2790_);
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_nat_dec_le(v___x_2924_, v___x_2924_);
if (v___x_2929_ == 0)
{
if (v___x_2925_ == 0)
{
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2790_);
goto v___jp_2871_;
}
else
{
size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = ((size_t)0ULL);
v___x_2931_ = lean_usize_of_nat(v___x_2924_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2923_, v___x_2930_, v___x_2931_, v___x_2928_, v_a_2790_);
lean_dec(v_a_2923_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_dec_ref(v___x_2932_);
goto v___jp_2871_;
}
else
{
return v___x_2932_;
}
}
}
else
{
size_t v___x_2933_; size_t v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = ((size_t)0ULL);
v___x_2934_ = lean_usize_of_nat(v___x_2924_);
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2923_, v___x_2933_, v___x_2934_, v___x_2928_, v_a_2790_);
lean_dec(v_a_2923_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_dec_ref(v___x_2935_);
goto v___jp_2871_;
}
else
{
return v___x_2935_;
}
}
}
}
v___jp_2792_:
{
lean_object* v_stderr_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_stderr_2795_ = lean_ctor_get(v___y_2793_, 1);
lean_inc_ref(v_stderr_2795_);
lean_dec_ref(v___y_2793_);
v___x_2796_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2797_ = lean_string_append(v___x_2796_, v_a_2794_);
lean_dec_ref(v_a_2794_);
v___x_2798_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2799_ = lean_string_append(v___x_2797_, v___x_2798_);
v___x_2800_ = lean_string_append(v___x_2799_, v_stderr_2795_);
lean_dec_ref(v_stderr_2795_);
v___x_2801_ = 3;
v___x_2802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1, v___x_2801_);
v___x_2803_ = lean_apply_2(v_a_2790_, v___x_2802_, lean_box(0));
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
v___jp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2808_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2809_ = lean_string_append(v___x_2808_, v_stderr_2807_);
lean_dec_ref(v_stderr_2807_);
v___x_2810_ = 3;
v___x_2811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1, v___x_2810_);
v___x_2812_ = lean_apply_2(v_a_2790_, v___x_2811_, lean_box(0));
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
v___jp_2815_:
{
lean_object* v_stderr_2817_; 
v_stderr_2817_ = lean_ctor_get(v___y_2816_, 1);
lean_inc_ref(v_stderr_2817_);
lean_dec_ref(v___y_2816_);
v_stderr_2807_ = v_stderr_2817_;
goto v___jp_2806_;
}
v___jp_2818_:
{
if (lean_obj_tag(v_a_2820_) == 0)
{
v___y_2816_ = v___y_2819_;
goto v___jp_2815_;
}
else
{
lean_object* v_val_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2845_; 
v_val_2821_ = lean_ctor_get(v_a_2820_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_a_2820_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2823_ = v_a_2820_;
v_isShared_2824_ = v_isSharedCheck_2845_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_val_2821_);
lean_dec(v_a_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2845_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_unsigned_to_nat(200u);
v___x_2826_ = lean_nat_dec_eq(v_val_2821_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v_stdout_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v_stdout_2827_ = lean_ctor_get(v___y_2819_, 0);
lean_inc_ref(v_stdout_2827_);
lean_dec_ref(v___y_2819_);
v___x_2828_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2829_ = l_Nat_reprFast(v_val_2821_);
v___x_2830_ = lean_string_append(v___x_2828_, v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2832_ = lean_string_append(v___x_2830_, v___x_2831_);
v___x_2833_ = lean_string_append(v___x_2832_, v_stdout_2827_);
lean_dec_ref(v_stdout_2827_);
v___x_2834_ = 3;
v___x_2835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set_uint8(v___x_2835_, sizeof(void*)*1, v___x_2834_);
v___x_2836_ = lean_apply_2(v_a_2790_, v___x_2835_, lean_box(0));
v___x_2837_ = lean_box(0);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2837_);
v___x_2839_ = v___x_2823_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
lean_dec(v_val_2821_);
lean_dec_ref(v___y_2819_);
lean_dec_ref(v_a_2790_);
v___x_2841_ = lean_box(0);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2841_);
v___x_2843_ = v___x_2823_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
v___jp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2850_ = l_Lake_JsonObject_getJson_x3f(v___y_2848_, v___x_2849_);
lean_dec(v___y_2848_);
if (lean_obj_tag(v___x_2850_) == 0)
{
v___y_2816_ = v___y_2847_;
goto v___jp_2815_;
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2852_; 
v_val_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_val_2851_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2855_ = lean_string_append(v___x_2854_, v_a_2853_);
lean_dec(v_a_2853_);
v___y_2793_ = v___y_2847_;
v_a_2794_ = v___x_2855_;
goto v___jp_2792_;
}
else
{
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2852_);
v___y_2793_ = v___y_2847_;
v_a_2794_ = v_a_2856_;
goto v___jp_2792_;
}
else
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2857_);
lean_dec_ref(v___x_2852_);
v___y_2819_ = v___y_2847_;
v_a_2820_ = v_a_2857_;
goto v___jp_2818_;
}
}
}
}
v___jp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2861_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2862_ = lean_string_append(v___x_2861_, v_a_2860_);
lean_dec_ref(v_a_2860_);
v___x_2863_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2864_ = lean_string_append(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_string_append(v___x_2864_, v_stderr_2859_);
lean_dec_ref(v_stderr_2859_);
v___x_2866_ = 3;
v___x_2867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*1, v___x_2866_);
v___x_2868_ = lean_apply_2(v_a_2790_, v___x_2867_, lean_box(0));
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
v___jp_2871_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2936_, lean_object* v_contentType_2937_, lean_object* v_url_2938_, lean_object* v_key_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2936_, v_contentType_2937_, v_url_2938_, v_key_2939_, v_a_2940_);
lean_dec_ref(v_contentType_2937_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2943_){
_start:
{
lean_object* v_name_x3f_2944_; 
v_name_x3f_2944_ = lean_ctor_get(v_service_2943_, 0);
lean_inc(v_name_x3f_2944_);
return v_name_x3f_2944_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lake_CacheService_name_x3f(v_service_2945_);
lean_dec_ref(v_service_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2947_){
_start:
{
uint8_t v_isReservoir_2948_; 
v_isReservoir_2948_ = lean_ctor_get_uint8(v_service_2947_, sizeof(void*)*5);
return v_isReservoir_2948_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2949_){
_start:
{
uint8_t v_res_2950_; lean_object* v_r_2951_; 
v_res_2950_ = l_Lake_CacheService_isReservoir(v_service_2949_);
lean_dec_ref(v_service_2949_);
v_r_2951_ = lean_box(v_res_2950_);
return v_r_2951_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2952_, lean_object* v_name_x3f_2953_){
_start:
{
lean_object* v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2955_ = 1;
v___x_2956_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2956_, 0, v_name_x3f_2953_);
lean_ctor_set(v___x_2956_, 1, v___x_2954_);
lean_ctor_set(v___x_2956_, 2, v___x_2954_);
lean_ctor_set(v___x_2956_, 3, v___x_2954_);
lean_ctor_set(v___x_2956_, 4, v_apiEndpoint_2952_);
lean_ctor_set_uint8(v___x_2956_, sizeof(void*)*5, v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2957_, lean_object* v_artifactEndpoint_2958_, lean_object* v_revisionEndpoint_2959_){
_start:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = 0;
v___x_2962_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2963_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2963_, 0, v___x_2960_);
lean_ctor_set(v___x_2963_, 1, v_key_2957_);
lean_ctor_set(v___x_2963_, 2, v_artifactEndpoint_2958_);
lean_ctor_set(v___x_2963_, 3, v_revisionEndpoint_2959_);
lean_ctor_set(v___x_2963_, 4, v___x_2962_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*5, v___x_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2964_, lean_object* v_revisionEndpoint_2965_, lean_object* v_name_x3f_2966_){
_start:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2968_ = 0;
v___x_2969_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2969_, 0, v_name_x3f_2966_);
lean_ctor_set(v___x_2969_, 1, v___x_2967_);
lean_ctor_set(v___x_2969_, 2, v_artifactEndpoint_2964_);
lean_ctor_set(v___x_2969_, 3, v_revisionEndpoint_2965_);
lean_ctor_set(v___x_2969_, 4, v___x_2967_);
lean_ctor_set_uint8(v___x_2969_, sizeof(void*)*5, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2970_, lean_object* v_name_x3f_2971_){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2973_ = 0;
v___x_2974_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2974_, 0, v_name_x3f_2971_);
lean_ctor_set(v___x_2974_, 1, v___x_2972_);
lean_ctor_set(v___x_2974_, 2, v_artifactEndpoint_2970_);
lean_ctor_set(v___x_2974_, 3, v___x_2972_);
lean_ctor_set(v___x_2974_, 4, v___x_2972_);
lean_ctor_set_uint8(v___x_2974_, sizeof(void*)*5, v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2975_, lean_object* v_key_2976_){
_start:
{
lean_object* v_name_x3f_2977_; lean_object* v_artifactEndpoint_2978_; lean_object* v_revisionEndpoint_2979_; uint8_t v_isReservoir_2980_; lean_object* v_apiEndpoint_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_name_x3f_2977_ = lean_ctor_get(v_service_2975_, 0);
v_artifactEndpoint_2978_ = lean_ctor_get(v_service_2975_, 2);
v_revisionEndpoint_2979_ = lean_ctor_get(v_service_2975_, 3);
v_isReservoir_2980_ = lean_ctor_get_uint8(v_service_2975_, sizeof(void*)*5);
v_apiEndpoint_2981_ = lean_ctor_get(v_service_2975_, 4);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_service_2975_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v_service_2975_, 1);
lean_dec(v_unused_2989_);
v___x_2983_ = v_service_2975_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_apiEndpoint_2981_);
lean_inc(v_revisionEndpoint_2979_);
lean_inc(v_artifactEndpoint_2978_);
lean_inc(v_name_x3f_2977_);
lean_dec(v_service_2975_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v_key_2976_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_name_x3f_2977_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_key_2976_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_artifactEndpoint_2978_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_revisionEndpoint_2979_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_apiEndpoint_2981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2987_, sizeof(void*)*5, v_isReservoir_2980_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2996_);
lean_dec_ref(v_s_2996_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2998_, lean_object* v___x_2999_, lean_object* v___x_3000_, lean_object* v_a_3001_, lean_object* v_b_3002_){
_start:
{
if (lean_obj_tag(v_a_3001_) == 0)
{
lean_object* v_currPos_3003_; lean_object* v_searcher_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3038_; 
v_currPos_3003_ = lean_ctor_get(v_a_3001_, 0);
v_searcher_3004_ = lean_ctor_get(v_a_3001_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_3001_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3006_ = v_a_3001_;
v_isShared_3007_ = v_isSharedCheck_3038_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_searcher_3004_);
lean_inc(v_currPos_3003_);
lean_dec(v_a_3001_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3038_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v_startInclusive_3008_; lean_object* v_endExclusive_3009_; uint32_t v___x_3010_; lean_object* v_it_3012_; lean_object* v_startInclusive_3013_; lean_object* v_endExclusive_3014_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_startInclusive_3008_ = lean_ctor_get(v___x_2999_, 1);
v_endExclusive_3009_ = lean_ctor_get(v___x_2999_, 2);
v___x_3010_ = 47;
v___x_3019_ = lean_nat_sub(v_endExclusive_3009_, v_startInclusive_3008_);
v___x_3020_ = lean_nat_dec_eq(v_searcher_3004_, v___x_3019_);
lean_dec(v___x_3019_);
if (v___x_3020_ == 0)
{
uint32_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = lean_string_utf8_get_fast(v_scope_2998_, v_searcher_3004_);
v___x_3022_ = lean_uint32_dec_eq(v___x_3021_, v___x_3010_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = lean_string_utf8_next_fast(v_scope_2998_, v_searcher_3004_);
lean_dec(v_searcher_3004_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_3023_);
v___x_3025_ = v___x_3006_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_currPos_3003_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
v_a_3001_ = v___x_3025_;
goto _start;
}
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v_slice_3031_; lean_object* v_nextIt_3033_; 
v___x_3028_ = lean_string_utf8_next_fast(v_scope_2998_, v_searcher_3004_);
v___x_3029_ = lean_nat_sub(v___x_3028_, v_searcher_3004_);
v___x_3030_ = lean_nat_add(v_searcher_3004_, v___x_3029_);
lean_dec(v___x_3029_);
v_slice_3031_ = l_String_Slice_subslice_x21(v___x_2999_, v_currPos_3003_, v_searcher_3004_);
lean_inc(v___x_3030_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_3030_);
lean_ctor_set(v___x_3006_, 0, v___x_3030_);
v_nextIt_3033_ = v___x_3006_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3030_);
v_nextIt_3033_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v_startInclusive_3034_; lean_object* v_endExclusive_3035_; 
v_startInclusive_3034_ = lean_ctor_get(v_slice_3031_, 0);
lean_inc(v_startInclusive_3034_);
v_endExclusive_3035_ = lean_ctor_get(v_slice_3031_, 1);
lean_inc(v_endExclusive_3035_);
lean_dec_ref(v_slice_3031_);
v_it_3012_ = v_nextIt_3033_;
v_startInclusive_3013_ = v_startInclusive_3034_;
v_endExclusive_3014_ = v_endExclusive_3035_;
goto v___jp_3011_;
}
}
}
else
{
lean_object* v___x_3037_; 
lean_del_object(v___x_3006_);
lean_dec(v_searcher_3004_);
v___x_3037_ = lean_box(1);
lean_inc(v___x_3000_);
v_it_3012_ = v___x_3037_;
v_startInclusive_3013_ = v_currPos_3003_;
v_endExclusive_3014_ = v___x_3000_;
goto v___jp_3011_;
}
v___jp_3011_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_string_utf8_extract(v_scope_2998_, v_startInclusive_3013_, v_endExclusive_3014_);
lean_dec(v_endExclusive_3014_);
lean_dec(v_startInclusive_3013_);
v___x_3016_ = lean_string_push(v_b_3002_, v___x_3010_);
v___x_3017_ = l_Lake_uriEncode(v___x_3015_, v___x_3016_);
v_a_3001_ = v_it_3012_;
v_b_3002_ = v___x_3017_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3000_);
return v_b_3002_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_3039_, lean_object* v___x_3040_, lean_object* v___x_3041_, lean_object* v_a_3042_, lean_object* v_b_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_3039_, v___x_3040_, v___x_3041_, v_a_3042_, v_b_3043_);
lean_dec_ref(v___x_3040_);
lean_dec_ref(v_scope_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_3045_, lean_object* v_scope_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = lean_string_utf8_byte_size(v_scope_3046_);
lean_inc_ref(v_scope_3046_);
v___x_3049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3049_, 0, v_scope_3046_);
lean_ctor_set(v___x_3049_, 1, v___x_3047_);
lean_ctor_set(v___x_3049_, 2, v___x_3048_);
v___x_3050_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_3049_);
v___x_3051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_3046_, v___x_3049_, v___x_3048_, v___x_3050_, v_endpoint_3045_);
lean_dec_ref(v___x_3049_);
lean_dec_ref(v_scope_3046_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_3052_, lean_object* v___x_3053_, lean_object* v___x_3054_, lean_object* v_inst_3055_, lean_object* v_R_3056_, lean_object* v_a_3057_, lean_object* v_b_3058_, lean_object* v_c_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_3052_, v___x_3053_, v___x_3054_, v_a_3057_, v_b_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_3061_, lean_object* v___x_3062_, lean_object* v___x_3063_, lean_object* v_inst_3064_, lean_object* v_R_3065_, lean_object* v_a_3066_, lean_object* v_b_3067_, lean_object* v_c_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_3061_, v___x_3062_, v___x_3063_, v_inst_3064_, v_R_3065_, v_a_3066_, v_b_3067_, v_c_3068_);
lean_dec_ref(v___x_3062_);
lean_dec_ref(v_scope_3061_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_3070_, lean_object* v_scope_3071_){
_start:
{
lean_object* v_artifactEndpoint_3072_; lean_object* v___x_3073_; 
v_artifactEndpoint_3072_ = lean_ctor_get(v_service_3070_, 2);
lean_inc_ref(v_artifactEndpoint_3072_);
lean_dec_ref(v_service_3070_);
v___x_3073_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_3072_, v_scope_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_3076_, lean_object* v_service_3077_, lean_object* v_scope_3078_){
_start:
{
lean_object* v___y_3080_; lean_object* v_s_3087_; lean_object* v___x_3088_; 
v_s_3087_ = lean_ctor_get(v_scope_3078_, 0);
lean_inc_ref(v_s_3087_);
lean_dec_ref(v_scope_3078_);
v___x_3088_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_3077_, v_s_3087_);
v___y_3080_ = v___x_3088_;
goto v___jp_3079_;
v___jp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3081_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_3082_ = lean_string_append(v___y_3080_, v___x_3081_);
v___x_3083_ = l_Lake_Hash_hex(v_contentHash_3076_);
v___x_3084_ = lean_string_append(v___x_3082_, v___x_3083_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_3086_ = lean_string_append(v___x_3084_, v___x_3085_);
return v___x_3086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_3089_, lean_object* v_service_3090_, lean_object* v_scope_3091_){
_start:
{
uint64_t v_contentHash_boxed_3092_; lean_object* v_res_3093_; 
v_contentHash_boxed_3092_ = lean_unbox_uint64(v_contentHash_3089_);
lean_dec_ref(v_contentHash_3089_);
v_res_3093_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_3092_, v_service_3090_, v_scope_3091_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_3097_, lean_object* v_service_3098_, lean_object* v_scope_3099_){
_start:
{
lean_object* v___y_3101_; uint8_t v_isReservoir_3108_; 
v_isReservoir_3108_ = lean_ctor_get_uint8(v_service_3098_, sizeof(void*)*5);
if (v_isReservoir_3108_ == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3097_, v_service_3098_, v_scope_3099_);
return v___x_3109_;
}
else
{
if (lean_obj_tag(v_scope_3099_) == 0)
{
lean_object* v_apiEndpoint_3110_; lean_object* v_s_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_apiEndpoint_3110_ = lean_ctor_get(v_service_3098_, 4);
lean_inc_ref(v_apiEndpoint_3110_);
lean_dec_ref(v_service_3098_);
v_s_3111_ = lean_ctor_get(v_scope_3099_, 0);
lean_inc_ref(v_s_3111_);
lean_dec_ref(v_scope_3099_);
v___x_3112_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_3113_ = lean_string_append(v_apiEndpoint_3110_, v___x_3112_);
v___x_3114_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3113_, v_s_3111_);
v___y_3101_ = v___x_3114_;
goto v___jp_3100_;
}
else
{
lean_object* v_apiEndpoint_3115_; lean_object* v_s_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_apiEndpoint_3115_ = lean_ctor_get(v_service_3098_, 4);
lean_inc_ref(v_apiEndpoint_3115_);
lean_dec_ref(v_service_3098_);
v_s_3116_ = lean_ctor_get(v_scope_3099_, 0);
lean_inc_ref(v_s_3116_);
lean_dec_ref(v_scope_3099_);
v___x_3117_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3118_ = lean_string_append(v_apiEndpoint_3115_, v___x_3117_);
v___x_3119_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3118_, v_s_3116_);
v___y_3101_ = v___x_3119_;
goto v___jp_3100_;
}
}
v___jp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3102_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_3103_ = lean_string_append(v___y_3101_, v___x_3102_);
v___x_3104_ = l_Lake_Hash_hex(v_contentHash_3097_);
v___x_3105_ = lean_string_append(v___x_3103_, v___x_3104_);
lean_dec_ref(v___x_3104_);
v___x_3106_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_3107_ = lean_string_append(v___x_3105_, v___x_3106_);
return v___x_3107_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_3120_, lean_object* v_service_3121_, lean_object* v_scope_3122_){
_start:
{
uint64_t v_contentHash_boxed_3123_; lean_object* v_res_3124_; 
v_contentHash_boxed_3123_ = lean_unbox_uint64(v_contentHash_3120_);
lean_dec_ref(v_contentHash_3120_);
v_res_3124_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_3123_, v_service_3121_, v_scope_3122_);
return v_res_3124_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3129_ = lean_array_get_size(v___x_3128_);
return v___x_3129_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3130_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_nat_dec_lt(v___x_3131_, v___x_3130_);
return v___x_3132_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3133_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3134_ = lean_nat_dec_le(v___x_3133_, v___x_3133_);
return v___x_3134_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_3135_; size_t v___x_3136_; 
v___x_3135_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3136_ = lean_usize_of_nat(v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_3137_, lean_object* v_cache_3138_, lean_object* v_service_3139_, lean_object* v_scope_3140_, uint8_t v_force_3141_, lean_object* v_a_3142_){
_start:
{
uint64_t v_hash_3147_; lean_object* v_ext_3148_; lean_object* v_url_3149_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3213_; lean_object* v___y_3216_; uint8_t v_a_3217_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___y_3223_; lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v_hash_3147_ = lean_ctor_get_uint64(v_descr_3137_, sizeof(void*)*1);
v_ext_3148_ = lean_ctor_get(v_descr_3137_, 0);
lean_inc_ref(v_scope_3140_);
v_url_3149_ = l_Lake_CacheService_artifactUrl(v_hash_3147_, v_service_3139_, v_scope_3140_);
v___x_3220_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3221_ = l_System_FilePath_join(v_cache_3138_, v___x_3220_);
v___x_3236_ = lean_string_utf8_byte_size(v_ext_3148_);
v___x_3237_ = lean_unsigned_to_nat(0u);
v___x_3238_ = lean_nat_dec_eq(v___x_3236_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3239_ = l_Lake_Hash_hex(v_hash_3147_);
v___x_3240_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3241_ = lean_string_append(v___x_3239_, v___x_3240_);
v___x_3242_ = lean_string_append(v___x_3241_, v_ext_3148_);
v___y_3223_ = v___x_3242_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lake_Hash_hex(v_hash_3147_);
v___y_3223_ = v___x_3243_;
goto v___jp_3222_;
}
v___jp_3144_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_box(0);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
v___jp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3153_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3154_ = lean_string_append(v___y_3152_, v___x_3153_);
v___x_3155_ = l_Lake_Hash_hex(v_hash_3147_);
v___x_3156_ = lean_string_append(v___x_3154_, v___x_3155_);
lean_dec_ref(v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3158_ = lean_string_append(v___x_3156_, v___x_3157_);
v___x_3159_ = lean_string_append(v___x_3158_, v___y_3151_);
v___x_3160_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3161_ = lean_string_append(v___x_3159_, v___x_3160_);
v___x_3162_ = lean_string_append(v___x_3161_, v_url_3149_);
v___x_3163_ = 1;
v___x_3164_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set_uint8(v___x_3164_, sizeof(void*)*1, v___x_3163_);
lean_inc_ref(v_a_3142_);
v___x_3165_ = lean_apply_2(v_a_3142_, v___x_3164_, lean_box(0));
v___x_3166_ = lean_unsigned_to_nat(0u);
v___x_3167_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3168_ = l_Lake_downloadArtifactCore(v_hash_3147_, v_url_3149_, v___y_3151_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v_a_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
v_a_3170_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3168_);
v___x_3171_ = lean_array_get_size(v_a_3170_);
v___x_3172_ = lean_nat_dec_lt(v___x_3166_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; 
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3142_);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_a_3169_);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3174_ = lean_box(0);
v___x_3175_ = lean_nat_dec_le(v___x_3171_, v___x_3171_);
if (v___x_3175_ == 0)
{
if (v___x_3172_ == 0)
{
lean_object* v___x_3176_; 
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3142_);
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_a_3169_);
return v___x_3176_;
}
else
{
size_t v___x_3177_; size_t v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = ((size_t)0ULL);
v___x_3178_ = lean_usize_of_nat(v___x_3171_);
v___x_3179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3170_, v___x_3177_, v___x_3178_, v___x_3174_, v_a_3142_);
lean_dec(v_a_3170_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; 
v_unused_3187_ = lean_ctor_get(v___x_3179_, 0);
lean_dec(v_unused_3187_);
v___x_3181_ = v___x_3179_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_dec(v___x_3179_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v_a_3169_);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3169_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_dec(v_a_3169_);
return v___x_3179_;
}
}
}
else
{
size_t v___x_3188_; size_t v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = ((size_t)0ULL);
v___x_3189_ = lean_usize_of_nat(v___x_3171_);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3170_, v___x_3188_, v___x_3189_, v___x_3174_, v_a_3142_);
lean_dec(v_a_3170_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; 
v_unused_3198_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3198_);
v___x_3192_ = v___x_3190_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v___x_3190_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_a_3169_);
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3169_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
else
{
lean_dec(v_a_3169_);
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
v_a_3199_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_a_3199_);
lean_dec_ref(v___x_3168_);
v___x_3200_ = lean_array_get_size(v_a_3199_);
v___x_3201_ = lean_nat_dec_lt(v___x_3166_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3142_);
v___x_3202_ = lean_box(0);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; uint8_t v___x_3205_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_nat_dec_le(v___x_3200_, v___x_3200_);
if (v___x_3205_ == 0)
{
if (v___x_3201_ == 0)
{
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3142_);
goto v___jp_3144_;
}
else
{
size_t v___x_3206_; size_t v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((size_t)0ULL);
v___x_3207_ = lean_usize_of_nat(v___x_3200_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3199_, v___x_3206_, v___x_3207_, v___x_3204_, v_a_3142_);
lean_dec(v_a_3199_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_dec_ref(v___x_3208_);
goto v___jp_3144_;
}
else
{
return v___x_3208_;
}
}
}
else
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = lean_usize_of_nat(v___x_3200_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3199_, v___x_3209_, v___x_3210_, v___x_3204_, v_a_3142_);
lean_dec(v_a_3199_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_dec_ref(v___x_3211_);
goto v___jp_3144_;
}
else
{
return v___x_3211_;
}
}
}
}
}
v___jp_3212_:
{
lean_object* v_s_3214_; 
v_s_3214_ = lean_ctor_get(v_scope_3140_, 0);
lean_inc_ref(v_s_3214_);
lean_dec_ref(v_scope_3140_);
v___y_3151_ = v___y_3213_;
v___y_3152_ = v_s_3214_;
goto v___jp_3150_;
}
v___jp_3215_:
{
if (v_a_3217_ == 0)
{
v___y_3213_ = v___y_3216_;
goto v___jp_3212_;
}
else
{
if (v_force_3141_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec_ref(v___y_3216_);
lean_dec_ref(v_url_3149_);
lean_dec_ref(v_a_3142_);
lean_dec_ref(v_scope_3140_);
v___x_3218_ = lean_box(0);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
else
{
v___y_3213_ = v___y_3216_;
goto v___jp_3212_;
}
}
}
v___jp_3222_:
{
lean_object* v_path_3224_; uint8_t v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v_path_3224_ = l_System_FilePath_join(v___x_3221_, v___y_3223_);
v___x_3225_ = l_System_FilePath_pathExists(v_path_3224_);
v___x_3226_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3227_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3227_ == 0)
{
v___y_3216_ = v_path_3224_;
v_a_3217_ = v___x_3225_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3229_ == 0)
{
if (v___x_3227_ == 0)
{
v___y_3216_ = v_path_3224_;
v_a_3217_ = v___x_3225_;
goto v___jp_3215_;
}
else
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_3142_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3226_, v___x_3230_, v___x_3231_, v___x_3228_, v_a_3142_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_dec_ref(v___x_3232_);
v___y_3216_ = v_path_3224_;
v_a_3217_ = v___x_3225_;
goto v___jp_3215_;
}
else
{
lean_dec_ref(v_path_3224_);
lean_dec_ref(v_url_3149_);
lean_dec_ref(v_a_3142_);
lean_dec_ref(v_scope_3140_);
return v___x_3232_;
}
}
}
else
{
size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_3142_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3226_, v___x_3233_, v___x_3234_, v___x_3228_, v_a_3142_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_dec_ref(v___x_3235_);
v___y_3216_ = v_path_3224_;
v_a_3217_ = v___x_3225_;
goto v___jp_3215_;
}
else
{
lean_dec_ref(v_path_3224_);
lean_dec_ref(v_url_3149_);
lean_dec_ref(v_a_3142_);
lean_dec_ref(v_scope_3140_);
return v___x_3235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3244_, lean_object* v_cache_3245_, lean_object* v_service_3246_, lean_object* v_scope_3247_, lean_object* v_force_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
uint8_t v_force_boxed_3251_; lean_object* v_res_3252_; 
v_force_boxed_3251_ = lean_unbox(v_force_3248_);
v_res_3252_ = l_Lake_CacheService_downloadArtifact(v_descr_3244_, v_cache_3245_, v_service_3246_, v_scope_3247_, v_force_boxed_3251_, v_a_3249_);
lean_dec_ref(v_descr_3244_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object* v___y_3253_, lean_object* v_descr_3254_, lean_object* v_cache_3255_, lean_object* v_service_3256_, lean_object* v_scope_3257_, uint8_t v_force_3258_){
_start:
{
uint64_t v_hash_3263_; lean_object* v_ext_3264_; lean_object* v_url_3265_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3329_; lean_object* v___y_3332_; uint8_t v_a_3333_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___y_3339_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v_hash_3263_ = lean_ctor_get_uint64(v_descr_3254_, sizeof(void*)*1);
v_ext_3264_ = lean_ctor_get(v_descr_3254_, 0);
lean_inc_ref(v_scope_3257_);
v_url_3265_ = l_Lake_CacheService_artifactUrl(v_hash_3263_, v_service_3256_, v_scope_3257_);
v___x_3336_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3337_ = l_System_FilePath_join(v_cache_3255_, v___x_3336_);
v___x_3352_ = lean_string_utf8_byte_size(v_ext_3264_);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_nat_dec_eq(v___x_3352_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3355_ = l_Lake_Hash_hex(v_hash_3263_);
v___x_3356_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3357_ = lean_string_append(v___x_3355_, v___x_3356_);
v___x_3358_ = lean_string_append(v___x_3357_, v_ext_3264_);
v___y_3339_ = v___x_3358_;
goto v___jp_3338_;
}
else
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lake_Hash_hex(v_hash_3263_);
v___y_3339_ = v___x_3359_;
goto v___jp_3338_;
}
v___jp_3260_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
v___jp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3269_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3270_ = lean_string_append(v___y_3268_, v___x_3269_);
v___x_3271_ = l_Lake_Hash_hex(v_hash_3263_);
v___x_3272_ = lean_string_append(v___x_3270_, v___x_3271_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3274_ = lean_string_append(v___x_3272_, v___x_3273_);
v___x_3275_ = lean_string_append(v___x_3274_, v___y_3267_);
v___x_3276_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3277_ = lean_string_append(v___x_3275_, v___x_3276_);
v___x_3278_ = lean_string_append(v___x_3277_, v_url_3265_);
v___x_3279_ = 1;
v___x_3280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*1, v___x_3279_);
lean_inc_ref(v___y_3253_);
v___x_3281_ = lean_apply_2(v___y_3253_, v___x_3280_, lean_box(0));
v___x_3282_ = lean_unsigned_to_nat(0u);
v___x_3283_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3284_ = l_Lake_downloadArtifactCore(v_hash_3263_, v_url_3265_, v___y_3267_, v___x_3283_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v_a_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
v_a_3286_ = lean_ctor_get(v___x_3284_, 1);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3284_);
v___x_3287_ = lean_array_get_size(v_a_3286_);
v___x_3288_ = lean_nat_dec_lt(v___x_3282_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_dec(v_a_3286_);
lean_dec_ref(v___y_3253_);
v___x_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3289_, 0, v_a_3285_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_nat_dec_le(v___x_3287_, v___x_3287_);
if (v___x_3291_ == 0)
{
if (v___x_3288_ == 0)
{
lean_object* v___x_3292_; 
lean_dec(v_a_3286_);
lean_dec_ref(v___y_3253_);
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_a_3285_);
return v___x_3292_;
}
else
{
size_t v___x_3293_; size_t v___x_3294_; lean_object* v___x_3295_; 
v___x_3293_ = ((size_t)0ULL);
v___x_3294_ = lean_usize_of_nat(v___x_3287_);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3286_, v___x_3293_, v___x_3294_, v___x_3290_, v___y_3253_);
lean_dec(v_a_3286_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; 
v_unused_3303_ = lean_ctor_get(v___x_3295_, 0);
lean_dec(v_unused_3303_);
v___x_3297_ = v___x_3295_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_dec(v___x_3295_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v_a_3285_);
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3285_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_dec(v_a_3285_);
return v___x_3295_;
}
}
}
else
{
size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = lean_usize_of_nat(v___x_3287_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3286_, v___x_3304_, v___x_3305_, v___x_3290_, v___y_3253_);
lean_dec(v_a_3286_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v___x_3306_, 0);
lean_dec(v_unused_3314_);
v___x_3308_ = v___x_3306_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v___x_3306_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v_a_3285_);
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3285_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
else
{
lean_dec(v_a_3285_);
return v___x_3306_;
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_a_3315_ = lean_ctor_get(v___x_3284_, 1);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3284_);
v___x_3316_ = lean_array_get_size(v_a_3315_);
v___x_3317_ = lean_nat_dec_lt(v___x_3282_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec(v_a_3315_);
lean_dec_ref(v___y_3253_);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_nat_dec_le(v___x_3316_, v___x_3316_);
if (v___x_3321_ == 0)
{
if (v___x_3317_ == 0)
{
lean_dec(v_a_3315_);
lean_dec_ref(v___y_3253_);
goto v___jp_3260_;
}
else
{
size_t v___x_3322_; size_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = lean_usize_of_nat(v___x_3316_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3315_, v___x_3322_, v___x_3323_, v___x_3320_, v___y_3253_);
lean_dec(v_a_3315_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_dec_ref(v___x_3324_);
goto v___jp_3260_;
}
else
{
return v___x_3324_;
}
}
}
else
{
size_t v___x_3325_; size_t v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = ((size_t)0ULL);
v___x_3326_ = lean_usize_of_nat(v___x_3316_);
v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3315_, v___x_3325_, v___x_3326_, v___x_3320_, v___y_3253_);
lean_dec(v_a_3315_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_dec_ref(v___x_3327_);
goto v___jp_3260_;
}
else
{
return v___x_3327_;
}
}
}
}
}
v___jp_3328_:
{
lean_object* v_s_3330_; 
v_s_3330_ = lean_ctor_get(v_scope_3257_, 0);
lean_inc_ref(v_s_3330_);
lean_dec_ref(v_scope_3257_);
v___y_3267_ = v___y_3329_;
v___y_3268_ = v_s_3330_;
goto v___jp_3266_;
}
v___jp_3331_:
{
if (v_a_3333_ == 0)
{
v___y_3329_ = v___y_3332_;
goto v___jp_3328_;
}
else
{
if (v_force_3258_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v___y_3332_);
lean_dec_ref(v_url_3265_);
lean_dec_ref(v_scope_3257_);
lean_dec_ref(v___y_3253_);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
else
{
v___y_3329_ = v___y_3332_;
goto v___jp_3328_;
}
}
}
v___jp_3338_:
{
lean_object* v_path_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v_path_3340_ = l_System_FilePath_join(v___x_3337_, v___y_3339_);
v___x_3341_ = l_System_FilePath_pathExists(v_path_3340_);
v___x_3342_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3343_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3343_ == 0)
{
v___y_3332_ = v_path_3340_;
v_a_3333_ = v___x_3341_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3344_; uint8_t v___x_3345_; 
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3345_ == 0)
{
if (v___x_3343_ == 0)
{
v___y_3332_ = v_path_3340_;
v_a_3333_ = v___x_3341_;
goto v___jp_3331_;
}
else
{
size_t v___x_3346_; size_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = ((size_t)0ULL);
v___x_3347_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v___y_3253_);
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3342_, v___x_3346_, v___x_3347_, v___x_3344_, v___y_3253_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_dec_ref(v___x_3348_);
v___y_3332_ = v_path_3340_;
v_a_3333_ = v___x_3341_;
goto v___jp_3331_;
}
else
{
lean_dec_ref(v_path_3340_);
lean_dec_ref(v_url_3265_);
lean_dec_ref(v_scope_3257_);
lean_dec_ref(v___y_3253_);
return v___x_3348_;
}
}
}
else
{
size_t v___x_3349_; size_t v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = ((size_t)0ULL);
v___x_3350_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v___y_3253_);
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3342_, v___x_3349_, v___x_3350_, v___x_3344_, v___y_3253_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_dec_ref(v___x_3351_);
v___y_3332_ = v_path_3340_;
v_a_3333_ = v___x_3341_;
goto v___jp_3331_;
}
else
{
lean_dec_ref(v_path_3340_);
lean_dec_ref(v_url_3265_);
lean_dec_ref(v_scope_3257_);
lean_dec_ref(v___y_3253_);
return v___x_3351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object* v___y_3360_, lean_object* v_descr_3361_, lean_object* v_cache_3362_, lean_object* v_service_3363_, lean_object* v_scope_3364_, lean_object* v_force_3365_, lean_object* v_a_3366_){
_start:
{
uint8_t v_force_boxed_3367_; lean_object* v_res_3368_; 
v_force_boxed_3367_ = lean_unbox(v_force_3365_);
v_res_3368_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3360_, v_descr_3361_, v_cache_3362_, v_service_3363_, v_scope_3364_, v_force_boxed_3367_);
lean_dec_ref(v_descr_3361_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object* v_cache_3369_, lean_object* v_service_3370_, lean_object* v_scope_3371_, uint8_t v_force_3372_, uint8_t v_ok_3373_, lean_object* v_descr_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3375_, v_descr_3374_, v_cache_3369_, v_service_3370_, v_scope_3371_, v_force_3372_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3385_; 
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v___x_3377_, 0);
lean_dec(v_unused_3386_);
v___x_3379_ = v___x_3377_;
v_isShared_3380_ = v_isSharedCheck_3385_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v___x_3377_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3385_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = lean_box(v_ok_3373_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
else
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3395_; 
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v___x_3377_, 0);
lean_dec(v_unused_3396_);
v___x_3388_ = v___x_3377_;
v_isShared_3389_ = v_isSharedCheck_3395_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v___x_3377_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3395_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3390_ = 0;
v___x_3391_ = lean_box(v___x_3390_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3391_);
v___x_3393_ = v___x_3388_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object* v_cache_3397_, lean_object* v_service_3398_, lean_object* v_scope_3399_, lean_object* v_force_3400_, lean_object* v_ok_3401_, lean_object* v_descr_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
uint8_t v_force_boxed_3405_; uint8_t v_ok_boxed_3406_; lean_object* v_res_3407_; 
v_force_boxed_3405_ = lean_unbox(v_force_3400_);
v_ok_boxed_3406_ = lean_unbox(v_ok_3401_);
v_res_3407_ = l_Lake_CacheService_downloadArtifacts___elam__0(v_cache_3397_, v_service_3398_, v_scope_3399_, v_force_boxed_3405_, v_ok_boxed_3406_, v_descr_3402_, v___y_3403_);
lean_dec_ref(v_descr_3402_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(lean_object* v___y_3408_, lean_object* v_cache_3409_, lean_object* v_service_3410_, lean_object* v_scope_3411_, uint8_t v_force_3412_, uint8_t v_ok_3413_, lean_object* v_descr_3414_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3408_, v_descr_3414_, v_cache_3409_, v_service_3410_, v_scope_3411_, v_force_3412_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3425_);
v___x_3418_ = v___x_3416_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_dec(v___x_3416_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_box(v_ok_3413_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3434_; 
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3435_);
v___x_3427_ = v___x_3416_;
v_isShared_3428_ = v_isSharedCheck_3434_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v___x_3416_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3434_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3432_; 
v___x_3429_ = 0;
v___x_3430_ = lean_box(v___x_3429_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3430_);
v___x_3432_ = v___x_3427_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2___boxed(lean_object* v___y_3436_, lean_object* v_cache_3437_, lean_object* v_service_3438_, lean_object* v_scope_3439_, lean_object* v_force_3440_, lean_object* v_ok_3441_, lean_object* v_descr_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v_force_boxed_3444_; uint8_t v_ok_boxed_3445_; lean_object* v_res_3446_; 
v_force_boxed_3444_ = lean_unbox(v_force_3440_);
v_ok_boxed_3445_ = lean_unbox(v_ok_3441_);
v_res_3446_ = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(v___y_3436_, v_cache_3437_, v_service_3438_, v_scope_3439_, v_force_boxed_3444_, v_ok_boxed_3445_, v_descr_3442_);
lean_dec_ref(v_descr_3442_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object* v_cache_3447_, lean_object* v_service_3448_, lean_object* v_scope_3449_, uint8_t v_force_3450_, lean_object* v_as_3451_, size_t v_i_3452_, size_t v_stop_3453_, uint8_t v_b_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v___x_3457_; 
v___x_3457_ = lean_usize_dec_eq(v_i_3452_, v_stop_3453_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_array_uget_borrowed(v_as_3451_, v_i_3452_);
lean_inc_ref(v_scope_3449_);
lean_inc_ref(v_service_3448_);
lean_inc_ref(v_cache_3447_);
lean_inc_ref(v___y_3455_);
v___x_3459_ = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(v___y_3455_, v_cache_3447_, v_service_3448_, v_scope_3449_, v_force_3450_, v_b_3454_, v___x_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; size_t v___x_3461_; size_t v___x_3462_; uint8_t v___x_3463_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = ((size_t)1ULL);
v___x_3462_ = lean_usize_add(v_i_3452_, v___x_3461_);
v___x_3463_ = lean_unbox(v_a_3460_);
lean_dec(v_a_3460_);
v_i_3452_ = v___x_3462_;
v_b_3454_ = v___x_3463_;
goto _start;
}
else
{
lean_dec_ref(v___y_3455_);
lean_dec_ref(v_scope_3449_);
lean_dec_ref(v_service_3448_);
lean_dec_ref(v_cache_3447_);
return v___x_3459_;
}
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec_ref(v___y_3455_);
lean_dec_ref(v_scope_3449_);
lean_dec_ref(v_service_3448_);
lean_dec_ref(v_cache_3447_);
v___x_3465_ = lean_box(v_b_3454_);
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
return v___x_3466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_cache_3467_, lean_object* v_service_3468_, lean_object* v_scope_3469_, lean_object* v_force_3470_, lean_object* v_as_3471_, lean_object* v_i_3472_, lean_object* v_stop_3473_, lean_object* v_b_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v_force_boxed_3477_; size_t v_i_boxed_3478_; size_t v_stop_boxed_3479_; uint8_t v_b_boxed_3480_; lean_object* v_res_3481_; 
v_force_boxed_3477_ = lean_unbox(v_force_3470_);
v_i_boxed_3478_ = lean_unbox_usize(v_i_3472_);
lean_dec(v_i_3472_);
v_stop_boxed_3479_ = lean_unbox_usize(v_stop_3473_);
lean_dec(v_stop_3473_);
v_b_boxed_3480_ = lean_unbox(v_b_3474_);
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3467_, v_service_3468_, v_scope_3469_, v_force_boxed_3477_, v_as_3471_, v_i_boxed_3478_, v_stop_boxed_3479_, v_b_boxed_3480_, v___y_3475_);
lean_dec_ref(v_as_3471_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_3483_, lean_object* v_cache_3484_, lean_object* v_service_3485_, lean_object* v_scope_3486_, uint8_t v_force_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v___y_3494_; lean_object* v___y_3503_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = lean_array_get_size(v_descrs_3483_);
v___x_3517_ = lean_nat_dec_lt(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_dec_ref(v_a_3488_);
lean_dec_ref(v_scope_3486_);
lean_dec_ref(v_service_3485_);
lean_dec_ref(v_cache_3484_);
goto v___jp_3490_;
}
else
{
uint8_t v___x_3518_; 
v___x_3518_ = lean_nat_dec_le(v___x_3516_, v___x_3516_);
if (v___x_3518_ == 0)
{
if (v___x_3517_ == 0)
{
lean_dec_ref(v_a_3488_);
lean_dec_ref(v_scope_3486_);
lean_dec_ref(v_service_3485_);
lean_dec_ref(v_cache_3484_);
goto v___jp_3490_;
}
else
{
size_t v___x_3519_; size_t v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = ((size_t)0ULL);
v___x_3520_ = lean_usize_of_nat(v___x_3516_);
lean_inc_ref(v_a_3488_);
lean_inc_ref(v_scope_3486_);
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3484_, v_service_3485_, v_scope_3486_, v_force_3487_, v_descrs_3483_, v___x_3519_, v___x_3520_, v___x_3517_, v_a_3488_);
v___y_3503_ = v___x_3521_;
goto v___jp_3502_;
}
}
else
{
size_t v___x_3522_; size_t v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = ((size_t)0ULL);
v___x_3523_ = lean_usize_of_nat(v___x_3516_);
lean_inc_ref(v_a_3488_);
lean_inc_ref(v_scope_3486_);
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3484_, v_service_3485_, v_scope_3486_, v_force_3487_, v_descrs_3483_, v___x_3522_, v___x_3523_, v___x_3517_, v_a_3488_);
v___y_3503_ = v___x_3524_;
goto v___jp_3502_;
}
}
v___jp_3490_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
v___jp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3495_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_3496_ = lean_string_append(v___y_3494_, v___x_3495_);
v___x_3497_ = 3;
v___x_3498_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3498_, 0, v___x_3496_);
lean_ctor_set_uint8(v___x_3498_, sizeof(void*)*1, v___x_3497_);
v___x_3499_ = lean_apply_2(v_a_3488_, v___x_3498_, lean_box(0));
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
return v___x_3501_;
}
v___jp_3502_:
{
if (lean_obj_tag(v___y_3503_) == 0)
{
lean_object* v_a_3504_; uint8_t v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___y_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___y_3503_);
v___x_3505_ = lean_unbox(v_a_3504_);
lean_dec(v_a_3504_);
if (v___x_3505_ == 0)
{
lean_object* v_s_3506_; 
v_s_3506_ = lean_ctor_get(v_scope_3486_, 0);
lean_inc_ref(v_s_3506_);
lean_dec_ref(v_scope_3486_);
v___y_3494_ = v_s_3506_;
goto v___jp_3493_;
}
else
{
lean_dec_ref(v_a_3488_);
lean_dec_ref(v_scope_3486_);
goto v___jp_3490_;
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v_a_3488_);
lean_dec_ref(v_scope_3486_);
v_a_3507_ = lean_ctor_get(v___y_3503_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___y_3503_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___y_3503_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___y_3503_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_3525_, lean_object* v_cache_3526_, lean_object* v_service_3527_, lean_object* v_scope_3528_, lean_object* v_force_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
uint8_t v_force_boxed_3532_; lean_object* v_res_3533_; 
v_force_boxed_3532_ = lean_unbox(v_force_3529_);
v_res_3533_ = l_Lake_CacheService_downloadArtifacts(v_descrs_3525_, v_cache_3526_, v_service_3527_, v_scope_3528_, v_force_boxed_3532_, v_a_3530_);
lean_dec_ref(v_descrs_3525_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_3534_, lean_object* v_descrs_3535_, lean_object* v_cache_3536_, lean_object* v_service_3537_, lean_object* v_scope_3538_, uint8_t v_force_3539_){
_start:
{
lean_object* v___y_3545_; lean_object* v___y_3554_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3566_ = lean_unsigned_to_nat(0u);
v___x_3567_ = lean_array_get_size(v_descrs_3535_);
v___x_3568_ = lean_nat_dec_lt(v___x_3566_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_dec_ref(v_scope_3538_);
lean_dec_ref(v_service_3537_);
lean_dec_ref(v_cache_3536_);
lean_dec_ref(v_a_3534_);
goto v___jp_3541_;
}
else
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_nat_dec_le(v___x_3567_, v___x_3567_);
if (v___x_3569_ == 0)
{
if (v___x_3568_ == 0)
{
lean_dec_ref(v_scope_3538_);
lean_dec_ref(v_service_3537_);
lean_dec_ref(v_cache_3536_);
lean_dec_ref(v_a_3534_);
goto v___jp_3541_;
}
else
{
size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = lean_usize_of_nat(v___x_3567_);
lean_inc_ref(v_a_3534_);
lean_inc_ref(v_scope_3538_);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3536_, v_service_3537_, v_scope_3538_, v_force_3539_, v_descrs_3535_, v___x_3570_, v___x_3571_, v___x_3568_, v_a_3534_);
v___y_3554_ = v___x_3572_;
goto v___jp_3553_;
}
}
else
{
size_t v___x_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((size_t)0ULL);
v___x_3574_ = lean_usize_of_nat(v___x_3567_);
lean_inc_ref(v_a_3534_);
lean_inc_ref(v_scope_3538_);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3536_, v_service_3537_, v_scope_3538_, v_force_3539_, v_descrs_3535_, v___x_3573_, v___x_3574_, v___x_3568_, v_a_3534_);
v___y_3554_ = v___x_3575_;
goto v___jp_3553_;
}
}
v___jp_3541_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
v___jp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3546_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_3547_ = lean_string_append(v___y_3545_, v___x_3546_);
v___x_3548_ = 3;
v___x_3549_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*1, v___x_3548_);
v___x_3550_ = lean_apply_2(v_a_3534_, v___x_3549_, lean_box(0));
v___x_3551_ = lean_box(0);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
v___jp_3553_:
{
if (lean_obj_tag(v___y_3554_) == 0)
{
lean_object* v_a_3555_; uint8_t v___x_3556_; 
v_a_3555_ = lean_ctor_get(v___y_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref(v___y_3554_);
v___x_3556_ = lean_unbox(v_a_3555_);
lean_dec(v_a_3555_);
if (v___x_3556_ == 0)
{
lean_object* v_s_3557_; 
v_s_3557_ = lean_ctor_get(v_scope_3538_, 0);
lean_inc_ref(v_s_3557_);
lean_dec_ref(v_scope_3538_);
v___y_3545_ = v_s_3557_;
goto v___jp_3544_;
}
else
{
lean_dec_ref(v_scope_3538_);
lean_dec_ref(v_a_3534_);
goto v___jp_3541_;
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v_scope_3538_);
lean_dec_ref(v_a_3534_);
v_a_3558_ = lean_ctor_get(v___y_3554_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___y_3554_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___y_3554_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___y_3554_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_3576_, lean_object* v_descrs_3577_, lean_object* v_cache_3578_, lean_object* v_service_3579_, lean_object* v_scope_3580_, lean_object* v_force_3581_, lean_object* v_a_3582_){
_start:
{
uint8_t v_force_boxed_3583_; lean_object* v_res_3584_; 
v_force_boxed_3583_ = lean_unbox(v_force_3581_);
v_res_3584_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3576_, v_descrs_3577_, v_cache_3578_, v_service_3579_, v_scope_3580_, v_force_boxed_3583_);
lean_dec_ref(v_descrs_3577_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_3585_, lean_object* v_cache_3586_, lean_object* v_service_3587_, lean_object* v_localScope_3588_, lean_object* v_remoteScope_3589_, uint8_t v_force_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_name_x3f_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_name_x3f_3596_ = lean_ctor_get(v_service_3587_, 0);
lean_inc_ref(v_remoteScope_3589_);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v_remoteScope_3589_);
lean_inc(v_name_x3f_3596_);
lean_inc_ref(v_cache_3586_);
v___x_3598_ = l_Lake_Cache_writeMap(v_cache_3586_, v_localScope_3588_, v_map_3585_, v_name_x3f_3596_, v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3636_; 
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v___x_3598_, 0);
lean_dec(v_unused_3637_);
v___x_3600_ = v___x_3598_;
v_isShared_3601_ = v_isSharedCheck_3636_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v___x_3598_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3636_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_unsigned_to_nat(0u);
v___x_3603_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3604_ = l_Lake_CacheMap_collectOutputDescrs(v_map_3585_, v___x_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v_a_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
lean_del_object(v___x_3600_);
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
v_a_3606_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3604_);
v___x_3607_ = lean_array_get_size(v_a_3606_);
v___x_3608_ = lean_nat_dec_lt(v___x_3602_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
lean_dec(v_a_3606_);
v___x_3609_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3591_, v_a_3605_, v_cache_3586_, v_service_3587_, v_remoteScope_3589_, v_force_3590_);
lean_dec(v_a_3605_);
return v___x_3609_;
}
else
{
lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3610_ = lean_box(0);
v___x_3611_ = lean_nat_dec_le(v___x_3607_, v___x_3607_);
if (v___x_3611_ == 0)
{
if (v___x_3608_ == 0)
{
lean_object* v___x_3612_; 
lean_dec(v_a_3606_);
v___x_3612_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3591_, v_a_3605_, v_cache_3586_, v_service_3587_, v_remoteScope_3589_, v_force_3590_);
lean_dec(v_a_3605_);
return v___x_3612_;
}
else
{
size_t v___x_3613_; size_t v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = lean_usize_of_nat(v___x_3607_);
lean_inc_ref(v_a_3591_);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3606_, v___x_3613_, v___x_3614_, v___x_3610_, v_a_3591_);
lean_dec(v_a_3606_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3616_; 
lean_dec_ref(v___x_3615_);
v___x_3616_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3591_, v_a_3605_, v_cache_3586_, v_service_3587_, v_remoteScope_3589_, v_force_3590_);
lean_dec(v_a_3605_);
return v___x_3616_;
}
else
{
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3591_);
lean_dec_ref(v_remoteScope_3589_);
lean_dec_ref(v_service_3587_);
lean_dec_ref(v_cache_3586_);
return v___x_3615_;
}
}
}
else
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = lean_usize_of_nat(v___x_3607_);
lean_inc_ref(v_a_3591_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3606_, v___x_3617_, v___x_3618_, v___x_3610_, v_a_3591_);
lean_dec(v_a_3606_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref(v___x_3619_);
v___x_3620_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3591_, v_a_3605_, v_cache_3586_, v_service_3587_, v_remoteScope_3589_, v_force_3590_);
lean_dec(v_a_3605_);
return v___x_3620_;
}
else
{
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3591_);
lean_dec_ref(v_remoteScope_3589_);
lean_dec_ref(v_service_3587_);
lean_dec_ref(v_cache_3586_);
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; 
lean_dec_ref(v_remoteScope_3589_);
lean_dec_ref(v_service_3587_);
lean_dec_ref(v_cache_3586_);
v_a_3621_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3604_);
v___x_3622_ = lean_array_get_size(v_a_3621_);
v___x_3623_ = lean_nat_dec_lt(v___x_3602_, v___x_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3591_);
v___x_3624_ = lean_box(0);
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 1);
lean_ctor_set(v___x_3600_, 0, v___x_3624_);
v___x_3626_ = v___x_3600_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
else
{
lean_object* v___x_3628_; uint8_t v___x_3629_; 
lean_del_object(v___x_3600_);
v___x_3628_ = lean_box(0);
v___x_3629_ = lean_nat_dec_le(v___x_3622_, v___x_3622_);
if (v___x_3629_ == 0)
{
if (v___x_3623_ == 0)
{
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3591_);
goto v___jp_3593_;
}
else
{
size_t v___x_3630_; size_t v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = ((size_t)0ULL);
v___x_3631_ = lean_usize_of_nat(v___x_3622_);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3621_, v___x_3630_, v___x_3631_, v___x_3628_, v_a_3591_);
lean_dec(v_a_3621_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_dec_ref(v___x_3632_);
goto v___jp_3593_;
}
else
{
return v___x_3632_;
}
}
}
else
{
size_t v___x_3633_; size_t v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = ((size_t)0ULL);
v___x_3634_ = lean_usize_of_nat(v___x_3622_);
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3621_, v___x_3633_, v___x_3634_, v___x_3628_, v_a_3591_);
lean_dec(v_a_3621_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_dec_ref(v___x_3635_);
goto v___jp_3593_;
}
else
{
return v___x_3635_;
}
}
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3650_; 
lean_dec_ref(v_remoteScope_3589_);
lean_dec_ref(v_service_3587_);
lean_dec_ref(v_cache_3586_);
lean_dec_ref(v_map_3585_);
v_a_3638_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3640_ = v___x_3598_;
v_isShared_3641_ = v_isSharedCheck_3650_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3598_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3650_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3642_ = lean_io_error_to_string(v_a_3638_);
v___x_3643_ = 3;
v___x_3644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set_uint8(v___x_3644_, sizeof(void*)*1, v___x_3643_);
v___x_3645_ = lean_apply_2(v_a_3591_, v___x_3644_, lean_box(0));
v___x_3646_ = lean_box(0);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3646_);
v___x_3648_ = v___x_3640_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
v___jp_3593_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = lean_box(0);
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_3651_, lean_object* v_cache_3652_, lean_object* v_service_3653_, lean_object* v_localScope_3654_, lean_object* v_remoteScope_3655_, lean_object* v_force_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
uint8_t v_force_boxed_3659_; lean_object* v_res_3660_; 
v_force_boxed_3659_ = lean_unbox(v_force_3656_);
v_res_3660_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_3651_, v_cache_3652_, v_service_3653_, v_localScope_3654_, v_remoteScope_3655_, v_force_boxed_3659_, v_a_3657_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3661_, lean_object* v_file_3662_, lean_object* v_contentType_3663_, lean_object* v_url_3664_, lean_object* v_key_3665_){
_start:
{
lean_object* v___y_3668_; lean_object* v_a_3669_; lean_object* v_stderr_3682_; lean_object* v___y_3691_; lean_object* v___y_3694_; lean_object* v_a_3695_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v_stderr_3734_; lean_object* v_a_3735_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; uint8_t v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3749_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3750_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3751_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3752_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3753_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3754_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3755_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3756_ = lean_string_append(v___x_3755_, v_contentType_3663_);
v___x_3757_ = lean_unsigned_to_nat(14u);
v___x_3758_ = lean_mk_empty_array_with_capacity(v___x_3757_);
lean_dec_ref(v___x_3758_);
v___x_3759_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3760_ = lean_array_push(v___x_3759_, v_key_3665_);
v___x_3761_ = lean_array_push(v___x_3760_, v___x_3751_);
v___x_3762_ = lean_array_push(v___x_3761_, v___x_3752_);
v___x_3763_ = lean_array_push(v___x_3762_, v___x_3753_);
v___x_3764_ = lean_array_push(v___x_3763_, v_file_3662_);
v___x_3765_ = lean_array_push(v___x_3764_, v_url_3664_);
v___x_3766_ = lean_array_push(v___x_3765_, v___x_3754_);
v___x_3767_ = lean_array_push(v___x_3766_, v___x_3756_);
v___x_3768_ = lean_box(0);
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3771_ = 1;
v___x_3772_ = 0;
v___x_3773_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3773_, 0, v___x_3749_);
lean_ctor_set(v___x_3773_, 1, v___x_3750_);
lean_ctor_set(v___x_3773_, 2, v___x_3767_);
lean_ctor_set(v___x_3773_, 3, v___x_3768_);
lean_ctor_set(v___x_3773_, 4, v___x_3770_);
lean_ctor_set_uint8(v___x_3773_, sizeof(void*)*5, v___x_3771_);
lean_ctor_set_uint8(v___x_3773_, sizeof(void*)*5 + 1, v___x_3772_);
v___x_3774_ = l_Lake_captureProc_x27(v___x_3773_, v___x_3770_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v_a_3776_; lean_object* v___x_3790_; uint8_t v___x_3791_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
v_a_3776_ = lean_ctor_get(v___x_3774_, 1);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3774_);
v___x_3790_ = lean_array_get_size(v_a_3776_);
v___x_3791_ = lean_nat_dec_lt(v___x_3769_, v___x_3790_);
if (v___x_3791_ == 0)
{
lean_dec(v_a_3776_);
goto v___jp_3777_;
}
else
{
lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = lean_box(0);
v___x_3793_ = lean_nat_dec_le(v___x_3790_, v___x_3790_);
if (v___x_3793_ == 0)
{
if (v___x_3791_ == 0)
{
lean_dec(v_a_3776_);
goto v___jp_3777_;
}
else
{
size_t v___x_3794_; size_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = ((size_t)0ULL);
v___x_3795_ = lean_usize_of_nat(v___x_3790_);
lean_inc_ref(v_a_3661_);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3776_, v___x_3794_, v___x_3795_, v___x_3792_, v_a_3661_);
lean_dec(v_a_3776_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_dec_ref(v___x_3796_);
goto v___jp_3777_;
}
else
{
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3661_);
return v___x_3796_;
}
}
}
else
{
size_t v___x_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = ((size_t)0ULL);
v___x_3798_ = lean_usize_of_nat(v___x_3790_);
lean_inc_ref(v_a_3661_);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3776_, v___x_3797_, v___x_3798_, v___x_3792_, v_a_3661_);
lean_dec(v_a_3776_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref(v___x_3799_);
goto v___jp_3777_;
}
else
{
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3661_);
return v___x_3799_;
}
}
}
v___jp_3777_:
{
lean_object* v_stderr_3778_; lean_object* v___x_3779_; 
v_stderr_3778_ = lean_ctor_get(v_a_3775_, 1);
lean_inc_ref(v_stderr_3778_);
v___x_3779_ = l_Lean_Json_parse(v_stderr_3778_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; 
lean_inc_ref(v_stderr_3778_);
lean_dec(v_a_3775_);
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3779_);
v_stderr_3734_ = v_stderr_3778_;
v_a_3735_ = v_a_3780_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3782_; 
v_a_3781_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3781_);
lean_dec_ref(v___x_3779_);
v___x_3782_ = l_Lean_Json_getObj_x3f(v_a_3781_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; 
lean_inc_ref(v_stderr_3778_);
lean_dec(v_a_3775_);
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref(v___x_3782_);
v_stderr_3734_ = v_stderr_3778_;
v_a_3735_ = v_a_3783_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_a_3784_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3782_);
v___x_3785_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3786_ = l_Lake_JsonObject_getJson_x3f(v_a_3784_, v___x_3785_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_inc_ref(v_stderr_3778_);
lean_dec(v_a_3784_);
lean_dec(v_a_3775_);
v_stderr_3682_ = v_stderr_3778_;
goto v___jp_3681_;
}
else
{
lean_object* v_val_3787_; lean_object* v___x_3788_; 
v_val_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_val_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3787_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref(v___x_3788_);
v___y_3722_ = v_a_3784_;
v___y_3723_ = v_a_3775_;
goto v___jp_3721_;
}
else
{
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref(v___x_3788_);
v___y_3722_ = v_a_3784_;
v___y_3723_ = v_a_3775_;
goto v___jp_3721_;
}
else
{
lean_object* v_a_3789_; 
lean_dec(v_a_3784_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref(v___x_3788_);
v___y_3694_ = v_a_3775_;
v_a_3695_ = v_a_3789_;
goto v___jp_3693_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_a_3800_ = lean_ctor_get(v___x_3774_, 1);
lean_inc(v_a_3800_);
lean_dec_ref(v___x_3774_);
v___x_3801_ = lean_array_get_size(v_a_3800_);
v___x_3802_ = lean_nat_dec_lt(v___x_3769_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3661_);
v___x_3803_ = lean_box(0);
v___x_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
return v___x_3804_;
}
else
{
lean_object* v___x_3805_; uint8_t v___x_3806_; 
v___x_3805_ = lean_box(0);
v___x_3806_ = lean_nat_dec_le(v___x_3801_, v___x_3801_);
if (v___x_3806_ == 0)
{
if (v___x_3802_ == 0)
{
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3661_);
goto v___jp_3746_;
}
else
{
size_t v___x_3807_; size_t v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = ((size_t)0ULL);
v___x_3808_ = lean_usize_of_nat(v___x_3801_);
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3800_, v___x_3807_, v___x_3808_, v___x_3805_, v_a_3661_);
lean_dec(v_a_3800_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_dec_ref(v___x_3809_);
goto v___jp_3746_;
}
else
{
return v___x_3809_;
}
}
}
else
{
size_t v___x_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = ((size_t)0ULL);
v___x_3811_ = lean_usize_of_nat(v___x_3801_);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3800_, v___x_3810_, v___x_3811_, v___x_3805_, v_a_3661_);
lean_dec(v_a_3800_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_dec_ref(v___x_3812_);
goto v___jp_3746_;
}
else
{
return v___x_3812_;
}
}
}
}
v___jp_3667_:
{
lean_object* v_stderr_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v_stderr_3670_ = lean_ctor_get(v___y_3668_, 1);
lean_inc_ref(v_stderr_3670_);
lean_dec_ref(v___y_3668_);
v___x_3671_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3672_ = lean_string_append(v___x_3671_, v_a_3669_);
lean_dec_ref(v_a_3669_);
v___x_3673_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3674_ = lean_string_append(v___x_3672_, v___x_3673_);
v___x_3675_ = lean_string_append(v___x_3674_, v_stderr_3670_);
lean_dec_ref(v_stderr_3670_);
v___x_3676_ = 3;
v___x_3677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set_uint8(v___x_3677_, sizeof(void*)*1, v___x_3676_);
v___x_3678_ = lean_apply_2(v_a_3661_, v___x_3677_, lean_box(0));
v___x_3679_ = lean_box(0);
v___x_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
return v___x_3680_;
}
v___jp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3683_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3684_ = lean_string_append(v___x_3683_, v_stderr_3682_);
lean_dec_ref(v_stderr_3682_);
v___x_3685_ = 3;
v___x_3686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set_uint8(v___x_3686_, sizeof(void*)*1, v___x_3685_);
v___x_3687_ = lean_apply_2(v_a_3661_, v___x_3686_, lean_box(0));
v___x_3688_ = lean_box(0);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
v___jp_3690_:
{
lean_object* v_stderr_3692_; 
v_stderr_3692_ = lean_ctor_get(v___y_3691_, 1);
lean_inc_ref(v_stderr_3692_);
lean_dec_ref(v___y_3691_);
v_stderr_3682_ = v_stderr_3692_;
goto v___jp_3681_;
}
v___jp_3693_:
{
if (lean_obj_tag(v_a_3695_) == 0)
{
v___y_3691_ = v___y_3694_;
goto v___jp_3690_;
}
else
{
lean_object* v_val_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3720_; 
v_val_3696_ = lean_ctor_get(v_a_3695_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_a_3695_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3698_ = v_a_3695_;
v_isShared_3699_ = v_isSharedCheck_3720_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_val_3696_);
lean_dec(v_a_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3720_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = lean_unsigned_to_nat(200u);
v___x_3701_ = lean_nat_dec_eq(v_val_3696_, v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v_stdout_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
v_stdout_3702_ = lean_ctor_get(v___y_3694_, 0);
lean_inc_ref(v_stdout_3702_);
lean_dec_ref(v___y_3694_);
v___x_3703_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3704_ = l_Nat_reprFast(v_val_3696_);
v___x_3705_ = lean_string_append(v___x_3703_, v___x_3704_);
lean_dec_ref(v___x_3704_);
v___x_3706_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3707_ = lean_string_append(v___x_3705_, v___x_3706_);
v___x_3708_ = lean_string_append(v___x_3707_, v_stdout_3702_);
lean_dec_ref(v_stdout_3702_);
v___x_3709_ = 3;
v___x_3710_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set_uint8(v___x_3710_, sizeof(void*)*1, v___x_3709_);
v___x_3711_ = lean_apply_2(v_a_3661_, v___x_3710_, lean_box(0));
v___x_3712_ = lean_box(0);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3712_);
v___x_3714_ = v___x_3698_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v_val_3696_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_a_3661_);
v___x_3716_ = lean_box(0);
if (v_isShared_3699_ == 0)
{
lean_ctor_set_tag(v___x_3698_, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3716_);
v___x_3718_ = v___x_3698_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
v___jp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3725_ = l_Lake_JsonObject_getJson_x3f(v___y_3722_, v___x_3724_);
lean_dec(v___y_3722_);
if (lean_obj_tag(v___x_3725_) == 0)
{
v___y_3691_ = v___y_3723_;
goto v___jp_3690_;
}
else
{
lean_object* v_val_3726_; lean_object* v___x_3727_; 
v_val_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_val_3726_);
lean_dec_ref(v___x_3725_);
v___x_3727_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3726_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3730_ = lean_string_append(v___x_3729_, v_a_3728_);
lean_dec(v_a_3728_);
v___y_3668_ = v___y_3723_;
v_a_3669_ = v___x_3730_;
goto v___jp_3667_;
}
else
{
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3731_; 
v_a_3731_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3731_);
lean_dec_ref(v___x_3727_);
v___y_3668_ = v___y_3723_;
v_a_3669_ = v_a_3731_;
goto v___jp_3667_;
}
else
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3727_);
v___y_3694_ = v___y_3723_;
v_a_3695_ = v_a_3732_;
goto v___jp_3693_;
}
}
}
}
v___jp_3733_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; uint8_t v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3736_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3737_ = lean_string_append(v___x_3736_, v_a_3735_);
lean_dec_ref(v_a_3735_);
v___x_3738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3739_ = lean_string_append(v___x_3737_, v___x_3738_);
v___x_3740_ = lean_string_append(v___x_3739_, v_stderr_3734_);
lean_dec_ref(v_stderr_3734_);
v___x_3741_ = 3;
v___x_3742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set_uint8(v___x_3742_, sizeof(void*)*1, v___x_3741_);
v___x_3743_ = lean_apply_2(v_a_3661_, v___x_3742_, lean_box(0));
v___x_3744_ = lean_box(0);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
v___jp_3746_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = lean_box(0);
v___x_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
return v___x_3748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3813_, lean_object* v_file_3814_, lean_object* v_contentType_3815_, lean_object* v_url_3816_, lean_object* v_key_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3813_, v_file_3814_, v_contentType_3815_, v_url_3816_, v_key_3817_);
lean_dec_ref(v_contentType_3815_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3821_, lean_object* v_art_3822_, lean_object* v_service_3823_, lean_object* v_scope_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v_url_3827_; lean_object* v___y_3829_; lean_object* v_s_3846_; 
lean_inc_ref(v_scope_3824_);
lean_inc_ref(v_service_3823_);
v_url_3827_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3821_, v_service_3823_, v_scope_3824_);
v_s_3846_ = lean_ctor_get(v_scope_3824_, 0);
lean_inc_ref(v_s_3846_);
lean_dec_ref(v_scope_3824_);
v___y_3829_ = v_s_3846_;
goto v___jp_3828_;
v___jp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v_key_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3830_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3831_ = lean_string_append(v___y_3829_, v___x_3830_);
v___x_3832_ = l_Lake_Hash_hex(v_contentHash_3821_);
v___x_3833_ = lean_string_append(v___x_3831_, v___x_3832_);
lean_dec_ref(v___x_3832_);
v___x_3834_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3835_ = lean_string_append(v___x_3833_, v___x_3834_);
v___x_3836_ = lean_string_append(v___x_3835_, v_art_3822_);
v___x_3837_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3838_ = lean_string_append(v___x_3836_, v___x_3837_);
v___x_3839_ = lean_string_append(v___x_3838_, v_url_3827_);
v___x_3840_ = 1;
v___x_3841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set_uint8(v___x_3841_, sizeof(void*)*1, v___x_3840_);
lean_inc_ref(v_a_3825_);
v___x_3842_ = lean_apply_2(v_a_3825_, v___x_3841_, lean_box(0));
v_key_3843_ = lean_ctor_get(v_service_3823_, 1);
lean_inc_ref(v_key_3843_);
lean_dec_ref(v_service_3823_);
v___x_3844_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3845_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3825_, v_art_3822_, v___x_3844_, v_url_3827_, v_key_3843_);
return v___x_3845_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3847_, lean_object* v_art_3848_, lean_object* v_service_3849_, lean_object* v_scope_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
uint64_t v_contentHash_boxed_3853_; lean_object* v_res_3854_; 
v_contentHash_boxed_3853_ = lean_unbox_uint64(v_contentHash_3847_);
lean_dec_ref(v_contentHash_3847_);
v_res_3854_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3853_, v_art_3848_, v_service_3849_, v_scope_3850_, v_a_3851_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object* v___y_3855_, uint64_t v_contentHash_3856_, lean_object* v_art_3857_, lean_object* v_service_3858_, lean_object* v_scope_3859_){
_start:
{
lean_object* v_url_3861_; lean_object* v___y_3863_; lean_object* v_s_3880_; 
lean_inc_ref(v_scope_3859_);
lean_inc_ref(v_service_3858_);
v_url_3861_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3856_, v_service_3858_, v_scope_3859_);
v_s_3880_ = lean_ctor_get(v_scope_3859_, 0);
lean_inc_ref(v_s_3880_);
lean_dec_ref(v_scope_3859_);
v___y_3863_ = v_s_3880_;
goto v___jp_3862_;
v___jp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v_key_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3864_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3865_ = lean_string_append(v___y_3863_, v___x_3864_);
v___x_3866_ = l_Lake_Hash_hex(v_contentHash_3856_);
v___x_3867_ = lean_string_append(v___x_3865_, v___x_3866_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3869_ = lean_string_append(v___x_3867_, v___x_3868_);
v___x_3870_ = lean_string_append(v___x_3869_, v_art_3857_);
v___x_3871_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3872_ = lean_string_append(v___x_3870_, v___x_3871_);
v___x_3873_ = lean_string_append(v___x_3872_, v_url_3861_);
v___x_3874_ = 1;
v___x_3875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3875_, 0, v___x_3873_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*1, v___x_3874_);
lean_inc_ref(v___y_3855_);
v___x_3876_ = lean_apply_2(v___y_3855_, v___x_3875_, lean_box(0));
v_key_3877_ = lean_ctor_get(v_service_3858_, 1);
lean_inc_ref(v_key_3877_);
lean_dec_ref(v_service_3858_);
v___x_3878_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3879_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v___y_3855_, v_art_3857_, v___x_3878_, v_url_3861_, v_key_3877_);
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object* v___y_3881_, lean_object* v_contentHash_3882_, lean_object* v_art_3883_, lean_object* v_service_3884_, lean_object* v_scope_3885_, lean_object* v_a_3886_){
_start:
{
uint64_t v_contentHash_boxed_3887_; lean_object* v_res_3888_; 
v_contentHash_boxed_3887_ = lean_unbox_uint64(v_contentHash_3882_);
lean_dec_ref(v_contentHash_3882_);
v_res_3888_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3881_, v_contentHash_boxed_3887_, v_art_3883_, v_service_3884_, v_scope_3885_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object* v_descrs_3889_, lean_object* v_paths_3890_, lean_object* v_service_3891_, lean_object* v_scope_3892_, lean_object* v_n_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; uint64_t v_hash_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3896_ = lean_array_fget_borrowed(v_descrs_3889_, v_n_3893_);
v_hash_3897_ = lean_ctor_get_uint64(v___x_3896_, sizeof(void*)*1);
v___x_3898_ = lean_array_fget_borrowed(v_paths_3890_, v_n_3893_);
lean_inc(v___x_3898_);
v___x_3899_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3894_, v_hash_3897_, v___x_3898_, v_service_3891_, v_scope_3892_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object* v_descrs_3900_, lean_object* v_paths_3901_, lean_object* v_service_3902_, lean_object* v_scope_3903_, lean_object* v_n_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(v_descrs_3900_, v_paths_3901_, v_service_3902_, v_scope_3903_, v_n_3904_, v___y_3905_);
lean_dec(v_n_3904_);
lean_dec_ref(v_paths_3901_);
lean_dec_ref(v_descrs_3900_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object* v_descrs_3908_, lean_object* v_paths_3909_, lean_object* v_service_3910_, lean_object* v_scope_3911_, lean_object* v_n_3912_, lean_object* v_h_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(v_descrs_3908_, v_paths_3909_, v_service_3910_, v_scope_3911_, v_n_3912_, v___y_3914_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object* v_descrs_3917_, lean_object* v_paths_3918_, lean_object* v_service_3919_, lean_object* v_scope_3920_, lean_object* v_n_3921_, lean_object* v_h_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lake_CacheService_uploadArtifacts___elam__0(v_descrs_3917_, v_paths_3918_, v_service_3919_, v_scope_3920_, v_n_3921_, v_h_3922_, v___y_3923_);
lean_dec(v_n_3921_);
lean_dec_ref(v_paths_3918_);
lean_dec_ref(v_descrs_3917_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(lean_object* v___y_3926_, lean_object* v_descrs_3927_, lean_object* v_paths_3928_, lean_object* v_service_3929_, lean_object* v_scope_3930_, lean_object* v_n_3931_){
_start:
{
lean_object* v___x_3933_; uint64_t v_hash_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3933_ = lean_array_fget_borrowed(v_descrs_3927_, v_n_3931_);
v_hash_3934_ = lean_ctor_get_uint64(v___x_3933_, sizeof(void*)*1);
v___x_3935_ = lean_array_fget_borrowed(v_paths_3928_, v_n_3931_);
lean_inc(v___x_3935_);
v___x_3936_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3926_, v_hash_3934_, v___x_3935_, v_service_3929_, v_scope_3930_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg___boxed(lean_object* v___y_3937_, lean_object* v_descrs_3938_, lean_object* v_paths_3939_, lean_object* v_service_3940_, lean_object* v_scope_3941_, lean_object* v_n_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3937_, v_descrs_3938_, v_paths_3939_, v_service_3940_, v_scope_3941_, v_n_3942_);
lean_dec(v_n_3942_);
lean_dec_ref(v_paths_3939_);
lean_dec_ref(v_descrs_3938_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(lean_object* v_descrs_3945_, lean_object* v_paths_3946_, lean_object* v_service_3947_, lean_object* v_scope_3948_, lean_object* v_n_3949_, lean_object* v_i_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_zero_3953_; uint8_t v_isZero_3954_; 
v_zero_3953_ = lean_unsigned_to_nat(0u);
v_isZero_3954_ = lean_nat_dec_eq(v_i_3950_, v_zero_3953_);
if (v_isZero_3954_ == 1)
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref(v___y_3951_);
lean_dec(v_i_3950_);
lean_dec_ref(v_scope_3948_);
lean_dec_ref(v_service_3947_);
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
else
{
lean_object* v_one_3957_; lean_object* v_n_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v_one_3957_ = lean_unsigned_to_nat(1u);
v_n_3958_ = lean_nat_sub(v_i_3950_, v_one_3957_);
lean_dec(v_i_3950_);
v___x_3959_ = lean_nat_sub(v_n_3949_, v_n_3958_);
v___x_3960_ = lean_nat_sub(v___x_3959_, v_one_3957_);
lean_dec(v___x_3959_);
lean_inc_ref(v_scope_3948_);
lean_inc_ref(v_service_3947_);
lean_inc_ref(v___y_3951_);
v___x_3961_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3951_, v_descrs_3945_, v_paths_3946_, v_service_3947_, v_scope_3948_, v___x_3960_);
lean_dec(v___x_3960_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_dec_ref(v___x_3961_);
v_i_3950_ = v_n_3958_;
goto _start;
}
else
{
lean_dec(v_n_3958_);
lean_dec_ref(v___y_3951_);
lean_dec_ref(v_scope_3948_);
lean_dec_ref(v_service_3947_);
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg___boxed(lean_object* v_descrs_3963_, lean_object* v_paths_3964_, lean_object* v_service_3965_, lean_object* v_scope_3966_, lean_object* v_n_3967_, lean_object* v_i_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3963_, v_paths_3964_, v_service_3965_, v_scope_3966_, v_n_3967_, v_i_3968_, v___y_3969_);
lean_dec(v_n_3967_);
lean_dec_ref(v_paths_3964_);
lean_dec_ref(v_descrs_3963_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_3972_, lean_object* v_descrs_3973_, lean_object* v_paths_3974_, lean_object* v_service_3975_, lean_object* v_scope_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v___x_3979_; 
lean_inc(v_n_3972_);
v___x_3979_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3973_, v_paths_3974_, v_service_3975_, v_scope_3976_, v_n_3972_, v_n_3972_, v_a_3977_);
lean_dec(v_n_3972_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_3980_, lean_object* v_descrs_3981_, lean_object* v_paths_3982_, lean_object* v_service_3983_, lean_object* v_scope_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lake_CacheService_uploadArtifacts(v_n_3980_, v_descrs_3981_, v_paths_3982_, v_service_3983_, v_scope_3984_, v_a_3985_);
lean_dec_ref(v_paths_3982_);
lean_dec_ref(v_descrs_3981_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(lean_object* v_descrs_3988_, lean_object* v_paths_3989_, lean_object* v_service_3990_, lean_object* v_scope_3991_, lean_object* v_n_3992_, lean_object* v_i_3993_, lean_object* v_a_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3988_, v_paths_3989_, v_service_3990_, v_scope_3991_, v_n_3992_, v_i_3993_, v___y_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___boxed(lean_object* v_descrs_3998_, lean_object* v_paths_3999_, lean_object* v_service_4000_, lean_object* v_scope_4001_, lean_object* v_n_4002_, lean_object* v_i_4003_, lean_object* v_a_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(v_descrs_3998_, v_paths_3999_, v_service_4000_, v_scope_4001_, v_n_4002_, v_i_4003_, v_a_4004_, v___y_4005_);
lean_dec(v_n_4002_);
lean_dec_ref(v_paths_3999_);
lean_dec_ref(v_descrs_3998_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(lean_object* v___y_4008_, lean_object* v_descrs_4009_, lean_object* v_paths_4010_, lean_object* v_service_4011_, lean_object* v_scope_4012_, lean_object* v_n_4013_, lean_object* v_h_4014_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_4008_, v_descrs_4009_, v_paths_4010_, v_service_4011_, v_scope_4012_, v_n_4013_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___boxed(lean_object* v___y_4017_, lean_object* v_descrs_4018_, lean_object* v_paths_4019_, lean_object* v_service_4020_, lean_object* v_scope_4021_, lean_object* v_n_4022_, lean_object* v_h_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(v___y_4017_, v_descrs_4018_, v_paths_4019_, v_service_4020_, v_scope_4021_, v_n_4022_, v_h_4023_);
lean_dec(v_n_4022_);
lean_dec_ref(v_paths_4019_);
lean_dec_ref(v_descrs_4018_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_4030_, lean_object* v_service_4031_, lean_object* v_scope_4032_, lean_object* v_platform_4033_, lean_object* v_toolchain_4034_){
_start:
{
lean_object* v_url_4036_; lean_object* v_url_4043_; 
if (lean_obj_tag(v_scope_4032_) == 0)
{
lean_object* v_s_4052_; lean_object* v_revisionEndpoint_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec_ref(v_platform_4033_);
v_s_4052_ = lean_ctor_get(v_scope_4032_, 0);
lean_inc_ref(v_s_4052_);
lean_dec_ref(v_scope_4032_);
v_revisionEndpoint_4053_ = lean_ctor_get(v_service_4031_, 3);
lean_inc_ref(v_revisionEndpoint_4053_);
lean_dec_ref(v_service_4031_);
v___x_4054_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_4053_, v_s_4052_);
v___x_4055_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_4056_ = lean_string_append(v___x_4055_, v_rev_4030_);
v___x_4057_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_4058_ = lean_string_append(v___x_4056_, v___x_4057_);
v___x_4059_ = lean_string_append(v___x_4054_, v___x_4058_);
lean_dec_ref(v___x_4058_);
return v___x_4059_;
}
else
{
lean_object* v_s_4060_; lean_object* v_revisionEndpoint_4061_; lean_object* v_url_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v_s_4060_ = lean_ctor_get(v_scope_4032_, 0);
lean_inc_ref(v_s_4060_);
lean_dec_ref(v_scope_4032_);
v_revisionEndpoint_4061_ = lean_ctor_get(v_service_4031_, 3);
lean_inc_ref(v_revisionEndpoint_4061_);
lean_dec_ref(v_service_4031_);
v_url_4062_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_4061_, v_s_4060_);
v___x_4063_ = lean_string_utf8_byte_size(v_platform_4033_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = lean_nat_dec_eq(v___x_4063_, v___x_4064_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v_url_4068_; 
v___x_4066_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_4067_ = lean_string_append(v_url_4062_, v___x_4066_);
v_url_4068_ = l_Lake_uriEncode(v_platform_4033_, v___x_4067_);
v_url_4043_ = v_url_4068_;
goto v___jp_4042_;
}
else
{
lean_dec_ref(v_platform_4033_);
v_url_4043_ = v_url_4062_;
goto v___jp_4042_;
}
}
v___jp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4037_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_4038_ = lean_string_append(v_url_4036_, v___x_4037_);
v___x_4039_ = lean_string_append(v___x_4038_, v_rev_4030_);
v___x_4040_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_4041_ = lean_string_append(v___x_4039_, v___x_4040_);
return v___x_4041_;
}
v___jp_4042_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4044_ = lean_string_utf8_byte_size(v_toolchain_4034_);
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = lean_nat_dec_eq(v___x_4044_, v___x_4045_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v_url_4051_; 
v___x_4047_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_4048_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_4034_, v___x_4047_, v___x_4045_);
v___x_4049_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_4050_ = lean_string_append(v_url_4043_, v___x_4049_);
v_url_4051_ = l_Lake_uriEncode(v___x_4048_, v___x_4050_);
v_url_4036_ = v_url_4051_;
goto v___jp_4035_;
}
else
{
v_url_4036_ = v_url_4043_;
goto v___jp_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_4069_, lean_object* v_service_4070_, lean_object* v_scope_4071_, lean_object* v_platform_4072_, lean_object* v_toolchain_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_4069_, v_service_4070_, v_scope_4071_, v_platform_4072_, v_toolchain_4073_);
lean_dec_ref(v_toolchain_4073_);
lean_dec_ref(v_rev_4069_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_4078_, lean_object* v_service_4079_, lean_object* v_scope_4080_, lean_object* v_platform_4081_, lean_object* v_toolchain_4082_){
_start:
{
lean_object* v_url_4084_; lean_object* v___y_4092_; uint8_t v_isReservoir_4102_; 
v_isReservoir_4102_ = lean_ctor_get_uint8(v_service_4079_, sizeof(void*)*5);
if (v_isReservoir_4102_ == 0)
{
lean_object* v___x_4103_; 
v___x_4103_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_4078_, v_service_4079_, v_scope_4080_, v_platform_4081_, v_toolchain_4082_);
lean_dec_ref(v_toolchain_4082_);
return v___x_4103_;
}
else
{
if (lean_obj_tag(v_scope_4080_) == 0)
{
lean_object* v_apiEndpoint_4104_; lean_object* v_s_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_apiEndpoint_4104_ = lean_ctor_get(v_service_4079_, 4);
lean_inc_ref(v_apiEndpoint_4104_);
lean_dec_ref(v_service_4079_);
v_s_4105_ = lean_ctor_get(v_scope_4080_, 0);
lean_inc_ref(v_s_4105_);
lean_dec_ref(v_scope_4080_);
v___x_4106_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_4107_ = lean_string_append(v_apiEndpoint_4104_, v___x_4106_);
v___x_4108_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4107_, v_s_4105_);
v___y_4092_ = v___x_4108_;
goto v___jp_4091_;
}
else
{
lean_object* v_apiEndpoint_4109_; lean_object* v_s_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v_apiEndpoint_4109_ = lean_ctor_get(v_service_4079_, 4);
lean_inc_ref(v_apiEndpoint_4109_);
lean_dec_ref(v_service_4079_);
v_s_4110_ = lean_ctor_get(v_scope_4080_, 0);
lean_inc_ref(v_s_4110_);
lean_dec_ref(v_scope_4080_);
v___x_4111_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_4112_ = lean_string_append(v_apiEndpoint_4109_, v___x_4111_);
v___x_4113_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4112_, v_s_4110_);
v___y_4092_ = v___x_4113_;
goto v___jp_4091_;
}
}
v___jp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; 
v___x_4085_ = lean_string_utf8_byte_size(v_toolchain_4082_);
v___x_4086_ = lean_unsigned_to_nat(0u);
v___x_4087_ = lean_nat_dec_eq(v___x_4085_, v___x_4086_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v_url_4090_; 
v___x_4088_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_4089_ = lean_string_append(v_url_4084_, v___x_4088_);
v_url_4090_ = l_Lake_uriEncode(v_toolchain_4082_, v___x_4089_);
return v_url_4090_;
}
else
{
lean_dec_ref(v_toolchain_4082_);
return v_url_4084_;
}
}
v___jp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v_url_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; 
v___x_4093_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_4094_ = lean_string_append(v___y_4092_, v___x_4093_);
v_url_4095_ = lean_string_append(v___x_4094_, v_rev_4078_);
v___x_4096_ = lean_string_utf8_byte_size(v_platform_4081_);
v___x_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = lean_nat_dec_eq(v___x_4096_, v___x_4097_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v_url_4101_; 
v___x_4099_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_4100_ = lean_string_append(v_url_4095_, v___x_4099_);
v_url_4101_ = l_Lake_uriEncode(v_platform_4081_, v___x_4100_);
v_url_4084_ = v_url_4101_;
goto v___jp_4083_;
}
else
{
lean_dec_ref(v_platform_4081_);
v_url_4084_ = v_url_4095_;
goto v___jp_4083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_4114_, lean_object* v_service_4115_, lean_object* v_scope_4116_, lean_object* v_platform_4117_, lean_object* v_toolchain_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lake_CacheService_revisionUrl(v_rev_4114_, v_service_4115_, v_scope_4116_, v_platform_4117_, v_toolchain_4118_);
lean_dec_ref(v_rev_4114_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_4124_, lean_object* v_cache_4125_, lean_object* v_service_4126_, lean_object* v_localScope_4127_, lean_object* v_remoteScope_4128_, lean_object* v_platform_4129_, lean_object* v_toolchain_4130_, uint8_t v_force_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v_a_4138_; lean_object* v_a_4145_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v_a_4158_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v_path_4167_; lean_object* v_a_4169_; lean_object* v___y_4271_; lean_object* v___y_4272_; uint8_t v___x_4321_; lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4162_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_4163_ = l_System_FilePath_join(v_cache_4125_, v___x_4162_);
lean_inc_ref(v_localScope_4127_);
v___x_4164_ = l_System_FilePath_join(v___x_4163_, v_localScope_4127_);
v___x_4165_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_4124_);
v___x_4166_ = lean_string_append(v_rev_4124_, v___x_4165_);
v_path_4167_ = l_System_FilePath_join(v___x_4164_, v___x_4166_);
v___x_4321_ = l_System_FilePath_pathExists(v_path_4167_);
v___x_4385_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4386_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_4386_ == 0)
{
goto v___jp_4322_;
}
else
{
lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4387_ = lean_box(0);
v___x_4388_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_4388_ == 0)
{
if (v___x_4386_ == 0)
{
goto v___jp_4322_;
}
else
{
size_t v___x_4389_; size_t v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = ((size_t)0ULL);
v___x_4390_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_4132_);
v___x_4391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_4385_, v___x_4389_, v___x_4390_, v___x_4387_, v_a_4132_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_dec_ref(v___x_4391_);
goto v___jp_4322_;
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_a_4132_);
lean_dec_ref(v_toolchain_4130_);
lean_dec_ref(v_platform_4129_);
lean_dec_ref(v_remoteScope_4128_);
lean_dec_ref(v_localScope_4127_);
lean_dec_ref(v_service_4126_);
lean_dec_ref(v_rev_4124_);
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
else
{
size_t v___x_4400_; size_t v___x_4401_; lean_object* v___x_4402_; 
v___x_4400_ = ((size_t)0ULL);
v___x_4401_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_4132_);
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_4385_, v___x_4400_, v___x_4401_, v___x_4387_, v_a_4132_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref(v___x_4402_);
goto v___jp_4322_;
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_a_4132_);
lean_dec_ref(v_toolchain_4130_);
lean_dec_ref(v_platform_4129_);
lean_dec_ref(v_remoteScope_4128_);
lean_dec_ref(v_localScope_4127_);
lean_dec_ref(v_service_4126_);
lean_dec_ref(v_rev_4124_);
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4402_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4402_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
v___jp_4134_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = lean_box(0);
v___x_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
v___jp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4139_, 0, v_a_4138_);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
return v___x_4140_;
}
v___jp_4141_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_box(0);
v___x_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
return v___x_4143_;
}
v___jp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_a_4145_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
return v___x_4147_;
}
v___jp_4148_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4151_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_4152_ = lean_string_append(v___y_4150_, v___x_4151_);
v___x_4153_ = 3;
v___x_4154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4154_, 0, v___x_4152_);
lean_ctor_set_uint8(v___x_4154_, sizeof(void*)*1, v___x_4153_);
v___x_4155_ = lean_apply_2(v_a_4132_, v___x_4154_, lean_box(0));
v___x_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4149_);
return v___x_4156_;
}
v___jp_4157_:
{
lean_object* v_s_4159_; 
v_s_4159_ = lean_ctor_get(v_remoteScope_4128_, 0);
lean_inc_ref(v_s_4159_);
lean_dec_ref(v_remoteScope_4128_);
v___y_4149_ = v_a_4158_;
v___y_4150_ = v_s_4159_;
goto v___jp_4148_;
}
v___jp_4160_:
{
lean_object* v___x_4161_; 
v___x_4161_ = lean_box(0);
v_a_4158_ = v___x_4161_;
goto v___jp_4157_;
}
v___jp_4168_:
{
if (lean_obj_tag(v_a_4169_) == 1)
{
lean_object* v_val_4170_; lean_object* v___x_4171_; 
v_val_4170_ = lean_ctor_get(v_a_4169_, 0);
lean_inc(v_val_4170_);
lean_dec_ref(v_a_4169_);
lean_inc_ref(v_path_4167_);
v___x_4171_ = l_Lake_createParentDirs(v_path_4167_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v___x_4171_);
v___x_4172_ = l_IO_FS_writeFile(v_path_4167_, v_val_4170_);
lean_dec(v_val_4170_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4240_; 
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4240_ == 0)
{
lean_object* v_unused_4241_; 
v_unused_4241_ = lean_ctor_get(v___x_4172_, 0);
lean_dec(v_unused_4241_);
v___x_4174_ = v___x_4172_;
v_isShared_4175_ = v_isSharedCheck_4240_;
goto v_resetjp_4173_;
}
else
{
lean_dec(v___x_4172_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4240_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4176_ = lean_string_utf8_byte_size(v_platform_4129_);
lean_dec_ref(v_platform_4129_);
v___x_4177_ = lean_unsigned_to_nat(0u);
v___x_4178_ = lean_nat_dec_eq(v___x_4176_, v___x_4177_);
v___x_4179_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4180_ = l_Lake_CacheMap_load(v_path_4167_, v___x_4178_, v___x_4179_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v_a_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
lean_del_object(v___x_4174_);
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
v_a_4182_ = lean_ctor_get(v___x_4180_, 1);
lean_inc(v_a_4182_);
lean_dec_ref(v___x_4180_);
v___x_4183_ = lean_array_get_size(v_a_4182_);
v___x_4184_ = lean_nat_dec_lt(v___x_4177_, v___x_4183_);
if (v___x_4184_ == 0)
{
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4132_);
v_a_4145_ = v_a_4181_;
goto v___jp_4144_;
}
else
{
lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4185_ = lean_box(0);
v___x_4186_ = lean_nat_dec_le(v___x_4183_, v___x_4183_);
if (v___x_4186_ == 0)
{
if (v___x_4184_ == 0)
{
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4132_);
v_a_4145_ = v_a_4181_;
goto v___jp_4144_;
}
else
{
size_t v___x_4187_; size_t v___x_4188_; lean_object* v___x_4189_; 
v___x_4187_ = ((size_t)0ULL);
v___x_4188_ = lean_usize_of_nat(v___x_4183_);
v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4182_, v___x_4187_, v___x_4188_, v___x_4185_, v_a_4132_);
lean_dec(v_a_4182_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref(v___x_4189_);
v_a_4145_ = v_a_4181_;
goto v___jp_4144_;
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec(v_a_4181_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
else
{
size_t v___x_4198_; size_t v___x_4199_; lean_object* v___x_4200_; 
v___x_4198_ = ((size_t)0ULL);
v___x_4199_ = lean_usize_of_nat(v___x_4183_);
v___x_4200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4182_, v___x_4198_, v___x_4199_, v___x_4185_, v_a_4132_);
lean_dec(v_a_4182_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_dec_ref(v___x_4200_);
v_a_4145_ = v_a_4181_;
goto v___jp_4144_;
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_a_4181_);
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
v_a_4209_ = lean_ctor_get(v___x_4180_, 1);
lean_inc(v_a_4209_);
lean_dec_ref(v___x_4180_);
v___x_4210_ = lean_array_get_size(v_a_4209_);
v___x_4211_ = lean_nat_dec_lt(v___x_4177_, v___x_4210_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; lean_object* v___x_4214_; 
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4132_);
v___x_4212_ = lean_box(0);
if (v_isShared_4175_ == 0)
{
lean_ctor_set_tag(v___x_4174_, 1);
lean_ctor_set(v___x_4174_, 0, v___x_4212_);
v___x_4214_ = v___x_4174_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
else
{
lean_object* v___x_4216_; uint8_t v___x_4217_; 
lean_del_object(v___x_4174_);
v___x_4216_ = lean_box(0);
v___x_4217_ = lean_nat_dec_le(v___x_4210_, v___x_4210_);
if (v___x_4217_ == 0)
{
if (v___x_4211_ == 0)
{
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4132_);
goto v___jp_4141_;
}
else
{
size_t v___x_4218_; size_t v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = ((size_t)0ULL);
v___x_4219_ = lean_usize_of_nat(v___x_4210_);
v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4209_, v___x_4218_, v___x_4219_, v___x_4216_, v_a_4132_);
lean_dec(v_a_4209_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_dec_ref(v___x_4220_);
goto v___jp_4141_;
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
else
{
size_t v___x_4229_; size_t v___x_4230_; lean_object* v___x_4231_; 
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = lean_usize_of_nat(v___x_4210_);
v___x_4231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4209_, v___x_4229_, v___x_4230_, v___x_4216_, v_a_4132_);
lean_dec(v_a_4209_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_dec_ref(v___x_4231_);
goto v___jp_4141_;
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
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
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_platform_4129_);
v_a_4242_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4244_ = v___x_4172_;
v_isShared_4245_ = v_isSharedCheck_4254_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4172_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4254_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4252_; 
v___x_4246_ = lean_io_error_to_string(v_a_4242_);
v___x_4247_ = 3;
v___x_4248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set_uint8(v___x_4248_, sizeof(void*)*1, v___x_4247_);
v___x_4249_ = lean_apply_2(v_a_4132_, v___x_4248_, lean_box(0));
v___x_4250_ = lean_box(0);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4250_);
v___x_4252_ = v___x_4244_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4250_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v_val_4170_);
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_platform_4129_);
v_a_4255_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4257_ = v___x_4171_;
v_isShared_4258_ = v_isSharedCheck_4267_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4171_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4267_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4265_; 
v___x_4259_ = lean_io_error_to_string(v_a_4255_);
v___x_4260_ = 3;
v___x_4261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4261_, 0, v___x_4259_);
lean_ctor_set_uint8(v___x_4261_, sizeof(void*)*1, v___x_4260_);
v___x_4262_ = lean_apply_2(v_a_4132_, v___x_4261_, lean_box(0));
v___x_4263_ = lean_box(0);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4263_);
v___x_4265_ = v___x_4257_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_dec(v_a_4169_);
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_a_4132_);
lean_dec_ref(v_platform_4129_);
v___x_4268_ = lean_box(0);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
}
v___jp_4270_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = lean_unsigned_to_nat(0u);
v___x_4274_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4275_ = l_Lake_getUrl_x3f(v___y_4271_, v___y_4272_, v___x_4274_);
lean_dec_ref(v___y_4272_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v_a_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
v_a_4277_ = lean_ctor_get(v___x_4275_, 1);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4275_);
v___x_4278_ = lean_array_get_size(v_a_4277_);
v___x_4279_ = lean_nat_dec_lt(v___x_4273_, v___x_4278_);
if (v___x_4279_ == 0)
{
lean_dec(v_a_4277_);
lean_dec_ref(v_remoteScope_4128_);
v_a_4169_ = v_a_4276_;
goto v___jp_4168_;
}
else
{
lean_object* v___x_4280_; uint8_t v___x_4281_; 
v___x_4280_ = lean_box(0);
v___x_4281_ = lean_nat_dec_le(v___x_4278_, v___x_4278_);
if (v___x_4281_ == 0)
{
if (v___x_4279_ == 0)
{
lean_dec(v_a_4277_);
lean_dec_ref(v_remoteScope_4128_);
v_a_4169_ = v_a_4276_;
goto v___jp_4168_;
}
else
{
size_t v___x_4282_; size_t v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = ((size_t)0ULL);
v___x_4283_ = lean_usize_of_nat(v___x_4278_);
lean_inc_ref(v_a_4132_);
v___x_4284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4277_, v___x_4282_, v___x_4283_, v___x_4280_, v_a_4132_);
lean_dec(v_a_4277_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_dec_ref(v___x_4284_);
lean_dec_ref(v_remoteScope_4128_);
v_a_4169_ = v_a_4276_;
goto v___jp_4168_;
}
else
{
lean_object* v_a_4285_; 
lean_dec(v_a_4276_);
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_platform_4129_);
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref(v___x_4284_);
v_a_4158_ = v_a_4285_;
goto v___jp_4157_;
}
}
}
else
{
size_t v___x_4286_; size_t v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = ((size_t)0ULL);
v___x_4287_ = lean_usize_of_nat(v___x_4278_);
lean_inc_ref(v_a_4132_);
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4277_, v___x_4286_, v___x_4287_, v___x_4280_, v_a_4132_);
lean_dec(v_a_4277_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_dec_ref(v___x_4288_);
lean_dec_ref(v_remoteScope_4128_);
v_a_4169_ = v_a_4276_;
goto v___jp_4168_;
}
else
{
lean_object* v_a_4289_; 
lean_dec(v_a_4276_);
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_platform_4129_);
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref(v___x_4288_);
v_a_4158_ = v_a_4289_;
goto v___jp_4157_;
}
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
lean_dec_ref(v_path_4167_);
lean_dec_ref(v_platform_4129_);
v_a_4290_ = lean_ctor_get(v___x_4275_, 1);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4275_);
v___x_4291_ = lean_array_get_size(v_a_4290_);
v___x_4292_ = lean_nat_dec_lt(v___x_4273_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
lean_dec(v_a_4290_);
v___x_4293_ = lean_box(0);
v_a_4158_ = v___x_4293_;
goto v___jp_4157_;
}
else
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_box(0);
v___x_4295_ = lean_nat_dec_le(v___x_4291_, v___x_4291_);
if (v___x_4295_ == 0)
{
if (v___x_4292_ == 0)
{
lean_dec(v_a_4290_);
goto v___jp_4160_;
}
else
{
size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = ((size_t)0ULL);
v___x_4297_ = lean_usize_of_nat(v___x_4291_);
lean_inc_ref(v_a_4132_);
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4290_, v___x_4296_, v___x_4297_, v___x_4294_, v_a_4132_);
lean_dec(v_a_4290_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_dec_ref(v___x_4298_);
goto v___jp_4160_;
}
else
{
lean_object* v_a_4299_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref(v___x_4298_);
v_a_4158_ = v_a_4299_;
goto v___jp_4157_;
}
}
}
else
{
size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = ((size_t)0ULL);
v___x_4301_ = lean_usize_of_nat(v___x_4291_);
lean_inc_ref(v_a_4132_);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4290_, v___x_4300_, v___x_4301_, v___x_4294_, v_a_4132_);
lean_dec(v_a_4290_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_dec_ref(v___x_4302_);
goto v___jp_4160_;
}
else
{
lean_object* v_a_4303_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref(v___x_4302_);
v_a_4158_ = v_a_4303_;
goto v___jp_4157_;
}
}
}
}
}
v___jp_4304_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v_isReservoir_4318_; 
lean_inc_ref(v_platform_4129_);
lean_inc_ref(v_remoteScope_4128_);
lean_inc_ref(v_service_4126_);
v___x_4305_ = l_Lake_CacheService_revisionUrl(v_rev_4124_, v_service_4126_, v_remoteScope_4128_, v_platform_4129_, v_toolchain_4130_);
v___x_4306_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_4307_ = lean_string_append(v_localScope_4127_, v___x_4306_);
v___x_4308_ = lean_string_append(v___x_4307_, v_rev_4124_);
lean_dec_ref(v_rev_4124_);
v___x_4309_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4310_ = lean_string_append(v___x_4308_, v___x_4309_);
v___x_4311_ = lean_string_append(v___x_4310_, v_path_4167_);
v___x_4312_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4313_ = lean_string_append(v___x_4311_, v___x_4312_);
v___x_4314_ = lean_string_append(v___x_4313_, v___x_4305_);
v___x_4315_ = 1;
v___x_4316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set_uint8(v___x_4316_, sizeof(void*)*1, v___x_4315_);
lean_inc_ref(v_a_4132_);
v___x_4317_ = lean_apply_2(v_a_4132_, v___x_4316_, lean_box(0));
v_isReservoir_4318_ = lean_ctor_get_uint8(v_service_4126_, sizeof(void*)*5);
lean_dec_ref(v_service_4126_);
if (v_isReservoir_4318_ == 0)
{
lean_object* v___x_4319_; 
v___x_4319_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_4271_ = v___x_4305_;
v___y_4272_ = v___x_4319_;
goto v___jp_4270_;
}
else
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lake_Reservoir_lakeHeaders;
v___y_4271_ = v___x_4305_;
v___y_4272_ = v___x_4320_;
goto v___jp_4270_;
}
}
v___jp_4322_:
{
if (v___x_4321_ == 0)
{
goto v___jp_4304_;
}
else
{
if (v_force_4131_ == 0)
{
lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
lean_dec_ref(v_toolchain_4130_);
lean_dec_ref(v_remoteScope_4128_);
lean_dec_ref(v_localScope_4127_);
lean_dec_ref(v_service_4126_);
lean_dec_ref(v_rev_4124_);
v___x_4323_ = lean_string_utf8_byte_size(v_platform_4129_);
lean_dec_ref(v_platform_4129_);
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = lean_nat_dec_eq(v___x_4323_, v___x_4324_);
v___x_4326_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4327_ = l_Lake_CacheMap_load(v_path_4167_, v___x_4325_, v___x_4326_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v_a_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
v_a_4329_ = lean_ctor_get(v___x_4327_, 1);
lean_inc(v_a_4329_);
lean_dec_ref(v___x_4327_);
v___x_4330_ = lean_array_get_size(v_a_4329_);
v___x_4331_ = lean_nat_dec_lt(v___x_4324_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4132_);
v_a_4138_ = v_a_4328_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4332_ = lean_box(0);
v___x_4333_ = lean_nat_dec_le(v___x_4330_, v___x_4330_);
if (v___x_4333_ == 0)
{
if (v___x_4331_ == 0)
{
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4132_);
v_a_4138_ = v_a_4328_;
goto v___jp_4137_;
}
else
{
size_t v___x_4334_; size_t v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = ((size_t)0ULL);
v___x_4335_ = lean_usize_of_nat(v___x_4330_);
v___x_4336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4329_, v___x_4334_, v___x_4335_, v___x_4332_, v_a_4132_);
lean_dec(v_a_4329_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_dec_ref(v___x_4336_);
v_a_4138_ = v_a_4328_;
goto v___jp_4137_;
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec(v_a_4328_);
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
else
{
size_t v___x_4345_; size_t v___x_4346_; lean_object* v___x_4347_; 
v___x_4345_ = ((size_t)0ULL);
v___x_4346_ = lean_usize_of_nat(v___x_4330_);
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4329_, v___x_4345_, v___x_4346_, v___x_4332_, v_a_4132_);
lean_dec(v_a_4329_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_dec_ref(v___x_4347_);
v_a_4138_ = v_a_4328_;
goto v___jp_4137_;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec(v_a_4328_);
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4347_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_a_4356_ = lean_ctor_get(v___x_4327_, 1);
lean_inc(v_a_4356_);
lean_dec_ref(v___x_4327_);
v___x_4357_ = lean_array_get_size(v_a_4356_);
v___x_4358_ = lean_nat_dec_lt(v___x_4324_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_dec(v_a_4356_);
lean_dec_ref(v_a_4132_);
v___x_4359_ = lean_box(0);
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
return v___x_4360_;
}
else
{
lean_object* v___x_4361_; uint8_t v___x_4362_; 
v___x_4361_ = lean_box(0);
v___x_4362_ = lean_nat_dec_le(v___x_4357_, v___x_4357_);
if (v___x_4362_ == 0)
{
if (v___x_4358_ == 0)
{
lean_dec(v_a_4356_);
lean_dec_ref(v_a_4132_);
goto v___jp_4134_;
}
else
{
size_t v___x_4363_; size_t v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = ((size_t)0ULL);
v___x_4364_ = lean_usize_of_nat(v___x_4357_);
v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4356_, v___x_4363_, v___x_4364_, v___x_4361_, v_a_4132_);
lean_dec(v_a_4356_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_dec_ref(v___x_4365_);
goto v___jp_4134_;
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
else
{
size_t v___x_4374_; size_t v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = ((size_t)0ULL);
v___x_4375_ = lean_usize_of_nat(v___x_4357_);
v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4356_, v___x_4374_, v___x_4375_, v___x_4361_, v_a_4132_);
lean_dec(v_a_4356_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_dec_ref(v___x_4376_);
goto v___jp_4134_;
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4376_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4376_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
}
}
else
{
goto v___jp_4304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_4411_, lean_object* v_cache_4412_, lean_object* v_service_4413_, lean_object* v_localScope_4414_, lean_object* v_remoteScope_4415_, lean_object* v_platform_4416_, lean_object* v_toolchain_4417_, lean_object* v_force_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
uint8_t v_force_boxed_4421_; lean_object* v_res_4422_; 
v_force_boxed_4421_ = lean_unbox(v_force_4418_);
v_res_4422_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_4411_, v_cache_4412_, v_service_4413_, v_localScope_4414_, v_remoteScope_4415_, v_platform_4416_, v_toolchain_4417_, v_force_boxed_4421_, v_a_4419_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_4424_, lean_object* v_outputs_4425_, lean_object* v_service_4426_, lean_object* v_scope_4427_, lean_object* v_platform_4428_, lean_object* v_toolchain_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v_url_4432_; lean_object* v___y_4434_; lean_object* v_s_4450_; 
lean_inc_ref(v_scope_4427_);
lean_inc_ref(v_service_4426_);
v_url_4432_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_4424_, v_service_4426_, v_scope_4427_, v_platform_4428_, v_toolchain_4429_);
v_s_4450_ = lean_ctor_get(v_scope_4427_, 0);
lean_inc_ref(v_s_4450_);
lean_dec_ref(v_scope_4427_);
v___y_4434_ = v_s_4450_;
goto v___jp_4433_;
v___jp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v_key_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4435_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_4436_ = lean_string_append(v___y_4434_, v___x_4435_);
v___x_4437_ = lean_string_append(v___x_4436_, v_rev_4424_);
v___x_4438_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4439_ = lean_string_append(v___x_4437_, v___x_4438_);
v___x_4440_ = lean_string_append(v___x_4439_, v_outputs_4425_);
v___x_4441_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4442_ = lean_string_append(v___x_4440_, v___x_4441_);
v___x_4443_ = lean_string_append(v___x_4442_, v_url_4432_);
v___x_4444_ = 1;
v___x_4445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4445_, 0, v___x_4443_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*1, v___x_4444_);
lean_inc_ref(v_a_4430_);
v___x_4446_ = lean_apply_2(v_a_4430_, v___x_4445_, lean_box(0));
v_key_4447_ = lean_ctor_get(v_service_4426_, 1);
lean_inc_ref(v_key_4447_);
lean_dec_ref(v_service_4426_);
v___x_4448_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_4449_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_4430_, v_outputs_4425_, v___x_4448_, v_url_4432_, v_key_4447_);
return v___x_4449_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_4451_, lean_object* v_outputs_4452_, lean_object* v_service_4453_, lean_object* v_scope_4454_, lean_object* v_platform_4455_, lean_object* v_toolchain_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_4451_, v_outputs_4452_, v_service_4453_, v_scope_4454_, v_platform_4455_, v_toolchain_4456_, v_a_4457_);
lean_dec_ref(v_toolchain_4456_);
lean_dec_ref(v_rev_4451_);
return v_res_4459_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedCache_default = _init_l_Lake_instInhabitedCache_default();
lean_mark_persistent(l_Lake_instInhabitedCache_default);
l_Lake_instInhabitedCache = _init_l_Lake_instInhabitedCache();
lean_mark_persistent(l_Lake_instInhabitedCache);
l_Lake_CachePlatform_system = _init_l_Lake_CachePlatform_system();
lean_mark_persistent(l_Lake_CachePlatform_system);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Cache(builtin);
}
#ifdef __cplusplus
}
#endif
