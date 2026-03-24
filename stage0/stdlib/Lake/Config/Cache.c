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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_Hash_hex(uint64_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
extern lean_object* l_System_instInhabitedFilePath_default;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheMap_parse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_parse___closed__0;
static const lean_array_object l_Lake_CacheMap_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheMap_parse___closed__1 = (const lean_object*)&l_Lake_CacheMap_parse___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_downloadArtifactCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": downloaded artifact hash mismatch, got "};
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ": uploading artifact "};
static const lean_object* l_Lake_CacheService_uploadArtifact___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "urlnum"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "curl JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nunexpected response:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "size_download"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "content_type"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "errormsg"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  curl error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": failed to "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " (status code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "download"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "upload"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": downloaded artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ": uploaded artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = ": unidentifiable transfer completed: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "curl produced invalid JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "property not found: http_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "url = "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-o "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-T "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = ": curl exited with code "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": curl produced unexpected output:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " some artifacts"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-Z"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--retry"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--config"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Content-Type: application/vnd.reservoir.artifact"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_CacheService_downloadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__0_value;
static const lean_string_object l_Lake_CacheService_downloadArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "no artifacts to download"};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__1_value;
static const lean_ctor_object l_Lake_CacheService_downloadArtifacts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__2 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no artifacts to upload"};
static const lean_object* l_Lake_CacheService_uploadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__0_value;
static const lean_ctor_object l_Lake_CacheService_uploadArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheService_uploadArtifacts___closed__1 = (const lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v___y_405_);
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
lean_dec_ref(v___y_439_);
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
return v___x_486_;
}
}
else
{
lean_dec(v___x_477_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
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
lean_dec_ref(v_a_502_);
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
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
return v___x_555_;
}
}
else
{
lean_dec(v___x_546_);
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
lean_dec_ref(v_a_577_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object* v_as_617_, size_t v_i_618_, size_t v_stop_619_, lean_object* v_b_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_618_, v_stop_619_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; size_t v___x_626_; size_t v___x_627_; 
v___x_624_ = lean_array_uget_borrowed(v_as_617_, v_i_618_);
lean_inc_ref(v___y_621_);
lean_inc(v___x_624_);
v___x_625_ = lean_apply_2(v___y_621_, v___x_624_, lean_box(0));
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_618_, v___x_626_);
v_i_618_ = v___x_627_;
v_b_620_ = v___x_625_;
goto _start;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_620_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_stop_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_632_);
lean_dec(v_stop_632_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_as_630_, v_i_boxed_636_, v_stop_boxed_637_, v_b_633_, v___y_634_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v_as_630_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(lean_object* v___x_639_, lean_object* v_contents_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v_startInclusive_643_; lean_object* v_endExclusive_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_startInclusive_643_ = lean_ctor_get(v___x_639_, 1);
v_endExclusive_644_ = lean_ctor_get(v___x_639_, 2);
v___x_645_ = lean_nat_sub(v_endExclusive_644_, v_startInclusive_643_);
v___x_646_ = lean_nat_dec_eq(v_a_641_, v___x_645_);
lean_dec(v___x_645_);
if (v___x_646_ == 0)
{
uint32_t v___x_647_; uint32_t v___x_648_; uint8_t v___x_649_; 
lean_dec(v_b_642_);
v___x_647_ = lean_string_utf8_get_fast(v_contents_640_, v_a_641_);
v___x_648_ = 10;
v___x_649_ = lean_uint32_dec_eq(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_string_utf8_next_fast(v_contents_640_, v_a_641_);
lean_dec(v_a_641_);
v_a_641_ = v___x_651_;
v_b_642_ = v___x_650_;
goto _start;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_a_641_);
return v___x_653_;
}
}
else
{
lean_dec(v_a_641_);
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object* v___x_654_, lean_object* v_contents_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_654_, v_contents_655_, v_a_656_, v_b_657_);
lean_dec_ref(v_contents_655_);
lean_dec_ref(v___x_654_);
return v_res_658_;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__0(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_box(0);
v___x_660_ = lean_unsigned_to_nat(16u);
v___x_661_ = lean_mk_array(v___x_660_, v___x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* v_inputName_664_, lean_object* v_contents_665_, uint8_t v_platformIndependent_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_698_; lean_object* v_searcher_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_searcher_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_string_utf8_byte_size(v_contents_665_);
lean_inc_ref(v_contents_665_);
v___x_736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_736_, 0, v_contents_665_);
lean_ctor_set(v___x_736_, 1, v_searcher_734_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = lean_box(0);
v___x_738_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_736_, v_contents_665_, v_searcher_734_, v___x_737_);
lean_dec_ref(v___x_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
v___y_698_ = v___x_735_;
goto v___jp_697_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref(v___x_738_);
v___y_698_ = v_val_739_;
goto v___jp_697_;
}
v___jp_669_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
v___jp_672_:
{
if (v___y_674_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = lean_unsigned_to_nat(2u);
v___x_677_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_675_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_string_utf8_next_fast(v_contents_665_, v___y_673_);
lean_dec(v___y_673_);
v___x_680_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_667_, v_inputName_664_, v_platformIndependent_666_, v___x_676_, v___x_678_, v_contents_665_, v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___y_673_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
v___x_681_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_675_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
v___jp_684_:
{
if (lean_obj_tag(v___y_688_) == 0)
{
lean_dec_ref(v___y_688_);
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
goto v___jp_672_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___y_687_);
lean_dec(v___y_685_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
v_a_689_ = lean_ctor_get(v___y_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___y_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___y_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___y_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v_line_700_; lean_object* v___x_701_; lean_object* v_str_702_; lean_object* v_startInclusive_703_; lean_object* v_endExclusive_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_699_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_698_);
lean_inc_ref(v_contents_665_);
v_line_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_700_, 0, v_contents_665_);
lean_ctor_set(v_line_700_, 1, v___x_699_);
lean_ctor_set(v_line_700_, 2, v___y_698_);
v___x_701_ = l_String_Slice_trimAscii(v_line_700_);
v_str_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_ref(v_str_702_);
v_startInclusive_703_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_startInclusive_703_);
v_endExclusive_704_ = lean_ctor_get(v___x_701_, 2);
lean_inc(v_endExclusive_704_);
lean_dec_ref(v___x_701_);
v___x_705_ = lean_string_utf8_extract(v_str_702_, v_startInclusive_703_, v_endExclusive_704_);
lean_dec(v_endExclusive_704_);
lean_dec(v_startInclusive_703_);
lean_dec_ref(v_str_702_);
v___x_706_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
lean_inc_ref(v_inputName_664_);
v___x_707_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_664_, v___x_705_, v___x_706_);
v___x_708_ = lean_string_utf8_byte_size(v_contents_665_);
v___x_709_ = lean_nat_dec_eq(v___y_698_, v___x_708_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_a_710_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_a_710_);
lean_dec_ref(v___x_707_);
v___x_711_ = lean_array_get_size(v_a_710_);
v___x_712_ = lean_nat_dec_lt(v___x_699_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec(v_a_710_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_709_;
v___y_675_ = v___x_699_;
goto v___jp_672_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_nat_dec_le(v___x_711_, v___x_711_);
if (v___x_714_ == 0)
{
if (v___x_712_ == 0)
{
lean_dec(v_a_710_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_709_;
v___y_675_ = v___x_699_;
goto v___jp_672_;
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_711_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_710_, v___x_715_, v___x_716_, v___x_713_, v_a_667_);
lean_dec(v_a_710_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_dec_ref(v___x_717_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_709_;
v___y_675_ = v___x_699_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_709_;
v___y_687_ = v___x_699_;
v___y_688_ = v___x_717_;
goto v___jp_684_;
}
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_711_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_710_, v___x_718_, v___x_719_, v___x_713_, v_a_667_);
lean_dec(v_a_710_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref(v___x_720_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_709_;
v___y_675_ = v___x_699_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_709_;
v___y_687_ = v___x_699_;
v___y_688_ = v___x_720_;
goto v___jp_684_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_a_721_);
lean_dec_ref(v___x_707_);
v___x_722_ = lean_array_get_size(v_a_721_);
v___x_723_ = lean_nat_dec_lt(v___x_699_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_a_721_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_nat_dec_le(v___x_722_, v___x_722_);
if (v___x_727_ == 0)
{
if (v___x_723_ == 0)
{
lean_dec(v_a_721_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)0ULL);
v___x_729_ = lean_usize_of_nat(v___x_722_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_721_, v___x_728_, v___x_729_, v___x_726_, v_a_667_);
lean_dec(v_a_721_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_dec_ref(v___x_730_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_709_;
v___y_687_ = v___x_699_;
v___y_688_ = v___x_730_;
goto v___jp_684_;
}
}
}
else
{
size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_722_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_721_, v___x_731_, v___x_732_, v___x_726_, v_a_667_);
lean_dec(v_a_721_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_dec_ref(v___x_733_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_709_;
v___y_687_ = v___x_699_;
v___y_688_ = v___x_733_;
goto v___jp_684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* v_inputName_740_, lean_object* v_contents_741_, lean_object* v_platformIndependent_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
uint8_t v_platformIndependent_boxed_745_; lean_object* v_res_746_; 
v_platformIndependent_boxed_745_ = lean_unbox(v_platformIndependent_742_);
v_res_746_ = l_Lake_CacheMap_parse(v_inputName_740_, v_contents_741_, v_platformIndependent_boxed_745_, v_a_743_);
lean_dec_ref(v_a_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(lean_object* v___x_747_, lean_object* v_contents_748_, lean_object* v_inst_749_, lean_object* v_R_750_, lean_object* v_a_751_, lean_object* v_b_752_, lean_object* v_c_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_747_, v_contents_748_, v_a_751_, v_b_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object* v___x_755_, lean_object* v_contents_756_, lean_object* v_inst_757_, lean_object* v_R_758_, lean_object* v_a_759_, lean_object* v_b_760_, lean_object* v_c_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(v___x_755_, v_contents_756_, v_inst_757_, v_R_758_, v_a_759_, v_b_760_, v_c_761_);
lean_dec_ref(v_contents_756_);
lean_dec_ref(v___x_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object* v_inputName_763_, lean_object* v_lineNo_764_, lean_object* v_cache_765_, lean_object* v_line_766_, uint8_t v_platformIndependent_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
lean_inc_ref(v_cache_765_);
v___x_770_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_765_, v_line_766_, v_platformIndependent_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_773_ = lean_string_append(v_inputName_763_, v___x_772_);
v___x_774_ = l_Nat_reprFast(v_lineNo_764_);
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = lean_string_append(v___x_777_, v_a_771_);
lean_dec(v_a_771_);
v___x_779_ = 2;
v___x_780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*1, v___x_779_);
v___x_781_ = lean_array_push(v___y_768_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_cache_765_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; 
lean_dec_ref(v_cache_765_);
lean_dec(v_lineNo_764_);
lean_dec_ref(v_inputName_763_);
v_a_783_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_770_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_783_);
lean_ctor_set(v___x_784_, 1, v___y_768_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object* v_inputName_785_, lean_object* v_lineNo_786_, lean_object* v_cache_787_, lean_object* v_line_788_, lean_object* v_platformIndependent_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_platformIndependent_boxed_792_; lean_object* v_res_793_; 
v_platformIndependent_boxed_792_ = lean_unbox(v_platformIndependent_789_);
v_res_793_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_inputName_785_, v_lineNo_786_, v_cache_787_, v_line_788_, v_platformIndependent_boxed_792_, v___y_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* v_h_794_, lean_object* v_fileName_795_, uint8_t v_platformIndependent_796_, lean_object* v_i_797_, lean_object* v_cache_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = lean_io_prim_handle_get_line(v_h_794_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_string_utf8_byte_size(v_a_802_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_nat_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_inc(v_i_797_);
lean_inc_ref(v_fileName_795_);
v___x_806_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_fileName_795_, v_i_797_, v_cache_798_, v_a_802_, v_platformIndependent_796_, v_a_799_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
v_a_808_ = lean_ctor_get(v___x_806_, 1);
lean_inc(v_a_808_);
lean_dec_ref(v___x_806_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_i_797_, v___x_809_);
lean_dec(v_i_797_);
v_i_797_ = v___x_810_;
v_cache_798_ = v_a_807_;
v_a_799_ = v_a_808_;
goto _start;
}
else
{
lean_dec(v_i_797_);
lean_dec_ref(v_fileName_795_);
return v___x_806_;
}
}
else
{
lean_object* v___x_812_; 
lean_dec(v_a_802_);
lean_dec(v_i_797_);
lean_dec_ref(v_fileName_795_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_cache_798_);
lean_ctor_set(v___x_812_, 1, v_a_799_);
return v___x_812_;
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_cache_798_);
lean_dec(v_i_797_);
lean_dec_ref(v_fileName_795_);
v_a_813_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_801_);
v___x_814_ = lean_io_error_to_string(v_a_813_);
v___x_815_ = 3;
v___x_816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___x_817_ = lean_array_get_size(v_a_799_);
v___x_818_ = lean_array_push(v_a_799_, v___x_816_);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* v_h_820_, lean_object* v_fileName_821_, lean_object* v_platformIndependent_822_, lean_object* v_i_823_, lean_object* v_cache_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
uint8_t v_platformIndependent_boxed_827_; lean_object* v_res_828_; 
v_platformIndependent_boxed_827_ = lean_unbox(v_platformIndependent_822_);
v_res_828_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_820_, v_fileName_821_, v_platformIndependent_boxed_827_, v_i_823_, v_cache_824_, v_a_825_);
lean_dec(v_h_820_);
return v_res_828_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* v_h_832_, lean_object* v_fileName_833_, uint8_t v_platformIndependent_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_io_prim_handle_get_line(v_h_832_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
lean_inc_ref(v_fileName_833_);
v___x_839_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_fileName_833_, v_a_838_, v_a_835_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_a_840_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
v___x_841_ = lean_unsigned_to_nat(2u);
v___x_842_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_843_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_832_, v_fileName_833_, v_platformIndependent_834_, v___x_841_, v___x_842_, v_a_840_);
return v___x_843_;
}
else
{
lean_object* v_a_844_; lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v_fileName_833_);
v_a_844_ = lean_ctor_get(v___x_839_, 0);
v_a_845_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_839_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_inc(v_a_844_);
lean_dec(v___x_839_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_844_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v_fileName_833_);
v_a_853_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_837_);
v___x_854_ = lean_io_error_to_string(v_a_853_);
v___x_855_ = 3;
v___x_856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_855_);
v___x_857_ = lean_array_get_size(v_a_835_);
v___x_858_ = lean_array_push(v_a_835_, v___x_856_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* v_h_860_, lean_object* v_fileName_861_, lean_object* v_platformIndependent_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_platformIndependent_boxed_865_; lean_object* v_res_866_; 
v_platformIndependent_boxed_865_ = lean_unbox(v_platformIndependent_862_);
v_res_866_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(v_h_860_, v_fileName_861_, v_platformIndependent_boxed_865_, v_a_863_);
lean_dec(v_h_860_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* v_file_868_, uint8_t v_platformIndependent_869_, lean_object* v_a_870_){
_start:
{
uint8_t v___x_872_; lean_object* v___x_873_; 
v___x_872_ = 0;
v___x_873_ = lean_io_prim_handle_mk(v_file_868_, v___x_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; lean_object* v___x_876_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_io_prim_handle_lock(v_a_874_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
lean_dec_ref(v___x_876_);
v___x_877_ = lean_io_prim_handle_get_line(v_a_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
lean_inc_ref(v_file_868_);
v___x_879_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_868_, v_a_878_, v_a_870_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_879_, 1);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = lean_unsigned_to_nat(2u);
v___x_882_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_883_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_874_, v_file_868_, v_platformIndependent_869_, v___x_881_, v___x_882_, v_a_880_);
lean_dec(v_a_874_);
return v___x_883_;
}
else
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_874_);
lean_dec_ref(v_file_868_);
v_a_884_ = lean_ctor_get(v___x_879_, 0);
v_a_885_ = lean_ctor_get(v___x_879_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_879_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_inc(v_a_884_);
lean_dec(v___x_879_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_a_874_);
lean_dec_ref(v_file_868_);
v_a_893_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_877_);
v___x_894_ = lean_io_error_to_string(v_a_893_);
v___x_895_ = 3;
v___x_896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_895_);
v___x_897_ = lean_array_get_size(v_a_870_);
v___x_898_ = lean_array_push(v_a_870_, v___x_896_);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v_a_874_);
lean_dec_ref(v_file_868_);
v_a_900_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_876_);
v___x_901_ = lean_io_error_to_string(v_a_900_);
v___x_902_ = 3;
v___x_903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_902_);
v___x_904_ = lean_array_get_size(v_a_870_);
v___x_905_ = lean_array_push(v_a_870_, v___x_903_);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_907_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_873_);
v___x_908_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_909_ = lean_string_append(v_file_868_, v___x_908_);
v___x_910_ = lean_io_error_to_string(v_a_907_);
v___x_911_ = lean_string_append(v___x_909_, v___x_910_);
lean_dec_ref(v___x_910_);
v___x_912_ = 3;
v___x_913_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_912_);
v___x_914_ = lean_array_get_size(v_a_870_);
v___x_915_ = lean_array_push(v_a_870_, v___x_913_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object* v_file_917_, lean_object* v_platformIndependent_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_platformIndependent_boxed_921_; lean_object* v_res_922_; 
v_platformIndependent_boxed_921_ = lean_unbox(v_platformIndependent_918_);
v_res_922_ = l_Lake_CacheMap_load(v_file_917_, v_platformIndependent_boxed_921_, v_a_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* v_file_923_, uint8_t v_platformIndependent_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_a_928_; lean_object* v_a_929_; uint8_t v___x_931_; lean_object* v___x_932_; 
v___x_931_ = 0;
v___x_932_ = lean_io_prim_handle_mk(v_file_923_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v___x_932_);
v___x_934_ = 0;
v___x_935_ = lean_io_prim_handle_lock(v_a_933_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v___x_935_);
v___x_936_ = lean_io_prim_handle_get_line(v_a_933_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_962_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_962_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_962_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_962_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; 
lean_inc_ref(v_file_923_);
v___x_941_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_923_, v_a_937_, v_a_925_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_942_);
lean_dec_ref(v___x_941_);
v___x_943_ = lean_unsigned_to_nat(2u);
v___x_944_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_945_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_933_, v_file_923_, v_platformIndependent_924_, v___x_943_, v___x_944_, v_a_942_);
lean_dec(v_a_933_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_a_947_ = lean_ctor_get(v___x_945_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_949_ = v___x_945_;
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
lean_ctor_set(v___x_939_, 0, v_a_946_);
v___x_952_ = v___x_939_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_946_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_947_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v_a_959_; 
lean_del_object(v___x_939_);
v_a_958_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_958_);
v_a_959_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_a_959_);
lean_dec_ref(v___x_945_);
v_a_928_ = v_a_958_;
v_a_929_ = v_a_959_;
goto v___jp_927_;
}
}
else
{
lean_object* v_a_960_; lean_object* v_a_961_; 
lean_del_object(v___x_939_);
lean_dec(v_a_933_);
lean_dec_ref(v_file_923_);
v_a_960_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_960_);
v_a_961_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_961_);
lean_dec_ref(v___x_941_);
v_a_928_ = v_a_960_;
v_a_929_ = v_a_961_;
goto v___jp_927_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_a_933_);
lean_dec_ref(v_file_923_);
v_a_963_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_936_);
v___x_964_ = lean_io_error_to_string(v_a_963_);
v___x_965_ = 3;
v___x_966_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*1, v___x_965_);
v___x_967_ = lean_array_get_size(v_a_925_);
v___x_968_ = lean_array_push(v_a_925_, v___x_966_);
v_a_928_ = v___x_967_;
v_a_929_ = v___x_968_;
goto v___jp_927_;
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_a_933_);
lean_dec_ref(v_file_923_);
v_a_969_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_935_);
v___x_970_ = lean_io_error_to_string(v_a_969_);
v___x_971_ = 3;
v___x_972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_971_);
v___x_973_ = lean_array_get_size(v_a_925_);
v___x_974_ = lean_array_push(v_a_925_, v___x_972_);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
return v___x_975_;
}
}
else
{
lean_object* v_a_976_; 
v_a_976_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_932_);
if (lean_obj_tag(v_a_976_) == 11)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec_ref(v_a_976_);
lean_dec_ref(v_file_923_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_925_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_979_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_980_ = lean_string_append(v_file_923_, v___x_979_);
v___x_981_ = lean_io_error_to_string(v_a_976_);
v___x_982_ = lean_string_append(v___x_980_, v___x_981_);
lean_dec_ref(v___x_981_);
v___x_983_ = 3;
v___x_984_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*1, v___x_983_);
v___x_985_ = lean_array_get_size(v_a_925_);
v___x_986_ = lean_array_push(v_a_925_, v___x_984_);
v___x_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
return v___x_987_;
}
}
v___jp_927_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v_a_928_);
lean_ctor_set(v___x_930_, 1, v_a_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object* v_file_988_, lean_object* v_platformIndependent_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
uint8_t v_platformIndependent_boxed_992_; lean_object* v_res_993_; 
v_platformIndependent_boxed_992_ = lean_unbox(v_platformIndependent_989_);
v_res_993_ = l_Lake_CacheMap_load_x3f(v_file_988_, v_platformIndependent_boxed_992_, v_a_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object* v_h_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_x_995_);
lean_ctor_set(v___x_999_, 1, v___y_997_);
return v___x_999_;
}
else
{
lean_object* v_value_1000_; lean_object* v_key_1001_; lean_object* v_tail_1002_; lean_object* v_out_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1028_; 
v_value_1000_ = lean_ctor_get(v_x_996_, 1);
lean_inc(v_value_1000_);
v_key_1001_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_key_1001_);
v_tail_1002_ = lean_ctor_get(v_x_996_, 2);
lean_inc(v_tail_1002_);
lean_dec_ref(v_x_996_);
v_out_1003_ = lean_ctor_get(v_value_1000_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_value_1000_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1005_ = v_value_1000_;
v_isShared_1006_ = v_isSharedCheck_1028_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_out_1003_);
lean_dec(v_value_1000_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1028_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint64_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1007_ = lean_unbox_uint64(v_key_1001_);
lean_dec(v_key_1001_);
v___x_1008_ = l_Lake_Hash_hex(v___x_1007_);
v___x_1009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(2u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1009_);
v___x_1013_ = lean_array_push(v___x_1012_, v_out_1003_);
v___x_1014_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = l_Lean_Json_compress(v___x_1014_);
v___x_1016_ = l_IO_FS_Handle_putStrLn(v_h_994_, v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; 
lean_del_object(v___x_1005_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v_x_995_ = v_a_1017_;
v_x_996_ = v_tail_1002_;
goto _start;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1023_; 
lean_dec(v_tail_1002_);
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1016_);
v___x_1020_ = lean_io_error_to_string(v_a_1019_);
v___x_1021_ = 3;
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1020_);
v___x_1023_ = v___x_1005_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*1, v___x_1021_);
v___x_1024_ = lean_array_get_size(v___y_997_);
v___x_1025_ = lean_array_push(v___y_997_, v___x_1023_);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object* v_h_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1029_, v_x_1030_, v_x_1031_, v___y_1032_);
lean_dec(v_h_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object* v_h_1035_, lean_object* v_as_1036_, size_t v_i_1037_, size_t v_stop_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_eq(v_i_1037_, v_stop_1038_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_array_uget_borrowed(v_as_1036_, v_i_1037_);
v___x_1044_ = lean_box(0);
lean_inc(v___x_1043_);
v___x_1045_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1035_, v___x_1044_, v___x_1043_, v___y_1040_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v_a_1047_; size_t v___x_1048_; size_t v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
v_a_1047_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1037_, v___x_1048_);
v_i_1037_ = v___x_1049_;
v_b_1039_ = v_a_1046_;
v___y_1040_ = v_a_1047_;
goto _start;
}
else
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_b_1039_);
lean_ctor_set(v___x_1051_, 1, v___y_1040_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object* v_h_1052_, lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_stop_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
size_t v_i_boxed_1059_; size_t v_stop_boxed_1060_; lean_object* v_res_1061_; 
v_i_boxed_1059_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_stop_boxed_1060_ = lean_unbox_usize(v_stop_1055_);
lean_dec(v_stop_1055_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1052_, v_as_1053_, v_i_boxed_1059_, v_stop_boxed_1060_, v_b_1056_, v___y_1057_);
lean_dec_ref(v_as_1053_);
lean_dec(v_h_1052_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object* v_h_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_){
_start:
{
if (lean_obj_tag(v_x_1064_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_x_1063_);
lean_ctor_set(v___x_1067_, 1, v___y_1065_);
return v___x_1067_;
}
else
{
lean_object* v_value_1068_; uint8_t v_platformIndependent_1069_; 
v_value_1068_ = lean_ctor_get(v_x_1064_, 1);
lean_inc(v_value_1068_);
v_platformIndependent_1069_ = lean_ctor_get_uint8(v_value_1068_, sizeof(void*)*1);
if (v_platformIndependent_1069_ == 0)
{
lean_object* v_tail_1070_; lean_object* v___x_1071_; 
lean_dec(v_value_1068_);
v_tail_1070_ = lean_ctor_get(v_x_1064_, 2);
lean_inc(v_tail_1070_);
lean_dec_ref(v_x_1064_);
v___x_1071_ = lean_box(0);
v_x_1063_ = v___x_1071_;
v_x_1064_ = v_tail_1070_;
goto _start;
}
else
{
lean_object* v_key_1073_; lean_object* v_tail_1074_; lean_object* v_out_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1100_; 
v_key_1073_ = lean_ctor_get(v_x_1064_, 0);
lean_inc(v_key_1073_);
v_tail_1074_ = lean_ctor_get(v_x_1064_, 2);
lean_inc(v_tail_1074_);
lean_dec_ref(v_x_1064_);
v_out_1075_ = lean_ctor_get(v_value_1068_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_value_1068_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1077_ = v_value_1068_;
v_isShared_1078_ = v_isSharedCheck_1100_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_out_1075_);
lean_dec(v_value_1068_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1100_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint64_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1079_ = lean_unbox_uint64(v_key_1073_);
lean_dec(v_key_1073_);
v___x_1080_ = l_Lake_Hash_hex(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = lean_unsigned_to_nat(2u);
v___x_1083_ = lean_mk_empty_array_with_capacity(v___x_1082_);
v___x_1084_ = lean_array_push(v___x_1083_, v___x_1081_);
v___x_1085_ = lean_array_push(v___x_1084_, v_out_1075_);
v___x_1086_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = l_Lean_Json_compress(v___x_1086_);
v___x_1088_ = l_IO_FS_Handle_putStrLn(v_h_1062_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; 
lean_del_object(v___x_1077_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v___x_1088_);
v_x_1063_ = v_a_1089_;
v_x_1064_ = v_tail_1074_;
goto _start;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_tail_1074_);
v_a_1091_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1088_);
v___x_1092_ = lean_io_error_to_string(v_a_1091_);
v___x_1093_ = 3;
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1092_);
v___x_1095_ = v___x_1077_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1092_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1093_);
v___x_1096_ = lean_array_get_size(v___y_1065_);
v___x_1097_ = lean_array_push(v___y_1065_, v___x_1095_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
return v___x_1098_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object* v_h_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1101_, v_x_1102_, v_x_1103_, v___y_1104_);
lean_dec(v_h_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(lean_object* v_h_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_usize_dec_eq(v_i_1109_, v_stop_1110_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_array_uget_borrowed(v_as_1108_, v_i_1109_);
v___x_1116_ = lean_box(0);
lean_inc(v___x_1115_);
v___x_1117_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1107_, v___x_1116_, v___x_1115_, v___y_1112_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_a_1119_; size_t v___x_1120_; size_t v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1117_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1109_, v___x_1120_);
v_i_1109_ = v___x_1121_;
v_b_1111_ = v_a_1118_;
v___y_1112_ = v_a_1119_;
goto _start;
}
else
{
return v___x_1117_;
}
}
else
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_b_1111_);
lean_ctor_set(v___x_1123_, 1, v___y_1112_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3___boxed(lean_object* v_h_1124_, lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_stop_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; lean_object* v_res_1133_; 
v_i_boxed_1131_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1127_);
lean_dec(v_stop_1127_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1124_, v_as_1125_, v_i_boxed_1131_, v_stop_boxed_1132_, v_b_1128_, v___y_1129_);
lean_dec_ref(v_as_1125_);
lean_dec(v_h_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(lean_object* v_h_1134_, lean_object* v_cache_1135_, uint8_t v_platformIndependent_1136_, lean_object* v_a_1137_){
_start:
{
if (v_platformIndependent_1136_ == 0)
{
lean_object* v_buckets_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1160_; 
v_buckets_1139_ = lean_ctor_get(v_cache_1135_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_cache_1135_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_cache_1135_, 0);
lean_dec(v_unused_1161_);
v___x_1141_ = v_cache_1135_;
v_isShared_1142_ = v_isSharedCheck_1160_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_buckets_1139_);
lean_dec(v_cache_1135_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1160_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_array_get_size(v_buckets_1139_);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_nat_dec_lt(v___x_1143_, v___x_1144_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v_buckets_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_a_1137_);
lean_ctor_set(v___x_1141_, 0, v___x_1145_);
v___x_1148_ = v___x_1141_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1137_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_nat_dec_le(v___x_1144_, v___x_1144_);
if (v___x_1150_ == 0)
{
if (v___x_1146_ == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref(v_buckets_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_a_1137_);
lean_ctor_set(v___x_1141_, 0, v___x_1145_);
v___x_1152_ = v___x_1141_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_a_1137_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1141_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1144_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1134_, v_buckets_1139_, v___x_1154_, v___x_1155_, v___x_1145_, v_a_1137_);
lean_dec_ref(v_buckets_1139_);
return v___x_1156_;
}
}
else
{
size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
lean_del_object(v___x_1141_);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1144_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1134_, v_buckets_1139_, v___x_1157_, v___x_1158_, v___x_1145_, v_a_1137_);
lean_dec_ref(v_buckets_1139_);
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_buckets_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1183_; 
v_buckets_1162_ = lean_ctor_get(v_cache_1135_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_cache_1135_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v_cache_1135_, 0);
lean_dec(v_unused_1184_);
v___x_1164_ = v_cache_1135_;
v_isShared_1165_ = v_isSharedCheck_1183_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_buckets_1162_);
lean_dec(v_cache_1135_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1183_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_array_get_size(v_buckets_1162_);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_nat_dec_lt(v___x_1166_, v___x_1167_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v_buckets_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v_a_1137_);
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1171_ = v___x_1164_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_a_1137_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_le(v___x_1167_, v___x_1167_);
if (v___x_1173_ == 0)
{
if (v___x_1169_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v_buckets_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v_a_1137_);
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1175_ = v___x_1164_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1137_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
lean_del_object(v___x_1164_);
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1167_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1134_, v_buckets_1162_, v___x_1177_, v___x_1178_, v___x_1168_, v_a_1137_);
lean_dec_ref(v_buckets_1162_);
return v___x_1179_;
}
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1164_);
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1167_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1134_, v_buckets_1162_, v___x_1180_, v___x_1181_, v___x_1168_, v_a_1137_);
lean_dec_ref(v_buckets_1162_);
return v___x_1182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries___boxed(lean_object* v_h_1185_, lean_object* v_cache_1186_, lean_object* v_platformIndependent_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
uint8_t v_platformIndependent_boxed_1190_; lean_object* v_res_1191_; 
v_platformIndependent_boxed_1190_ = lean_unbox(v_platformIndependent_1187_);
v_res_1191_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_h_1185_, v_cache_1186_, v_platformIndependent_boxed_1190_, v_a_1188_);
lean_dec(v_h_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
return v_x_1192_;
}
else
{
lean_object* v_key_1194_; lean_object* v_value_1195_; lean_object* v_tail_1196_; uint64_t v___x_1197_; lean_object* v___x_1198_; 
v_key_1194_ = lean_ctor_get(v_x_1193_, 0);
lean_inc(v_key_1194_);
v_value_1195_ = lean_ctor_get(v_x_1193_, 1);
lean_inc(v_value_1195_);
v_tail_1196_ = lean_ctor_get(v_x_1193_, 2);
lean_inc(v_tail_1196_);
lean_dec_ref(v_x_1193_);
v___x_1197_ = lean_unbox_uint64(v_key_1194_);
lean_dec(v_key_1194_);
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_x_1192_, v___x_1197_, v_value_1195_);
v_x_1192_ = v___x_1198_;
v_x_1193_ = v_tail_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(lean_object* v_as_1200_, size_t v_i_1201_, size_t v_stop_1202_, lean_object* v_b_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_eq(v_i_1201_, v_stop_1202_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; 
v___x_1205_ = lean_array_uget_borrowed(v_as_1200_, v_i_1201_);
lean_inc(v___x_1205_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(v_b_1203_, v___x_1205_);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = lean_usize_add(v_i_1201_, v___x_1207_);
v_i_1201_ = v___x_1208_;
v_b_1203_ = v___x_1206_;
goto _start;
}
else
{
return v_b_1203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object* v_as_1210_, lean_object* v_i_1211_, lean_object* v_stop_1212_, lean_object* v_b_1213_){
_start:
{
size_t v_i_boxed_1214_; size_t v_stop_boxed_1215_; lean_object* v_res_1216_; 
v_i_boxed_1214_ = lean_unbox_usize(v_i_1211_);
lean_dec(v_i_1211_);
v_stop_boxed_1215_ = lean_unbox_usize(v_stop_1212_);
lean_dec(v_stop_1212_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_as_1210_, v_i_boxed_1214_, v_stop_boxed_1215_, v_b_1213_);
lean_dec_ref(v_as_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* v_file_1217_, lean_object* v_cache_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_a_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; 
lean_inc_ref(v_file_1217_);
v___x_1225_ = l_Lake_createParentDirs(v_file_1217_);
if (lean_obj_tag(v___x_1225_) == 0)
{
uint8_t v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v___x_1225_);
v___x_1226_ = 4;
v___x_1227_ = lean_io_prim_handle_mk(v_file_1217_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
uint8_t v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1227_);
v___x_1228_ = 3;
v___x_1229_ = lean_io_prim_handle_mk(v_file_1217_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = 1;
v___x_1232_ = lean_io_prim_handle_lock(v_a_1230_, v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1232_);
v___x_1233_ = lean_io_prim_handle_get_line(v_a_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
lean_inc_ref(v_file_1217_);
v___x_1235_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_1217_, v_a_1234_, v_a_1219_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = 0;
v___x_1238_ = lean_unsigned_to_nat(2u);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_1241_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_1230_, v_file_1217_, v___x_1237_, v___x_1238_, v___x_1240_, v_a_1236_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1270_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_a_1243_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1245_ = v___x_1241_;
v_isShared_1246_ = v_isSharedCheck_1270_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1270_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___y_1248_; lean_object* v_buckets_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_buckets_1260_ = lean_ctor_get(v_cache_1218_, 1);
v___x_1261_ = lean_array_get_size(v_buckets_1260_);
v___x_1262_ = lean_nat_dec_lt(v___x_1239_, v___x_1261_);
if (v___x_1262_ == 0)
{
v___y_1248_ = v_a_1242_;
goto v___jp_1247_;
}
else
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_le(v___x_1261_, v___x_1261_);
if (v___x_1263_ == 0)
{
if (v___x_1262_ == 0)
{
v___y_1248_ = v_a_1242_;
goto v___jp_1247_;
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = lean_usize_of_nat(v___x_1261_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1260_, v___x_1264_, v___x_1265_, v_a_1242_);
v___y_1248_ = v___x_1266_;
goto v___jp_1247_;
}
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((size_t)0ULL);
v___x_1268_ = lean_usize_of_nat(v___x_1261_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1260_, v___x_1267_, v___x_1268_, v_a_1242_);
v___y_1248_ = v___x_1269_;
goto v___jp_1247_;
}
}
v___jp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_io_prim_handle_rewind(v_a_1230_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref(v___x_1249_);
lean_del_object(v___x_1245_);
v___x_1250_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1230_, v___y_1248_, v___x_1237_, v_a_1243_);
lean_dec(v_a_1230_);
return v___x_1250_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec_ref(v___y_1248_);
lean_dec(v_a_1230_);
v_a_1251_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1249_);
v___x_1252_ = lean_io_error_to_string(v_a_1251_);
v___x_1253_ = 3;
v___x_1254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*1, v___x_1253_);
v___x_1255_ = lean_array_get_size(v_a_1243_);
v___x_1256_ = lean_array_push(v_a_1243_, v___x_1254_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 1);
lean_ctor_set(v___x_1245_, 1, v___x_1256_);
lean_ctor_set(v___x_1245_, 0, v___x_1255_);
v___x_1258_ = v___x_1245_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v_a_1272_; 
lean_dec(v_a_1230_);
v_a_1271_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1271_);
v_a_1272_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1241_);
v_a_1222_ = v_a_1271_;
v_a_1223_ = v_a_1272_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1273_; lean_object* v_a_1274_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_file_1217_);
v_a_1273_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1273_);
v_a_1274_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1235_);
v_a_1222_ = v_a_1273_;
v_a_1223_ = v_a_1274_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_file_1217_);
v_a_1275_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1233_);
v___x_1276_ = lean_io_error_to_string(v_a_1275_);
v___x_1277_ = 3;
v___x_1278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1277_);
v___x_1279_ = lean_array_get_size(v_a_1219_);
v___x_1280_ = lean_array_push(v_a_1219_, v___x_1278_);
v_a_1222_ = v___x_1279_;
v_a_1223_ = v___x_1280_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_file_1217_);
v_a_1281_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1232_);
v___x_1282_ = lean_io_error_to_string(v_a_1281_);
v___x_1283_ = 3;
v___x_1284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
v___x_1285_ = lean_array_get_size(v_a_1219_);
v___x_1286_ = lean_array_push(v_a_1219_, v___x_1284_);
v___x_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1288_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1229_);
v___x_1289_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1290_ = lean_string_append(v_file_1217_, v___x_1289_);
v___x_1291_ = lean_io_error_to_string(v_a_1288_);
v___x_1292_ = lean_string_append(v___x_1290_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = 3;
v___x_1294_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*1, v___x_1293_);
v___x_1295_ = lean_array_get_size(v_a_1219_);
v___x_1296_ = lean_array_push(v_a_1219_, v___x_1294_);
v___x_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
return v___x_1297_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref(v_file_1217_);
v_a_1298_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1227_);
v___x_1299_ = lean_io_error_to_string(v_a_1298_);
v___x_1300_ = 3;
v___x_1301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*1, v___x_1300_);
v___x_1302_ = lean_array_get_size(v_a_1219_);
v___x_1303_ = lean_array_push(v_a_1219_, v___x_1301_);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
return v___x_1304_;
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec_ref(v_file_1217_);
v_a_1305_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1225_);
v___x_1306_ = lean_io_error_to_string(v_a_1305_);
v___x_1307_ = 3;
v___x_1308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*1, v___x_1307_);
v___x_1309_ = lean_array_get_size(v_a_1219_);
v___x_1310_ = lean_array_push(v_a_1219_, v___x_1308_);
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
return v___x_1311_;
}
v___jp_1221_:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1222_);
lean_ctor_set(v___x_1224_, 1, v_a_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object* v_file_1312_, lean_object* v_cache_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_CacheMap_updateFile(v_file_1312_, v_cache_1313_, v_a_1314_);
lean_dec_ref(v_cache_1313_);
return v_res_1316_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__0(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_1318_ = l_Lake_Date_toString(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__1(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__0, &l_Lake_CacheMap_writeFile___closed__0_once, _init_l_Lake_CacheMap_writeFile___closed__0);
v___x_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__2(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__1, &l_Lake_CacheMap_writeFile___closed__1_once, _init_l_Lake_CacheMap_writeFile___closed__1);
v___x_1322_ = l_Lean_Json_compress(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* v_file_1323_, lean_object* v_cache_1324_, uint8_t v_platformIndependent_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; 
lean_inc_ref(v_file_1323_);
v___x_1328_ = l_Lake_createParentDirs(v_file_1323_);
if (lean_obj_tag(v___x_1328_) == 0)
{
uint8_t v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___x_1328_);
v___x_1329_ = 1;
v___x_1330_ = lean_io_prim_handle_mk(v_file_1323_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v_file_1323_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = 1;
v___x_1333_ = lean_io_prim_handle_lock(v_a_1331_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v___x_1333_);
v___x_1334_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__2, &l_Lake_CacheMap_writeFile___closed__2_once, _init_l_Lake_CacheMap_writeFile___closed__2);
v___x_1335_ = l_IO_FS_Handle_putStrLn(v_a_1331_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v___x_1335_);
v___x_1336_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1331_, v_cache_1324_, v_platformIndependent_1325_, v_a_1326_);
lean_dec(v_a_1331_);
return v___x_1336_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_a_1331_);
lean_dec_ref(v_cache_1324_);
v_a_1337_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1335_);
v___x_1338_ = lean_io_error_to_string(v_a_1337_);
v___x_1339_ = 3;
v___x_1340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*1, v___x_1339_);
v___x_1341_ = lean_array_get_size(v_a_1326_);
v___x_1342_ = lean_array_push(v_a_1326_, v___x_1340_);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
return v___x_1343_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_a_1331_);
lean_dec_ref(v_cache_1324_);
v_a_1344_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1333_);
v___x_1345_ = lean_io_error_to_string(v_a_1344_);
v___x_1346_ = 3;
v___x_1347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*1, v___x_1346_);
v___x_1348_ = lean_array_get_size(v_a_1326_);
v___x_1349_ = lean_array_push(v_a_1326_, v___x_1347_);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
return v___x_1350_;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_cache_1324_);
v_a_1351_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1330_);
v___x_1352_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1353_ = lean_string_append(v_file_1323_, v___x_1352_);
v___x_1354_ = lean_io_error_to_string(v_a_1351_);
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = 3;
v___x_1357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1, v___x_1356_);
v___x_1358_ = lean_array_get_size(v_a_1326_);
v___x_1359_ = lean_array_push(v_a_1326_, v___x_1357_);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
return v___x_1360_;
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v_cache_1324_);
lean_dec_ref(v_file_1323_);
v_a_1361_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1328_);
v___x_1362_ = lean_io_error_to_string(v_a_1361_);
v___x_1363_ = 3;
v___x_1364_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*1, v___x_1363_);
v___x_1365_ = lean_array_get_size(v_a_1326_);
v___x_1366_ = lean_array_push(v_a_1326_, v___x_1364_);
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object* v_file_1368_, lean_object* v_cache_1369_, lean_object* v_platformIndependent_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
uint8_t v_platformIndependent_boxed_1373_; lean_object* v_res_1374_; 
v_platformIndependent_boxed_1373_ = lean_unbox(v_platformIndependent_1370_);
v_res_1374_ = l_Lake_CacheMap_writeFile(v_file_1368_, v_cache_1369_, v_platformIndependent_boxed_1373_, v_a_1371_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t v_a_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_box(0);
return v___x_1377_;
}
else
{
lean_object* v_key_1378_; lean_object* v_value_1379_; lean_object* v_tail_1380_; uint64_t v___x_1381_; uint8_t v___x_1382_; 
v_key_1378_ = lean_ctor_get(v_x_1376_, 0);
v_value_1379_ = lean_ctor_get(v_x_1376_, 1);
v_tail_1380_ = lean_ctor_get(v_x_1376_, 2);
v___x_1381_ = lean_unbox_uint64(v_key_1378_);
v___x_1382_ = lean_uint64_dec_eq(v___x_1381_, v_a_1375_);
if (v___x_1382_ == 0)
{
v_x_1376_ = v_tail_1380_;
goto _start;
}
else
{
lean_object* v___x_1384_; 
lean_inc(v_value_1379_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_value_1379_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
uint64_t v_a_boxed_1387_; lean_object* v_res_1388_; 
v_a_boxed_1387_ = lean_unbox_uint64(v_a_1385_);
lean_dec_ref(v_a_1385_);
v_res_1388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_boxed_1387_, v_x_1386_);
lean_dec(v_x_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* v_m_1389_, uint64_t v_a_1390_){
_start:
{
lean_object* v_buckets_1391_; lean_object* v___x_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint64_t v_fold_1395_; uint64_t v___x_1396_; uint64_t v___x_1397_; uint64_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_buckets_1391_ = lean_ctor_get(v_m_1389_, 1);
v___x_1392_ = lean_array_get_size(v_buckets_1391_);
v___x_1393_ = 32ULL;
v___x_1394_ = lean_uint64_shift_right(v_a_1390_, v___x_1393_);
v_fold_1395_ = lean_uint64_xor(v_a_1390_, v___x_1394_);
v___x_1396_ = 16ULL;
v___x_1397_ = lean_uint64_shift_right(v_fold_1395_, v___x_1396_);
v___x_1398_ = lean_uint64_xor(v_fold_1395_, v___x_1397_);
v___x_1399_ = lean_uint64_to_usize(v___x_1398_);
v___x_1400_ = lean_usize_of_nat(v___x_1392_);
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_sub(v___x_1400_, v___x_1401_);
v___x_1403_ = lean_usize_land(v___x_1399_, v___x_1402_);
v___x_1404_ = lean_array_uget_borrowed(v_buckets_1391_, v___x_1403_);
v___x_1405_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1390_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* v_m_1406_, lean_object* v_a_1407_){
_start:
{
uint64_t v_a_boxed_1408_; lean_object* v_res_1409_; 
v_a_boxed_1408_ = lean_unbox_uint64(v_a_1407_);
lean_dec_ref(v_a_1407_);
v_res_1409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1406_, v_a_boxed_1408_);
lean_dec_ref(v_m_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t v_inputHash_1410_, lean_object* v_cache_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_cache_1411_, v_inputHash_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_val_1414_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_out_1418_; lean_object* v___x_1420_; 
v_out_1418_ = lean_ctor_get(v_val_1414_, 0);
lean_inc(v_out_1418_);
lean_dec(v_val_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_out_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_out_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* v_inputHash_1423_, lean_object* v_cache_1424_){
_start:
{
uint64_t v_inputHash_boxed_1425_; lean_object* v_res_1426_; 
v_inputHash_boxed_1425_ = lean_unbox_uint64(v_inputHash_1423_);
lean_dec_ref(v_inputHash_1423_);
v_res_1426_ = l_Lake_CacheMap_get_x3f(v_inputHash_boxed_1425_, v_cache_1424_);
lean_dec_ref(v_cache_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, uint64_t v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1428_, v_a_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_a_1433_){
_start:
{
uint64_t v_a_boxed_1434_; lean_object* v_res_1435_; 
v_a_boxed_1434_ = lean_unbox_uint64(v_a_1433_);
lean_dec_ref(v_a_1433_);
v_res_1435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(v_00_u03b2_1431_, v_m_1432_, v_a_boxed_1434_);
lean_dec_ref(v_m_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1436_, uint64_t v_a_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
uint64_t v_a_boxed_1443_; lean_object* v_res_1444_; 
v_a_boxed_1443_ = lean_unbox_uint64(v_a_1441_);
lean_dec_ref(v_a_1441_);
v_res_1444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(v_00_u03b2_1440_, v_a_boxed_1443_, v_x_1442_);
lean_dec(v_x_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t v_inputHash_1445_, lean_object* v_out_1446_, lean_object* v_cache_1447_, uint8_t v_platformIndependent_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1449_, 0, v_out_1446_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1, v_platformIndependent_1448_);
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_cache_1447_, v_inputHash_1445_, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore___boxed(lean_object* v_inputHash_1451_, lean_object* v_out_1452_, lean_object* v_cache_1453_, lean_object* v_platformIndependent_1454_){
_start:
{
uint64_t v_inputHash_boxed_1455_; uint8_t v_platformIndependent_boxed_1456_; lean_object* v_res_1457_; 
v_inputHash_boxed_1455_ = lean_unbox_uint64(v_inputHash_1451_);
lean_dec_ref(v_inputHash_1451_);
v_platformIndependent_boxed_1456_ = lean_unbox(v_platformIndependent_1454_);
v_res_1457_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_boxed_1455_, v_out_1452_, v_cache_1453_, v_platformIndependent_boxed_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* v_inst_1458_, uint64_t v_inputHash_1459_, lean_object* v_val_1460_, lean_object* v_cache_1461_, uint8_t v_platformIndependent_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_apply_1(v_inst_1458_, v_val_1460_);
v___x_1464_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1459_, v___x_1463_, v_cache_1461_, v_platformIndependent_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* v_inst_1465_, lean_object* v_inputHash_1466_, lean_object* v_val_1467_, lean_object* v_cache_1468_, lean_object* v_platformIndependent_1469_){
_start:
{
uint64_t v_inputHash_boxed_1470_; uint8_t v_platformIndependent_boxed_1471_; lean_object* v_res_1472_; 
v_inputHash_boxed_1470_ = lean_unbox_uint64(v_inputHash_1466_);
lean_dec_ref(v_inputHash_1466_);
v_platformIndependent_boxed_1471_ = lean_unbox(v_platformIndependent_1469_);
v_res_1472_ = l_Lake_CacheMap_insert___redArg(v_inst_1465_, v_inputHash_boxed_1470_, v_val_1467_, v_cache_1468_, v_platformIndependent_boxed_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* v_00_u03b1_1473_, lean_object* v_inst_1474_, uint64_t v_inputHash_1475_, lean_object* v_val_1476_, lean_object* v_cache_1477_, uint8_t v_platformIndependent_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_apply_1(v_inst_1474_, v_val_1476_);
v___x_1480_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1475_, v___x_1479_, v_cache_1477_, v_platformIndependent_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_, lean_object* v_inputHash_1483_, lean_object* v_val_1484_, lean_object* v_cache_1485_, lean_object* v_platformIndependent_1486_){
_start:
{
uint64_t v_inputHash_boxed_1487_; uint8_t v_platformIndependent_boxed_1488_; lean_object* v_res_1489_; 
v_inputHash_boxed_1487_ = lean_unbox_uint64(v_inputHash_1483_);
lean_dec_ref(v_inputHash_1483_);
v_platformIndependent_boxed_1488_ = lean_unbox(v_platformIndependent_1486_);
v_res_1489_ = l_Lake_CacheMap_insert(v_00_u03b1_1481_, v_inst_1482_, v_inputHash_boxed_1487_, v_val_1484_, v_cache_1485_, v_platformIndependent_boxed_1488_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* v_init_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_){
_start:
{
if (lean_obj_tag(v_x_1494_) == 0)
{
lean_object* v_v_1497_; lean_object* v_l_1498_; lean_object* v_r_1499_; lean_object* v___x_1500_; 
v_v_1497_ = lean_ctor_get(v_x_1494_, 2);
lean_inc(v_v_1497_);
v_l_1498_ = lean_ctor_get(v_x_1494_, 3);
lean_inc(v_l_1498_);
v_r_1499_ = lean_ctor_get(v_x_1494_, 4);
lean_inc(v_r_1499_);
lean_dec_ref(v_x_1494_);
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1493_, v_l_1498_, v___y_1495_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1502_);
lean_dec_ref(v___x_1500_);
v___x_1503_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1501_, v_v_1497_, v_a_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v_a_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
v_a_1505_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1503_);
v_init_1493_ = v_a_1504_;
v_x_1494_ = v_r_1499_;
v___y_1495_ = v_a_1505_;
goto _start;
}
else
{
lean_dec(v_r_1499_);
return v___x_1503_;
}
}
else
{
lean_dec(v_r_1499_);
lean_dec(v_v_1497_);
return v___x_1500_;
}
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_init_1493_);
lean_ctor_set(v___x_1507_, 1, v___y_1495_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* v_as_1508_, lean_object* v_o_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___y_1513_; 
switch(lean_obj_tag(v_o_1509_))
{
case 0:
{
v___y_1513_ = v_a_1510_;
goto v___jp_1512_;
}
case 1:
{
lean_object* v___x_1515_; 
lean_dec_ref(v_o_1509_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_as_1508_);
lean_ctor_set(v___x_1515_, 1, v_a_1510_);
return v___x_1515_;
}
case 2:
{
lean_object* v_n_1516_; lean_object* v___x_1517_; 
v_n_1516_ = lean_ctor_get(v_o_1509_, 0);
lean_inc_ref(v_n_1516_);
lean_dec_ref(v_o_1509_);
v___x_1517_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
v___x_1520_ = lean_string_append(v___x_1519_, v_a_1518_);
lean_dec(v_a_1518_);
v___x_1521_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_1522_ = lean_string_append(v___x_1520_, v___x_1521_);
v___x_1523_ = l_Lean_JsonNumber_toString(v_n_1516_);
v___x_1524_ = lean_string_append(v___x_1522_, v___x_1523_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = 3;
v___x_1526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1, v___x_1525_);
v___x_1527_ = lean_array_push(v_a_1510_, v___x_1526_);
v___y_1513_ = v___x_1527_;
goto v___jp_1512_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint64_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec_ref(v_n_1516_);
v_a_1528_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1517_);
v___x_1529_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1));
v___x_1530_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = lean_unbox_uint64(v_a_1528_);
lean_dec(v_a_1528_);
lean_ctor_set_uint64(v___x_1530_, sizeof(void*)*1, v___x_1531_);
v___x_1532_ = lean_array_push(v_as_1508_, v___x_1530_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_a_1510_);
return v___x_1533_;
}
}
case 3:
{
lean_object* v_s_1534_; lean_object* v___x_1535_; 
v_s_1534_ = lean_ctor_get(v_o_1509_, 0);
lean_inc_ref(v_s_1534_);
lean_dec_ref(v_o_1509_);
v___x_1535_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2));
v___x_1538_ = lean_string_append(v___x_1537_, v_a_1536_);
lean_dec(v_a_1536_);
v___x_1539_ = 3;
v___x_1540_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*1, v___x_1539_);
v___x_1541_ = lean_array_push(v_a_1510_, v___x_1540_);
v___y_1513_ = v___x_1541_;
goto v___jp_1512_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_a_1542_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1535_);
v___x_1543_ = lean_array_push(v_as_1508_, v_a_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1510_);
return v___x_1544_;
}
}
case 4:
{
lean_object* v_elems_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_elems_1545_ = lean_ctor_get(v_o_1509_, 0);
lean_inc_ref(v_elems_1545_);
lean_dec_ref(v_o_1509_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_array_get_size(v_elems_1545_);
v___x_1548_ = lean_nat_dec_lt(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref(v_elems_1545_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_as_1508_);
lean_ctor_set(v___x_1549_, 1, v_a_1510_);
return v___x_1549_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_le(v___x_1547_, v___x_1547_);
if (v___x_1550_ == 0)
{
if (v___x_1548_ == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v_elems_1545_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_as_1508_);
lean_ctor_set(v___x_1551_, 1, v_a_1510_);
return v___x_1551_;
}
else
{
size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = lean_usize_of_nat(v___x_1547_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1545_, v___x_1552_, v___x_1553_, v_as_1508_, v_a_1510_);
lean_dec_ref(v_elems_1545_);
return v___x_1554_;
}
}
else
{
size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = lean_usize_of_nat(v___x_1547_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1545_, v___x_1555_, v___x_1556_, v_as_1508_, v_a_1510_);
lean_dec_ref(v_elems_1545_);
return v___x_1557_;
}
}
}
default: 
{
lean_object* v_kvPairs_1558_; lean_object* v___x_1559_; 
v_kvPairs_1558_ = lean_ctor_get(v_o_1509_, 0);
lean_inc(v_kvPairs_1558_);
lean_dec_ref(v_o_1509_);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_as_1508_, v_kvPairs_1558_, v_a_1510_);
return v___x_1559_;
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_as_1508_);
lean_ctor_set(v___x_1514_, 1, v___y_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* v_as_1560_, size_t v_i_1561_, size_t v_stop_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_usize_dec_eq(v_i_1561_, v_stop_1562_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_array_uget_borrowed(v_as_1560_, v_i_1561_);
lean_inc(v___x_1567_);
v___x_1568_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_b_1563_, v___x_1567_, v___y_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_a_1570_; size_t v___x_1571_; size_t v___x_1572_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
v_a_1570_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1568_);
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1561_, v___x_1571_);
v_i_1561_ = v___x_1572_;
v_b_1563_ = v_a_1569_;
v___y_1564_ = v_a_1570_;
goto _start;
}
else
{
return v___x_1568_;
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_b_1563_);
lean_ctor_set(v___x_1574_, 1, v___y_1564_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* v_as_1575_, lean_object* v_i_1576_, lean_object* v_stop_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
size_t v_i_boxed_1581_; size_t v_stop_boxed_1582_; lean_object* v_res_1583_; 
v_i_boxed_1581_ = lean_unbox_usize(v_i_1576_);
lean_dec(v_i_1576_);
v_stop_boxed_1582_ = lean_unbox_usize(v_stop_1577_);
lean_dec(v_stop_1577_);
v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_as_1575_, v_i_boxed_1581_, v_stop_boxed_1582_, v_b_1578_, v___y_1579_);
lean_dec_ref(v_as_1575_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* v_init_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1584_, v_x_1585_, v___y_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* v_as_1589_, lean_object* v_o_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_as_1589_, v_o_1590_, v_a_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v___y_1596_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_x_1594_);
lean_ctor_set(v___x_1598_, 1, v___y_1596_);
return v___x_1598_;
}
else
{
lean_object* v_value_1599_; lean_object* v_tail_1600_; lean_object* v_out_1601_; lean_object* v___x_1602_; 
v_value_1599_ = lean_ctor_get(v_x_1595_, 1);
lean_inc(v_value_1599_);
v_tail_1600_ = lean_ctor_get(v_x_1595_, 2);
lean_inc(v_tail_1600_);
lean_dec_ref(v_x_1595_);
v_out_1601_ = lean_ctor_get(v_value_1599_, 0);
lean_inc(v_out_1601_);
lean_dec(v_value_1599_);
v___x_1602_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_x_1594_, v_out_1601_, v___y_1596_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v_a_1604_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
v_a_1604_ = lean_ctor_get(v___x_1602_, 1);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1602_);
v_x_1594_ = v_a_1603_;
v_x_1595_ = v_tail_1600_;
v___y_1596_ = v_a_1604_;
goto _start;
}
else
{
lean_dec(v_tail_1600_);
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_x_1606_, v_x_1607_, v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* v_as_1611_, size_t v_i_1612_, size_t v_stop_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_usize_dec_eq(v_i_1612_, v_stop_1613_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_array_uget_borrowed(v_as_1611_, v_i_1612_);
lean_inc(v___x_1618_);
v___x_1619_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_b_1614_, v___x_1618_, v___y_1615_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_a_1621_; size_t v___x_1622_; size_t v___x_1623_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
v_a_1621_ = lean_ctor_get(v___x_1619_, 1);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1619_);
v___x_1622_ = ((size_t)1ULL);
v___x_1623_ = lean_usize_add(v_i_1612_, v___x_1622_);
v_i_1612_ = v___x_1623_;
v_b_1614_ = v_a_1620_;
v___y_1615_ = v_a_1621_;
goto _start;
}
else
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_b_1614_);
lean_ctor_set(v___x_1625_, 1, v___y_1615_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_stop_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
size_t v_i_boxed_1632_; size_t v_stop_boxed_1633_; lean_object* v_res_1634_; 
v_i_boxed_1632_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v_stop_boxed_1633_ = lean_unbox_usize(v_stop_1628_);
lean_dec(v_stop_1628_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_as_1626_, v_i_boxed_1632_, v_stop_boxed_1633_, v_b_1629_, v___y_1630_);
lean_dec_ref(v_as_1626_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* v_map_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_buckets_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1669_; 
v_buckets_1640_ = lean_ctor_get(v_map_1637_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_map_1637_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v_map_1637_, 0);
lean_dec(v_unused_1670_);
v___x_1642_ = v_map_1637_;
v_isShared_1643_ = v_isSharedCheck_1669_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_buckets_1640_);
lean_dec(v_map_1637_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1669_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1648_; lean_object* v_a_1649_; lean_object* v___y_1656_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = ((lean_object*)(l_Lake_CacheMap_collectOutputDescrs___closed__0));
v___x_1646_ = lean_array_get_size(v_a_1638_);
v___x_1658_ = lean_array_get_size(v_buckets_1640_);
v___x_1659_ = lean_nat_dec_lt(v___x_1644_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v_buckets_1640_);
lean_inc_ref(v_a_1638_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1645_);
lean_ctor_set(v___x_1660_, 1, v_a_1638_);
v___y_1648_ = v___x_1660_;
v_a_1649_ = v_a_1638_;
goto v___jp_1647_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_le(v___x_1658_, v___x_1658_);
if (v___x_1661_ == 0)
{
if (v___x_1659_ == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref(v_buckets_1640_);
lean_inc_ref(v_a_1638_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1645_);
lean_ctor_set(v___x_1662_, 1, v_a_1638_);
v___y_1648_ = v___x_1662_;
v_a_1649_ = v_a_1638_;
goto v___jp_1647_;
}
else
{
size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = ((size_t)0ULL);
v___x_1664_ = lean_usize_of_nat(v___x_1658_);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1640_, v___x_1663_, v___x_1664_, v___x_1645_, v_a_1638_);
lean_dec_ref(v_buckets_1640_);
v___y_1656_ = v___x_1665_;
goto v___jp_1655_;
}
}
else
{
size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = lean_usize_of_nat(v___x_1658_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1640_, v___x_1666_, v___x_1667_, v___x_1645_, v_a_1638_);
lean_dec_ref(v_buckets_1640_);
v___y_1656_ = v___x_1668_;
goto v___jp_1655_;
}
}
v___jp_1647_:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_array_get_size(v_a_1649_);
v___x_1651_ = lean_nat_dec_eq(v___x_1646_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v___y_1648_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
lean_ctor_set(v___x_1642_, 1, v_a_1649_);
lean_ctor_set(v___x_1642_, 0, v___x_1646_);
v___x_1653_ = v___x_1642_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_a_1649_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_dec_ref(v_a_1649_);
lean_del_object(v___x_1642_);
return v___y_1648_;
}
}
v___jp_1655_:
{
if (lean_obj_tag(v___y_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___y_1656_, 1);
lean_inc(v_a_1657_);
v___y_1648_ = v___y_1656_;
v_a_1649_ = v_a_1657_;
goto v___jp_1647_;
}
else
{
lean_del_object(v___x_1642_);
return v___y_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* v_map_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lake_CacheMap_collectOutputDescrs(v_map_1671_, v_a_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* v_init_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_st_mk_ref(v_init_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* v_init_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lake_CacheRef_mk(v_init_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t v_inputHash_1681_, lean_object* v_cache_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_st_ref_take(v_cache_1682_);
v___x_1685_ = l_Lake_CacheMap_get_x3f(v_inputHash_1681_, v___x_1684_);
v___x_1686_ = lean_st_ref_set(v_cache_1682_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* v_inputHash_1687_, lean_object* v_cache_1688_, lean_object* v_a_1689_){
_start:
{
uint64_t v_inputHash_boxed_1690_; lean_object* v_res_1691_; 
v_inputHash_boxed_1690_ = lean_unbox_uint64(v_inputHash_1687_);
lean_dec_ref(v_inputHash_1687_);
v_res_1691_ = l_Lake_CacheRef_get_x3f(v_inputHash_boxed_1690_, v_cache_1688_);
lean_dec(v_cache_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* v_inst_1692_, uint64_t v_inputHash_1693_, lean_object* v_val_1694_, lean_object* v_cache_1695_, uint8_t v_platformIndependent_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_st_ref_take(v_cache_1695_);
v___x_1699_ = lean_apply_1(v_inst_1692_, v_val_1694_);
v___x_1700_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1693_, v___x_1699_, v___x_1698_, v_platformIndependent_1696_);
v___x_1701_ = lean_st_ref_set(v_cache_1695_, v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* v_inst_1702_, lean_object* v_inputHash_1703_, lean_object* v_val_1704_, lean_object* v_cache_1705_, lean_object* v_platformIndependent_1706_, lean_object* v_a_1707_){
_start:
{
uint64_t v_inputHash_boxed_1708_; uint8_t v_platformIndependent_boxed_1709_; lean_object* v_res_1710_; 
v_inputHash_boxed_1708_ = lean_unbox_uint64(v_inputHash_1703_);
lean_dec_ref(v_inputHash_1703_);
v_platformIndependent_boxed_1709_ = lean_unbox(v_platformIndependent_1706_);
v_res_1710_ = l_Lake_CacheRef_insert___redArg(v_inst_1702_, v_inputHash_boxed_1708_, v_val_1704_, v_cache_1705_, v_platformIndependent_boxed_1709_);
lean_dec(v_cache_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* v_00_u03b1_1711_, lean_object* v_inst_1712_, uint64_t v_inputHash_1713_, lean_object* v_val_1714_, lean_object* v_cache_1715_, uint8_t v_platformIndependent_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = lean_st_ref_take(v_cache_1715_);
v___x_1719_ = lean_apply_1(v_inst_1712_, v_val_1714_);
v___x_1720_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1713_, v___x_1719_, v___x_1718_, v_platformIndependent_1716_);
v___x_1721_ = lean_st_ref_set(v_cache_1715_, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_inst_1723_, lean_object* v_inputHash_1724_, lean_object* v_val_1725_, lean_object* v_cache_1726_, lean_object* v_platformIndependent_1727_, lean_object* v_a_1728_){
_start:
{
uint64_t v_inputHash_boxed_1729_; uint8_t v_platformIndependent_boxed_1730_; lean_object* v_res_1731_; 
v_inputHash_boxed_1729_ = lean_unbox_uint64(v_inputHash_1724_);
lean_dec_ref(v_inputHash_1724_);
v_platformIndependent_boxed_1730_ = lean_unbox(v_platformIndependent_1727_);
v_res_1731_ = l_Lake_CacheRef_insert(v_00_u03b1_1722_, v_inst_1723_, v_inputHash_boxed_1729_, v_val_1725_, v_cache_1726_, v_platformIndependent_boxed_1730_);
lean_dec(v_cache_1726_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object* v_s_1734_){
_start:
{
lean_inc_ref(v_s_1734_);
return v_s_1734_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object* v_s_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lake_CacheServiceName_ofString(v_s_1735_);
lean_dec_ref(v_s_1735_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object* v_self_1737_){
_start:
{
lean_inc_ref(v_self_1737_);
return v_self_1737_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object* v_self_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lake_CacheServiceName_toString(v_self_1738_);
lean_dec_ref(v_self_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object* v_j_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Json_getStr_x3f(v_j_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object* v_self_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_self_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_unsigned_to_nat(1u);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object* v_x_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(v_x_1769_);
lean_dec_ref(v_x_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object* v_t_1771_, lean_object* v_k_1772_){
_start:
{
lean_object* v_s_1773_; lean_object* v___x_1774_; 
v_s_1773_ = lean_ctor_get(v_t_1771_, 0);
lean_inc_ref(v_s_1773_);
lean_dec_ref(v_t_1771_);
v___x_1774_ = lean_apply_1(v_k_1772_, v_s_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object* v_motive_1775_, lean_object* v_ctorIdx_1776_, lean_object* v_t_1777_, lean_object* v_h_1778_, lean_object* v_k_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1777_, v_k_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object* v_motive_1781_, lean_object* v_ctorIdx_1782_, lean_object* v_t_1783_, lean_object* v_h_1784_, lean_object* v_k_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(v_motive_1781_, v_ctorIdx_1782_, v_t_1783_, v_h_1784_, v_k_1785_);
lean_dec(v_ctorIdx_1782_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object* v_t_1787_, lean_object* v_str_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1787_, v_str_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object* v_motive_1790_, lean_object* v_t_1791_, lean_object* v_h_1792_, lean_object* v_str_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1791_, v_str_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object* v_t_1795_, lean_object* v_repo_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1795_, v_repo_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object* v_motive_1798_, lean_object* v_t_1799_, lean_object* v_h_1800_, lean_object* v_repo_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1799_, v_repo_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object* v_s_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_s_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object* v_fullName_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_fullName_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object* v_self_1807_){
_start:
{
if (lean_obj_tag(v_self_1807_) == 1)
{
uint8_t v___x_1808_; 
v___x_1808_ = 1;
return v___x_1808_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = 0;
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object* v_self_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Lake_CacheServiceScope_isRepo(v_self_1810_);
lean_dec_ref(v_self_1810_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object* v_self_1813_){
_start:
{
lean_object* v_s_1814_; 
v_s_1814_ = lean_ctor_get(v_self_1813_, 0);
lean_inc_ref(v_s_1814_);
return v_s_1814_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object* v_self_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lake_CacheServiceScope_toString(v_self_1815_);
lean_dec_ref(v_self_1815_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object* v_self_1819_){
_start:
{
lean_object* v_s_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_s_1820_ = lean_ctor_get(v_self_1819_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_self_1819_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v_self_1819_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_s_1820_);
lean_dec(v_self_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 3);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_s_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object* v_data_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1839_, 0, v_data_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_box(0);
return v___x_1841_;
}
else
{
lean_object* v_val_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_val_1842_ = lean_ctor_get(v_x_1840_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v_x_1840_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_val_1842_);
lean_dec(v_x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 3);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_val_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
static lean_object* _init_l_Lake_CacheOutput_toJson___closed__3(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1854_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__2));
v___x_1855_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1856_ = lean_box(1);
v___x_1857_ = l_Lake_JsonObject_insertJson(v___x_1856_, v___x_1855_, v___x_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object* v_out_1861_){
_start:
{
lean_object* v_data_1862_; lean_object* v_service_x3f_1863_; lean_object* v_scope_x3f_1864_; lean_object* v_obj_1866_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v_obj_1873_; 
v_data_1862_ = lean_ctor_get(v_out_1861_, 0);
lean_inc(v_data_1862_);
v_service_x3f_1863_ = lean_ctor_get(v_out_1861_, 1);
lean_inc(v_service_x3f_1863_);
v_scope_x3f_1864_ = lean_ctor_get(v_out_1861_, 2);
lean_inc(v_scope_x3f_1864_);
lean_dec_ref(v_out_1861_);
v___x_1870_ = lean_obj_once(&l_Lake_CacheOutput_toJson___closed__3, &l_Lake_CacheOutput_toJson___closed__3_once, _init_l_Lake_CacheOutput_toJson___closed__3);
v___x_1871_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1872_ = l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1863_);
v_obj_1873_ = l_Lake_JsonObject_insertJson(v___x_1870_, v___x_1871_, v___x_1872_);
if (lean_obj_tag(v_scope_x3f_1864_) == 1)
{
lean_object* v_val_1874_; lean_object* v___y_1876_; uint8_t v___x_1879_; 
v_val_1874_ = lean_ctor_get(v_scope_x3f_1864_, 0);
lean_inc(v_val_1874_);
lean_dec_ref(v_scope_x3f_1864_);
v___x_1879_ = l_Lake_CacheServiceScope_isRepo(v_val_1874_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___y_1876_ = v___x_1880_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___y_1876_ = v___x_1881_;
goto v___jp_1875_;
}
v___jp_1875_:
{
lean_object* v___x_1877_; lean_object* v_obj_1878_; 
v___x_1877_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(v_val_1874_);
v_obj_1878_ = l_Lake_JsonObject_insertJson(v_obj_1873_, v___y_1876_, v___x_1877_);
v_obj_1866_ = v_obj_1878_;
goto v___jp_1865_;
}
}
else
{
lean_dec(v_scope_x3f_1864_);
v_obj_1866_ = v_obj_1873_;
goto v___jp_1865_;
}
v___jp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1868_ = l_Lake_JsonObject_insertJson(v_obj_1866_, v___x_1867_, v_data_1862_);
v___x_1869_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1886_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Json_getStr_x3f(v_x_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
v_a_1897_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v_a_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Json_getStr_x3f(v_x_1906_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
v_a_1917_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_a_1917_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object* v_k_1926_, lean_object* v_t_1927_){
_start:
{
if (lean_obj_tag(v_t_1927_) == 0)
{
lean_object* v_k_1928_; lean_object* v_l_1929_; lean_object* v_r_1930_; uint8_t v___x_1931_; 
v_k_1928_ = lean_ctor_get(v_t_1927_, 1);
v_l_1929_ = lean_ctor_get(v_t_1927_, 3);
v_r_1930_ = lean_ctor_get(v_t_1927_, 4);
v___x_1931_ = lean_string_dec_lt(v_k_1926_, v_k_1928_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_string_dec_eq(v_k_1926_, v_k_1928_);
if (v___x_1932_ == 0)
{
v_t_1927_ = v_r_1930_;
goto _start;
}
else
{
return v___x_1932_;
}
}
else
{
v_t_1927_ = v_l_1929_;
goto _start;
}
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = 0;
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object* v_k_1936_, lean_object* v_t_1937_){
_start:
{
uint8_t v_res_1938_; lean_object* v_r_1939_; 
v_res_1938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1936_, v_t_1937_);
lean_dec(v_t_1937_);
lean_dec_ref(v_k_1936_);
v_r_1939_ = lean_box(v_res_1938_);
return v_r_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object* v_json_1946_){
_start:
{
if (lean_obj_tag(v_json_1946_) == 5)
{
lean_object* v_kvPairs_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v_kvPairs_1951_ = lean_ctor_get(v_json_1946_, 0);
v___x_1952_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1953_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v___x_1952_, v_kvPairs_1951_);
if (v___x_1953_ == 0)
{
goto v___jp_1947_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_inc(v_kvPairs_1951_);
lean_dec_ref(v_json_1946_);
v___x_1954_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1955_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_kvPairs_1951_);
v___x_1956_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__1));
return v___x_1956_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2075_; 
v_val_1957_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_1959_ = v___x_1955_;
v_isShared_1960_ = v_isSharedCheck_2075_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_val_1957_);
lean_dec(v___x_1955_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2075_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___y_1962_; lean_object* v_a_1963_; lean_object* v___y_1969_; lean_object* v___y_1972_; lean_object* v_a_2012_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_2052_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_box(0);
v_a_2012_ = v___x_2053_;
goto v___jp_2011_;
}
else
{
lean_object* v_val_2054_; lean_object* v___x_2055_; 
v_val_2054_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_val_2054_);
lean_dec_ref(v___x_2052_);
v___x_2055_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2065_; 
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2060_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__4));
v___x_2061_ = lean_string_append(v___x_2060_, v_a_2056_);
lean_dec(v_a_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2061_);
v___x_2063_ = v___x_2058_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2066_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2055_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2055_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 0);
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2055_);
v_a_2012_ = v_a_2074_;
goto v___jp_2011_;
}
}
}
v___jp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1964_, 0, v_val_1957_);
lean_ctor_set(v___x_1964_, 1, v___y_1962_);
lean_ctor_set(v___x_1964_, 2, v_a_1963_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1964_);
v___x_1966_ = v___x_1959_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
v___jp_1968_:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_box(0);
v___y_1962_ = v___y_1969_;
v_a_1963_ = v___x_1970_;
goto v___jp_1961_;
}
v___jp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___x_1974_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_1973_);
lean_dec(v_kvPairs_1951_);
if (lean_obj_tag(v___x_1974_) == 0)
{
v___y_1969_ = v___y_1972_;
goto v___jp_1968_;
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2010_; 
v_val_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2010_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2010_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1975_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1989_; 
lean_del_object(v___x_1977_);
lean_dec(v___y_1972_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1984_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__2));
v___x_1985_ = lean_string_append(v___x_1984_, v_a_1980_);
lean_dec(v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1985_);
v___x_1987_ = v___x_1982_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_del_object(v___x_1977_);
lean_dec(v___y_1972_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
v_a_1990_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1979_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1979_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 0);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1979_);
if (lean_obj_tag(v_a_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
v_val_1999_ = lean_ctor_get(v_a_1998_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2001_ = v_a_1998_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v_a_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 0);
lean_ctor_set(v___x_1977_, 0, v_val_1999_);
v___x_2004_ = v___x_1977_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_val_1999_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
v___y_1962_ = v___y_1972_;
v_a_1963_ = v___x_2006_;
goto v___jp_1961_;
}
}
}
}
else
{
lean_dec(v_a_1998_);
lean_del_object(v___x_1977_);
v___y_1969_ = v___y_1972_;
goto v___jp_1968_;
}
}
}
}
}
}
v___jp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___x_2014_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
v___y_1972_ = v_a_2012_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2050_; 
v_val_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2050_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2050_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_2015_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2029_; 
lean_del_object(v___x_2017_);
lean_dec(v_a_2012_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__3));
v___x_2025_ = lean_string_append(v___x_2024_, v_a_2020_);
lean_dec(v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_del_object(v___x_2017_);
lean_dec(v_a_2012_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2030_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2019_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2019_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 0);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2019_);
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_kvPairs_1951_);
v_val_2039_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2041_ = v_a_2038_;
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v_a_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_val_2039_);
v___x_2044_ = v___x_2017_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_val_2039_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2044_);
v___x_2046_ = v___x_2041_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
v___y_1962_ = v_a_2012_;
v_a_1963_ = v___x_2046_;
goto v___jp_1961_;
}
}
}
}
else
{
lean_dec(v_a_2038_);
lean_del_object(v___x_2017_);
v___y_1972_ = v_a_2012_;
goto v___jp_1971_;
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
goto v___jp_1947_;
}
v___jp_1947_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1949_, 0, v_json_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
lean_ctor_set(v___x_1949_, 2, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object* v_00_u03b2_2076_, lean_object* v_k_2077_, lean_object* v_t_2078_){
_start:
{
uint8_t v___x_2079_; 
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_2077_, v_t_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object* v_00_u03b2_2080_, lean_object* v_k_2081_, lean_object* v_t_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(v_00_u03b2_2080_, v_k_2081_, v_t_2082_);
lean_dec(v_t_2082_);
lean_dec_ref(v_k_2081_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache_default(void){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_System_instInhabitedFilePath_default;
return v___x_2087_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache(void){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_System_instInhabitedFilePath_default;
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_2090_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2092_ = l_System_FilePath_join(v_cache_2090_, v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_2094_, uint64_t v_contentHash_2095_, lean_object* v_ext_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2097_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2098_ = l_System_FilePath_join(v_cache_2094_, v___x_2097_);
v___x_2099_ = lean_string_utf8_byte_size(v_ext_2096_);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = lean_nat_dec_eq(v___x_2099_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2102_ = l_Lake_Hash_hex(v_contentHash_2095_);
v___x_2103_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2104_ = lean_string_append(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_string_append(v___x_2104_, v_ext_2096_);
v___x_2106_ = l_System_FilePath_join(v___x_2098_, v___x_2105_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = l_Lake_Hash_hex(v_contentHash_2095_);
v___x_2108_ = l_System_FilePath_join(v___x_2098_, v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_2109_, lean_object* v_contentHash_2110_, lean_object* v_ext_2111_){
_start:
{
uint64_t v_contentHash_boxed_2112_; lean_object* v_res_2113_; 
v_contentHash_boxed_2112_ = lean_unbox_uint64(v_contentHash_2110_);
lean_dec_ref(v_contentHash_2110_);
v_res_2113_ = l_Lake_Cache_artifactPath(v_cache_2109_, v_contentHash_boxed_2112_, v_ext_2111_);
lean_dec_ref(v_ext_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_2114_, lean_object* v_descr_2115_){
_start:
{
uint64_t v_hash_2117_; lean_object* v_ext_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___y_2122_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_hash_2117_ = lean_ctor_get_uint64(v_descr_2115_, sizeof(void*)*1);
v_ext_2118_ = lean_ctor_get(v_descr_2115_, 0);
v___x_2119_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2120_ = l_System_FilePath_join(v_cache_2114_, v___x_2119_);
v___x_2136_ = lean_string_utf8_byte_size(v_ext_2118_);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_nat_dec_eq(v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = l_Lake_Hash_hex(v_hash_2117_);
v___x_2140_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2141_ = lean_string_append(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2141_, v_ext_2118_);
v___y_2122_ = v___x_2142_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lake_Hash_hex(v_hash_2117_);
v___y_2122_ = v___x_2143_;
goto v___jp_2121_;
}
v___jp_2121_:
{
lean_object* v_path_2123_; lean_object* v___x_2124_; 
v_path_2123_ = l_System_FilePath_join(v___x_2120_, v___y_2122_);
v___x_2124_ = lean_io_metadata(v_path_2123_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2134_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2134_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2134_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_modified_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v_modified_2129_ = lean_ctor_get(v_a_2125_, 1);
lean_inc_ref(v_modified_2129_);
lean_dec(v_a_2125_);
lean_inc_ref(v_path_2123_);
v___x_2130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2130_, 0, v_descr_2115_);
lean_ctor_set(v___x_2130_, 1, v_path_2123_);
lean_ctor_set(v___x_2130_, 2, v_path_2123_);
lean_ctor_set(v___x_2130_, 3, v_modified_2129_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 1);
lean_ctor_set(v___x_2127_, 0, v___x_2130_);
v___x_2132_ = v___x_2127_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec_ref(v___x_2124_);
lean_dec_ref(v_path_2123_);
lean_dec_ref(v_descr_2115_);
v___x_2135_ = lean_box(0);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_2144_, lean_object* v_descr_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lake_Cache_getArtifact_x3f(v_cache_2144_, v_descr_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_2150_, lean_object* v_descr_2151_){
_start:
{
uint64_t v_hash_2153_; lean_object* v_ext_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___y_2158_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_hash_2153_ = lean_ctor_get_uint64(v_descr_2151_, sizeof(void*)*1);
v_ext_2154_ = lean_ctor_get(v_descr_2151_, 0);
v___x_2155_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2156_ = l_System_FilePath_join(v_cache_2150_, v___x_2155_);
v___x_2187_ = lean_string_utf8_byte_size(v_ext_2154_);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_nat_dec_eq(v___x_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2190_ = l_Lake_Hash_hex(v_hash_2153_);
v___x_2191_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2192_ = lean_string_append(v___x_2190_, v___x_2191_);
v___x_2193_ = lean_string_append(v___x_2192_, v_ext_2154_);
v___y_2158_ = v___x_2193_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lake_Hash_hex(v_hash_2153_);
v___y_2158_ = v___x_2194_;
goto v___jp_2157_;
}
v___jp_2157_:
{
lean_object* v_path_2159_; lean_object* v___x_2160_; 
v_path_2159_ = l_System_FilePath_join(v___x_2156_, v___y_2158_);
v___x_2160_ = lean_io_metadata(v_path_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2170_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_modified_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v_modified_2165_ = lean_ctor_get(v_a_2161_, 1);
lean_inc_ref(v_modified_2165_);
lean_dec(v_a_2161_);
lean_inc_ref(v_path_2159_);
v___x_2166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2166_, 0, v_descr_2151_);
lean_ctor_set(v___x_2166_, 1, v_path_2159_);
lean_ctor_set(v___x_2166_, 2, v_path_2159_);
lean_ctor_set(v___x_2166_, 3, v_modified_2165_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2166_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_descr_2151_);
v_a_2171_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2173_ = v___x_2160_;
v_isShared_2174_ = v_isSharedCheck_2186_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2160_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2186_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
if (lean_obj_tag(v_a_2171_) == 11)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec_ref(v_a_2171_);
v___x_2175_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2176_ = lean_string_append(v___x_2175_, v_path_2159_);
lean_dec_ref(v_path_2159_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2176_);
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
lean_dec_ref(v_path_2159_);
v___x_2180_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_2181_ = lean_io_error_to_string(v_a_2171_);
v___x_2182_ = lean_string_append(v___x_2180_, v___x_2181_);
lean_dec_ref(v___x_2181_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2182_);
v___x_2184_ = v___x_2173_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_2195_, lean_object* v_descr_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lake_Cache_getArtifact(v_cache_2195_, v_descr_2196_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object* v_cache_2199_, lean_object* v_out_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___y_2204_; lean_object* v___y_2205_; uint64_t v_hash_2207_; lean_object* v_ext_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___y_2212_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_hash_2207_ = lean_ctor_get_uint64(v_out_2200_, sizeof(void*)*1);
v_ext_2208_ = lean_ctor_get(v_out_2200_, 0);
v___x_2209_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2210_ = l_System_FilePath_join(v_cache_2199_, v___x_2209_);
v___x_2220_ = lean_string_utf8_byte_size(v_ext_2208_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_nat_dec_eq(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2223_ = l_Lake_Hash_hex(v_hash_2207_);
v___x_2224_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_string_append(v___x_2225_, v_ext_2208_);
v___y_2212_ = v___x_2226_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lake_Hash_hex(v_hash_2207_);
v___y_2212_ = v___x_2227_;
goto v___jp_2211_;
}
v___jp_2203_:
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___y_2204_);
lean_ctor_set(v___x_2206_, 1, v___y_2205_);
return v___x_2206_;
}
v___jp_2211_:
{
lean_object* v_art_2213_; uint8_t v___x_2214_; 
v_art_2213_ = l_System_FilePath_join(v___x_2210_, v___y_2212_);
v___x_2214_ = l_System_FilePath_pathExists(v_art_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2215_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2216_ = lean_string_append(v___x_2215_, v_art_2213_);
v___x_2217_ = 3;
v___x_2218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*1, v___x_2217_);
v___x_2219_ = lean_array_push(v___y_2201_, v___x_2218_);
v___y_2204_ = v_art_2213_;
v___y_2205_ = v___x_2219_;
goto v___jp_2203_;
}
else
{
v___y_2204_ = v_art_2213_;
v___y_2205_ = v___y_2201_;
goto v___jp_2203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object* v_cache_2228_, lean_object* v_out_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lake_Cache_getArtifactPaths___lam__0(v_cache_2228_, v_out_2229_, v___y_2230_);
lean_dec_ref(v_out_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object* v_n_2233_, lean_object* v_f_2234_, lean_object* v_xs_2235_, lean_object* v_k_2236_, lean_object* v_acc_2237_, lean_object* v___y_2238_){
_start:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_nat_dec_lt(v_k_2236_, v_n_2233_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_dec(v_k_2236_);
lean_dec_ref(v_f_2234_);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_acc_2237_);
lean_ctor_set(v___x_2241_, 1, v___y_2238_);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_array_fget_borrowed(v_xs_2235_, v_k_2236_);
lean_inc_ref(v_f_2234_);
lean_inc(v___x_2242_);
v___x_2243_ = lean_apply_3(v_f_2234_, v___x_2242_, v___y_2238_, lean_box(0));
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v_a_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
v_a_2245_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2243_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_add(v_k_2236_, v___x_2246_);
lean_dec(v_k_2236_);
v___x_2248_ = lean_array_push(v_acc_2237_, v_a_2244_);
v_k_2236_ = v___x_2247_;
v_acc_2237_ = v___x_2248_;
v___y_2238_ = v_a_2245_;
goto _start;
}
else
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v_acc_2237_);
lean_dec(v_k_2236_);
lean_dec_ref(v_f_2234_);
v_a_2250_ = lean_ctor_get(v___x_2243_, 0);
v_a_2251_ = lean_ctor_get(v___x_2243_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2243_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_inc(v_a_2250_);
lean_dec(v___x_2243_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2250_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object* v_n_2259_, lean_object* v_f_2260_, lean_object* v_xs_2261_, lean_object* v_k_2262_, lean_object* v_acc_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2259_, v_f_2260_, v_xs_2261_, v_k_2262_, v_acc_2263_, v___y_2264_);
lean_dec_ref(v_xs_2261_);
lean_dec(v_n_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object* v_cache_2269_, lean_object* v_descrs_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___f_2273_ = lean_alloc_closure((void*)(l_Lake_Cache_getArtifactPaths___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2273_, 0, v_cache_2269_);
v___x_2274_ = lean_array_get_size(v_descrs_2270_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_a_2271_);
v___x_2277_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v___x_2274_, v___f_2273_, v_descrs_2270_, v___x_2275_, v___x_2276_, v_a_2271_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 1);
lean_inc(v_a_2278_);
v___x_2279_ = lean_array_get_size(v_a_2271_);
lean_dec_ref(v_a_2271_);
v___x_2280_ = lean_array_get_size(v_a_2278_);
v___x_2281_ = lean_nat_dec_eq(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2289_ = lean_ctor_get(v___x_2277_, 1);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2290_);
v___x_2283_ = v___x_2277_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v___x_2277_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 1);
lean_ctor_set(v___x_2283_, 0, v___x_2279_);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_a_2278_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
else
{
lean_dec(v_a_2278_);
return v___x_2277_;
}
}
else
{
lean_dec_ref(v_a_2271_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object* v_cache_2291_, lean_object* v_descrs_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lake_Cache_getArtifactPaths(v_cache_2291_, v_descrs_2292_, v_a_2293_);
lean_dec_ref(v_descrs_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object* v_00_u03b1_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_n_2298_, lean_object* v_f_2299_, lean_object* v_xs_2300_, lean_object* v_k_2301_, lean_object* v_h_2302_, lean_object* v_acc_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2298_, v_f_2299_, v_xs_2300_, v_k_2301_, v_acc_2303_, v___y_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_00_u03b2_2308_, lean_object* v_n_2309_, lean_object* v_f_2310_, lean_object* v_xs_2311_, lean_object* v_k_2312_, lean_object* v_h_2313_, lean_object* v_acc_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(v_00_u03b1_2307_, v_00_u03b2_2308_, v_n_2309_, v_f_2310_, v_xs_2311_, v_k_2312_, v_h_2313_, v_acc_2314_, v___y_2315_);
lean_dec_ref(v_xs_2311_);
lean_dec(v_n_2309_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2321_ = l_System_FilePath_join(v_cache_2319_, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2323_, lean_object* v_scope_2324_, uint64_t v_inputHash_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2326_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2327_ = l_System_FilePath_join(v_cache_2323_, v___x_2326_);
v___x_2328_ = l_System_FilePath_join(v___x_2327_, v_scope_2324_);
v___x_2329_ = l_Lake_Hash_hex(v_inputHash_2325_);
v___x_2330_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2331_ = lean_string_append(v___x_2329_, v___x_2330_);
v___x_2332_ = l_System_FilePath_join(v___x_2328_, v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2333_, lean_object* v_scope_2334_, lean_object* v_inputHash_2335_){
_start:
{
uint64_t v_inputHash_boxed_2336_; lean_object* v_res_2337_; 
v_inputHash_boxed_2336_ = lean_unbox_uint64(v_inputHash_2335_);
lean_dec_ref(v_inputHash_2335_);
v_res_2337_ = l_Lake_Cache_outputsFile(v_cache_2333_, v_scope_2334_, v_inputHash_boxed_2336_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2338_, lean_object* v_scope_2339_, uint64_t v_inputHash_2340_, lean_object* v_out_2341_, lean_object* v_service_x3f_2342_, lean_object* v_remoteScope_x3f_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_file_2351_; lean_object* v___x_2352_; 
v___x_2345_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2346_ = l_System_FilePath_join(v_cache_2338_, v___x_2345_);
v___x_2347_ = l_System_FilePath_join(v___x_2346_, v_scope_2339_);
v___x_2348_ = l_Lake_Hash_hex(v_inputHash_2340_);
v___x_2349_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2350_ = lean_string_append(v___x_2348_, v___x_2349_);
v_file_2351_ = l_System_FilePath_join(v___x_2347_, v___x_2350_);
lean_inc_ref(v_file_2351_);
v___x_2352_ = l_Lake_createParentDirs(v_file_2351_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec_ref(v___x_2352_);
v___x_2353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2353_, 0, v_out_2341_);
lean_ctor_set(v___x_2353_, 1, v_service_x3f_2342_);
lean_ctor_set(v___x_2353_, 2, v_remoteScope_x3f_2343_);
v___x_2354_ = l_Lake_CacheOutput_toJson(v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(80u);
v___x_2356_ = l_Lean_Json_pretty(v___x_2354_, v___x_2355_);
v___x_2357_ = l_IO_FS_writeFile(v_file_2351_, v___x_2356_);
lean_dec_ref(v___x_2356_);
lean_dec_ref(v_file_2351_);
return v___x_2357_;
}
else
{
lean_dec_ref(v_file_2351_);
lean_dec(v_remoteScope_x3f_2343_);
lean_dec(v_service_x3f_2342_);
lean_dec(v_out_2341_);
return v___x_2352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2358_, lean_object* v_scope_2359_, lean_object* v_inputHash_2360_, lean_object* v_out_2361_, lean_object* v_service_x3f_2362_, lean_object* v_remoteScope_x3f_2363_, lean_object* v_a_2364_){
_start:
{
uint64_t v_inputHash_boxed_2365_; lean_object* v_res_2366_; 
v_inputHash_boxed_2365_ = lean_unbox_uint64(v_inputHash_2360_);
lean_dec_ref(v_inputHash_2360_);
v_res_2366_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2358_, v_scope_2359_, v_inputHash_boxed_2365_, v_out_2361_, v_service_x3f_2362_, v_remoteScope_x3f_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2367_, lean_object* v_cache_2368_, lean_object* v_scope_2369_, uint64_t v_inputHash_2370_, lean_object* v_outputs_2371_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_apply_1(v_inst_2367_, v_outputs_2371_);
v___x_2374_ = lean_box(0);
v___x_2375_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2368_, v_scope_2369_, v_inputHash_2370_, v___x_2373_, v___x_2374_, v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2376_, lean_object* v_cache_2377_, lean_object* v_scope_2378_, lean_object* v_inputHash_2379_, lean_object* v_outputs_2380_, lean_object* v_a_2381_){
_start:
{
uint64_t v_inputHash_boxed_2382_; lean_object* v_res_2383_; 
v_inputHash_boxed_2382_ = lean_unbox_uint64(v_inputHash_2379_);
lean_dec_ref(v_inputHash_2379_);
v_res_2383_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2376_, v_cache_2377_, v_scope_2378_, v_inputHash_boxed_2382_, v_outputs_2380_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2384_, lean_object* v_inst_2385_, lean_object* v_cache_2386_, lean_object* v_scope_2387_, uint64_t v_inputHash_2388_, lean_object* v_outputs_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_apply_1(v_inst_2385_, v_outputs_2389_);
v___x_2392_ = lean_box(0);
v___x_2393_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2386_, v_scope_2387_, v_inputHash_2388_, v___x_2391_, v___x_2392_, v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_inst_2395_, lean_object* v_cache_2396_, lean_object* v_scope_2397_, lean_object* v_inputHash_2398_, lean_object* v_outputs_2399_, lean_object* v_a_2400_){
_start:
{
uint64_t v_inputHash_boxed_2401_; lean_object* v_res_2402_; 
v_inputHash_boxed_2401_ = lean_unbox_uint64(v_inputHash_2398_);
lean_dec_ref(v_inputHash_2398_);
v_res_2402_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2394_, v_inst_2395_, v_cache_2396_, v_scope_2397_, v_inputHash_boxed_2401_, v_outputs_2399_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2403_, lean_object* v_scope_2404_, lean_object* v_service_x3f_2405_, lean_object* v_remoteScope_x3f_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v___x_2410_; 
lean_dec(v_remoteScope_x3f_2406_);
lean_dec(v_service_x3f_2405_);
lean_dec_ref(v_scope_2404_);
lean_dec_ref(v_cache_2403_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_x_2407_);
return v___x_2410_;
}
else
{
lean_object* v_value_2411_; lean_object* v_key_2412_; lean_object* v_tail_2413_; lean_object* v_out_2414_; uint64_t v___x_2415_; lean_object* v___x_2416_; 
v_value_2411_ = lean_ctor_get(v_x_2408_, 1);
lean_inc(v_value_2411_);
v_key_2412_ = lean_ctor_get(v_x_2408_, 0);
lean_inc(v_key_2412_);
v_tail_2413_ = lean_ctor_get(v_x_2408_, 2);
lean_inc(v_tail_2413_);
lean_dec_ref(v_x_2408_);
v_out_2414_ = lean_ctor_get(v_value_2411_, 0);
lean_inc(v_out_2414_);
lean_dec(v_value_2411_);
v___x_2415_ = lean_unbox_uint64(v_key_2412_);
lean_dec(v_key_2412_);
lean_inc(v_remoteScope_x3f_2406_);
lean_inc(v_service_x3f_2405_);
lean_inc_ref(v_scope_2404_);
lean_inc_ref(v_cache_2403_);
v___x_2416_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2403_, v_scope_2404_, v___x_2415_, v_out_2414_, v_service_x3f_2405_, v_remoteScope_x3f_2406_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
v_x_2407_ = v_a_2417_;
v_x_2408_ = v_tail_2413_;
goto _start;
}
else
{
lean_dec(v_tail_2413_);
lean_dec(v_remoteScope_x3f_2406_);
lean_dec(v_service_x3f_2405_);
lean_dec_ref(v_scope_2404_);
lean_dec_ref(v_cache_2403_);
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2419_, lean_object* v_scope_2420_, lean_object* v_service_x3f_2421_, lean_object* v_remoteScope_x3f_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2419_, v_scope_2420_, v_service_x3f_2421_, v_remoteScope_x3f_2422_, v_x_2423_, v_x_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2427_, lean_object* v_scope_2428_, lean_object* v_service_x3f_2429_, lean_object* v_remoteScope_x3f_2430_, lean_object* v_as_2431_, size_t v_i_2432_, size_t v_stop_2433_, lean_object* v_b_2434_){
_start:
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_usize_dec_eq(v_i_2432_, v_stop_2433_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_array_uget_borrowed(v_as_2431_, v_i_2432_);
v___x_2438_ = lean_box(0);
lean_inc(v___x_2437_);
lean_inc(v_remoteScope_x3f_2430_);
lean_inc(v_service_x3f_2429_);
lean_inc_ref(v_scope_2428_);
lean_inc_ref(v_cache_2427_);
v___x_2439_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2427_, v_scope_2428_, v_service_x3f_2429_, v_remoteScope_x3f_2430_, v___x_2438_, v___x_2437_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; size_t v___x_2441_; size_t v___x_2442_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2432_, v___x_2441_);
v_i_2432_ = v___x_2442_;
v_b_2434_ = v_a_2440_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2430_);
lean_dec(v_service_x3f_2429_);
lean_dec_ref(v_scope_2428_);
lean_dec_ref(v_cache_2427_);
return v___x_2439_;
}
}
else
{
lean_object* v___x_2444_; 
lean_dec(v_remoteScope_x3f_2430_);
lean_dec(v_service_x3f_2429_);
lean_dec_ref(v_scope_2428_);
lean_dec_ref(v_cache_2427_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_b_2434_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2445_, lean_object* v_scope_2446_, lean_object* v_service_x3f_2447_, lean_object* v_remoteScope_x3f_2448_, lean_object* v_as_2449_, lean_object* v_i_2450_, lean_object* v_stop_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_){
_start:
{
size_t v_i_boxed_2454_; size_t v_stop_boxed_2455_; lean_object* v_res_2456_; 
v_i_boxed_2454_ = lean_unbox_usize(v_i_2450_);
lean_dec(v_i_2450_);
v_stop_boxed_2455_ = lean_unbox_usize(v_stop_2451_);
lean_dec(v_stop_2451_);
v_res_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2445_, v_scope_2446_, v_service_x3f_2447_, v_remoteScope_x3f_2448_, v_as_2449_, v_i_boxed_2454_, v_stop_boxed_2455_, v_b_2452_);
lean_dec_ref(v_as_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2457_, lean_object* v_scope_2458_, lean_object* v_map_2459_, lean_object* v_service_x3f_2460_, lean_object* v_remoteScope_x3f_2461_){
_start:
{
lean_object* v_buckets_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_buckets_2463_ = lean_ctor_get(v_map_2459_, 1);
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_array_get_size(v_buckets_2463_);
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_nat_dec_lt(v___x_2464_, v___x_2465_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec(v_remoteScope_x3f_2461_);
lean_dec(v_service_x3f_2460_);
lean_dec_ref(v_scope_2458_);
lean_dec_ref(v_cache_2457_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
return v___x_2468_;
}
else
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_nat_dec_le(v___x_2465_, v___x_2465_);
if (v___x_2469_ == 0)
{
if (v___x_2467_ == 0)
{
lean_object* v___x_2470_; 
lean_dec(v_remoteScope_x3f_2461_);
lean_dec(v_service_x3f_2460_);
lean_dec_ref(v_scope_2458_);
lean_dec_ref(v_cache_2457_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2466_);
return v___x_2470_;
}
else
{
size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((size_t)0ULL);
v___x_2472_ = lean_usize_of_nat(v___x_2465_);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2457_, v_scope_2458_, v_service_x3f_2460_, v_remoteScope_x3f_2461_, v_buckets_2463_, v___x_2471_, v___x_2472_, v___x_2466_);
return v___x_2473_;
}
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = lean_usize_of_nat(v___x_2465_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2457_, v_scope_2458_, v_service_x3f_2460_, v_remoteScope_x3f_2461_, v_buckets_2463_, v___x_2474_, v___x_2475_, v___x_2466_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2477_, lean_object* v_scope_2478_, lean_object* v_map_2479_, lean_object* v_service_x3f_2480_, lean_object* v_remoteScope_x3f_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lake_Cache_writeMap(v_cache_2477_, v_scope_2478_, v_map_2479_, v_service_x3f_2480_, v_remoteScope_x3f_2481_);
lean_dec_ref(v_map_2479_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2486_){
_start:
{
if (lean_obj_tag(v_x_2486_) == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lake_CacheOutput_fromJson_x3f(v_x_2486_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2505_; 
v_a_2497_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2499_ = v___x_2488_;
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2488_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2497_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2501_);
v___x_2503_ = v___x_2499_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2508_, lean_object* v_scope_2509_, uint64_t v_inputHash_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_path_2519_; lean_object* v___x_2520_; 
v___x_2513_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2514_ = l_System_FilePath_join(v_cache_2508_, v___x_2513_);
v___x_2515_ = l_System_FilePath_join(v___x_2514_, v_scope_2509_);
v___x_2516_ = l_Lake_Hash_hex(v_inputHash_2510_);
v___x_2517_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2518_ = lean_string_append(v___x_2516_, v___x_2517_);
v_path_2519_ = l_System_FilePath_join(v___x_2515_, v___x_2518_);
v___x_2520_ = l_IO_FS_readFile(v_path_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v_a_2523_; lean_object* v___x_2532_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v___x_2532_ = l_Lean_Json_parse(v_a_2521_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
v_a_2523_ = v_a_2533_;
goto v___jp_2522_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; 
v_a_2534_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2534_);
lean_dec_ref(v___x_2532_);
v___x_2535_ = l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v___x_2535_);
v_a_2523_ = v_a_2536_;
goto v___jp_2522_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
lean_dec_ref(v_path_2519_);
v_a_2537_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2535_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v_a_2537_);
lean_ctor_set(v___x_2538_, 1, v_a_2511_);
return v___x_2538_;
}
}
v___jp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2524_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2525_ = lean_string_append(v_path_2519_, v___x_2524_);
v___x_2526_ = lean_string_append(v___x_2525_, v_a_2523_);
lean_dec_ref(v_a_2523_);
v___x_2527_ = 2;
v___x_2528_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*1, v___x_2527_);
v___x_2529_ = lean_array_push(v_a_2511_, v___x_2528_);
v___x_2530_ = lean_box(0);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v___x_2529_);
return v___x_2531_;
}
}
else
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2520_);
if (lean_obj_tag(v_a_2539_) == 11)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_path_2519_);
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v_a_2511_);
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2542_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2543_ = lean_string_append(v_path_2519_, v___x_2542_);
v___x_2544_ = lean_io_error_to_string(v_a_2539_);
v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = 3;
v___x_2547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*1, v___x_2546_);
v___x_2548_ = lean_array_get_size(v_a_2511_);
v___x_2549_ = lean_array_push(v_a_2511_, v___x_2547_);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2551_, lean_object* v_scope_2552_, lean_object* v_inputHash_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
uint64_t v_inputHash_boxed_2556_; lean_object* v_res_2557_; 
v_inputHash_boxed_2556_ = lean_unbox_uint64(v_inputHash_2553_);
lean_dec_ref(v_inputHash_2553_);
v_res_2557_ = l_Lake_Cache_readOutputs_x3f(v_cache_2551_, v_scope_2552_, v_inputHash_boxed_2556_, v_a_2554_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2559_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2561_ = l_System_FilePath_join(v_cache_2559_, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2563_, lean_object* v_scope_2564_, lean_object* v_rev_2565_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2566_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2567_ = l_System_FilePath_join(v_cache_2563_, v___x_2566_);
v___x_2568_ = l_System_FilePath_join(v___x_2567_, v_scope_2564_);
v___x_2569_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2570_ = lean_string_append(v_rev_2565_, v___x_2569_);
v___x_2571_ = l_System_FilePath_join(v___x_2568_, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2574_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = lean_string_utf8_byte_size(v_self_2574_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_nat_dec_eq(v___x_2575_, v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2578_){
_start:
{
uint8_t v_res_2579_; lean_object* v_r_2580_; 
v_res_2579_ = l_Lake_CachePlatform_isNone(v_self_2578_);
lean_dec_ref(v_self_2578_);
v_r_2580_ = lean_box(v_res_2579_);
return v_r_2580_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_System_Platform_target;
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2582_){
_start:
{
lean_inc_ref(v_s_2582_);
return v_s_2582_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lake_CachePlatform_ofString(v_s_2583_);
lean_dec_ref(v_s_2583_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_string_length(v_self_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object* v_self_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lake_CachePlatform_length(v_self_2587_);
lean_dec_ref(v_self_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2591_ = lean_string_utf8_byte_size(v_self_2590_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_nat_dec_eq(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_inc_ref(v_self_2590_);
return v_self_2590_;
}
else
{
lean_object* v___x_2594_; 
v___x_2594_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lake_CachePlatform_toString(v_self_2595_);
lean_dec_ref(v_self_2595_);
return v_res_2596_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2601_ = lean_string_utf8_byte_size(v_self_2600_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_nat_dec_eq(v___x_2601_, v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2604_){
_start:
{
uint8_t v_res_2605_; lean_object* v_r_2606_; 
v_res_2605_ = l_Lake_CacheToolchain_isNone(v_self_2604_);
lean_dec_ref(v_self_2604_);
v_r_2606_ = lean_box(v_res_2605_);
return v_r_2606_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2607_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lake_normalizeToolchain(v_s_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2609_){
_start:
{
lean_inc_ref(v_s_2609_);
return v_s_2609_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2610_);
lean_dec_ref(v_s_2610_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2612_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_string_length(v_self_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object* v_self_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lake_CacheToolchain_length(v_self_2614_);
lean_dec_ref(v_self_2614_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2617_ = lean_string_utf8_byte_size(v_self_2616_);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_nat_dec_eq(v___x_2617_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_inc_ref(v_self_2616_);
return v_self_2616_;
}
else
{
lean_object* v___x_2620_; 
v___x_2620_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lake_CacheToolchain_toString(v_self_2621_);
lean_dec_ref(v_self_2621_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2626_, lean_object* v_url_2627_, lean_object* v_path_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_path_2628_);
v___x_2632_ = l_Lake_download(v_url_2627_, v_path_2628_, v___x_2631_, v_a_2629_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2675_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___x_2632_, 0);
lean_dec(v_unused_2676_);
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2675_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2675_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lake_computeBinFileHash(v_path_2628_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; uint64_t v___x_2639_; uint8_t v___x_2640_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = lean_unbox_uint64(v_a_2638_);
v___x_2640_ = lean_uint64_dec_eq(v___x_2639_, v_hash_2626_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint64_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2641_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2628_);
v___x_2642_ = lean_string_append(v_path_2628_, v___x_2641_);
v___x_2643_ = lean_unbox_uint64(v_a_2638_);
lean_dec(v_a_2638_);
v___x_2644_ = l_Lake_Hash_hex(v___x_2643_);
v___x_2645_ = lean_string_append(v___x_2642_, v___x_2644_);
lean_dec_ref(v___x_2644_);
v___x_2646_ = 3;
v___x_2647_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*1, v___x_2646_);
lean_inc(v_a_2633_);
v___x_2648_ = lean_array_push(v_a_2633_, v___x_2647_);
v___x_2649_ = lean_io_remove_file(v_path_2628_);
lean_dec_ref(v_path_2628_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_dec_ref(v___x_2649_);
v___x_2650_ = lean_array_get_size(v_a_2633_);
lean_dec(v_a_2633_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 1, v___x_2648_);
lean_ctor_set(v___x_2635_, 0, v___x_2650_);
v___x_2652_ = v___x_2635_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2648_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
lean_dec(v_a_2633_);
v_a_2654_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v___x_2649_);
v___x_2655_ = lean_io_error_to_string(v_a_2654_);
v___x_2656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*1, v___x_2646_);
v___x_2657_ = lean_array_get_size(v___x_2648_);
v___x_2658_ = lean_array_push(v___x_2648_, v___x_2656_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 1, v___x_2658_);
lean_ctor_set(v___x_2635_, 0, v___x_2657_);
v___x_2660_ = v___x_2635_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
lean_dec(v_a_2638_);
lean_dec_ref(v_path_2628_);
v___x_2662_ = lean_box(0);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2662_);
v___x_2664_ = v___x_2635_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_a_2633_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_dec_ref(v_path_2628_);
v_a_2666_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2666_);
lean_dec_ref(v___x_2637_);
v___x_2667_ = lean_io_error_to_string(v_a_2666_);
v___x_2668_ = 3;
v___x_2669_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set_uint8(v___x_2669_, sizeof(void*)*1, v___x_2668_);
v___x_2670_ = lean_array_get_size(v_a_2633_);
v___x_2671_ = lean_array_push(v_a_2633_, v___x_2669_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 1, v___x_2671_);
lean_ctor_set(v___x_2635_, 0, v___x_2670_);
v___x_2673_ = v___x_2635_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_dec_ref(v_path_2628_);
return v___x_2632_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2677_, lean_object* v_url_2678_, lean_object* v_path_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
uint64_t v_hash_boxed_2682_; lean_object* v_res_2683_; 
v_hash_boxed_2682_ = lean_unbox_uint64(v_hash_2677_);
lean_dec_ref(v_hash_2677_);
v_res_2683_ = l_Lake_downloadArtifactCore(v_hash_boxed_2682_, v_url_2678_, v_path_2679_, v_a_2680_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2686_){
_start:
{
if (lean_obj_tag(v_x_2686_) == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_Json_getNat_x3f(v_x_2686_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2705_; 
v_a_2697_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2699_ = v___x_2688_;
v_isShared_2700_ = v_isSharedCheck_2705_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2688_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2705_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_a_2697_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2701_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2728_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2729_ = lean_unsigned_to_nat(14u);
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2729_);
v___x_2731_ = lean_array_push(v___x_2730_, v___x_2728_);
return v___x_2731_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2733_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2734_ = lean_array_push(v___x_2733_, v___x_2732_);
return v___x_2734_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2736_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2737_ = lean_array_push(v___x_2736_, v___x_2735_);
return v___x_2737_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2739_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2740_ = lean_array_push(v___x_2739_, v___x_2738_);
return v___x_2740_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2741_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2742_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2743_ = lean_array_push(v___x_2742_, v___x_2741_);
return v___x_2743_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2745_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2746_ = lean_array_push(v___x_2745_, v___x_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2750_, lean_object* v_contentType_2751_, lean_object* v_url_2752_, lean_object* v_key_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___y_2757_; lean_object* v_a_2758_; lean_object* v_stderr_2771_; lean_object* v___y_2780_; lean_object* v___y_2783_; lean_object* v_a_2784_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v_stderr_2823_; lean_object* v_a_2824_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2838_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2839_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2840_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2841_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2842_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2843_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2844_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2845_ = lean_string_append(v___x_2844_, v_contentType_2751_);
v___x_2846_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2847_ = lean_array_push(v___x_2846_, v_key_2753_);
v___x_2848_ = lean_array_push(v___x_2847_, v___x_2840_);
v___x_2849_ = lean_array_push(v___x_2848_, v___x_2841_);
v___x_2850_ = lean_array_push(v___x_2849_, v___x_2842_);
v___x_2851_ = lean_array_push(v___x_2850_, v_file_2750_);
v___x_2852_ = lean_array_push(v___x_2851_, v_url_2752_);
v___x_2853_ = lean_array_push(v___x_2852_, v___x_2843_);
v___x_2854_ = lean_array_push(v___x_2853_, v___x_2845_);
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2858_ = 1;
v___x_2859_ = 0;
v___x_2860_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2860_, 0, v___x_2838_);
lean_ctor_set(v___x_2860_, 1, v___x_2839_);
lean_ctor_set(v___x_2860_, 2, v___x_2854_);
lean_ctor_set(v___x_2860_, 3, v___x_2855_);
lean_ctor_set(v___x_2860_, 4, v___x_2857_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*5, v___x_2858_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*5 + 1, v___x_2859_);
v___x_2861_ = l_Lake_captureProc_x27(v___x_2860_, v___x_2857_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_a_2863_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
v_a_2863_ = lean_ctor_get(v___x_2861_, 1);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2861_);
v___x_2877_ = lean_array_get_size(v_a_2863_);
v___x_2878_ = lean_nat_dec_lt(v___x_2856_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_dec(v_a_2863_);
goto v___jp_2864_;
}
else
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_nat_dec_le(v___x_2877_, v___x_2877_);
if (v___x_2880_ == 0)
{
if (v___x_2878_ == 0)
{
lean_dec(v_a_2863_);
goto v___jp_2864_;
}
else
{
size_t v___x_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = ((size_t)0ULL);
v___x_2882_ = lean_usize_of_nat(v___x_2877_);
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2863_, v___x_2881_, v___x_2882_, v___x_2879_, v_a_2754_);
lean_dec(v_a_2863_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_dec_ref(v___x_2883_);
goto v___jp_2864_;
}
else
{
lean_dec(v_a_2862_);
return v___x_2883_;
}
}
}
else
{
size_t v___x_2884_; size_t v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = lean_usize_of_nat(v___x_2877_);
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2863_, v___x_2884_, v___x_2885_, v___x_2879_, v_a_2754_);
lean_dec(v_a_2863_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_dec_ref(v___x_2886_);
goto v___jp_2864_;
}
else
{
lean_dec(v_a_2862_);
return v___x_2886_;
}
}
}
v___jp_2864_:
{
lean_object* v_stderr_2865_; lean_object* v___x_2866_; 
v_stderr_2865_ = lean_ctor_get(v_a_2862_, 1);
lean_inc_ref(v_stderr_2865_);
v___x_2866_ = l_Lean_Json_parse(v_stderr_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
lean_inc_ref(v_stderr_2865_);
lean_dec(v_a_2862_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v_stderr_2823_ = v_stderr_2865_;
v_a_2824_ = v_a_2867_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2869_; 
v_a_2868_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2866_);
v___x_2869_ = l_Lean_Json_getObj_x3f(v_a_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
lean_inc_ref(v_stderr_2865_);
lean_dec(v_a_2862_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v_stderr_2823_ = v_stderr_2865_;
v_a_2824_ = v_a_2870_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_a_2871_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2869_);
v___x_2872_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2873_ = l_Lake_JsonObject_getJson_x3f(v_a_2871_, v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_inc_ref(v_stderr_2865_);
lean_dec(v_a_2871_);
lean_dec(v_a_2862_);
v_stderr_2771_ = v_stderr_2865_;
goto v___jp_2770_;
}
else
{
lean_object* v_val_2874_; lean_object* v___x_2875_; 
v_val_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_val_2874_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref(v___x_2875_);
v___y_2811_ = v_a_2871_;
v___y_2812_ = v_a_2862_;
goto v___jp_2810_;
}
else
{
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref(v___x_2875_);
v___y_2811_ = v_a_2871_;
v___y_2812_ = v_a_2862_;
goto v___jp_2810_;
}
else
{
lean_object* v_a_2876_; 
lean_dec(v_a_2871_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___y_2783_ = v_a_2862_;
v_a_2784_ = v_a_2876_;
goto v___jp_2782_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v_a_2887_ = lean_ctor_get(v___x_2861_, 1);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2861_);
v___x_2888_ = lean_array_get_size(v_a_2887_);
v___x_2889_ = lean_nat_dec_lt(v___x_2856_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v_a_2887_);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2892_ = lean_box(0);
v___x_2893_ = lean_nat_dec_le(v___x_2888_, v___x_2888_);
if (v___x_2893_ == 0)
{
if (v___x_2889_ == 0)
{
lean_dec(v_a_2887_);
goto v___jp_2835_;
}
else
{
size_t v___x_2894_; size_t v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = ((size_t)0ULL);
v___x_2895_ = lean_usize_of_nat(v___x_2888_);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2887_, v___x_2894_, v___x_2895_, v___x_2892_, v_a_2754_);
lean_dec(v_a_2887_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_dec_ref(v___x_2896_);
goto v___jp_2835_;
}
else
{
return v___x_2896_;
}
}
}
else
{
size_t v___x_2897_; size_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = lean_usize_of_nat(v___x_2888_);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2887_, v___x_2897_, v___x_2898_, v___x_2892_, v_a_2754_);
lean_dec(v_a_2887_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref(v___x_2899_);
goto v___jp_2835_;
}
else
{
return v___x_2899_;
}
}
}
}
v___jp_2756_:
{
lean_object* v_stderr_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_stderr_2759_ = lean_ctor_get(v___y_2757_, 1);
lean_inc_ref(v_stderr_2759_);
lean_dec_ref(v___y_2757_);
v___x_2760_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2761_ = lean_string_append(v___x_2760_, v_a_2758_);
lean_dec_ref(v_a_2758_);
v___x_2762_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2763_ = lean_string_append(v___x_2761_, v___x_2762_);
v___x_2764_ = lean_string_append(v___x_2763_, v_stderr_2759_);
lean_dec_ref(v_stderr_2759_);
v___x_2765_ = 3;
v___x_2766_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*1, v___x_2765_);
lean_inc_ref(v_a_2754_);
v___x_2767_ = lean_apply_2(v_a_2754_, v___x_2766_, lean_box(0));
v___x_2768_ = lean_box(0);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
v___jp_2770_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2772_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2773_ = lean_string_append(v___x_2772_, v_stderr_2771_);
lean_dec_ref(v_stderr_2771_);
v___x_2774_ = 3;
v___x_2775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*1, v___x_2774_);
lean_inc_ref(v_a_2754_);
v___x_2776_ = lean_apply_2(v_a_2754_, v___x_2775_, lean_box(0));
v___x_2777_ = lean_box(0);
v___x_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
v___jp_2779_:
{
lean_object* v_stderr_2781_; 
v_stderr_2781_ = lean_ctor_get(v___y_2780_, 1);
lean_inc_ref(v_stderr_2781_);
lean_dec_ref(v___y_2780_);
v_stderr_2771_ = v_stderr_2781_;
goto v___jp_2770_;
}
v___jp_2782_:
{
if (lean_obj_tag(v_a_2784_) == 0)
{
v___y_2780_ = v___y_2783_;
goto v___jp_2779_;
}
else
{
lean_object* v_val_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2809_; 
v_val_2785_ = lean_ctor_get(v_a_2784_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_a_2784_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2787_ = v_a_2784_;
v_isShared_2788_ = v_isSharedCheck_2809_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_val_2785_);
lean_dec(v_a_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2809_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(200u);
v___x_2790_ = lean_nat_dec_eq(v_val_2785_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v_stdout_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2803_; 
v_stdout_2791_ = lean_ctor_get(v___y_2783_, 0);
lean_inc_ref(v_stdout_2791_);
lean_dec_ref(v___y_2783_);
v___x_2792_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2793_ = l_Nat_reprFast(v_val_2785_);
v___x_2794_ = lean_string_append(v___x_2792_, v___x_2793_);
lean_dec_ref(v___x_2793_);
v___x_2795_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2796_ = lean_string_append(v___x_2794_, v___x_2795_);
v___x_2797_ = lean_string_append(v___x_2796_, v_stdout_2791_);
lean_dec_ref(v_stdout_2791_);
v___x_2798_ = 3;
v___x_2799_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*1, v___x_2798_);
lean_inc_ref(v_a_2754_);
v___x_2800_ = lean_apply_2(v_a_2754_, v___x_2799_, lean_box(0));
v___x_2801_ = lean_box(0);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2801_);
v___x_2803_ = v___x_2787_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_dec(v_val_2785_);
lean_dec_ref(v___y_2783_);
v___x_2805_ = lean_box(0);
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2805_);
v___x_2807_ = v___x_2787_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
v___jp_2810_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2814_ = l_Lake_JsonObject_getJson_x3f(v___y_2811_, v___x_2813_);
lean_dec(v___y_2811_);
if (lean_obj_tag(v___x_2814_) == 0)
{
v___y_2780_ = v___y_2812_;
goto v___jp_2779_;
}
else
{
lean_object* v_val_2815_; lean_object* v___x_2816_; 
v_val_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_val_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2819_ = lean_string_append(v___x_2818_, v_a_2817_);
lean_dec(v_a_2817_);
v___y_2757_ = v___y_2812_;
v_a_2758_ = v___x_2819_;
goto v___jp_2756_;
}
else
{
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2820_; 
v_a_2820_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2816_);
v___y_2757_ = v___y_2812_;
v_a_2758_ = v_a_2820_;
goto v___jp_2756_;
}
else
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2816_);
v___y_2783_ = v___y_2812_;
v_a_2784_ = v_a_2821_;
goto v___jp_2782_;
}
}
}
}
v___jp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2825_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2826_ = lean_string_append(v___x_2825_, v_a_2824_);
lean_dec_ref(v_a_2824_);
v___x_2827_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
v___x_2829_ = lean_string_append(v___x_2828_, v_stderr_2823_);
lean_dec_ref(v_stderr_2823_);
v___x_2830_ = 3;
v___x_2831_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*1, v___x_2830_);
lean_inc_ref(v_a_2754_);
v___x_2832_ = lean_apply_2(v_a_2754_, v___x_2831_, lean_box(0));
v___x_2833_ = lean_box(0);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
v___jp_2835_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2900_, lean_object* v_contentType_2901_, lean_object* v_url_2902_, lean_object* v_key_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2900_, v_contentType_2901_, v_url_2902_, v_key_2903_, v_a_2904_);
lean_dec_ref(v_a_2904_);
lean_dec_ref(v_contentType_2901_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2907_){
_start:
{
lean_object* v_name_x3f_2908_; 
v_name_x3f_2908_ = lean_ctor_get(v_service_2907_, 0);
lean_inc(v_name_x3f_2908_);
return v_name_x3f_2908_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lake_CacheService_name_x3f(v_service_2909_);
lean_dec_ref(v_service_2909_);
return v_res_2910_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2911_){
_start:
{
uint8_t v_isReservoir_2912_; 
v_isReservoir_2912_ = lean_ctor_get_uint8(v_service_2911_, sizeof(void*)*5);
return v_isReservoir_2912_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2913_){
_start:
{
uint8_t v_res_2914_; lean_object* v_r_2915_; 
v_res_2914_ = l_Lake_CacheService_isReservoir(v_service_2913_);
lean_dec_ref(v_service_2913_);
v_r_2915_ = lean_box(v_res_2914_);
return v_r_2915_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2916_, lean_object* v_name_x3f_2917_){
_start:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2919_ = 1;
v___x_2920_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2920_, 0, v_name_x3f_2917_);
lean_ctor_set(v___x_2920_, 1, v___x_2918_);
lean_ctor_set(v___x_2920_, 2, v___x_2918_);
lean_ctor_set(v___x_2920_, 3, v___x_2918_);
lean_ctor_set(v___x_2920_, 4, v_apiEndpoint_2916_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*5, v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2921_, lean_object* v_artifactEndpoint_2922_, lean_object* v_revisionEndpoint_2923_){
_start:
{
lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = lean_box(0);
v___x_2925_ = 0;
v___x_2926_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2927_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2927_, 0, v___x_2924_);
lean_ctor_set(v___x_2927_, 1, v_key_2921_);
lean_ctor_set(v___x_2927_, 2, v_artifactEndpoint_2922_);
lean_ctor_set(v___x_2927_, 3, v_revisionEndpoint_2923_);
lean_ctor_set(v___x_2927_, 4, v___x_2926_);
lean_ctor_set_uint8(v___x_2927_, sizeof(void*)*5, v___x_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2928_, lean_object* v_revisionEndpoint_2929_, lean_object* v_name_x3f_2930_){
_start:
{
lean_object* v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2932_ = 0;
v___x_2933_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2933_, 0, v_name_x3f_2930_);
lean_ctor_set(v___x_2933_, 1, v___x_2931_);
lean_ctor_set(v___x_2933_, 2, v_artifactEndpoint_2928_);
lean_ctor_set(v___x_2933_, 3, v_revisionEndpoint_2929_);
lean_ctor_set(v___x_2933_, 4, v___x_2931_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*5, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2934_, lean_object* v_name_x3f_2935_){
_start:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2937_ = 0;
v___x_2938_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2938_, 0, v_name_x3f_2935_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
lean_ctor_set(v___x_2938_, 2, v_artifactEndpoint_2934_);
lean_ctor_set(v___x_2938_, 3, v___x_2936_);
lean_ctor_set(v___x_2938_, 4, v___x_2936_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*5, v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2939_, lean_object* v_key_2940_){
_start:
{
lean_object* v_name_x3f_2941_; lean_object* v_artifactEndpoint_2942_; lean_object* v_revisionEndpoint_2943_; uint8_t v_isReservoir_2944_; lean_object* v_apiEndpoint_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_name_x3f_2941_ = lean_ctor_get(v_service_2939_, 0);
v_artifactEndpoint_2942_ = lean_ctor_get(v_service_2939_, 2);
v_revisionEndpoint_2943_ = lean_ctor_get(v_service_2939_, 3);
v_isReservoir_2944_ = lean_ctor_get_uint8(v_service_2939_, sizeof(void*)*5);
v_apiEndpoint_2945_ = lean_ctor_get(v_service_2939_, 4);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_service_2939_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_service_2939_, 1);
lean_dec(v_unused_2953_);
v___x_2947_ = v_service_2939_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_apiEndpoint_2945_);
lean_inc(v_revisionEndpoint_2943_);
lean_inc(v_artifactEndpoint_2942_);
lean_inc(v_name_x3f_2941_);
lean_dec(v_service_2939_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v_key_2940_);
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_name_x3f_2941_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_key_2940_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v_artifactEndpoint_2942_);
lean_ctor_set(v_reuseFailAlloc_2951_, 3, v_revisionEndpoint_2943_);
lean_ctor_set(v_reuseFailAlloc_2951_, 4, v_apiEndpoint_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_2951_, sizeof(void*)*5, v_isReservoir_2944_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2960_);
lean_dec_ref(v_s_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2962_, lean_object* v___x_2963_, lean_object* v___x_2964_, lean_object* v_a_2965_, lean_object* v_b_2966_){
_start:
{
if (lean_obj_tag(v_a_2965_) == 0)
{
lean_object* v_currPos_2967_; lean_object* v_searcher_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3002_; 
v_currPos_2967_ = lean_ctor_get(v_a_2965_, 0);
v_searcher_2968_ = lean_ctor_get(v_a_2965_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_a_2965_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2970_ = v_a_2965_;
v_isShared_2971_ = v_isSharedCheck_3002_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_searcher_2968_);
lean_inc(v_currPos_2967_);
lean_dec(v_a_2965_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3002_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v_startInclusive_2972_; lean_object* v_endExclusive_2973_; uint32_t v___x_2974_; lean_object* v_it_2976_; lean_object* v_startInclusive_2977_; lean_object* v_endExclusive_2978_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_startInclusive_2972_ = lean_ctor_get(v___x_2963_, 1);
v_endExclusive_2973_ = lean_ctor_get(v___x_2963_, 2);
v___x_2974_ = 47;
v___x_2983_ = lean_nat_sub(v_endExclusive_2973_, v_startInclusive_2972_);
v___x_2984_ = lean_nat_dec_eq(v_searcher_2968_, v___x_2983_);
lean_dec(v___x_2983_);
if (v___x_2984_ == 0)
{
uint32_t v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_string_utf8_get_fast(v_scope_2962_, v_searcher_2968_);
v___x_2986_ = lean_uint32_dec_eq(v___x_2985_, v___x_2974_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = lean_string_utf8_next_fast(v_scope_2962_, v_searcher_2968_);
lean_dec(v_searcher_2968_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2987_);
v___x_2989_ = v___x_2970_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_currPos_2967_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
v_a_2965_ = v___x_2989_;
goto _start;
}
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_slice_2995_; lean_object* v_nextIt_2997_; 
v___x_2992_ = lean_string_utf8_next_fast(v_scope_2962_, v_searcher_2968_);
v___x_2993_ = lean_nat_sub(v___x_2992_, v_searcher_2968_);
v___x_2994_ = lean_nat_add(v_searcher_2968_, v___x_2993_);
lean_dec(v___x_2993_);
v_slice_2995_ = l_String_Slice_subslice_x21(v___x_2963_, v_currPos_2967_, v_searcher_2968_);
lean_inc(v___x_2994_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2994_);
lean_ctor_set(v___x_2970_, 0, v___x_2994_);
v_nextIt_2997_ = v___x_2970_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2994_);
v_nextIt_2997_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v_startInclusive_2998_; lean_object* v_endExclusive_2999_; 
v_startInclusive_2998_ = lean_ctor_get(v_slice_2995_, 0);
lean_inc(v_startInclusive_2998_);
v_endExclusive_2999_ = lean_ctor_get(v_slice_2995_, 1);
lean_inc(v_endExclusive_2999_);
lean_dec_ref(v_slice_2995_);
v_it_2976_ = v_nextIt_2997_;
v_startInclusive_2977_ = v_startInclusive_2998_;
v_endExclusive_2978_ = v_endExclusive_2999_;
goto v___jp_2975_;
}
}
}
else
{
lean_object* v___x_3001_; 
lean_del_object(v___x_2970_);
lean_dec(v_searcher_2968_);
v___x_3001_ = lean_box(1);
lean_inc(v___x_2964_);
v_it_2976_ = v___x_3001_;
v_startInclusive_2977_ = v_currPos_2967_;
v_endExclusive_2978_ = v___x_2964_;
goto v___jp_2975_;
}
v___jp_2975_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_string_utf8_extract(v_scope_2962_, v_startInclusive_2977_, v_endExclusive_2978_);
lean_dec(v_endExclusive_2978_);
lean_dec(v_startInclusive_2977_);
v___x_2980_ = lean_string_push(v_b_2966_, v___x_2974_);
v___x_2981_ = l_Lake_uriEncode(v___x_2979_, v___x_2980_);
v_a_2965_ = v_it_2976_;
v_b_2966_ = v___x_2981_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2964_);
return v_b_2966_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_3003_, lean_object* v___x_3004_, lean_object* v___x_3005_, lean_object* v_a_3006_, lean_object* v_b_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_3003_, v___x_3004_, v___x_3005_, v_a_3006_, v_b_3007_);
lean_dec_ref(v___x_3004_);
lean_dec_ref(v_scope_3003_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_3009_, lean_object* v_scope_3010_){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_string_utf8_byte_size(v_scope_3010_);
lean_inc_ref(v_scope_3010_);
v___x_3013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3013_, 0, v_scope_3010_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
v___x_3014_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_3013_);
v___x_3015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_3010_, v___x_3013_, v___x_3012_, v___x_3014_, v_endpoint_3009_);
lean_dec_ref(v___x_3013_);
lean_dec_ref(v_scope_3010_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_3016_, lean_object* v___x_3017_, lean_object* v___x_3018_, lean_object* v_inst_3019_, lean_object* v_R_3020_, lean_object* v_a_3021_, lean_object* v_b_3022_, lean_object* v_c_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_3016_, v___x_3017_, v___x_3018_, v_a_3021_, v_b_3022_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_3025_, lean_object* v___x_3026_, lean_object* v___x_3027_, lean_object* v_inst_3028_, lean_object* v_R_3029_, lean_object* v_a_3030_, lean_object* v_b_3031_, lean_object* v_c_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_3025_, v___x_3026_, v___x_3027_, v_inst_3028_, v_R_3029_, v_a_3030_, v_b_3031_, v_c_3032_);
lean_dec_ref(v___x_3026_);
lean_dec_ref(v_scope_3025_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_3034_, lean_object* v_scope_3035_){
_start:
{
lean_object* v_artifactEndpoint_3036_; lean_object* v___x_3037_; 
v_artifactEndpoint_3036_ = lean_ctor_get(v_service_3034_, 2);
lean_inc_ref(v_artifactEndpoint_3036_);
lean_dec_ref(v_service_3034_);
v___x_3037_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_3036_, v_scope_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_3040_, lean_object* v_service_3041_, lean_object* v_scope_3042_){
_start:
{
lean_object* v___y_3044_; lean_object* v_s_3051_; lean_object* v___x_3052_; 
v_s_3051_ = lean_ctor_get(v_scope_3042_, 0);
lean_inc_ref(v_s_3051_);
lean_dec_ref(v_scope_3042_);
v___x_3052_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_3041_, v_s_3051_);
v___y_3044_ = v___x_3052_;
goto v___jp_3043_;
v___jp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3045_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_3046_ = lean_string_append(v___y_3044_, v___x_3045_);
v___x_3047_ = l_Lake_Hash_hex(v_contentHash_3040_);
v___x_3048_ = lean_string_append(v___x_3046_, v___x_3047_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_3050_ = lean_string_append(v___x_3048_, v___x_3049_);
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_3053_, lean_object* v_service_3054_, lean_object* v_scope_3055_){
_start:
{
uint64_t v_contentHash_boxed_3056_; lean_object* v_res_3057_; 
v_contentHash_boxed_3056_ = lean_unbox_uint64(v_contentHash_3053_);
lean_dec_ref(v_contentHash_3053_);
v_res_3057_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_3056_, v_service_3054_, v_scope_3055_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_3061_, lean_object* v_service_3062_, lean_object* v_scope_3063_){
_start:
{
lean_object* v___y_3065_; uint8_t v_isReservoir_3072_; 
v_isReservoir_3072_ = lean_ctor_get_uint8(v_service_3062_, sizeof(void*)*5);
if (v_isReservoir_3072_ == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3061_, v_service_3062_, v_scope_3063_);
return v___x_3073_;
}
else
{
if (lean_obj_tag(v_scope_3063_) == 0)
{
lean_object* v_apiEndpoint_3074_; lean_object* v_s_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_apiEndpoint_3074_ = lean_ctor_get(v_service_3062_, 4);
lean_inc_ref(v_apiEndpoint_3074_);
lean_dec_ref(v_service_3062_);
v_s_3075_ = lean_ctor_get(v_scope_3063_, 0);
lean_inc_ref(v_s_3075_);
lean_dec_ref(v_scope_3063_);
v___x_3076_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_3077_ = lean_string_append(v_apiEndpoint_3074_, v___x_3076_);
v___x_3078_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3077_, v_s_3075_);
v___y_3065_ = v___x_3078_;
goto v___jp_3064_;
}
else
{
lean_object* v_apiEndpoint_3079_; lean_object* v_s_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_apiEndpoint_3079_ = lean_ctor_get(v_service_3062_, 4);
lean_inc_ref(v_apiEndpoint_3079_);
lean_dec_ref(v_service_3062_);
v_s_3080_ = lean_ctor_get(v_scope_3063_, 0);
lean_inc_ref(v_s_3080_);
lean_dec_ref(v_scope_3063_);
v___x_3081_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3082_ = lean_string_append(v_apiEndpoint_3079_, v___x_3081_);
v___x_3083_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3082_, v_s_3080_);
v___y_3065_ = v___x_3083_;
goto v___jp_3064_;
}
}
v___jp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3066_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_3067_ = lean_string_append(v___y_3065_, v___x_3066_);
v___x_3068_ = l_Lake_Hash_hex(v_contentHash_3061_);
v___x_3069_ = lean_string_append(v___x_3067_, v___x_3068_);
lean_dec_ref(v___x_3068_);
v___x_3070_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_3071_ = lean_string_append(v___x_3069_, v___x_3070_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_3084_, lean_object* v_service_3085_, lean_object* v_scope_3086_){
_start:
{
uint64_t v_contentHash_boxed_3087_; lean_object* v_res_3088_; 
v_contentHash_boxed_3087_ = lean_unbox_uint64(v_contentHash_3084_);
lean_dec_ref(v_contentHash_3084_);
v_res_3088_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_3087_, v_service_3085_, v_scope_3086_);
return v_res_3088_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3093_ = lean_array_get_size(v___x_3092_);
return v___x_3093_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3094_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_nat_dec_lt(v___x_3095_, v___x_3094_);
return v___x_3096_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3098_ = lean_nat_dec_le(v___x_3097_, v___x_3097_);
return v___x_3098_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_3099_; size_t v___x_3100_; 
v___x_3099_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3100_ = lean_usize_of_nat(v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_3101_, lean_object* v_cache_3102_, lean_object* v_service_3103_, lean_object* v_scope_3104_, uint8_t v_force_3105_, lean_object* v_a_3106_){
_start:
{
uint64_t v_hash_3111_; lean_object* v_ext_3112_; lean_object* v_url_3113_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3177_; lean_object* v___y_3180_; uint8_t v_a_3181_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___y_3187_; lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_hash_3111_ = lean_ctor_get_uint64(v_descr_3101_, sizeof(void*)*1);
v_ext_3112_ = lean_ctor_get(v_descr_3101_, 0);
lean_inc_ref(v_scope_3104_);
v_url_3113_ = l_Lake_CacheService_artifactUrl(v_hash_3111_, v_service_3103_, v_scope_3104_);
v___x_3184_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3185_ = l_System_FilePath_join(v_cache_3102_, v___x_3184_);
v___x_3200_ = lean_string_utf8_byte_size(v_ext_3112_);
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = lean_nat_dec_eq(v___x_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3203_ = l_Lake_Hash_hex(v_hash_3111_);
v___x_3204_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3205_ = lean_string_append(v___x_3203_, v___x_3204_);
v___x_3206_ = lean_string_append(v___x_3205_, v_ext_3112_);
v___y_3187_ = v___x_3206_;
goto v___jp_3186_;
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lake_Hash_hex(v_hash_3111_);
v___y_3187_ = v___x_3207_;
goto v___jp_3186_;
}
v___jp_3108_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = lean_box(0);
v___x_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
return v___x_3110_;
}
v___jp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3117_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3118_ = lean_string_append(v___y_3116_, v___x_3117_);
v___x_3119_ = l_Lake_Hash_hex(v_hash_3111_);
v___x_3120_ = lean_string_append(v___x_3118_, v___x_3119_);
lean_dec_ref(v___x_3119_);
v___x_3121_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3122_ = lean_string_append(v___x_3120_, v___x_3121_);
v___x_3123_ = lean_string_append(v___x_3122_, v___y_3115_);
v___x_3124_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3125_ = lean_string_append(v___x_3123_, v___x_3124_);
v___x_3126_ = lean_string_append(v___x_3125_, v_url_3113_);
v___x_3127_ = 1;
v___x_3128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3128_, 0, v___x_3126_);
lean_ctor_set_uint8(v___x_3128_, sizeof(void*)*1, v___x_3127_);
lean_inc_ref(v_a_3106_);
v___x_3129_ = lean_apply_2(v_a_3106_, v___x_3128_, lean_box(0));
v___x_3130_ = lean_unsigned_to_nat(0u);
v___x_3131_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3132_ = l_Lake_downloadArtifactCore(v_hash_3111_, v_url_3113_, v___y_3115_, v___x_3131_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v_a_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
v_a_3134_ = lean_ctor_get(v___x_3132_, 1);
lean_inc(v_a_3134_);
lean_dec_ref(v___x_3132_);
v___x_3135_ = lean_array_get_size(v_a_3134_);
v___x_3136_ = lean_nat_dec_lt(v___x_3130_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
lean_dec(v_a_3134_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_a_3133_);
return v___x_3137_;
}
else
{
lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = lean_nat_dec_le(v___x_3135_, v___x_3135_);
if (v___x_3139_ == 0)
{
if (v___x_3136_ == 0)
{
lean_object* v___x_3140_; 
lean_dec(v_a_3134_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_a_3133_);
return v___x_3140_;
}
else
{
size_t v___x_3141_; size_t v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = ((size_t)0ULL);
v___x_3142_ = lean_usize_of_nat(v___x_3135_);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3134_, v___x_3141_, v___x_3142_, v___x_3138_, v_a_3106_);
lean_dec(v_a_3134_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3143_, 0);
lean_dec(v_unused_3151_);
v___x_3145_ = v___x_3143_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_dec(v___x_3143_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_a_3133_);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3133_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
else
{
lean_dec(v_a_3133_);
return v___x_3143_;
}
}
}
else
{
size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = lean_usize_of_nat(v___x_3135_);
v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3134_, v___x_3152_, v___x_3153_, v___x_3138_, v_a_3106_);
lean_dec(v_a_3134_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___x_3154_, 0);
lean_dec(v_unused_3162_);
v___x_3156_ = v___x_3154_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_dec(v___x_3154_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v_a_3133_);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3133_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
lean_dec(v_a_3133_);
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3132_, 1);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3132_);
v___x_3164_ = lean_array_get_size(v_a_3163_);
v___x_3165_ = lean_nat_dec_lt(v___x_3130_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec(v_a_3163_);
v___x_3166_ = lean_box(0);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
else
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = lean_box(0);
v___x_3169_ = lean_nat_dec_le(v___x_3164_, v___x_3164_);
if (v___x_3169_ == 0)
{
if (v___x_3165_ == 0)
{
lean_dec(v_a_3163_);
goto v___jp_3108_;
}
else
{
size_t v___x_3170_; size_t v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = lean_usize_of_nat(v___x_3164_);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3163_, v___x_3170_, v___x_3171_, v___x_3168_, v_a_3106_);
lean_dec(v_a_3163_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_dec_ref(v___x_3172_);
goto v___jp_3108_;
}
else
{
return v___x_3172_;
}
}
}
else
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = ((size_t)0ULL);
v___x_3174_ = lean_usize_of_nat(v___x_3164_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3163_, v___x_3173_, v___x_3174_, v___x_3168_, v_a_3106_);
lean_dec(v_a_3163_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_dec_ref(v___x_3175_);
goto v___jp_3108_;
}
else
{
return v___x_3175_;
}
}
}
}
}
v___jp_3176_:
{
lean_object* v_s_3178_; 
v_s_3178_ = lean_ctor_get(v_scope_3104_, 0);
lean_inc_ref(v_s_3178_);
lean_dec_ref(v_scope_3104_);
v___y_3115_ = v___y_3177_;
v___y_3116_ = v_s_3178_;
goto v___jp_3114_;
}
v___jp_3179_:
{
if (v_a_3181_ == 0)
{
v___y_3177_ = v___y_3180_;
goto v___jp_3176_;
}
else
{
if (v_force_3105_ == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref(v___y_3180_);
lean_dec_ref(v_url_3113_);
lean_dec_ref(v_scope_3104_);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
else
{
v___y_3177_ = v___y_3180_;
goto v___jp_3176_;
}
}
}
v___jp_3186_:
{
lean_object* v_path_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v_path_3188_ = l_System_FilePath_join(v___x_3185_, v___y_3187_);
v___x_3189_ = l_System_FilePath_pathExists(v_path_3188_);
v___x_3190_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3191_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3191_ == 0)
{
v___y_3180_ = v_path_3188_;
v_a_3181_ = v___x_3189_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = lean_box(0);
v___x_3193_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3193_ == 0)
{
if (v___x_3191_ == 0)
{
v___y_3180_ = v_path_3188_;
v_a_3181_ = v___x_3189_;
goto v___jp_3179_;
}
else
{
size_t v___x_3194_; size_t v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3190_, v___x_3194_, v___x_3195_, v___x_3192_, v_a_3106_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_dec_ref(v___x_3196_);
v___y_3180_ = v_path_3188_;
v_a_3181_ = v___x_3189_;
goto v___jp_3179_;
}
else
{
lean_dec_ref(v_path_3188_);
lean_dec_ref(v_url_3113_);
lean_dec_ref(v_scope_3104_);
return v___x_3196_;
}
}
}
else
{
size_t v___x_3197_; size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = ((size_t)0ULL);
v___x_3198_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3190_, v___x_3197_, v___x_3198_, v___x_3192_, v_a_3106_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_dec_ref(v___x_3199_);
v___y_3180_ = v_path_3188_;
v_a_3181_ = v___x_3189_;
goto v___jp_3179_;
}
else
{
lean_dec_ref(v_path_3188_);
lean_dec_ref(v_url_3113_);
lean_dec_ref(v_scope_3104_);
return v___x_3199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3208_, lean_object* v_cache_3209_, lean_object* v_service_3210_, lean_object* v_scope_3211_, lean_object* v_force_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
uint8_t v_force_boxed_3215_; lean_object* v_res_3216_; 
v_force_boxed_3215_ = lean_unbox(v_force_3212_);
v_res_3216_ = l_Lake_CacheService_downloadArtifact(v_descr_3208_, v_cache_3209_, v_service_3210_, v_scope_3211_, v_force_boxed_3215_, v_a_3213_);
lean_dec_ref(v_a_3213_);
lean_dec_ref(v_descr_3208_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3217_, lean_object* v_file_3218_, lean_object* v_contentType_3219_, lean_object* v_url_3220_, lean_object* v_key_3221_){
_start:
{
lean_object* v___y_3224_; lean_object* v_a_3225_; lean_object* v_stderr_3238_; lean_object* v___y_3247_; lean_object* v___y_3250_; lean_object* v_a_3251_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v_stderr_3290_; lean_object* v_a_3291_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3305_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3306_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3307_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3308_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3309_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3310_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3311_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3312_ = lean_string_append(v___x_3311_, v_contentType_3219_);
v___x_3313_ = lean_unsigned_to_nat(14u);
v___x_3314_ = lean_mk_empty_array_with_capacity(v___x_3313_);
lean_dec_ref(v___x_3314_);
v___x_3315_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3316_ = lean_array_push(v___x_3315_, v_key_3221_);
v___x_3317_ = lean_array_push(v___x_3316_, v___x_3307_);
v___x_3318_ = lean_array_push(v___x_3317_, v___x_3308_);
v___x_3319_ = lean_array_push(v___x_3318_, v___x_3309_);
v___x_3320_ = lean_array_push(v___x_3319_, v_file_3218_);
v___x_3321_ = lean_array_push(v___x_3320_, v_url_3220_);
v___x_3322_ = lean_array_push(v___x_3321_, v___x_3310_);
v___x_3323_ = lean_array_push(v___x_3322_, v___x_3312_);
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_unsigned_to_nat(0u);
v___x_3326_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3327_ = 1;
v___x_3328_ = 0;
v___x_3329_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3329_, 0, v___x_3305_);
lean_ctor_set(v___x_3329_, 1, v___x_3306_);
lean_ctor_set(v___x_3329_, 2, v___x_3323_);
lean_ctor_set(v___x_3329_, 3, v___x_3324_);
lean_ctor_set(v___x_3329_, 4, v___x_3326_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*5, v___x_3327_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*5 + 1, v___x_3328_);
v___x_3330_ = l_Lake_captureProc_x27(v___x_3329_, v___x_3326_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v_a_3332_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
v_a_3332_ = lean_ctor_get(v___x_3330_, 1);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3330_);
v___x_3346_ = lean_array_get_size(v_a_3332_);
v___x_3347_ = lean_nat_dec_lt(v___x_3325_, v___x_3346_);
if (v___x_3347_ == 0)
{
lean_dec(v_a_3332_);
goto v___jp_3333_;
}
else
{
lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_nat_dec_le(v___x_3346_, v___x_3346_);
if (v___x_3349_ == 0)
{
if (v___x_3347_ == 0)
{
lean_dec(v_a_3332_);
goto v___jp_3333_;
}
else
{
size_t v___x_3350_; size_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = lean_usize_of_nat(v___x_3346_);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3332_, v___x_3350_, v___x_3351_, v___x_3348_, v_a_3217_);
lean_dec(v_a_3332_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_dec_ref(v___x_3352_);
goto v___jp_3333_;
}
else
{
lean_dec(v_a_3331_);
return v___x_3352_;
}
}
}
else
{
size_t v___x_3353_; size_t v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = lean_usize_of_nat(v___x_3346_);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3332_, v___x_3353_, v___x_3354_, v___x_3348_, v_a_3217_);
lean_dec(v_a_3332_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_dec_ref(v___x_3355_);
goto v___jp_3333_;
}
else
{
lean_dec(v_a_3331_);
return v___x_3355_;
}
}
}
v___jp_3333_:
{
lean_object* v_stderr_3334_; lean_object* v___x_3335_; 
v_stderr_3334_ = lean_ctor_get(v_a_3331_, 1);
lean_inc_ref(v_stderr_3334_);
v___x_3335_ = l_Lean_Json_parse(v_stderr_3334_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; 
lean_inc_ref(v_stderr_3334_);
lean_dec(v_a_3331_);
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v_stderr_3290_ = v_stderr_3334_;
v_a_3291_ = v_a_3336_;
goto v___jp_3289_;
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3338_; 
v_a_3337_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3337_);
lean_dec_ref(v___x_3335_);
v___x_3338_ = l_Lean_Json_getObj_x3f(v_a_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; 
lean_inc_ref(v_stderr_3334_);
lean_dec(v_a_3331_);
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref(v___x_3338_);
v_stderr_3290_ = v_stderr_3334_;
v_a_3291_ = v_a_3339_;
goto v___jp_3289_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_a_3340_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___x_3338_);
v___x_3341_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3342_ = l_Lake_JsonObject_getJson_x3f(v_a_3340_, v___x_3341_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_inc_ref(v_stderr_3334_);
lean_dec(v_a_3340_);
lean_dec(v_a_3331_);
v_stderr_3238_ = v_stderr_3334_;
goto v___jp_3237_;
}
else
{
lean_object* v_val_3343_; lean_object* v___x_3344_; 
v_val_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref(v___x_3342_);
v___x_3344_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_dec_ref(v___x_3344_);
v___y_3278_ = v_a_3331_;
v___y_3279_ = v_a_3340_;
goto v___jp_3277_;
}
else
{
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_dec_ref(v___x_3344_);
v___y_3278_ = v_a_3331_;
v___y_3279_ = v_a_3340_;
goto v___jp_3277_;
}
else
{
lean_object* v_a_3345_; 
lean_dec(v_a_3340_);
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref(v___x_3344_);
v___y_3250_ = v_a_3331_;
v_a_3251_ = v_a_3345_;
goto v___jp_3249_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v_a_3356_ = lean_ctor_get(v___x_3330_, 1);
lean_inc(v_a_3356_);
lean_dec_ref(v___x_3330_);
v___x_3357_ = lean_array_get_size(v_a_3356_);
v___x_3358_ = lean_nat_dec_lt(v___x_3325_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v_a_3356_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
else
{
lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_nat_dec_le(v___x_3357_, v___x_3357_);
if (v___x_3362_ == 0)
{
if (v___x_3358_ == 0)
{
lean_dec(v_a_3356_);
goto v___jp_3302_;
}
else
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = lean_usize_of_nat(v___x_3357_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3356_, v___x_3363_, v___x_3364_, v___x_3361_, v_a_3217_);
lean_dec(v_a_3356_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_dec_ref(v___x_3365_);
goto v___jp_3302_;
}
else
{
return v___x_3365_;
}
}
}
else
{
size_t v___x_3366_; size_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = ((size_t)0ULL);
v___x_3367_ = lean_usize_of_nat(v___x_3357_);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3356_, v___x_3366_, v___x_3367_, v___x_3361_, v_a_3217_);
lean_dec(v_a_3356_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_dec_ref(v___x_3368_);
goto v___jp_3302_;
}
else
{
return v___x_3368_;
}
}
}
}
v___jp_3223_:
{
lean_object* v_stderr_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v_stderr_3226_ = lean_ctor_get(v___y_3224_, 1);
lean_inc_ref(v_stderr_3226_);
lean_dec_ref(v___y_3224_);
v___x_3227_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3228_ = lean_string_append(v___x_3227_, v_a_3225_);
lean_dec_ref(v_a_3225_);
v___x_3229_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3230_ = lean_string_append(v___x_3228_, v___x_3229_);
v___x_3231_ = lean_string_append(v___x_3230_, v_stderr_3226_);
lean_dec_ref(v_stderr_3226_);
v___x_3232_ = 3;
v___x_3233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1, v___x_3232_);
lean_inc_ref(v_a_3217_);
v___x_3234_ = lean_apply_2(v_a_3217_, v___x_3233_, lean_box(0));
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
v___jp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3239_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3240_ = lean_string_append(v___x_3239_, v_stderr_3238_);
lean_dec_ref(v_stderr_3238_);
v___x_3241_ = 3;
v___x_3242_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set_uint8(v___x_3242_, sizeof(void*)*1, v___x_3241_);
lean_inc_ref(v_a_3217_);
v___x_3243_ = lean_apply_2(v_a_3217_, v___x_3242_, lean_box(0));
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
return v___x_3245_;
}
v___jp_3246_:
{
lean_object* v_stderr_3248_; 
v_stderr_3248_ = lean_ctor_get(v___y_3247_, 1);
lean_inc_ref(v_stderr_3248_);
lean_dec_ref(v___y_3247_);
v_stderr_3238_ = v_stderr_3248_;
goto v___jp_3237_;
}
v___jp_3249_:
{
if (lean_obj_tag(v_a_3251_) == 0)
{
v___y_3247_ = v___y_3250_;
goto v___jp_3246_;
}
else
{
lean_object* v_val_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3276_; 
v_val_3252_ = lean_ctor_get(v_a_3251_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_a_3251_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3254_ = v_a_3251_;
v_isShared_3255_ = v_isSharedCheck_3276_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_val_3252_);
lean_dec(v_a_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3276_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = lean_unsigned_to_nat(200u);
v___x_3257_ = lean_nat_dec_eq(v_val_3252_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_object* v_stdout_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3270_; 
v_stdout_3258_ = lean_ctor_get(v___y_3250_, 0);
lean_inc_ref(v_stdout_3258_);
lean_dec_ref(v___y_3250_);
v___x_3259_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3260_ = l_Nat_reprFast(v_val_3252_);
v___x_3261_ = lean_string_append(v___x_3259_, v___x_3260_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3263_ = lean_string_append(v___x_3261_, v___x_3262_);
v___x_3264_ = lean_string_append(v___x_3263_, v_stdout_3258_);
lean_dec_ref(v_stdout_3258_);
v___x_3265_ = 3;
v___x_3266_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*1, v___x_3265_);
lean_inc_ref(v_a_3217_);
v___x_3267_ = lean_apply_2(v_a_3217_, v___x_3266_, lean_box(0));
v___x_3268_ = lean_box(0);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3268_);
v___x_3270_ = v___x_3254_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
lean_dec(v_val_3252_);
lean_dec_ref(v___y_3250_);
v___x_3272_ = lean_box(0);
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3272_);
v___x_3274_ = v___x_3254_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
v___jp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3281_ = l_Lake_JsonObject_getJson_x3f(v___y_3279_, v___x_3280_);
lean_dec(v___y_3279_);
if (lean_obj_tag(v___x_3281_) == 0)
{
v___y_3247_ = v___y_3278_;
goto v___jp_3246_;
}
else
{
lean_object* v_val_3282_; lean_object* v___x_3283_; 
v_val_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_val_3282_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3282_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref(v___x_3283_);
v___x_3285_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3286_ = lean_string_append(v___x_3285_, v_a_3284_);
lean_dec(v_a_3284_);
v___y_3224_ = v___y_3278_;
v_a_3225_ = v___x_3286_;
goto v___jp_3223_;
}
else
{
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3287_; 
v_a_3287_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3283_);
v___y_3224_ = v___y_3278_;
v_a_3225_ = v_a_3287_;
goto v___jp_3223_;
}
else
{
lean_object* v_a_3288_; 
v_a_3288_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___x_3283_);
v___y_3250_ = v___y_3278_;
v_a_3251_ = v_a_3288_;
goto v___jp_3249_;
}
}
}
}
v___jp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3292_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3293_ = lean_string_append(v___x_3292_, v_a_3291_);
lean_dec_ref(v_a_3291_);
v___x_3294_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3295_ = lean_string_append(v___x_3293_, v___x_3294_);
v___x_3296_ = lean_string_append(v___x_3295_, v_stderr_3290_);
lean_dec_ref(v_stderr_3290_);
v___x_3297_ = 3;
v___x_3298_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set_uint8(v___x_3298_, sizeof(void*)*1, v___x_3297_);
lean_inc_ref(v_a_3217_);
v___x_3299_ = lean_apply_2(v_a_3217_, v___x_3298_, lean_box(0));
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
return v___x_3301_;
}
v___jp_3302_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3369_, lean_object* v_file_3370_, lean_object* v_contentType_3371_, lean_object* v_url_3372_, lean_object* v_key_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3369_, v_file_3370_, v_contentType_3371_, v_url_3372_, v_key_3373_);
lean_dec_ref(v_contentType_3371_);
lean_dec_ref(v_a_3369_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3377_, lean_object* v_art_3378_, lean_object* v_service_3379_, lean_object* v_scope_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_url_3383_; lean_object* v___y_3385_; lean_object* v_s_3402_; 
lean_inc_ref(v_scope_3380_);
lean_inc_ref(v_service_3379_);
v_url_3383_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3377_, v_service_3379_, v_scope_3380_);
v_s_3402_ = lean_ctor_get(v_scope_3380_, 0);
lean_inc_ref(v_s_3402_);
lean_dec_ref(v_scope_3380_);
v___y_3385_ = v_s_3402_;
goto v___jp_3384_;
v___jp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v_key_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3386_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3387_ = lean_string_append(v___y_3385_, v___x_3386_);
v___x_3388_ = l_Lake_Hash_hex(v_contentHash_3377_);
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3391_ = lean_string_append(v___x_3389_, v___x_3390_);
v___x_3392_ = lean_string_append(v___x_3391_, v_art_3378_);
v___x_3393_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
v___x_3395_ = lean_string_append(v___x_3394_, v_url_3383_);
v___x_3396_ = 1;
v___x_3397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set_uint8(v___x_3397_, sizeof(void*)*1, v___x_3396_);
lean_inc_ref(v_a_3381_);
v___x_3398_ = lean_apply_2(v_a_3381_, v___x_3397_, lean_box(0));
v_key_3399_ = lean_ctor_get(v_service_3379_, 1);
lean_inc_ref(v_key_3399_);
lean_dec_ref(v_service_3379_);
v___x_3400_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3401_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3381_, v_art_3378_, v___x_3400_, v_url_3383_, v_key_3399_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3403_, lean_object* v_art_3404_, lean_object* v_service_3405_, lean_object* v_scope_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
uint64_t v_contentHash_boxed_3409_; lean_object* v_res_3410_; 
v_contentHash_boxed_3409_ = lean_unbox_uint64(v_contentHash_3403_);
lean_dec_ref(v_contentHash_3403_);
v_res_3410_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3409_, v_art_3404_, v_service_3405_, v_scope_3406_, v_a_3407_);
lean_dec_ref(v_a_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(uint8_t v_x_3411_){
_start:
{
if (v_x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_unsigned_to_nat(0u);
return v___x_3412_;
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_unsigned_to_nat(1u);
return v___x_3413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___boxed(lean_object* v_x_3414_){
_start:
{
uint8_t v_x_boxed_3415_; lean_object* v_res_3416_; 
v_x_boxed_3415_ = lean_unbox(v_x_3414_);
v_res_3416_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_boxed_3415_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(uint8_t v_x_3417_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx___boxed(lean_object* v_x_3419_){
_start:
{
uint8_t v_x_4__boxed_3420_; lean_object* v_res_3421_; 
v_x_4__boxed_3420_ = lean_unbox(v_x_3419_);
v_res_3421_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(v_x_4__boxed_3420_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object* v_k_3422_){
_start:
{
lean_inc(v_k_3422_);
return v_k_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object* v_k_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(v_k_3423_);
lean_dec(v_k_3423_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object* v_motive_3425_, lean_object* v_ctorIdx_3426_, uint8_t v_t_3427_, lean_object* v_h_3428_, lean_object* v_k_3429_){
_start:
{
lean_inc(v_k_3429_);
return v_k_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object* v_motive_3430_, lean_object* v_ctorIdx_3431_, lean_object* v_t_3432_, lean_object* v_h_3433_, lean_object* v_k_3434_){
_start:
{
uint8_t v_t_boxed_3435_; lean_object* v_res_3436_; 
v_t_boxed_3435_ = lean_unbox(v_t_3432_);
v_res_3436_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(v_motive_3430_, v_ctorIdx_3431_, v_t_boxed_3435_, v_h_3433_, v_k_3434_);
lean_dec(v_k_3434_);
lean_dec(v_ctorIdx_3431_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object* v_get_3437_){
_start:
{
lean_inc(v_get_3437_);
return v_get_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object* v_get_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(v_get_3438_);
lean_dec(v_get_3438_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object* v_motive_3440_, uint8_t v_t_3441_, lean_object* v_h_3442_, lean_object* v_get_3443_){
_start:
{
lean_inc(v_get_3443_);
return v_get_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object* v_motive_3444_, lean_object* v_t_3445_, lean_object* v_h_3446_, lean_object* v_get_3447_){
_start:
{
uint8_t v_t_boxed_3448_; lean_object* v_res_3449_; 
v_t_boxed_3448_ = lean_unbox(v_t_3445_);
v_res_3449_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(v_motive_3444_, v_t_boxed_3448_, v_h_3446_, v_get_3447_);
lean_dec(v_get_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object* v_put_3450_){
_start:
{
lean_inc(v_put_3450_);
return v_put_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object* v_put_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(v_put_3451_);
lean_dec(v_put_3451_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object* v_motive_3453_, uint8_t v_t_3454_, lean_object* v_h_3455_, lean_object* v_put_3456_){
_start:
{
lean_inc(v_put_3456_);
return v_put_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object* v_motive_3457_, lean_object* v_t_3458_, lean_object* v_h_3459_, lean_object* v_put_3460_){
_start:
{
uint8_t v_t_boxed_3461_; lean_object* v_res_3462_; 
v_t_boxed_3461_ = lean_unbox(v_t_3458_);
v_res_3462_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(v_motive_3457_, v_t_boxed_3461_, v_h_3459_, v_put_3460_);
lean_dec(v_put_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object* v_n_3463_){
_start:
{
lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_nat_dec_le(v_n_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
uint8_t v___x_3466_; 
v___x_3466_ = 1;
return v___x_3466_;
}
else
{
uint8_t v___x_3467_; 
v___x_3467_ = 0;
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object* v_n_3468_){
_start:
{
uint8_t v_res_3469_; lean_object* v_r_3470_; 
v_res_3469_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(v_n_3468_);
lean_dec(v_n_3468_);
v_r_3470_ = lean_box(v_res_3469_);
return v_r_3470_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t v_x_3471_, uint8_t v_y_3472_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3473_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3471_);
v___x_3474_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_y_3472_);
v___x_3475_ = lean_nat_dec_eq(v___x_3473_, v___x_3474_);
lean_dec(v___x_3474_);
lean_dec(v___x_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object* v_x_3476_, lean_object* v_y_3477_){
_start:
{
uint8_t v_x_13__boxed_3478_; uint8_t v_y_14__boxed_3479_; uint8_t v_res_3480_; lean_object* v_r_3481_; 
v_x_13__boxed_3478_ = lean_unbox(v_x_3476_);
v_y_14__boxed_3479_ = lean_unbox(v_y_3477_);
v_res_3480_ = l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(v_x_13__boxed_3478_, v_y_14__boxed_3479_);
v_r_3481_ = lean_box(v_res_3480_);
return v_r_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object* v_cfg_3483_, lean_object* v_out_3484_){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0));
v___x_3486_ = l_Lake_JsonObject_getJson_x3f(v_out_3484_, v___x_3485_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_box(0);
return v___x_3487_;
}
else
{
lean_object* v_val_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3504_; 
v_val_3488_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3490_ = v___x_3486_;
v_isShared_3491_ = v_isSharedCheck_3504_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_val_3488_);
lean_dec(v___x_3486_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3504_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Json_getNat_x3f(v_val_3488_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v___x_3493_; 
lean_dec_ref(v___x_3492_);
lean_del_object(v___x_3490_);
v___x_3493_ = lean_box(0);
return v___x_3493_;
}
else
{
if (lean_obj_tag(v___x_3492_) == 1)
{
lean_object* v_a_3494_; lean_object* v_infos_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v_a_3494_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3492_);
v_infos_3495_ = lean_ctor_get(v_cfg_3483_, 1);
v___x_3496_ = lean_array_get_size(v_infos_3495_);
v___x_3497_ = lean_nat_dec_lt(v_a_3494_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
lean_dec(v_a_3494_);
lean_del_object(v___x_3490_);
v___x_3498_ = lean_box(0);
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3499_ = lean_array_fget_borrowed(v_infos_3495_, v_a_3494_);
lean_dec(v_a_3494_);
lean_inc(v___x_3499_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3499_);
v___x_3501_ = v___x_3490_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
else
{
lean_object* v___x_3503_; 
lean_dec_ref(v___x_3492_);
lean_del_object(v___x_3490_);
v___x_3503_ = lean_box(0);
return v___x_3503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object* v_cfg_3505_, lean_object* v_out_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3505_, v_out_3506_);
lean_dec(v_out_3506_);
lean_dec_ref(v_cfg_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object* v_s_3508_, lean_object* v_pos_3509_){
_start:
{
lean_object* v_str_3510_; lean_object* v_startInclusive_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v_str_3510_ = lean_ctor_get(v_s_3508_, 0);
v_startInclusive_3511_ = lean_ctor_get(v_s_3508_, 1);
v___x_3512_ = lean_nat_add(v_startInclusive_3511_, v_pos_3509_);
v___x_3513_ = lean_nat_sub(v___x_3512_, v_startInclusive_3511_);
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = lean_nat_dec_eq(v___x_3513_, v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___y_3524_; lean_object* v___x_3525_; uint32_t v___x_3526_; uint8_t v___y_3528_; uint32_t v___x_3533_; uint8_t v___x_3534_; 
lean_inc(v_startInclusive_3511_);
lean_inc_ref(v_str_3510_);
v___x_3516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3516_, 0, v_str_3510_);
lean_ctor_set(v___x_3516_, 1, v_startInclusive_3511_);
lean_ctor_set(v___x_3516_, 2, v___x_3512_);
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_sub(v___x_3513_, v___x_3517_);
lean_dec(v___x_3513_);
v___x_3519_ = l_String_Slice_posLE(v___x_3516_, v___x_3518_);
lean_dec_ref(v___x_3516_);
v___x_3525_ = lean_nat_add(v_startInclusive_3511_, v___x_3519_);
v___x_3526_ = lean_string_utf8_get_fast(v_str_3510_, v___x_3525_);
lean_dec(v___x_3525_);
v___x_3533_ = 32;
v___x_3534_ = lean_uint32_dec_eq(v___x_3526_, v___x_3533_);
if (v___x_3534_ == 0)
{
uint32_t v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = 9;
v___x_3536_ = lean_uint32_dec_eq(v___x_3526_, v___x_3535_);
v___y_3528_ = v___x_3536_;
goto v___jp_3527_;
}
else
{
v___y_3528_ = v___x_3534_;
goto v___jp_3527_;
}
v___jp_3520_:
{
uint8_t v___x_3521_; 
v___x_3521_ = l_String_instDecidableLtRaw___aux__1(v___x_3519_, v_pos_3509_);
if (v___x_3521_ == 0)
{
lean_dec(v___x_3519_);
return v_pos_3509_;
}
else
{
lean_dec(v_pos_3509_);
v_pos_3509_ = v___x_3519_;
goto _start;
}
}
v___jp_3523_:
{
if (v___y_3524_ == 0)
{
lean_dec(v___x_3519_);
return v_pos_3509_;
}
else
{
goto v___jp_3520_;
}
}
v___jp_3527_:
{
if (v___y_3528_ == 0)
{
uint32_t v___x_3529_; uint8_t v___x_3530_; 
v___x_3529_ = 13;
v___x_3530_ = lean_uint32_dec_eq(v___x_3526_, v___x_3529_);
if (v___x_3530_ == 0)
{
uint32_t v___x_3531_; uint8_t v___x_3532_; 
v___x_3531_ = 10;
v___x_3532_ = lean_uint32_dec_eq(v___x_3526_, v___x_3531_);
v___y_3524_ = v___x_3532_;
goto v___jp_3523_;
}
else
{
v___y_3524_ = v___x_3530_;
goto v___jp_3523_;
}
}
else
{
goto v___jp_3520_;
}
}
}
else
{
lean_dec(v___x_3513_);
lean_dec(v___x_3512_);
return v_pos_3509_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object* v_s_3537_, lean_object* v_pos_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v_s_3537_, v_pos_3538_);
lean_dec_ref(v_s_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object* v_cfg_3552_, lean_object* v_hOut_3553_, lean_object* v_info_3554_, lean_object* v_code_x3f_3555_, lean_object* v_out_3556_, lean_object* v_line_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_msg_3561_; lean_object* v___y_3562_; lean_object* v___y_3579_; lean_object* v_msg_3580_; lean_object* v___y_3581_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v_a_3600_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v_val_3611_; uint8_t v_kind_3622_; lean_object* v_scope_3623_; lean_object* v_msg_3625_; lean_object* v___y_3626_; lean_object* v_msg_3692_; lean_object* v___y_3693_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3722_; 
v_kind_3622_ = lean_ctor_get_uint8(v_cfg_3552_, sizeof(void*)*3);
v_scope_3623_ = lean_ctor_get(v_cfg_3552_, 0);
lean_inc_ref(v_scope_3623_);
lean_dec_ref(v_cfg_3552_);
if (v_kind_3622_ == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___y_3722_ = v___x_3724_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3725_; 
v___x_3725_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___y_3722_ = v___x_3725_;
goto v___jp_3721_;
}
v___jp_3560_:
{
uint8_t v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3563_ = 3;
v___x_3564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3564_, 0, v_msg_3561_);
lean_ctor_set_uint8(v___x_3564_, sizeof(void*)*1, v___x_3563_);
lean_inc_ref(v___y_3562_);
v___x_3565_ = lean_apply_2(v___y_3562_, v___x_3564_, lean_box(0));
v___x_3566_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0));
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = lean_string_utf8_byte_size(v_line_3557_);
lean_inc_ref(v_line_3557_);
v___x_3569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3569_, 0, v_line_3557_);
lean_ctor_set(v___x_3569_, 1, v___x_3567_);
lean_ctor_set(v___x_3569_, 2, v___x_3568_);
v___x_3570_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_3569_, v___x_3568_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3571_, 0, v_line_3557_);
lean_ctor_set(v___x_3571_, 1, v___x_3567_);
lean_ctor_set(v___x_3571_, 2, v___x_3570_);
v___x_3572_ = l_String_Slice_toString(v___x_3571_);
lean_dec_ref(v___x_3571_);
v___x_3573_ = lean_string_append(v___x_3566_, v___x_3572_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = 0;
v___x_3575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*1, v___x_3574_);
lean_inc_ref(v___y_3562_);
v___x_3576_ = lean_apply_2(v___y_3562_, v___x_3575_, lean_box(0));
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
return v___x_3577_;
}
v___jp_3578_:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lake_removeFileIfExists(v___y_3579_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_dec_ref(v___x_3582_);
v_msg_3561_ = v_msg_3580_;
v___y_3562_ = v___y_3581_;
goto v___jp_3560_;
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_msg_3580_);
lean_dec_ref(v_line_3557_);
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3595_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3595_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3587_ = lean_io_error_to_string(v_a_3583_);
v___x_3588_ = 3;
v___x_3589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set_uint8(v___x_3589_, sizeof(void*)*1, v___x_3588_);
lean_inc_ref(v___y_3581_);
v___x_3590_ = lean_apply_2(v___y_3581_, v___x_3589_, lean_box(0));
v___x_3591_ = lean_box(0);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3591_);
v___x_3593_ = v___x_3585_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3596_:
{
if (lean_obj_tag(v_a_3600_) == 1)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_a_3601_ = lean_ctor_get(v_a_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v_a_3600_);
v___x_3602_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3603_ = lean_string_append(v___y_3599_, v___x_3602_);
v___x_3604_ = lean_string_append(v___x_3603_, v_a_3601_);
lean_dec(v_a_3601_);
v___y_3579_ = v___y_3597_;
v_msg_3580_ = v___x_3604_;
v___y_3581_ = v___y_3598_;
goto v___jp_3578_;
}
else
{
lean_dec_ref(v_a_3600_);
v___y_3579_ = v___y_3597_;
v_msg_3580_ = v___y_3599_;
v___y_3581_ = v___y_3598_;
goto v___jp_3578_;
}
}
v___jp_3605_:
{
lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3612_ = lean_array_get_size(v___y_3607_);
v___x_3613_ = lean_nat_dec_lt(v___y_3610_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_dec_ref(v___y_3607_);
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3608_;
v___y_3599_ = v___y_3609_;
v_a_3600_ = v_val_3611_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_nat_dec_le(v___x_3612_, v___x_3612_);
if (v___x_3615_ == 0)
{
if (v___x_3613_ == 0)
{
lean_dec_ref(v___y_3607_);
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3608_;
v___y_3599_ = v___y_3609_;
v_a_3600_ = v_val_3611_;
goto v___jp_3596_;
}
else
{
size_t v___x_3616_; size_t v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = ((size_t)0ULL);
v___x_3617_ = lean_usize_of_nat(v___x_3612_);
v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3607_, v___x_3616_, v___x_3617_, v___x_3614_, v___y_3608_);
lean_dec_ref(v___y_3607_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_dec_ref(v___x_3618_);
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3608_;
v___y_3599_ = v___y_3609_;
v_a_3600_ = v_val_3611_;
goto v___jp_3596_;
}
else
{
lean_dec_ref(v_val_3611_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v_line_3557_);
return v___x_3618_;
}
}
}
else
{
size_t v___x_3619_; size_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = ((size_t)0ULL);
v___x_3620_ = lean_usize_of_nat(v___x_3612_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3607_, v___x_3619_, v___x_3620_, v___x_3614_, v___y_3608_);
lean_dec_ref(v___y_3607_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_dec_ref(v___x_3621_);
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3608_;
v___y_3599_ = v___y_3609_;
v_a_3600_ = v_val_3611_;
goto v___jp_3596_;
}
else
{
lean_dec_ref(v_val_3611_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v_line_3557_);
return v___x_3621_;
}
}
}
}
v___jp_3624_:
{
lean_object* v_url_3627_; lean_object* v_path_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_msg_3634_; 
v_url_3627_ = lean_ctor_get(v_info_3554_, 0);
v_path_3628_ = lean_ctor_get(v_info_3554_, 1);
v___x_3629_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3630_ = lean_string_append(v_msg_3625_, v___x_3629_);
v___x_3631_ = lean_string_append(v___x_3630_, v_path_3628_);
v___x_3632_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3633_ = lean_string_append(v___x_3631_, v___x_3632_);
v_msg_3634_ = lean_string_append(v___x_3633_, v_url_3627_);
if (v_kind_3622_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3636_ = l_Lake_JsonObject_getJson_x3f(v_out_3556_, v___x_3635_);
if (lean_obj_tag(v___x_3636_) == 0)
{
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
else
{
lean_object* v_val_3637_; lean_object* v___x_3638_; 
v_val_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_val_3637_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = l_Lean_Json_getNat_x3f(v_val_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_dec_ref(v___x_3638_);
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
else
{
if (lean_obj_tag(v___x_3638_) == 1)
{
lean_object* v_a_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3638_);
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = lean_nat_dec_lt(v___x_3640_, v_a_3639_);
lean_dec(v_a_3639_);
if (v___x_3641_ == 0)
{
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3));
v___x_3643_ = l_Lake_JsonObject_getJson_x3f(v_out_3556_, v___x_3642_);
if (lean_obj_tag(v___x_3643_) == 0)
{
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
else
{
lean_object* v_val_3644_; lean_object* v___x_3645_; 
v_val_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_val_3644_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = l_Lean_Json_getStr_x3f(v_val_3644_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_dec_ref(v___x_3645_);
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
else
{
if (lean_obj_tag(v___x_3645_) == 1)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3662_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3662_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3662_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3650_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3651_ = lean_string_dec_eq(v_a_3646_, v___x_3650_);
lean_dec(v_a_3646_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3653_ = l_IO_FS_readFile(v_path_3628_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref(v___x_3653_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v_a_3654_);
v___x_3656_ = v___x_3648_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
v___y_3606_ = v_path_3628_;
v___y_3607_ = v___x_3652_;
v___y_3608_ = v___y_3626_;
v___y_3609_ = v_msg_3634_;
v___y_3610_ = v___x_3640_;
v_val_3611_ = v___x_3656_;
goto v___jp_3605_;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; 
v_a_3658_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3658_);
lean_dec_ref(v___x_3653_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set_tag(v___x_3648_, 0);
lean_ctor_set(v___x_3648_, 0, v_a_3658_);
v___x_3660_ = v___x_3648_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
v___y_3606_ = v_path_3628_;
v___y_3607_ = v___x_3652_;
v___y_3608_ = v___y_3626_;
v___y_3609_ = v_msg_3634_;
v___y_3610_ = v___x_3640_;
v_val_3611_ = v___x_3660_;
goto v___jp_3605_;
}
}
}
else
{
lean_del_object(v___x_3648_);
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
}
}
else
{
lean_dec_ref(v___x_3645_);
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3638_);
v___y_3579_ = v_path_3628_;
v_msg_3580_ = v_msg_3634_;
v___y_3581_ = v___y_3626_;
goto v___jp_3578_;
}
}
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3664_ = l_Lake_JsonObject_getJson_x3f(v_out_3556_, v___x_3663_);
if (lean_obj_tag(v___x_3664_) == 0)
{
v_msg_3561_ = v_msg_3634_;
v___y_3562_ = v___y_3626_;
goto v___jp_3560_;
}
else
{
lean_object* v_val_3665_; lean_object* v___x_3666_; 
v_val_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_val_3665_);
lean_dec_ref(v___x_3664_);
v___x_3666_ = l_Lean_Json_getNat_x3f(v_val_3665_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_dec_ref(v___x_3666_);
v_msg_3561_ = v_msg_3634_;
v___y_3562_ = v___y_3626_;
goto v___jp_3560_;
}
else
{
if (lean_obj_tag(v___x_3666_) == 1)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref(v___x_3666_);
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = lean_nat_dec_lt(v___x_3668_, v_a_3667_);
if (v___x_3669_ == 0)
{
lean_dec(v_a_3667_);
v_msg_3561_ = v_msg_3634_;
v___y_3562_ = v___y_3626_;
goto v___jp_3560_;
}
else
{
size_t v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_usize_of_nat(v_a_3667_);
lean_dec(v_a_3667_);
v___x_3671_ = lean_io_prim_handle_read(v_hOut_3553_, v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; uint8_t v___x_3673_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref(v___x_3671_);
v___x_3673_ = lean_string_validate_utf8(v_a_3672_);
if (v___x_3673_ == 0)
{
lean_dec(v_a_3672_);
v_msg_3561_ = v_msg_3634_;
v___y_3562_ = v___y_3626_;
goto v___jp_3560_;
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3674_ = lean_string_from_utf8_unchecked(v_a_3672_);
v___x_3675_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3676_ = lean_string_append(v_msg_3634_, v___x_3675_);
v___x_3677_ = lean_string_append(v___x_3676_, v___x_3674_);
lean_dec_ref(v___x_3674_);
v_msg_3561_ = v___x_3677_;
v___y_3562_ = v___y_3626_;
goto v___jp_3560_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v_msg_3634_);
lean_dec_ref(v_line_3557_);
v_a_3678_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3680_ = v___x_3671_;
v_isShared_3681_ = v_isSharedCheck_3690_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3671_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3690_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; uint8_t v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3682_ = lean_io_error_to_string(v_a_3678_);
v___x_3683_ = 3;
v___x_3684_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*1, v___x_3683_);
lean_inc_ref(v___y_3626_);
v___x_3685_ = lean_apply_2(v___y_3626_, v___x_3684_, lean_box(0));
v___x_3686_ = lean_box(0);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3686_);
v___x_3688_ = v___x_3680_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3666_);
v_msg_3561_ = v_msg_3634_;
v___y_3562_ = v___y_3626_;
goto v___jp_3560_;
}
}
}
}
}
v___jp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_3695_ = l_Lake_JsonObject_getJson_x3f(v_out_3556_, v___x_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
v_msg_3625_ = v_msg_3692_;
v___y_3626_ = v___y_3693_;
goto v___jp_3624_;
}
else
{
lean_object* v_val_3696_; lean_object* v___x_3697_; 
v_val_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_val_3696_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = l_Lean_Json_getStr_x3f(v_val_3696_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_dec_ref(v___x_3697_);
v_msg_3625_ = v_msg_3692_;
v___y_3626_ = v___y_3693_;
goto v___jp_3624_;
}
else
{
if (lean_obj_tag(v___x_3697_) == 1)
{
lean_object* v_a_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_msg_3701_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5));
v___x_3700_ = lean_string_append(v_msg_3692_, v___x_3699_);
v_msg_3701_ = lean_string_append(v___x_3700_, v_a_3698_);
lean_dec(v_a_3698_);
v_msg_3625_ = v_msg_3701_;
v___y_3626_ = v___y_3693_;
goto v___jp_3624_;
}
else
{
lean_dec_ref(v___x_3697_);
v_msg_3625_ = v_msg_3692_;
v___y_3626_ = v___y_3693_;
goto v___jp_3624_;
}
}
}
}
v___jp_3702_:
{
lean_object* v_descr_3705_; uint64_t v_hash_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v_msg_3713_; 
v_descr_3705_ = lean_ctor_get(v_info_3554_, 2);
v_hash_3706_ = lean_ctor_get_uint64(v_descr_3705_, sizeof(void*)*1);
v___x_3707_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_3708_ = lean_string_append(v___y_3704_, v___x_3707_);
v___x_3709_ = lean_string_append(v___x_3708_, v___y_3703_);
lean_dec_ref(v___y_3703_);
v___x_3710_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7));
v___x_3711_ = lean_string_append(v___x_3709_, v___x_3710_);
v___x_3712_ = l_Lake_Hash_hex(v_hash_3706_);
v_msg_3713_ = lean_string_append(v___x_3711_, v___x_3712_);
lean_dec_ref(v___x_3712_);
if (lean_obj_tag(v_code_x3f_3555_) == 1)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_msg_3720_; 
v_a_3714_ = lean_ctor_get(v_code_x3f_3555_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v_code_x3f_3555_);
v___x_3715_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8));
v___x_3716_ = lean_string_append(v_msg_3713_, v___x_3715_);
v___x_3717_ = l_Nat_reprFast(v_a_3714_);
v___x_3718_ = lean_string_append(v___x_3716_, v___x_3717_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v_msg_3720_ = lean_string_append(v___x_3718_, v___x_3719_);
v_msg_3692_ = v_msg_3720_;
v___y_3693_ = v_a_3558_;
goto v___jp_3691_;
}
else
{
lean_dec_ref(v_code_x3f_3555_);
v_msg_3692_ = v_msg_3713_;
v___y_3693_ = v_a_3558_;
goto v___jp_3691_;
}
}
v___jp_3721_:
{
lean_object* v_s_3723_; 
v_s_3723_ = lean_ctor_get(v_scope_3623_, 0);
lean_inc_ref(v_s_3723_);
lean_dec_ref(v_scope_3623_);
v___y_3703_ = v___y_3722_;
v___y_3704_ = v_s_3723_;
goto v___jp_3702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object* v_cfg_3726_, lean_object* v_hOut_3727_, lean_object* v_info_3728_, lean_object* v_code_x3f_3729_, lean_object* v_out_3730_, lean_object* v_line_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3726_, v_hOut_3727_, v_info_3728_, v_code_x3f_3729_, v_out_3730_, v_line_3731_, v_a_3732_);
lean_dec_ref(v_a_3732_);
lean_dec(v_out_3730_);
lean_dec_ref(v_info_3728_);
lean_dec(v_hOut_3727_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object* v_cfg_3735_, lean_object* v_hOut_3736_, lean_object* v_val_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, uint8_t v___x_3740_, lean_object* v_code_x3f_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3735_, v_hOut_3736_, v_val_3737_, v_code_x3f_3741_, v_a_3738_, v_a_3739_, v___y_3743_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3762_; 
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v___x_3745_, 0);
lean_dec(v_unused_3763_);
v___x_3747_ = v___x_3745_;
v_isShared_3748_ = v_isSharedCheck_3762_;
goto v_resetjp_3746_;
}
else
{
lean_dec(v___x_3745_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3762_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_numSuccesses_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3761_; 
v_numSuccesses_3749_ = lean_ctor_get(v___y_3742_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___y_3742_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3751_ = v___y_3742_;
v_isShared_3752_ = v_isSharedCheck_3761_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_numSuccesses_3749_);
lean_dec(v___y_3742_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3761_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3753_ = lean_box(0);
if (v_isShared_3752_ == 0)
{
v___x_3755_ = v___x_3751_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_numSuccesses_3749_);
v___x_3755_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_ctor_set_uint8(v___x_3755_, sizeof(void*)*1, v___x_3740_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3753_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3756_);
v___x_3758_ = v___x_3747_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v___y_3742_);
v_a_3764_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3745_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3745_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object* v_cfg_3772_, lean_object* v_hOut_3773_, lean_object* v_val_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v___x_3777_, lean_object* v_code_x3f_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
uint8_t v___x_27917__boxed_3782_; lean_object* v_res_3783_; 
v___x_27917__boxed_3782_ = lean_unbox(v___x_3777_);
v_res_3783_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_3772_, v_hOut_3773_, v_val_3774_, v_a_3775_, v_a_3776_, v___x_27917__boxed_3782_, v_code_x3f_3778_, v___y_3779_, v___y_3780_);
lean_dec_ref(v___y_3780_);
lean_dec(v_a_3775_);
lean_dec_ref(v_val_3774_);
lean_dec(v_hOut_3773_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object* v_cfg_3786_, lean_object* v_path_3787_, uint8_t v___x_3788_, lean_object* v_descr_3789_, lean_object* v_url_3790_, uint8_t v___x_3791_, lean_object* v_00___3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
uint64_t v___y_3797_; lean_object* v___y_3837_; lean_object* v___y_3892_; uint8_t v_kind_3921_; 
v_kind_3921_ = lean_ctor_get_uint8(v_cfg_3786_, sizeof(void*)*3);
if (v_kind_3921_ == 0)
{
lean_object* v_scope_3922_; lean_object* v_s_3923_; 
v_scope_3922_ = lean_ctor_get(v_cfg_3786_, 0);
lean_inc_ref(v_scope_3922_);
lean_dec_ref(v_cfg_3786_);
v_s_3923_ = lean_ctor_get(v_scope_3922_, 0);
lean_inc_ref(v_s_3923_);
lean_dec_ref(v_scope_3922_);
v___y_3837_ = v_s_3923_;
goto v___jp_3836_;
}
else
{
lean_object* v_scope_3924_; lean_object* v_s_3925_; 
v_scope_3924_ = lean_ctor_get(v_cfg_3786_, 0);
lean_inc_ref(v_scope_3924_);
lean_dec_ref(v_cfg_3786_);
v_s_3925_ = lean_ctor_get(v_scope_3924_, 0);
lean_inc_ref(v_s_3925_);
lean_dec_ref(v_scope_3924_);
v___y_3892_ = v_s_3925_;
goto v___jp_3891_;
}
v___jp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3798_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_3787_);
v___x_3799_ = lean_string_append(v_path_3787_, v___x_3798_);
v___x_3800_ = l_Lake_Hash_hex(v___y_3797_);
v___x_3801_ = lean_string_append(v___x_3799_, v___x_3800_);
lean_dec_ref(v___x_3800_);
v___x_3802_ = 3;
v___x_3803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set_uint8(v___x_3803_, sizeof(void*)*1, v___x_3802_);
lean_inc_ref(v___y_3794_);
v___x_3804_ = lean_apply_2(v___y_3794_, v___x_3803_, lean_box(0));
v___x_3805_ = lean_io_remove_file(v_path_3787_);
lean_dec_ref(v_path_3787_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3822_; 
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3822_ == 0)
{
lean_object* v_unused_3823_; 
v_unused_3823_ = lean_ctor_get(v___x_3805_, 0);
lean_dec(v_unused_3823_);
v___x_3807_ = v___x_3805_;
v_isShared_3808_ = v_isSharedCheck_3822_;
goto v_resetjp_3806_;
}
else
{
lean_dec(v___x_3805_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3822_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_numSuccesses_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3821_; 
v_numSuccesses_3809_ = lean_ctor_get(v___y_3793_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___y_3793_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3811_ = v___y_3793_;
v_isShared_3812_ = v_isSharedCheck_3821_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_numSuccesses_3809_);
lean_dec(v___y_3793_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3821_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = lean_box(0);
if (v_isShared_3812_ == 0)
{
v___x_3815_ = v___x_3811_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_numSuccesses_3809_);
v___x_3815_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*1, v___x_3788_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3813_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3816_);
v___x_3818_ = v___x_3807_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v___y_3793_);
v_a_3824_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3826_ = v___x_3805_;
v_isShared_3827_ = v_isSharedCheck_3835_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3805_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3835_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3828_ = lean_io_error_to_string(v_a_3824_);
v___x_3829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*1, v___x_3802_);
lean_inc_ref(v___y_3794_);
v___x_3830_ = lean_apply_2(v___y_3794_, v___x_3829_, lean_box(0));
v___x_3831_ = lean_box(0);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3831_);
v___x_3833_ = v___x_3826_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
v___jp_3836_:
{
uint64_t v_hash_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_hash_3838_ = lean_ctor_get_uint64(v_descr_3789_, sizeof(void*)*1);
v___x_3839_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0));
v___x_3840_ = lean_string_append(v___y_3837_, v___x_3839_);
v___x_3841_ = l_Lake_Hash_hex(v_hash_3838_);
v___x_3842_ = lean_string_append(v___x_3840_, v___x_3841_);
lean_dec_ref(v___x_3841_);
v___x_3843_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3844_ = lean_string_append(v___x_3842_, v___x_3843_);
v___x_3845_ = lean_string_append(v___x_3844_, v_path_3787_);
v___x_3846_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3847_ = lean_string_append(v___x_3845_, v___x_3846_);
v___x_3848_ = lean_string_append(v___x_3847_, v_url_3790_);
v___x_3849_ = 1;
v___x_3850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set_uint8(v___x_3850_, sizeof(void*)*1, v___x_3849_);
lean_inc_ref(v___y_3794_);
v___x_3851_ = lean_apply_2(v___y_3794_, v___x_3850_, lean_box(0));
v___x_3852_ = l_Lake_computeBinFileHash(v_path_3787_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3877_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3877_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3877_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
uint64_t v___x_3857_; uint8_t v___x_3858_; 
v___x_3857_ = lean_unbox_uint64(v_a_3853_);
v___x_3858_ = lean_uint64_dec_eq(v___x_3857_, v_hash_3838_);
if (v___x_3858_ == 0)
{
uint64_t v___x_3859_; 
lean_del_object(v___x_3855_);
v___x_3859_ = lean_unbox_uint64(v_a_3853_);
lean_dec(v_a_3853_);
v___y_3797_ = v___x_3859_;
goto v___jp_3796_;
}
else
{
if (v___x_3791_ == 0)
{
uint8_t v_didError_3860_; lean_object* v_numSuccesses_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v_a_3853_);
lean_dec_ref(v_path_3787_);
v_didError_3860_ = lean_ctor_get_uint8(v___y_3793_, sizeof(void*)*1);
v_numSuccesses_3861_ = lean_ctor_get(v___y_3793_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___y_3793_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3863_ = v___y_3793_;
v_isShared_3864_ = v_isSharedCheck_3875_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_numSuccesses_3861_);
lean_dec(v___y_3793_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3875_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3865_ = lean_box(0);
v___x_3866_ = lean_unsigned_to_nat(1u);
v___x_3867_ = lean_nat_add(v_numSuccesses_3861_, v___x_3866_);
lean_dec(v_numSuccesses_3861_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3867_);
v___x_3869_ = v___x_3863_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3874_, sizeof(void*)*1, v_didError_3860_);
v___x_3869_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3865_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3870_);
v___x_3872_ = v___x_3855_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
uint64_t v___x_3876_; 
lean_del_object(v___x_3855_);
v___x_3876_ = lean_unbox_uint64(v_a_3853_);
lean_dec(v_a_3853_);
v___y_3797_ = v___x_3876_;
goto v___jp_3796_;
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v___y_3793_);
lean_dec_ref(v_path_3787_);
v_a_3878_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3880_ = v___x_3852_;
v_isShared_3881_ = v_isSharedCheck_3890_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3852_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3890_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3882_ = lean_io_error_to_string(v_a_3878_);
v___x_3883_ = 3;
v___x_3884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set_uint8(v___x_3884_, sizeof(void*)*1, v___x_3883_);
lean_inc_ref(v___y_3794_);
v___x_3885_ = lean_apply_2(v___y_3794_, v___x_3884_, lean_box(0));
v___x_3886_ = lean_box(0);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v___x_3886_);
v___x_3888_ = v___x_3880_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
v___jp_3891_:
{
uint64_t v_hash_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v_didError_3907_; lean_object* v_numSuccesses_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3920_; 
v_hash_3893_ = lean_ctor_get_uint64(v_descr_3789_, sizeof(void*)*1);
v___x_3894_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1));
v___x_3895_ = lean_string_append(v___y_3892_, v___x_3894_);
v___x_3896_ = l_Lake_Hash_hex(v_hash_3893_);
v___x_3897_ = lean_string_append(v___x_3895_, v___x_3896_);
lean_dec_ref(v___x_3896_);
v___x_3898_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3899_ = lean_string_append(v___x_3897_, v___x_3898_);
v___x_3900_ = lean_string_append(v___x_3899_, v_path_3787_);
lean_dec_ref(v_path_3787_);
v___x_3901_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3902_ = lean_string_append(v___x_3900_, v___x_3901_);
v___x_3903_ = lean_string_append(v___x_3902_, v_url_3790_);
v___x_3904_ = 1;
v___x_3905_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3905_, 0, v___x_3903_);
lean_ctor_set_uint8(v___x_3905_, sizeof(void*)*1, v___x_3904_);
lean_inc_ref(v___y_3794_);
v___x_3906_ = lean_apply_2(v___y_3794_, v___x_3905_, lean_box(0));
v_didError_3907_ = lean_ctor_get_uint8(v___y_3793_, sizeof(void*)*1);
v_numSuccesses_3908_ = lean_ctor_get(v___y_3793_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___y_3793_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3910_ = v___y_3793_;
v_isShared_3911_ = v_isSharedCheck_3920_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_numSuccesses_3908_);
lean_dec(v___y_3793_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3920_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3912_ = lean_box(0);
v___x_3913_ = lean_unsigned_to_nat(1u);
v___x_3914_ = lean_nat_add(v_numSuccesses_3908_, v___x_3913_);
lean_dec(v_numSuccesses_3908_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3914_);
v___x_3916_ = v___x_3910_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3914_);
lean_ctor_set_uint8(v_reuseFailAlloc_3919_, sizeof(void*)*1, v_didError_3907_);
v___x_3916_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3912_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
return v___x_3918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object* v_cfg_3926_, lean_object* v_path_3927_, lean_object* v___x_3928_, lean_object* v_descr_3929_, lean_object* v_url_3930_, lean_object* v___x_3931_, lean_object* v_00___3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v___x_27997__boxed_3936_; uint8_t v___x_28000__boxed_3937_; lean_object* v_res_3938_; 
v___x_27997__boxed_3936_ = lean_unbox(v___x_3928_);
v___x_28000__boxed_3937_ = lean_unbox(v___x_3931_);
v_res_3938_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_3926_, v_path_3927_, v___x_27997__boxed_3936_, v_descr_3929_, v_url_3930_, v___x_28000__boxed_3937_, v_00___3932_, v___y_3933_, v___y_3934_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v_url_3930_);
lean_dec_ref(v_descr_3929_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object* v_a_3945_, lean_object* v_cfg_3946_, lean_object* v_h_3947_, lean_object* v_hOut_3948_, lean_object* v_s_3949_){
_start:
{
lean_object* v___y_3952_; lean_object* v___x_3964_; 
v___x_3964_ = lean_io_prim_handle_get_line(v_h_3947_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_4063_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_4063_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_4063_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v_startInclusive_3977_; lean_object* v_endExclusive_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3973_ = lean_unsigned_to_nat(0u);
v___x_3974_ = lean_string_utf8_byte_size(v_a_3965_);
lean_inc(v_a_3965_);
v___x_3975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3975_, 0, v_a_3965_);
lean_ctor_set(v___x_3975_, 1, v___x_3973_);
lean_ctor_set(v___x_3975_, 2, v___x_3974_);
v___x_3976_ = l_String_Slice_trimAscii(v___x_3975_);
v_startInclusive_3977_ = lean_ctor_get(v___x_3976_, 1);
lean_inc(v_startInclusive_3977_);
v_endExclusive_3978_ = lean_ctor_get(v___x_3976_, 2);
lean_inc(v_endExclusive_3978_);
v___x_3979_ = lean_nat_sub(v_endExclusive_3978_, v_startInclusive_3977_);
lean_dec(v_startInclusive_3977_);
lean_dec(v_endExclusive_3978_);
v___x_3980_ = lean_nat_dec_eq(v___x_3979_, v___x_3973_);
lean_dec(v___x_3979_);
if (v___x_3980_ == 0)
{
uint8_t v___x_3981_; lean_object* v___y_3983_; lean_object* v_a_4001_; lean_object* v___x_4020_; 
lean_del_object(v___x_3967_);
v___x_3981_ = 1;
lean_inc(v_a_3965_);
v___x_4020_ = l_Lean_Json_parse(v_a_3965_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; 
lean_dec(v_a_3965_);
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref(v___x_4020_);
v_a_4001_ = v_a_4021_;
goto v___jp_4000_;
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4023_; 
v_a_4022_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4022_);
lean_dec_ref(v___x_4020_);
v___x_4023_ = l_Lean_Json_getObj_x3f(v_a_4022_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; 
lean_dec(v_a_3965_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4023_);
v_a_4001_ = v_a_4024_;
goto v___jp_4000_;
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4026_; 
v_a_4025_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4023_);
v___x_4026_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3946_, v_a_4025_);
if (lean_obj_tag(v___x_4026_) == 1)
{
lean_object* v_val_4027_; lean_object* v_url_4028_; lean_object* v_path_4029_; lean_object* v_descr_4030_; lean_object* v___x_4031_; lean_object* v___f_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec_ref(v___x_3976_);
v_val_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_val_4027_);
lean_dec_ref(v___x_4026_);
v_url_4028_ = lean_ctor_get(v_val_4027_, 0);
v_path_4029_ = lean_ctor_get(v_val_4027_, 1);
v_descr_4030_ = lean_ctor_get(v_val_4027_, 2);
v___x_4031_ = lean_box(v___x_3981_);
lean_inc(v_a_3965_);
lean_inc(v_a_4025_);
lean_inc(v_val_4027_);
lean_inc(v_hOut_3948_);
lean_inc_ref(v_cfg_3946_);
v___f_4032_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed), 10, 6);
lean_closure_set(v___f_4032_, 0, v_cfg_3946_);
lean_closure_set(v___f_4032_, 1, v_hOut_3948_);
lean_closure_set(v___f_4032_, 2, v_val_4027_);
lean_closure_set(v___f_4032_, 3, v_a_4025_);
lean_closure_set(v___f_4032_, 4, v_a_3965_);
lean_closure_set(v___f_4032_, 5, v___x_4031_);
v___x_4033_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4034_ = l_Lake_JsonObject_getJson_x3f(v_a_4025_, v___x_4033_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v___x_4035_; 
lean_dec(v_val_4027_);
lean_dec(v_a_4025_);
lean_dec(v_a_3965_);
v___x_4035_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_3970_ = v___f_4032_;
v___y_3971_ = v___x_4035_;
goto v___jp_3969_;
}
else
{
lean_object* v_val_4036_; lean_object* v___x_4037_; 
v_val_4036_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_val_4036_);
lean_dec_ref(v___x_4034_);
v___x_4037_ = l_Lean_Json_getNat_x3f(v_val_4036_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4047_; 
lean_dec(v_val_4027_);
lean_dec(v_a_4025_);
lean_dec(v_a_3965_);
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4047_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4047_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4045_; 
v___x_4042_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4043_ = lean_string_append(v___x_4042_, v_a_4038_);
lean_dec(v_a_4038_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4043_);
v___x_4045_ = v___x_4040_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
v___y_3970_ = v___f_4032_;
v___y_3971_ = v___x_4045_;
goto v___jp_3969_;
}
}
}
else
{
if (lean_obj_tag(v___x_4037_) == 1)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
lean_dec_ref(v___f_4032_);
v_a_4048_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4048_);
v___x_4049_ = lean_unsigned_to_nat(200u);
v___x_4050_ = lean_nat_dec_eq(v_a_4048_, v___x_4049_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4051_ = lean_unsigned_to_nat(201u);
v___x_4052_ = lean_nat_dec_eq(v_a_4048_, v___x_4051_);
lean_dec(v_a_4048_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4053_; 
lean_inc_ref(v_cfg_3946_);
v___x_4053_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_3946_, v_hOut_3948_, v_val_4027_, v_a_4025_, v_a_3965_, v___x_3981_, v___x_4037_, v_s_3949_, v_a_3945_);
lean_dec(v_a_4025_);
lean_dec(v_val_4027_);
v___y_3952_ = v___x_4053_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_inc_ref(v_descr_4030_);
lean_inc_ref(v_path_4029_);
lean_inc_ref(v_url_4028_);
lean_dec_ref(v___x_4037_);
lean_dec(v_val_4027_);
lean_dec(v_a_4025_);
lean_dec(v_a_3965_);
v___x_4054_ = lean_box(0);
lean_inc_ref(v_cfg_3946_);
v___x_4055_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_3946_, v_path_4029_, v___x_3981_, v_descr_4030_, v_url_4028_, v___x_3980_, v___x_4054_, v_s_3949_, v_a_3945_);
lean_dec_ref(v_url_4028_);
lean_dec_ref(v_descr_4030_);
v___y_3952_ = v___x_4055_;
goto v___jp_3951_;
}
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_inc_ref(v_descr_4030_);
lean_inc_ref(v_path_4029_);
lean_inc_ref(v_url_4028_);
lean_dec(v_a_4048_);
lean_dec_ref(v___x_4037_);
lean_dec(v_val_4027_);
lean_dec(v_a_4025_);
lean_dec(v_a_3965_);
v___x_4056_ = lean_box(0);
lean_inc_ref(v_cfg_3946_);
v___x_4057_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_3946_, v_path_4029_, v___x_3981_, v_descr_4030_, v_url_4028_, v___x_3980_, v___x_4056_, v_s_3949_, v_a_3945_);
lean_dec_ref(v_url_4028_);
lean_dec_ref(v_descr_4030_);
v___y_3952_ = v___x_4057_;
goto v___jp_3951_;
}
}
else
{
lean_dec(v_val_4027_);
lean_dec(v_a_4025_);
lean_dec(v_a_3965_);
v___y_3970_ = v___f_4032_;
v___y_3971_ = v___x_4037_;
goto v___jp_3969_;
}
}
}
}
else
{
lean_object* v_scope_4058_; lean_object* v_s_4059_; 
lean_dec(v___x_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_3965_);
v_scope_4058_ = lean_ctor_get(v_cfg_3946_, 0);
v_s_4059_ = lean_ctor_get(v_scope_4058_, 0);
lean_inc_ref(v_s_4059_);
v___y_3983_ = v_s_4059_;
goto v___jp_3982_;
}
}
}
v___jp_3982_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v_numSuccesses_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3999_; 
v___x_3984_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_3985_ = lean_string_append(v___y_3983_, v___x_3984_);
v___x_3986_ = l_String_Slice_toString(v___x_3976_);
lean_dec_ref(v___x_3976_);
v___x_3987_ = lean_string_append(v___x_3985_, v___x_3986_);
lean_dec_ref(v___x_3986_);
v___x_3988_ = 3;
v___x_3989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3989_, 0, v___x_3987_);
lean_ctor_set_uint8(v___x_3989_, sizeof(void*)*1, v___x_3988_);
lean_inc_ref(v_a_3945_);
v___x_3990_ = lean_apply_2(v_a_3945_, v___x_3989_, lean_box(0));
v_numSuccesses_3991_ = lean_ctor_get(v_s_3949_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_s_3949_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3993_ = v_s_3949_;
v_isShared_3994_ = v_isSharedCheck_3999_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_numSuccesses_3991_);
lean_dec(v_s_3949_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3999_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_numSuccesses_3991_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_ctor_set_uint8(v___x_3996_, sizeof(void*)*1, v___x_3981_);
v_s_3949_ = v___x_3996_;
goto _start;
}
}
}
v___jp_4000_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v_numSuccesses_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4019_; 
v___x_4002_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4003_ = lean_string_append(v___x_4002_, v_a_4001_);
lean_dec_ref(v_a_4001_);
v___x_4004_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4005_ = lean_string_append(v___x_4003_, v___x_4004_);
v___x_4006_ = l_String_Slice_toString(v___x_3976_);
lean_dec_ref(v___x_3976_);
v___x_4007_ = lean_string_append(v___x_4005_, v___x_4006_);
lean_dec_ref(v___x_4006_);
v___x_4008_ = 3;
v___x_4009_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set_uint8(v___x_4009_, sizeof(void*)*1, v___x_4008_);
lean_inc_ref(v_a_3945_);
v___x_4010_ = lean_apply_2(v_a_3945_, v___x_4009_, lean_box(0));
v_numSuccesses_4011_ = lean_ctor_get(v_s_3949_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_s_3949_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4013_ = v_s_3949_;
v_isShared_4014_ = v_isSharedCheck_4019_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_numSuccesses_4011_);
lean_dec(v_s_3949_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4019_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_numSuccesses_4011_);
v___x_4016_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*1, v___x_3981_);
v_s_3949_ = v___x_4016_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4061_; 
lean_dec_ref(v___x_3976_);
lean_dec(v_a_3965_);
lean_dec(v_hOut_3948_);
lean_dec_ref(v_cfg_3946_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v_s_3949_);
v___x_4061_ = v___x_3967_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_s_3949_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
v___jp_3969_:
{
lean_object* v___x_3972_; 
lean_inc_ref(v_a_3945_);
v___x_3972_ = lean_apply_4(v___y_3970_, v___y_3971_, v_s_3949_, v_a_3945_, lean_box(0));
v___y_3952_ = v___x_3972_;
goto v___jp_3951_;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4076_; 
lean_dec_ref(v_s_3949_);
lean_dec(v_hOut_3948_);
lean_dec_ref(v_cfg_3946_);
v_a_4064_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4066_ = v___x_3964_;
v_isShared_4067_ = v_isSharedCheck_4076_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_3964_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4076_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4068_ = lean_io_error_to_string(v_a_4064_);
v___x_4069_ = 3;
v___x_4070_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set_uint8(v___x_4070_, sizeof(void*)*1, v___x_4069_);
lean_inc_ref(v_a_3945_);
v___x_4071_ = lean_apply_2(v_a_3945_, v___x_4070_, lean_box(0));
v___x_4072_ = lean_box(0);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4072_);
v___x_4074_ = v___x_4066_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
v___jp_3951_:
{
if (lean_obj_tag(v___y_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v_snd_3954_; 
v_a_3953_ = lean_ctor_get(v___y_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref(v___y_3952_);
v_snd_3954_ = lean_ctor_get(v_a_3953_, 1);
lean_inc(v_snd_3954_);
lean_dec(v_a_3953_);
v_s_3949_ = v_snd_3954_;
goto _start;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_hOut_3948_);
lean_dec_ref(v_cfg_3946_);
v_a_3956_ = lean_ctor_get(v___y_3952_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___y_3952_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___y_3952_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___y_3952_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object* v_a_4077_, lean_object* v_cfg_4078_, lean_object* v_h_4079_, lean_object* v_hOut_4080_, lean_object* v_s_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4077_, v_cfg_4078_, v_h_4079_, v_hOut_4080_, v_s_4081_);
lean_dec(v_h_4079_);
lean_dec_ref(v_a_4077_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object* v_cfg_4084_, lean_object* v_h_4085_, lean_object* v_hOut_4086_, lean_object* v_s_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___y_4091_; lean_object* v___x_4103_; 
v___x_4103_ = lean_io_prim_handle_get_line(v_h_4085_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4199_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4199_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4199_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v_startInclusive_4112_; lean_object* v_endExclusive_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = lean_string_utf8_byte_size(v_a_4104_);
lean_inc(v_a_4104_);
v___x_4110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4110_, 0, v_a_4104_);
lean_ctor_set(v___x_4110_, 1, v___x_4108_);
lean_ctor_set(v___x_4110_, 2, v___x_4109_);
v___x_4111_ = l_String_Slice_trimAscii(v___x_4110_);
v_startInclusive_4112_ = lean_ctor_get(v___x_4111_, 1);
lean_inc(v_startInclusive_4112_);
v_endExclusive_4113_ = lean_ctor_get(v___x_4111_, 2);
lean_inc(v_endExclusive_4113_);
v___x_4114_ = lean_nat_sub(v_endExclusive_4113_, v_startInclusive_4112_);
lean_dec(v_startInclusive_4112_);
lean_dec(v_endExclusive_4113_);
v___x_4115_ = lean_nat_dec_eq(v___x_4114_, v___x_4108_);
lean_dec(v___x_4114_);
if (v___x_4115_ == 0)
{
uint8_t v___x_4116_; lean_object* v___y_4118_; lean_object* v_a_4136_; lean_object* v___x_4155_; 
lean_del_object(v___x_4106_);
v___x_4116_ = 1;
lean_inc(v_a_4104_);
v___x_4155_ = l_Lean_Json_parse(v_a_4104_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; 
lean_dec(v_a_4104_);
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___x_4155_);
v_a_4136_ = v_a_4156_;
goto v___jp_4135_;
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4157_);
lean_dec_ref(v___x_4155_);
v___x_4158_ = l_Lean_Json_getObj_x3f(v_a_4157_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; 
lean_dec(v_a_4104_);
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref(v___x_4158_);
v_a_4136_ = v_a_4159_;
goto v___jp_4135_;
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v___x_4158_);
v___x_4161_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4084_, v_a_4160_);
if (lean_obj_tag(v___x_4161_) == 1)
{
lean_object* v_val_4162_; lean_object* v_url_4163_; lean_object* v_path_4164_; lean_object* v_descr_4165_; lean_object* v___y_4167_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
lean_dec_ref(v___x_4111_);
v_val_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_val_4162_);
lean_dec_ref(v___x_4161_);
v_url_4163_ = lean_ctor_get(v_val_4162_, 0);
v_path_4164_ = lean_ctor_get(v_val_4162_, 1);
v_descr_4165_ = lean_ctor_get(v_val_4162_, 2);
v___x_4169_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4170_ = l_Lake_JsonObject_getJson_x3f(v_a_4160_, v___x_4169_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v___x_4171_; 
v___x_4171_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_4167_ = v___x_4171_;
goto v___jp_4166_;
}
else
{
lean_object* v_val_4172_; lean_object* v___x_4173_; 
v_val_4172_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_val_4172_);
lean_dec_ref(v___x_4170_);
v___x_4173_ = l_Lean_Json_getNat_x3f(v_val_4172_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4183_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4183_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4183_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v___x_4178_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4179_ = lean_string_append(v___x_4178_, v_a_4174_);
lean_dec(v_a_4174_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4179_);
v___x_4181_ = v___x_4176_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
v___y_4167_ = v___x_4181_;
goto v___jp_4166_;
}
}
}
else
{
if (lean_obj_tag(v___x_4173_) == 1)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v_a_4184_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4184_);
v___x_4185_ = lean_unsigned_to_nat(200u);
v___x_4186_ = lean_nat_dec_eq(v_a_4184_, v___x_4185_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; uint8_t v___x_4188_; 
v___x_4187_ = lean_unsigned_to_nat(201u);
v___x_4188_ = lean_nat_dec_eq(v_a_4184_, v___x_4187_);
lean_dec(v_a_4184_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; 
lean_inc_ref(v_cfg_4084_);
v___x_4189_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4084_, v_hOut_4086_, v_val_4162_, v_a_4160_, v_a_4104_, v___x_4116_, v___x_4173_, v_s_4087_, v_a_4088_);
lean_dec(v_a_4160_);
lean_dec(v_val_4162_);
v___y_4091_ = v___x_4189_;
goto v___jp_4090_;
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
lean_inc_ref(v_descr_4165_);
lean_inc_ref(v_path_4164_);
lean_inc_ref(v_url_4163_);
lean_dec_ref(v___x_4173_);
lean_dec(v_val_4162_);
lean_dec(v_a_4160_);
lean_dec(v_a_4104_);
v___x_4190_ = lean_box(0);
lean_inc_ref(v_cfg_4084_);
v___x_4191_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4084_, v_path_4164_, v___x_4116_, v_descr_4165_, v_url_4163_, v___x_4115_, v___x_4190_, v_s_4087_, v_a_4088_);
lean_dec_ref(v_url_4163_);
lean_dec_ref(v_descr_4165_);
v___y_4091_ = v___x_4191_;
goto v___jp_4090_;
}
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
lean_inc_ref(v_descr_4165_);
lean_inc_ref(v_path_4164_);
lean_inc_ref(v_url_4163_);
lean_dec_ref(v___x_4173_);
lean_dec(v_a_4184_);
lean_dec(v_val_4162_);
lean_dec(v_a_4160_);
lean_dec(v_a_4104_);
v___x_4192_ = lean_box(0);
lean_inc_ref(v_cfg_4084_);
v___x_4193_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4084_, v_path_4164_, v___x_4116_, v_descr_4165_, v_url_4163_, v___x_4115_, v___x_4192_, v_s_4087_, v_a_4088_);
lean_dec_ref(v_url_4163_);
lean_dec_ref(v_descr_4165_);
v___y_4091_ = v___x_4193_;
goto v___jp_4090_;
}
}
else
{
v___y_4167_ = v___x_4173_;
goto v___jp_4166_;
}
}
}
v___jp_4166_:
{
lean_object* v___x_4168_; 
lean_inc_ref(v_cfg_4084_);
v___x_4168_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4084_, v_hOut_4086_, v_val_4162_, v_a_4160_, v_a_4104_, v___x_4116_, v___y_4167_, v_s_4087_, v_a_4088_);
lean_dec(v_a_4160_);
lean_dec(v_val_4162_);
v___y_4091_ = v___x_4168_;
goto v___jp_4090_;
}
}
else
{
lean_object* v_scope_4194_; lean_object* v_s_4195_; 
lean_dec(v___x_4161_);
lean_dec(v_a_4160_);
lean_dec(v_a_4104_);
v_scope_4194_ = lean_ctor_get(v_cfg_4084_, 0);
v_s_4195_ = lean_ctor_get(v_scope_4194_, 0);
lean_inc_ref(v_s_4195_);
v___y_4118_ = v_s_4195_;
goto v___jp_4117_;
}
}
}
v___jp_4117_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v_numSuccesses_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4134_; 
v___x_4119_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4120_ = lean_string_append(v___y_4118_, v___x_4119_);
v___x_4121_ = l_String_Slice_toString(v___x_4111_);
lean_dec_ref(v___x_4111_);
v___x_4122_ = lean_string_append(v___x_4120_, v___x_4121_);
lean_dec_ref(v___x_4121_);
v___x_4123_ = 3;
v___x_4124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set_uint8(v___x_4124_, sizeof(void*)*1, v___x_4123_);
lean_inc_ref(v_a_4088_);
v___x_4125_ = lean_apply_2(v_a_4088_, v___x_4124_, lean_box(0));
v_numSuccesses_4126_ = lean_ctor_get(v_s_4087_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_s_4087_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4128_ = v_s_4087_;
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_numSuccesses_4126_);
lean_dec(v_s_4087_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_numSuccesses_4126_);
v___x_4131_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; 
lean_ctor_set_uint8(v___x_4131_, sizeof(void*)*1, v___x_4116_);
v___x_4132_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4088_, v_cfg_4084_, v_h_4085_, v_hOut_4086_, v___x_4131_);
return v___x_4132_;
}
}
}
v___jp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v_numSuccesses_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4154_; 
v___x_4137_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4138_ = lean_string_append(v___x_4137_, v_a_4136_);
lean_dec_ref(v_a_4136_);
v___x_4139_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4140_ = lean_string_append(v___x_4138_, v___x_4139_);
v___x_4141_ = l_String_Slice_toString(v___x_4111_);
lean_dec_ref(v___x_4111_);
v___x_4142_ = lean_string_append(v___x_4140_, v___x_4141_);
lean_dec_ref(v___x_4141_);
v___x_4143_ = 3;
v___x_4144_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set_uint8(v___x_4144_, sizeof(void*)*1, v___x_4143_);
lean_inc_ref(v_a_4088_);
v___x_4145_ = lean_apply_2(v_a_4088_, v___x_4144_, lean_box(0));
v_numSuccesses_4146_ = lean_ctor_get(v_s_4087_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_s_4087_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4148_ = v_s_4087_;
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_numSuccesses_4146_);
lean_dec(v_s_4087_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_numSuccesses_4146_);
v___x_4151_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; 
lean_ctor_set_uint8(v___x_4151_, sizeof(void*)*1, v___x_4116_);
v___x_4152_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4088_, v_cfg_4084_, v_h_4085_, v_hOut_4086_, v___x_4151_);
return v___x_4152_;
}
}
}
}
else
{
lean_object* v___x_4197_; 
lean_dec_ref(v___x_4111_);
lean_dec(v_a_4104_);
lean_dec(v_hOut_4086_);
lean_dec_ref(v_cfg_4084_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v_s_4087_);
v___x_4197_ = v___x_4106_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_s_4087_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v_s_4087_);
lean_dec(v_hOut_4086_);
lean_dec_ref(v_cfg_4084_);
v_a_4200_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4202_ = v___x_4103_;
v_isShared_4203_ = v_isSharedCheck_4212_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4103_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4212_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4204_ = lean_io_error_to_string(v_a_4200_);
v___x_4205_ = 3;
v___x_4206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4206_, 0, v___x_4204_);
lean_ctor_set_uint8(v___x_4206_, sizeof(void*)*1, v___x_4205_);
lean_inc_ref(v_a_4088_);
v___x_4207_ = lean_apply_2(v_a_4088_, v___x_4206_, lean_box(0));
v___x_4208_ = lean_box(0);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4208_);
v___x_4210_ = v___x_4202_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
v___jp_4090_:
{
if (lean_obj_tag(v___y_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v_snd_4093_; lean_object* v___x_4094_; 
v_a_4092_ = lean_ctor_get(v___y_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref(v___y_4091_);
v_snd_4093_ = lean_ctor_get(v_a_4092_, 1);
lean_inc(v_snd_4093_);
lean_dec(v_a_4092_);
v___x_4094_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4088_, v_cfg_4084_, v_h_4085_, v_hOut_4086_, v_snd_4093_);
return v___x_4094_;
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v_hOut_4086_);
lean_dec_ref(v_cfg_4084_);
v_a_4095_ = lean_ctor_get(v___y_4091_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___y_4091_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___y_4091_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___y_4091_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object* v_cfg_4213_, lean_object* v_h_4214_, lean_object* v_hOut_4215_, lean_object* v_s_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4213_, v_h_4214_, v_hOut_4215_, v_s_4216_, v_a_4217_);
lean_dec_ref(v_a_4217_);
lean_dec(v_h_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object* v_snd_4220_, lean_object* v___y_4221_, lean_object* v_a_x3f_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_io_remove_file(v_snd_4220_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4245_; 
v_a_4233_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4235_ = v___x_4224_;
v_isShared_4236_ = v_isSharedCheck_4245_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4224_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4245_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4237_ = lean_io_error_to_string(v_a_4233_);
v___x_4238_ = 3;
v___x_4239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*1, v___x_4238_);
lean_inc_ref(v___y_4221_);
v___x_4240_ = lean_apply_2(v___y_4221_, v___x_4239_, lean_box(0));
v___x_4241_ = lean_box(0);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v___x_4241_);
v___x_4243_ = v___x_4235_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object* v_snd_4246_, lean_object* v___y_4247_, lean_object* v_a_x3f_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4246_, v___y_4247_, v_a_x3f_4248_);
lean_dec(v_a_x3f_4248_);
lean_dec_ref(v___y_4247_);
lean_dec_ref(v_snd_4246_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object* v_f_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v_fst_4256_; lean_object* v_snd_4257_; lean_object* v_r_4258_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref(v___x_4254_);
v_fst_4256_ = lean_ctor_get(v_a_4255_, 0);
lean_inc(v_fst_4256_);
v_snd_4257_ = lean_ctor_get(v_a_4255_, 1);
lean_inc(v_snd_4257_);
lean_dec(v_a_4255_);
lean_inc_ref(v___y_4252_);
lean_inc(v_snd_4257_);
v_r_4258_ = lean_apply_4(v_f_4251_, v_fst_4256_, v_snd_4257_, v___y_4252_, lean_box(0));
if (lean_obj_tag(v_r_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4283_; 
v_a_4259_ = lean_ctor_get(v_r_4258_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_r_4258_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4261_ = v_r_4258_;
v_isShared_4262_ = v_isSharedCheck_4283_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v_r_4258_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4283_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
lean_inc(v_a_4259_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set_tag(v___x_4261_, 1);
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4257_, v___y_4252_, v___x_4264_);
lean_dec_ref(v___x_4264_);
lean_dec(v_snd_4257_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4272_ == 0)
{
lean_object* v_unused_4273_; 
v_unused_4273_ = lean_ctor_get(v___x_4265_, 0);
lean_dec(v_unused_4273_);
v___x_4267_ = v___x_4265_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_dec(v___x_4265_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 0, v_a_4259_);
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4259_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v_a_4259_);
v_a_4274_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4265_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4265_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v_a_4284_ = lean_ctor_get(v_r_4258_, 0);
lean_inc(v_a_4284_);
lean_dec_ref(v_r_4258_);
v___x_4285_ = lean_box(0);
v___x_4286_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4257_, v___y_4252_, v___x_4285_);
lean_dec(v_snd_4257_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4293_ == 0)
{
lean_object* v_unused_4294_; 
v_unused_4294_ = lean_ctor_get(v___x_4286_, 0);
lean_dec(v_unused_4294_);
v___x_4288_ = v___x_4286_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_dec(v___x_4286_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
lean_ctor_set_tag(v___x_4288_, 1);
lean_ctor_set(v___x_4288_, 0, v_a_4284_);
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4284_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec(v_a_4284_);
v_a_4295_ = lean_ctor_get(v___x_4286_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4286_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4286_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4286_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v_f_4251_);
v_a_4303_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4305_ = v___x_4254_;
v_isShared_4306_ = v_isSharedCheck_4315_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4254_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4315_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4307_; uint8_t v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4313_; 
v___x_4307_ = lean_io_error_to_string(v_a_4303_);
v___x_4308_ = 3;
v___x_4309_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4309_, 0, v___x_4307_);
lean_ctor_set_uint8(v___x_4309_, sizeof(void*)*1, v___x_4308_);
lean_inc_ref(v___y_4252_);
v___x_4310_ = lean_apply_2(v___y_4252_, v___x_4309_, lean_box(0));
v___x_4311_ = lean_box(0);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4311_);
v___x_4313_ = v___x_4305_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object* v_f_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4316_, v___y_4317_);
lean_dec_ref(v___y_4317_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object* v_00_u03b1_4320_, lean_object* v_f_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4321_, v___y_4322_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object* v_00_u03b1_4325_, lean_object* v_f_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(v_00_u03b1_4325_, v_f_4326_, v___y_4327_);
lean_dec_ref(v___y_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object* v_h_4332_, lean_object* v_as_4333_, size_t v_i_4334_, size_t v_stop_4335_, lean_object* v_b_4336_, lean_object* v___y_4337_){
_start:
{
uint8_t v___x_4339_; 
v___x_4339_ = lean_usize_dec_eq(v_i_4334_, v_stop_4335_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v_url_4341_; lean_object* v_path_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4340_ = lean_array_uget_borrowed(v_as_4333_, v_i_4334_);
v_url_4341_ = lean_ctor_get(v___x_4340_, 0);
v_path_4342_ = lean_ctor_get(v___x_4340_, 1);
v___x_4343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
v___x_4344_ = lean_string_append(v___x_4343_, v_url_4341_);
v___x_4345_ = l_IO_FS_Handle_putStrLn(v_h_4332_, v___x_4344_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
lean_dec_ref(v___x_4345_);
v___x_4346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1));
lean_inc_ref(v_path_4342_);
v___x_4347_ = l_String_quote(v_path_4342_);
v___x_4348_ = lean_string_append(v___x_4346_, v___x_4347_);
lean_dec_ref(v___x_4347_);
v___x_4349_ = l_IO_FS_Handle_putStrLn(v_h_4332_, v___x_4348_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; size_t v___x_4351_; size_t v___x_4352_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref(v___x_4349_);
v___x_4351_ = ((size_t)1ULL);
v___x_4352_ = lean_usize_add(v_i_4334_, v___x_4351_);
v_i_4334_ = v___x_4352_;
v_b_4336_ = v_a_4350_;
goto _start;
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4366_; 
v_a_4354_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4356_ = v___x_4349_;
v_isShared_4357_ = v_isSharedCheck_4366_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4349_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4366_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4364_; 
v___x_4358_ = lean_io_error_to_string(v_a_4354_);
v___x_4359_ = 3;
v___x_4360_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set_uint8(v___x_4360_, sizeof(void*)*1, v___x_4359_);
lean_inc_ref(v___y_4337_);
v___x_4361_ = lean_apply_2(v___y_4337_, v___x_4360_, lean_box(0));
v___x_4362_ = lean_box(0);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4362_);
v___x_4364_ = v___x_4356_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4362_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4379_; 
v_a_4367_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4369_ = v___x_4345_;
v_isShared_4370_ = v_isSharedCheck_4379_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4345_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4379_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; uint8_t v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
v___x_4371_ = lean_io_error_to_string(v_a_4367_);
v___x_4372_ = 3;
v___x_4373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set_uint8(v___x_4373_, sizeof(void*)*1, v___x_4372_);
lean_inc_ref(v___y_4337_);
v___x_4374_ = lean_apply_2(v___y_4337_, v___x_4373_, lean_box(0));
v___x_4375_ = lean_box(0);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4375_);
v___x_4377_ = v___x_4369_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v___x_4380_; 
v___x_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4380_, 0, v_b_4336_);
return v___x_4380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object* v_h_4381_, lean_object* v_as_4382_, lean_object* v_i_4383_, lean_object* v_stop_4384_, lean_object* v_b_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
size_t v_i_boxed_4388_; size_t v_stop_boxed_4389_; lean_object* v_res_4390_; 
v_i_boxed_4388_ = lean_unbox_usize(v_i_4383_);
lean_dec(v_i_4383_);
v_stop_boxed_4389_ = lean_unbox_usize(v_stop_4384_);
lean_dec(v_stop_4384_);
v_res_4390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4381_, v_as_4382_, v_i_boxed_4388_, v_stop_boxed_4389_, v_b_4385_, v___y_4386_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v_as_4382_);
lean_dec(v_h_4381_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object* v_h_4392_, lean_object* v_as_4393_, size_t v_i_4394_, size_t v_stop_4395_, lean_object* v_b_4396_, lean_object* v___y_4397_){
_start:
{
uint8_t v___x_4399_; 
v___x_4399_ = lean_usize_dec_eq(v_i_4394_, v_stop_4395_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v_url_4401_; lean_object* v_path_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4400_ = lean_array_uget_borrowed(v_as_4393_, v_i_4394_);
v_url_4401_ = lean_ctor_get(v___x_4400_, 0);
v_path_4402_ = lean_ctor_get(v___x_4400_, 1);
v___x_4403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0));
lean_inc_ref(v_path_4402_);
v___x_4404_ = l_String_quote(v_path_4402_);
v___x_4405_ = lean_string_append(v___x_4403_, v___x_4404_);
lean_dec_ref(v___x_4404_);
v___x_4406_ = l_IO_FS_Handle_putStrLn(v_h_4392_, v___x_4405_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
lean_dec_ref(v___x_4406_);
v___x_4407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
v___x_4408_ = lean_string_append(v___x_4407_, v_url_4401_);
v___x_4409_ = l_IO_FS_Handle_putStrLn(v_h_4392_, v___x_4408_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; size_t v___x_4411_; size_t v___x_4412_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref(v___x_4409_);
v___x_4411_ = ((size_t)1ULL);
v___x_4412_ = lean_usize_add(v_i_4394_, v___x_4411_);
v_i_4394_ = v___x_4412_;
v_b_4396_ = v_a_4410_;
goto _start;
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4426_; 
v_a_4414_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4416_ = v___x_4409_;
v_isShared_4417_ = v_isSharedCheck_4426_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4409_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4426_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4418_ = lean_io_error_to_string(v_a_4414_);
v___x_4419_ = 3;
v___x_4420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set_uint8(v___x_4420_, sizeof(void*)*1, v___x_4419_);
lean_inc_ref(v___y_4397_);
v___x_4421_ = lean_apply_2(v___y_4397_, v___x_4420_, lean_box(0));
v___x_4422_ = lean_box(0);
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4422_);
v___x_4424_ = v___x_4416_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4439_; 
v_a_4427_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4429_ = v___x_4406_;
v_isShared_4430_ = v_isSharedCheck_4439_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4406_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4439_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; uint8_t v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4431_ = lean_io_error_to_string(v_a_4427_);
v___x_4432_ = 3;
v___x_4433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4433_, 0, v___x_4431_);
lean_ctor_set_uint8(v___x_4433_, sizeof(void*)*1, v___x_4432_);
lean_inc_ref(v___y_4397_);
v___x_4434_ = lean_apply_2(v___y_4397_, v___x_4433_, lean_box(0));
v___x_4435_ = lean_box(0);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4435_);
v___x_4437_ = v___x_4429_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
else
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v_b_4396_);
return v___x_4440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object* v_h_4441_, lean_object* v_as_4442_, lean_object* v_i_4443_, lean_object* v_stop_4444_, lean_object* v_b_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
size_t v_i_boxed_4448_; size_t v_stop_boxed_4449_; lean_object* v_res_4450_; 
v_i_boxed_4448_ = lean_unbox_usize(v_i_4443_);
lean_dec(v_i_4443_);
v_stop_boxed_4449_ = lean_unbox_usize(v_stop_4444_);
lean_dec(v_stop_4444_);
v_res_4450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4441_, v_as_4442_, v_i_boxed_4448_, v_stop_boxed_4449_, v_b_4445_, v___y_4446_);
lean_dec_ref(v___y_4446_);
lean_dec_ref(v_as_4442_);
lean_dec(v_h_4441_);
return v_res_4450_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4466_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4467_ = lean_unsigned_to_nat(11u);
v___x_4468_ = lean_mk_empty_array_with_capacity(v___x_4467_);
v___x_4469_ = lean_array_push(v___x_4468_, v___x_4466_);
return v___x_4469_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4470_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4471_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11);
v___x_4472_ = lean_array_push(v___x_4471_, v___x_4470_);
return v___x_4472_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4473_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6));
v___x_4474_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12);
v___x_4475_ = lean_array_push(v___x_4474_, v___x_4473_);
return v___x_4475_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4476_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4477_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13);
v___x_4478_ = lean_array_push(v___x_4477_, v___x_4476_);
return v___x_4478_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4479_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4480_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14);
v___x_4481_ = lean_array_push(v___x_4480_, v___x_4479_);
return v___x_4481_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16(void){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4482_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4483_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15);
v___x_4484_ = lean_array_push(v___x_4483_, v___x_4482_);
return v___x_4484_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4485_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4486_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16);
v___x_4487_ = lean_array_push(v___x_4486_, v___x_4485_);
return v___x_4487_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4489_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17);
v___x_4490_ = lean_array_push(v___x_4489_, v___x_4488_);
return v___x_4490_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19(void){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4492_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18);
v___x_4493_ = lean_array_push(v___x_4492_, v___x_4491_);
return v___x_4493_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4495_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19);
v___x_4496_ = lean_array_push(v___x_4495_, v___x_4494_);
return v___x_4496_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4498_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4499_ = lean_unsigned_to_nat(17u);
v___x_4500_ = lean_mk_empty_array_with_capacity(v___x_4499_);
v___x_4501_ = lean_array_push(v___x_4500_, v___x_4498_);
return v___x_4501_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4503_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22);
v___x_4504_ = lean_array_push(v___x_4503_, v___x_4502_);
return v___x_4504_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_4506_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23);
v___x_4507_ = lean_array_push(v___x_4506_, v___x_4505_);
return v___x_4507_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25(void){
_start:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4509_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24);
v___x_4510_ = lean_array_push(v___x_4509_, v___x_4508_);
return v___x_4510_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26(void){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_4512_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25);
v___x_4513_ = lean_array_push(v___x_4512_, v___x_4511_);
return v___x_4513_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21));
v___x_4515_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26);
v___x_4516_ = lean_array_push(v___x_4515_, v___x_4514_);
return v___x_4516_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4518_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27);
v___x_4519_ = lean_array_push(v___x_4518_, v___x_4517_);
return v___x_4519_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29(void){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4521_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28);
v___x_4522_ = lean_array_push(v___x_4521_, v___x_4520_);
return v___x_4522_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30(void){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4523_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_4524_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29);
v___x_4525_ = lean_array_push(v___x_4524_, v___x_4523_);
return v___x_4525_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31(void){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_4527_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30);
v___x_4528_ = lean_array_push(v___x_4527_, v___x_4526_);
return v___x_4528_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_4530_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31);
v___x_4531_ = lean_array_push(v___x_4530_, v___x_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object* v_cfg_4532_, lean_object* v_h_4533_, lean_object* v_path_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___y_4538_; lean_object* v___y_4544_; uint8_t v___y_4545_; uint32_t v___y_4546_; lean_object* v___y_4547_; uint8_t v_kind_4556_; lean_object* v_scope_4557_; lean_object* v_infos_4558_; lean_object* v_key_4559_; uint8_t v___y_4561_; uint32_t v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4568_; lean_object* v___y_4569_; uint8_t v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; uint32_t v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4586_; lean_object* v___y_4587_; uint8_t v___y_4588_; uint32_t v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; uint8_t v___y_4598_; uint32_t v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4610_; lean_object* v___y_4611_; uint8_t v___y_4612_; uint32_t v___y_4613_; lean_object* v___y_4614_; lean_object* v_a_4617_; lean_object* v___y_4711_; lean_object* v___y_4739_; 
v_kind_4556_ = lean_ctor_get_uint8(v_cfg_4532_, sizeof(void*)*3);
v_scope_4557_ = lean_ctor_get(v_cfg_4532_, 0);
lean_inc_ref(v_scope_4557_);
v_infos_4558_ = lean_ctor_get(v_cfg_4532_, 1);
lean_inc_ref(v_infos_4558_);
v_key_4559_ = lean_ctor_get(v_cfg_4532_, 2);
if (v_kind_4556_ == 0)
{
lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4740_ = lean_unsigned_to_nat(0u);
v___x_4741_ = lean_array_get_size(v_infos_4558_);
v___x_4742_ = lean_nat_dec_lt(v___x_4740_, v___x_4741_);
if (v___x_4742_ == 0)
{
goto v___jp_4693_;
}
else
{
lean_object* v___x_4743_; uint8_t v___x_4744_; 
v___x_4743_ = lean_box(0);
v___x_4744_ = lean_nat_dec_le(v___x_4741_, v___x_4741_);
if (v___x_4744_ == 0)
{
if (v___x_4742_ == 0)
{
goto v___jp_4693_;
}
else
{
size_t v___x_4745_; size_t v___x_4746_; lean_object* v___x_4747_; 
v___x_4745_ = ((size_t)0ULL);
v___x_4746_ = lean_usize_of_nat(v___x_4741_);
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4533_, v_infos_4558_, v___x_4745_, v___x_4746_, v___x_4743_, v___y_4535_);
v___y_4711_ = v___x_4747_;
goto v___jp_4710_;
}
}
else
{
size_t v___x_4748_; size_t v___x_4749_; lean_object* v___x_4750_; 
v___x_4748_ = ((size_t)0ULL);
v___x_4749_ = lean_usize_of_nat(v___x_4741_);
v___x_4750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4533_, v_infos_4558_, v___x_4748_, v___x_4749_, v___x_4743_, v___y_4535_);
v___y_4711_ = v___x_4750_;
goto v___jp_4710_;
}
}
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4751_ = lean_unsigned_to_nat(0u);
v___x_4752_ = lean_array_get_size(v_infos_4558_);
v___x_4753_ = lean_nat_dec_lt(v___x_4751_, v___x_4752_);
if (v___x_4753_ == 0)
{
goto v___jp_4712_;
}
else
{
lean_object* v___x_4754_; uint8_t v___x_4755_; 
v___x_4754_ = lean_box(0);
v___x_4755_ = lean_nat_dec_le(v___x_4752_, v___x_4752_);
if (v___x_4755_ == 0)
{
if (v___x_4753_ == 0)
{
goto v___jp_4712_;
}
else
{
size_t v___x_4756_; size_t v___x_4757_; lean_object* v___x_4758_; 
v___x_4756_ = ((size_t)0ULL);
v___x_4757_ = lean_usize_of_nat(v___x_4752_);
v___x_4758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4533_, v_infos_4558_, v___x_4756_, v___x_4757_, v___x_4754_, v___y_4535_);
v___y_4739_ = v___x_4758_;
goto v___jp_4738_;
}
}
else
{
size_t v___x_4759_; size_t v___x_4760_; lean_object* v___x_4761_; 
v___x_4759_ = ((size_t)0ULL);
v___x_4760_ = lean_usize_of_nat(v___x_4752_);
v___x_4761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4533_, v_infos_4558_, v___x_4759_, v___x_4760_, v___x_4754_, v___y_4535_);
v___y_4739_ = v___x_4761_;
goto v___jp_4738_;
}
}
}
v___jp_4537_:
{
if (v___y_4538_ == 0)
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = lean_box(0);
v___x_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
v___jp_4543_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4548_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_4549_ = lean_string_append(v___y_4547_, v___x_4548_);
v___x_4550_ = lean_uint32_to_nat(v___y_4546_);
v___x_4551_ = l_Nat_reprFast(v___x_4550_);
v___x_4552_ = lean_string_append(v___x_4549_, v___x_4551_);
lean_dec_ref(v___x_4551_);
v___x_4553_ = 3;
v___x_4554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set_uint8(v___x_4554_, sizeof(void*)*1, v___x_4553_);
lean_inc_ref(v___y_4544_);
v___x_4555_ = lean_apply_2(v___y_4544_, v___x_4554_, lean_box(0));
v___y_4538_ = v___y_4545_;
goto v___jp_4537_;
}
v___jp_4560_:
{
uint32_t v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = 0;
v___x_4565_ = lean_uint32_dec_eq(v___y_4562_, v___x_4564_);
if (v___x_4565_ == 0)
{
lean_object* v_s_4566_; 
v_s_4566_ = lean_ctor_get(v_scope_4557_, 0);
lean_inc_ref(v_s_4566_);
lean_dec_ref(v_scope_4557_);
v___y_4544_ = v___y_4563_;
v___y_4545_ = v___y_4561_;
v___y_4546_ = v___y_4562_;
v___y_4547_ = v_s_4566_;
goto v___jp_4543_;
}
else
{
lean_dec_ref(v_scope_4557_);
v___y_4538_ = v___y_4561_;
goto v___jp_4537_;
}
}
v___jp_4567_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4575_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_4576_ = lean_string_append(v___y_4574_, v___x_4575_);
lean_inc(v___y_4571_);
lean_inc(v___y_4568_);
lean_inc_ref(v___y_4569_);
v___x_4577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4577_, 0, v___y_4569_);
lean_ctor_set(v___x_4577_, 1, v___y_4568_);
lean_ctor_set(v___x_4577_, 2, v___y_4571_);
v___x_4578_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_4577_, v___y_4571_);
lean_dec_ref(v___x_4577_);
v___x_4579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4579_, 0, v___y_4569_);
lean_ctor_set(v___x_4579_, 1, v___y_4568_);
lean_ctor_set(v___x_4579_, 2, v___x_4578_);
v___x_4580_ = l_String_Slice_toString(v___x_4579_);
lean_dec_ref(v___x_4579_);
v___x_4581_ = lean_string_append(v___x_4576_, v___x_4580_);
lean_dec_ref(v___x_4580_);
v___x_4582_ = 2;
v___x_4583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4583_, 0, v___x_4581_);
lean_ctor_set_uint8(v___x_4583_, sizeof(void*)*1, v___x_4582_);
lean_inc_ref(v___y_4572_);
v___x_4584_ = lean_apply_2(v___y_4572_, v___x_4583_, lean_box(0));
v___y_4561_ = v___y_4570_;
v___y_4562_ = v___y_4573_;
v___y_4563_ = v___y_4572_;
goto v___jp_4560_;
}
v___jp_4585_:
{
lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4591_ = lean_string_utf8_byte_size(v___y_4587_);
v___x_4592_ = lean_nat_dec_eq(v___x_4591_, v___y_4586_);
if (v___x_4592_ == 0)
{
lean_object* v_s_4593_; 
v_s_4593_ = lean_ctor_get(v_scope_4557_, 0);
lean_inc_ref(v_s_4593_);
v___y_4568_ = v___y_4586_;
v___y_4569_ = v___y_4587_;
v___y_4570_ = v___y_4588_;
v___y_4571_ = v___x_4591_;
v___y_4572_ = v___y_4590_;
v___y_4573_ = v___y_4589_;
v___y_4574_ = v_s_4593_;
goto v___jp_4567_;
}
else
{
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
v___y_4561_ = v___y_4588_;
v___y_4562_ = v___y_4589_;
v___y_4563_ = v___y_4590_;
goto v___jp_4560_;
}
}
v___jp_4594_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4601_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_4602_ = lean_string_append(v___y_4600_, v___x_4601_);
v___x_4603_ = lean_string_append(v___x_4602_, v___y_4596_);
lean_dec_ref(v___y_4596_);
v___x_4604_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_4605_ = lean_string_append(v___x_4603_, v___x_4604_);
v___x_4606_ = 3;
v___x_4607_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4607_, 0, v___x_4605_);
lean_ctor_set_uint8(v___x_4607_, sizeof(void*)*1, v___x_4606_);
lean_inc_ref(v___y_4535_);
v___x_4608_ = lean_apply_2(v___y_4535_, v___x_4607_, lean_box(0));
v___y_4586_ = v___y_4595_;
v___y_4587_ = v___y_4597_;
v___y_4588_ = v___y_4598_;
v___y_4589_ = v___y_4599_;
v___y_4590_ = v___y_4535_;
goto v___jp_4585_;
}
v___jp_4609_:
{
lean_object* v_s_4615_; 
v_s_4615_ = lean_ctor_get(v_scope_4557_, 0);
lean_inc_ref(v_s_4615_);
v___y_4595_ = v___y_4610_;
v___y_4596_ = v___y_4614_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v_s_4615_;
goto v___jp_4594_;
}
v___jp_4616_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; uint8_t v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4618_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_4619_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_4620_ = lean_box(0);
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_4623_ = 1;
v___x_4624_ = 0;
v___x_4625_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4625_, 0, v___x_4618_);
lean_ctor_set(v___x_4625_, 1, v___x_4619_);
lean_ctor_set(v___x_4625_, 2, v_a_4617_);
lean_ctor_set(v___x_4625_, 3, v___x_4620_);
lean_ctor_set(v___x_4625_, 4, v___x_4622_);
lean_ctor_set_uint8(v___x_4625_, sizeof(void*)*5, v___x_4623_);
lean_ctor_set_uint8(v___x_4625_, sizeof(void*)*5 + 1, v___x_4624_);
v___x_4626_ = lean_io_process_spawn(v___x_4625_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v_stdout_4628_; lean_object* v_stderr_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref(v___x_4626_);
v_stdout_4628_ = lean_ctor_get(v_a_4627_, 1);
lean_inc(v_stdout_4628_);
v_stderr_4629_ = lean_ctor_get(v_a_4627_, 2);
v___x_4630_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
lean_inc(v_stdout_4628_);
v___x_4631_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4532_, v_stderr_4629_, v_stdout_4628_, v___x_4630_, v___y_4535_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref(v___x_4631_);
v___x_4633_ = lean_io_process_child_wait(v___x_4618_, v_a_4627_);
lean_dec(v_a_4627_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4635_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref(v___x_4633_);
v___x_4635_ = l_IO_FS_Handle_readToEnd(v_stdout_4628_);
lean_dec(v_stdout_4628_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; uint8_t v_didError_4637_; lean_object* v_numSuccesses_4638_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref(v___x_4635_);
v_didError_4637_ = lean_ctor_get_uint8(v_a_4632_, sizeof(void*)*1);
v_numSuccesses_4638_ = lean_ctor_get(v_a_4632_, 0);
lean_inc(v_numSuccesses_4638_);
lean_dec(v_a_4632_);
v___x_4639_ = lean_array_get_size(v_infos_4558_);
lean_dec_ref(v_infos_4558_);
v___x_4640_ = lean_nat_dec_lt(v_numSuccesses_4638_, v___x_4639_);
lean_dec(v_numSuccesses_4638_);
if (v___x_4640_ == 0)
{
uint32_t v___x_4641_; 
v___x_4641_ = lean_unbox_uint32(v_a_4634_);
lean_dec(v_a_4634_);
v___y_4586_ = v___x_4621_;
v___y_4587_ = v_a_4636_;
v___y_4588_ = v_didError_4637_;
v___y_4589_ = v___x_4641_;
v___y_4590_ = v___y_4535_;
goto v___jp_4585_;
}
else
{
if (v_kind_4556_ == 0)
{
lean_object* v___x_4642_; uint32_t v___x_4643_; 
v___x_4642_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_4643_ = lean_unbox_uint32(v_a_4634_);
lean_dec(v_a_4634_);
v___y_4610_ = v___x_4621_;
v___y_4611_ = v_a_4636_;
v___y_4612_ = v_didError_4637_;
v___y_4613_ = v___x_4643_;
v___y_4614_ = v___x_4642_;
goto v___jp_4609_;
}
else
{
lean_object* v___x_4644_; uint32_t v___x_4645_; 
v___x_4644_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_4645_ = lean_unbox_uint32(v_a_4634_);
lean_dec(v_a_4634_);
v___y_4610_ = v___x_4621_;
v___y_4611_ = v_a_4636_;
v___y_4612_ = v_didError_4637_;
v___y_4613_ = v___x_4645_;
v___y_4614_ = v___x_4644_;
goto v___jp_4609_;
}
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4658_; 
lean_dec(v_a_4634_);
lean_dec(v_a_4632_);
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
v_a_4646_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4648_ = v___x_4635_;
v_isShared_4649_ = v_isSharedCheck_4658_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4635_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4658_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4650_; uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
v___x_4650_ = lean_io_error_to_string(v_a_4646_);
v___x_4651_ = 3;
v___x_4652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set_uint8(v___x_4652_, sizeof(void*)*1, v___x_4651_);
lean_inc_ref(v___y_4535_);
v___x_4653_ = lean_apply_2(v___y_4535_, v___x_4652_, lean_box(0));
v___x_4654_ = lean_box(0);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 0, v___x_4654_);
v___x_4656_ = v___x_4648_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4654_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4671_; 
lean_dec(v_a_4632_);
lean_dec(v_stdout_4628_);
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
v_a_4659_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4661_ = v___x_4633_;
v_isShared_4662_ = v_isSharedCheck_4671_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4633_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4671_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4663_; uint8_t v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4669_; 
v___x_4663_ = lean_io_error_to_string(v_a_4659_);
v___x_4664_ = 3;
v___x_4665_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4665_, 0, v___x_4663_);
lean_ctor_set_uint8(v___x_4665_, sizeof(void*)*1, v___x_4664_);
lean_inc_ref(v___y_4535_);
v___x_4666_ = lean_apply_2(v___y_4535_, v___x_4665_, lean_box(0));
v___x_4667_ = lean_box(0);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4667_);
v___x_4669_ = v___x_4661_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec(v_stdout_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
v_a_4672_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4631_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4631_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4692_; 
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
lean_dec_ref(v_cfg_4532_);
v_a_4680_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4682_ = v___x_4626_;
v_isShared_4683_ = v_isSharedCheck_4692_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4626_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4692_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; 
v___x_4684_ = lean_io_error_to_string(v_a_4680_);
v___x_4685_ = 3;
v___x_4686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4686_, 0, v___x_4684_);
lean_ctor_set_uint8(v___x_4686_, sizeof(void*)*1, v___x_4685_);
lean_inc_ref(v___y_4535_);
v___x_4687_ = lean_apply_2(v___y_4535_, v___x_4686_, lean_box(0));
v___x_4688_ = lean_box(0);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4688_);
v___x_4690_ = v___x_4682_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
v___jp_4693_:
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_io_prim_handle_flush(v_h_4533_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
lean_dec_ref(v___x_4694_);
v___x_4695_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_4696_ = lean_array_push(v___x_4695_, v_path_4534_);
v_a_4617_ = v___x_4696_;
goto v___jp_4616_;
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4709_; 
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
lean_dec_ref(v_path_4534_);
lean_dec_ref(v_cfg_4532_);
v_a_4697_ = lean_ctor_get(v___x_4694_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4694_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4699_ = v___x_4694_;
v_isShared_4700_ = v_isSharedCheck_4709_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4694_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4709_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4707_; 
v___x_4701_ = lean_io_error_to_string(v_a_4697_);
v___x_4702_ = 3;
v___x_4703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4703_, 0, v___x_4701_);
lean_ctor_set_uint8(v___x_4703_, sizeof(void*)*1, v___x_4702_);
lean_inc_ref(v___y_4535_);
v___x_4704_ = lean_apply_2(v___y_4535_, v___x_4703_, lean_box(0));
v___x_4705_ = lean_box(0);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v___x_4705_);
v___x_4707_ = v___x_4699_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
v___jp_4710_:
{
if (lean_obj_tag(v___y_4711_) == 0)
{
lean_dec_ref(v___y_4711_);
goto v___jp_4693_;
}
else
{
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
lean_dec_ref(v_path_4534_);
lean_dec_ref(v_cfg_4532_);
return v___y_4711_;
}
}
v___jp_4712_:
{
lean_object* v___x_4713_; 
v___x_4713_ = lean_io_prim_handle_flush(v_h_4533_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
lean_dec_ref(v___x_4713_);
v___x_4714_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4715_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4716_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4717_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4718_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_4559_);
v___x_4719_ = lean_array_push(v___x_4718_, v_key_4559_);
v___x_4720_ = lean_array_push(v___x_4719_, v___x_4714_);
v___x_4721_ = lean_array_push(v___x_4720_, v___x_4715_);
v___x_4722_ = lean_array_push(v___x_4721_, v___x_4716_);
v___x_4723_ = lean_array_push(v___x_4722_, v___x_4717_);
v___x_4724_ = lean_array_push(v___x_4723_, v_path_4534_);
v_a_4617_ = v___x_4724_;
goto v___jp_4616_;
}
else
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4737_; 
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
lean_dec_ref(v_path_4534_);
lean_dec_ref(v_cfg_4532_);
v_a_4725_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4727_ = v___x_4713_;
v_isShared_4728_ = v_isSharedCheck_4737_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4713_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4737_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4729_; uint8_t v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4735_; 
v___x_4729_ = lean_io_error_to_string(v_a_4725_);
v___x_4730_ = 3;
v___x_4731_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4731_, 0, v___x_4729_);
lean_ctor_set_uint8(v___x_4731_, sizeof(void*)*1, v___x_4730_);
lean_inc_ref(v___y_4535_);
v___x_4732_ = lean_apply_2(v___y_4535_, v___x_4731_, lean_box(0));
v___x_4733_ = lean_box(0);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4733_);
v___x_4735_ = v___x_4727_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4733_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
v___jp_4738_:
{
if (lean_obj_tag(v___y_4739_) == 0)
{
lean_dec_ref(v___y_4739_);
goto v___jp_4712_;
}
else
{
lean_dec_ref(v_infos_4558_);
lean_dec_ref(v_scope_4557_);
lean_dec_ref(v_path_4534_);
lean_dec_ref(v_cfg_4532_);
return v___y_4739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object* v_cfg_4762_, lean_object* v_h_4763_, lean_object* v_path_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(v_cfg_4762_, v_h_4763_, v_path_4764_, v___y_4765_);
lean_dec_ref(v___y_4765_);
lean_dec(v_h_4763_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object* v_cfg_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___f_4771_; lean_object* v___x_4772_; 
v___f_4771_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4771_, 0, v_cfg_4768_);
v___x_4772_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_4771_, v_a_4769_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object* v_cfg_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(v_cfg_4773_, v_a_4774_);
lean_dec_ref(v_a_4774_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object* v_cfg_4777_, lean_object* v_h_4778_, lean_object* v_path_4779_, lean_object* v___y_4780_){
_start:
{
uint8_t v___y_4783_; uint8_t v___y_4789_; lean_object* v___y_4790_; uint32_t v___y_4791_; lean_object* v___y_4792_; uint8_t v_kind_4801_; lean_object* v_scope_4802_; lean_object* v_infos_4803_; lean_object* v_key_4804_; uint8_t v___y_4806_; uint32_t v___y_4807_; lean_object* v___y_4808_; uint8_t v___y_4813_; uint32_t v___y_4814_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4819_; uint8_t v___y_4831_; uint32_t v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4840_; uint8_t v___y_4841_; uint32_t v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; uint8_t v___y_4855_; uint32_t v___y_4856_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v_a_4862_; lean_object* v___y_4958_; lean_object* v___y_4988_; 
v_kind_4801_ = lean_ctor_get_uint8(v_cfg_4777_, sizeof(void*)*3);
v_scope_4802_ = lean_ctor_get(v_cfg_4777_, 0);
lean_inc_ref(v_scope_4802_);
v_infos_4803_ = lean_ctor_get(v_cfg_4777_, 1);
lean_inc_ref(v_infos_4803_);
v_key_4804_ = lean_ctor_get(v_cfg_4777_, 2);
if (v_kind_4801_ == 0)
{
lean_object* v___x_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; 
v___x_4989_ = lean_unsigned_to_nat(0u);
v___x_4990_ = lean_array_get_size(v_infos_4803_);
v___x_4991_ = lean_nat_dec_lt(v___x_4989_, v___x_4990_);
if (v___x_4991_ == 0)
{
goto v___jp_4938_;
}
else
{
lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4992_ = lean_box(0);
v___x_4993_ = lean_nat_dec_le(v___x_4990_, v___x_4990_);
if (v___x_4993_ == 0)
{
if (v___x_4991_ == 0)
{
goto v___jp_4938_;
}
else
{
size_t v___x_4994_; size_t v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = ((size_t)0ULL);
v___x_4995_ = lean_usize_of_nat(v___x_4990_);
v___x_4996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4778_, v_infos_4803_, v___x_4994_, v___x_4995_, v___x_4992_, v___y_4780_);
v___y_4958_ = v___x_4996_;
goto v___jp_4957_;
}
}
else
{
size_t v___x_4997_; size_t v___x_4998_; lean_object* v___x_4999_; 
v___x_4997_ = ((size_t)0ULL);
v___x_4998_ = lean_usize_of_nat(v___x_4990_);
v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4778_, v_infos_4803_, v___x_4997_, v___x_4998_, v___x_4992_, v___y_4780_);
v___y_4958_ = v___x_4999_;
goto v___jp_4957_;
}
}
}
else
{
lean_object* v___x_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v___x_5000_ = lean_unsigned_to_nat(0u);
v___x_5001_ = lean_array_get_size(v_infos_4803_);
v___x_5002_ = lean_nat_dec_lt(v___x_5000_, v___x_5001_);
if (v___x_5002_ == 0)
{
goto v___jp_4959_;
}
else
{
lean_object* v___x_5003_; uint8_t v___x_5004_; 
v___x_5003_ = lean_box(0);
v___x_5004_ = lean_nat_dec_le(v___x_5001_, v___x_5001_);
if (v___x_5004_ == 0)
{
if (v___x_5002_ == 0)
{
goto v___jp_4959_;
}
else
{
size_t v___x_5005_; size_t v___x_5006_; lean_object* v___x_5007_; 
v___x_5005_ = ((size_t)0ULL);
v___x_5006_ = lean_usize_of_nat(v___x_5001_);
v___x_5007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4778_, v_infos_4803_, v___x_5005_, v___x_5006_, v___x_5003_, v___y_4780_);
v___y_4988_ = v___x_5007_;
goto v___jp_4987_;
}
}
else
{
size_t v___x_5008_; size_t v___x_5009_; lean_object* v___x_5010_; 
v___x_5008_ = ((size_t)0ULL);
v___x_5009_ = lean_usize_of_nat(v___x_5001_);
v___x_5010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4778_, v_infos_4803_, v___x_5008_, v___x_5009_, v___x_5003_, v___y_4780_);
v___y_4988_ = v___x_5010_;
goto v___jp_4987_;
}
}
}
v___jp_4782_:
{
if (v___y_4783_ == 0)
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_box(0);
v___x_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
else
{
lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4786_ = lean_box(0);
v___x_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
return v___x_4787_;
}
}
v___jp_4788_:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4793_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_4794_ = lean_string_append(v___y_4792_, v___x_4793_);
v___x_4795_ = lean_uint32_to_nat(v___y_4791_);
v___x_4796_ = l_Nat_reprFast(v___x_4795_);
v___x_4797_ = lean_string_append(v___x_4794_, v___x_4796_);
lean_dec_ref(v___x_4796_);
v___x_4798_ = 3;
v___x_4799_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4799_, 0, v___x_4797_);
lean_ctor_set_uint8(v___x_4799_, sizeof(void*)*1, v___x_4798_);
lean_inc_ref(v___y_4790_);
v___x_4800_ = lean_apply_2(v___y_4790_, v___x_4799_, lean_box(0));
v___y_4783_ = v___y_4789_;
goto v___jp_4782_;
}
v___jp_4805_:
{
uint32_t v___x_4809_; uint8_t v___x_4810_; 
v___x_4809_ = 0;
v___x_4810_ = lean_uint32_dec_eq(v___y_4807_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v_s_4811_; 
v_s_4811_ = lean_ctor_get(v_scope_4802_, 0);
lean_inc_ref(v_s_4811_);
lean_dec_ref(v_scope_4802_);
v___y_4789_ = v___y_4806_;
v___y_4790_ = v___y_4808_;
v___y_4791_ = v___y_4807_;
v___y_4792_ = v_s_4811_;
goto v___jp_4788_;
}
else
{
lean_dec_ref(v_scope_4802_);
v___y_4783_ = v___y_4806_;
goto v___jp_4782_;
}
}
v___jp_4812_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4820_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_4821_ = lean_string_append(v___y_4819_, v___x_4820_);
lean_inc(v___y_4816_);
lean_inc(v___y_4817_);
lean_inc_ref(v___y_4818_);
v___x_4822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4822_, 0, v___y_4818_);
lean_ctor_set(v___x_4822_, 1, v___y_4817_);
lean_ctor_set(v___x_4822_, 2, v___y_4816_);
v___x_4823_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_4822_, v___y_4816_);
lean_dec_ref(v___x_4822_);
v___x_4824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4824_, 0, v___y_4818_);
lean_ctor_set(v___x_4824_, 1, v___y_4817_);
lean_ctor_set(v___x_4824_, 2, v___x_4823_);
v___x_4825_ = l_String_Slice_toString(v___x_4824_);
lean_dec_ref(v___x_4824_);
v___x_4826_ = lean_string_append(v___x_4821_, v___x_4825_);
lean_dec_ref(v___x_4825_);
v___x_4827_ = 2;
v___x_4828_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set_uint8(v___x_4828_, sizeof(void*)*1, v___x_4827_);
lean_inc_ref(v___y_4815_);
v___x_4829_ = lean_apply_2(v___y_4815_, v___x_4828_, lean_box(0));
v___y_4806_ = v___y_4813_;
v___y_4807_ = v___y_4814_;
v___y_4808_ = v___y_4815_;
goto v___jp_4805_;
}
v___jp_4830_:
{
lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4836_ = lean_string_utf8_byte_size(v___y_4834_);
v___x_4837_ = lean_nat_dec_eq(v___x_4836_, v___y_4833_);
if (v___x_4837_ == 0)
{
lean_object* v_s_4838_; 
v_s_4838_ = lean_ctor_get(v_scope_4802_, 0);
lean_inc_ref(v_s_4838_);
v___y_4813_ = v___y_4831_;
v___y_4814_ = v___y_4832_;
v___y_4815_ = v___y_4835_;
v___y_4816_ = v___x_4836_;
v___y_4817_ = v___y_4833_;
v___y_4818_ = v___y_4834_;
v___y_4819_ = v_s_4838_;
goto v___jp_4812_;
}
else
{
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
v___y_4806_ = v___y_4831_;
v___y_4807_ = v___y_4832_;
v___y_4808_ = v___y_4835_;
goto v___jp_4805_;
}
}
v___jp_4839_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4846_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_4847_ = lean_string_append(v___y_4845_, v___x_4846_);
v___x_4848_ = lean_string_append(v___x_4847_, v___y_4840_);
lean_dec_ref(v___y_4840_);
v___x_4849_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_4850_ = lean_string_append(v___x_4848_, v___x_4849_);
v___x_4851_ = 3;
v___x_4852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set_uint8(v___x_4852_, sizeof(void*)*1, v___x_4851_);
lean_inc_ref(v___y_4780_);
v___x_4853_ = lean_apply_2(v___y_4780_, v___x_4852_, lean_box(0));
v___y_4831_ = v___y_4841_;
v___y_4832_ = v___y_4842_;
v___y_4833_ = v___y_4844_;
v___y_4834_ = v___y_4843_;
v___y_4835_ = v___y_4780_;
goto v___jp_4830_;
}
v___jp_4854_:
{
lean_object* v_s_4860_; 
v_s_4860_ = lean_ctor_get(v_scope_4802_, 0);
lean_inc_ref(v_s_4860_);
v___y_4840_ = v___y_4859_;
v___y_4841_ = v___y_4855_;
v___y_4842_ = v___y_4856_;
v___y_4843_ = v___y_4858_;
v___y_4844_ = v___y_4857_;
v___y_4845_ = v_s_4860_;
goto v___jp_4839_;
}
v___jp_4861_:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; uint8_t v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4863_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_4864_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_4865_ = lean_box(0);
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_4868_ = 1;
v___x_4869_ = 0;
v___x_4870_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4870_, 0, v___x_4863_);
lean_ctor_set(v___x_4870_, 1, v___x_4864_);
lean_ctor_set(v___x_4870_, 2, v_a_4862_);
lean_ctor_set(v___x_4870_, 3, v___x_4865_);
lean_ctor_set(v___x_4870_, 4, v___x_4867_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*5, v___x_4868_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*5 + 1, v___x_4869_);
v___x_4871_ = lean_io_process_spawn(v___x_4870_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v_stdout_4873_; lean_object* v_stderr_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref(v___x_4871_);
v_stdout_4873_ = lean_ctor_get(v_a_4872_, 1);
lean_inc(v_stdout_4873_);
v_stderr_4874_ = lean_ctor_get(v_a_4872_, 2);
v___x_4875_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
lean_inc(v_stdout_4873_);
v___x_4876_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4777_, v_stderr_4874_, v_stdout_4873_, v___x_4875_, v___y_4780_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4878_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref(v___x_4876_);
v___x_4878_ = lean_io_process_child_wait(v___x_4863_, v_a_4872_);
lean_dec(v_a_4872_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4880_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref(v___x_4878_);
v___x_4880_ = l_IO_FS_Handle_readToEnd(v_stdout_4873_);
lean_dec(v_stdout_4873_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; uint8_t v_didError_4882_; lean_object* v_numSuccesses_4883_; lean_object* v___x_4884_; uint8_t v___x_4885_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref(v___x_4880_);
v_didError_4882_ = lean_ctor_get_uint8(v_a_4877_, sizeof(void*)*1);
v_numSuccesses_4883_ = lean_ctor_get(v_a_4877_, 0);
lean_inc(v_numSuccesses_4883_);
lean_dec(v_a_4877_);
v___x_4884_ = lean_array_get_size(v_infos_4803_);
lean_dec_ref(v_infos_4803_);
v___x_4885_ = lean_nat_dec_lt(v_numSuccesses_4883_, v___x_4884_);
lean_dec(v_numSuccesses_4883_);
if (v___x_4885_ == 0)
{
uint32_t v___x_4886_; 
v___x_4886_ = lean_unbox_uint32(v_a_4879_);
lean_dec(v_a_4879_);
v___y_4831_ = v_didError_4882_;
v___y_4832_ = v___x_4886_;
v___y_4833_ = v___x_4866_;
v___y_4834_ = v_a_4881_;
v___y_4835_ = v___y_4780_;
goto v___jp_4830_;
}
else
{
if (v_kind_4801_ == 0)
{
lean_object* v___x_4887_; uint32_t v___x_4888_; 
v___x_4887_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_4888_ = lean_unbox_uint32(v_a_4879_);
lean_dec(v_a_4879_);
v___y_4855_ = v_didError_4882_;
v___y_4856_ = v___x_4888_;
v___y_4857_ = v___x_4866_;
v___y_4858_ = v_a_4881_;
v___y_4859_ = v___x_4887_;
goto v___jp_4854_;
}
else
{
lean_object* v___x_4889_; uint32_t v___x_4890_; 
v___x_4889_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_4890_ = lean_unbox_uint32(v_a_4879_);
lean_dec(v_a_4879_);
v___y_4855_ = v_didError_4882_;
v___y_4856_ = v___x_4890_;
v___y_4857_ = v___x_4866_;
v___y_4858_ = v_a_4881_;
v___y_4859_ = v___x_4889_;
goto v___jp_4854_;
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4903_; 
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
v_a_4891_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4893_ = v___x_4880_;
v_isShared_4894_ = v_isSharedCheck_4903_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4880_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4903_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4895_; uint8_t v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4895_ = lean_io_error_to_string(v_a_4891_);
v___x_4896_ = 3;
v___x_4897_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4897_, 0, v___x_4895_);
lean_ctor_set_uint8(v___x_4897_, sizeof(void*)*1, v___x_4896_);
lean_inc_ref(v___y_4780_);
v___x_4898_ = lean_apply_2(v___y_4780_, v___x_4897_, lean_box(0));
v___x_4899_ = lean_box(0);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v___x_4899_);
v___x_4901_ = v___x_4893_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
else
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4916_; 
lean_dec(v_a_4877_);
lean_dec(v_stdout_4873_);
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
v_a_4904_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4906_ = v___x_4878_;
v_isShared_4907_ = v_isSharedCheck_4916_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4878_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4916_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4908_; uint8_t v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4908_ = lean_io_error_to_string(v_a_4904_);
v___x_4909_ = 3;
v___x_4910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4910_, 0, v___x_4908_);
lean_ctor_set_uint8(v___x_4910_, sizeof(void*)*1, v___x_4909_);
lean_inc_ref(v___y_4780_);
v___x_4911_ = lean_apply_2(v___y_4780_, v___x_4910_, lean_box(0));
v___x_4912_ = lean_box(0);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v___x_4912_);
v___x_4914_ = v___x_4906_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4912_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec(v_stdout_4873_);
lean_dec(v_a_4872_);
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
v_a_4917_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4876_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4876_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4937_; 
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
lean_dec_ref(v_cfg_4777_);
v_a_4925_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4927_ = v___x_4871_;
v_isShared_4928_ = v_isSharedCheck_4937_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4871_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4937_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; uint8_t v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v___x_4929_ = lean_io_error_to_string(v_a_4925_);
v___x_4930_ = 3;
v___x_4931_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4931_, 0, v___x_4929_);
lean_ctor_set_uint8(v___x_4931_, sizeof(void*)*1, v___x_4930_);
lean_inc_ref(v___y_4780_);
v___x_4932_ = lean_apply_2(v___y_4780_, v___x_4931_, lean_box(0));
v___x_4933_ = lean_box(0);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v___x_4933_);
v___x_4935_ = v___x_4927_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
v___jp_4938_:
{
lean_object* v___x_4939_; 
v___x_4939_ = lean_io_prim_handle_flush(v_h_4778_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
lean_dec_ref(v___x_4939_);
v___x_4940_ = lean_unsigned_to_nat(11u);
v___x_4941_ = lean_mk_empty_array_with_capacity(v___x_4940_);
lean_dec_ref(v___x_4941_);
v___x_4942_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_4943_ = lean_array_push(v___x_4942_, v_path_4779_);
v_a_4862_ = v___x_4943_;
goto v___jp_4861_;
}
else
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4956_; 
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
lean_dec_ref(v_path_4779_);
lean_dec_ref(v_cfg_4777_);
v_a_4944_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4946_ = v___x_4939_;
v_isShared_4947_ = v_isSharedCheck_4956_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4939_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4956_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4948_; uint8_t v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4954_; 
v___x_4948_ = lean_io_error_to_string(v_a_4944_);
v___x_4949_ = 3;
v___x_4950_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set_uint8(v___x_4950_, sizeof(void*)*1, v___x_4949_);
lean_inc_ref(v___y_4780_);
v___x_4951_ = lean_apply_2(v___y_4780_, v___x_4950_, lean_box(0));
v___x_4952_ = lean_box(0);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v___x_4952_);
v___x_4954_ = v___x_4946_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4952_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
v___jp_4957_:
{
if (lean_obj_tag(v___y_4958_) == 0)
{
lean_dec_ref(v___y_4958_);
goto v___jp_4938_;
}
else
{
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
lean_dec_ref(v_path_4779_);
lean_dec_ref(v_cfg_4777_);
return v___y_4958_;
}
}
v___jp_4959_:
{
lean_object* v___x_4960_; 
v___x_4960_ = lean_io_prim_handle_flush(v_h_4778_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
lean_dec_ref(v___x_4960_);
v___x_4961_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4962_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4963_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4964_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4965_ = lean_unsigned_to_nat(17u);
v___x_4966_ = lean_mk_empty_array_with_capacity(v___x_4965_);
lean_dec_ref(v___x_4966_);
v___x_4967_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_4804_);
v___x_4968_ = lean_array_push(v___x_4967_, v_key_4804_);
v___x_4969_ = lean_array_push(v___x_4968_, v___x_4961_);
v___x_4970_ = lean_array_push(v___x_4969_, v___x_4962_);
v___x_4971_ = lean_array_push(v___x_4970_, v___x_4963_);
v___x_4972_ = lean_array_push(v___x_4971_, v___x_4964_);
v___x_4973_ = lean_array_push(v___x_4972_, v_path_4779_);
v_a_4862_ = v___x_4973_;
goto v___jp_4861_;
}
else
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4986_; 
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
lean_dec_ref(v_path_4779_);
lean_dec_ref(v_cfg_4777_);
v_a_4974_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4976_ = v___x_4960_;
v_isShared_4977_ = v_isSharedCheck_4986_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4960_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4986_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4978_; uint8_t v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4978_ = lean_io_error_to_string(v_a_4974_);
v___x_4979_ = 3;
v___x_4980_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4980_, 0, v___x_4978_);
lean_ctor_set_uint8(v___x_4980_, sizeof(void*)*1, v___x_4979_);
lean_inc_ref(v___y_4780_);
v___x_4981_ = lean_apply_2(v___y_4780_, v___x_4980_, lean_box(0));
v___x_4982_ = lean_box(0);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_4982_);
v___x_4984_ = v___x_4976_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
v___jp_4987_:
{
if (lean_obj_tag(v___y_4988_) == 0)
{
lean_dec_ref(v___y_4988_);
goto v___jp_4959_;
}
else
{
lean_dec_ref(v_infos_4803_);
lean_dec_ref(v_scope_4802_);
lean_dec_ref(v_path_4779_);
lean_dec_ref(v_cfg_4777_);
return v___y_4988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object* v_cfg_5011_, lean_object* v_h_5012_, lean_object* v_path_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(v_cfg_5011_, v_h_5012_, v_path_5013_, v___y_5014_);
lean_dec_ref(v___y_5014_);
lean_dec(v_h_5012_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object* v_a_5017_, lean_object* v_cfg_5018_){
_start:
{
lean_object* v___f_5020_; lean_object* v___x_5021_; 
v___f_5020_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed), 5, 1);
lean_closure_set(v___f_5020_, 0, v_cfg_5018_);
v___x_5021_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5020_, v_a_5017_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object* v_a_5022_, lean_object* v_cfg_5023_, lean_object* v_a_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_5022_, v_cfg_5023_);
lean_dec_ref(v_a_5022_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object* v_cache_5026_, lean_object* v_service_5027_, lean_object* v_scope_5028_, uint8_t v_force_5029_, lean_object* v_as_5030_, size_t v_i_5031_, size_t v_stop_5032_, lean_object* v_b_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_a_5037_; uint8_t v___x_5041_; 
v___x_5041_ = lean_usize_dec_eq(v_i_5031_, v_stop_5032_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; lean_object* v___y_5044_; lean_object* v___y_5050_; uint8_t v_a_5051_; uint64_t v_hash_5052_; lean_object* v_ext_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___y_5057_; lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5042_ = lean_array_uget_borrowed(v_as_5030_, v_i_5031_);
v_hash_5052_ = lean_ctor_get_uint64(v___x_5042_, sizeof(void*)*1);
v_ext_5053_ = lean_ctor_get(v___x_5042_, 0);
v___x_5054_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
lean_inc_ref(v_cache_5026_);
v___x_5055_ = l_System_FilePath_join(v_cache_5026_, v___x_5054_);
v___x_5100_ = lean_string_utf8_byte_size(v_ext_5053_);
v___x_5101_ = lean_unsigned_to_nat(0u);
v___x_5102_ = lean_nat_dec_eq(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5103_ = l_Lake_Hash_hex(v_hash_5052_);
v___x_5104_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_5105_ = lean_string_append(v___x_5103_, v___x_5104_);
v___x_5106_ = lean_string_append(v___x_5105_, v_ext_5053_);
v___y_5057_ = v___x_5106_;
goto v___jp_5056_;
}
else
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lake_Hash_hex(v_hash_5052_);
v___y_5057_ = v___x_5107_;
goto v___jp_5056_;
}
v___jp_5043_:
{
uint64_t v_hash_5045_; lean_object* v_url_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v_hash_5045_ = lean_ctor_get_uint64(v___x_5042_, sizeof(void*)*1);
lean_inc_ref(v_scope_5028_);
lean_inc_ref(v_service_5027_);
v_url_5046_ = l_Lake_CacheService_artifactUrl(v_hash_5045_, v_service_5027_, v_scope_5028_);
lean_inc(v___x_5042_);
v___x_5047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5047_, 0, v_url_5046_);
lean_ctor_set(v___x_5047_, 1, v___y_5044_);
lean_ctor_set(v___x_5047_, 2, v___x_5042_);
v___x_5048_ = lean_array_push(v_b_5033_, v___x_5047_);
v_a_5037_ = v___x_5048_;
goto v___jp_5036_;
}
v___jp_5049_:
{
if (v_a_5051_ == 0)
{
v___y_5044_ = v___y_5050_;
goto v___jp_5043_;
}
else
{
lean_dec_ref(v___y_5050_);
v_a_5037_ = v_b_5033_;
goto v___jp_5036_;
}
}
v___jp_5056_:
{
lean_object* v_path_5058_; 
v_path_5058_ = l_System_FilePath_join(v___x_5055_, v___y_5057_);
if (v_force_5029_ == 0)
{
uint8_t v___x_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
v___x_5059_ = l_System_FilePath_pathExists(v_path_5058_);
v___x_5060_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5061_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_5061_ == 0)
{
v___y_5050_ = v_path_5058_;
v_a_5051_ = v___x_5059_;
goto v___jp_5049_;
}
else
{
lean_object* v___x_5062_; uint8_t v___x_5063_; 
v___x_5062_ = lean_box(0);
v___x_5063_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_5063_ == 0)
{
if (v___x_5061_ == 0)
{
v___y_5050_ = v_path_5058_;
v_a_5051_ = v___x_5059_;
goto v___jp_5049_;
}
else
{
size_t v___x_5064_; size_t v___x_5065_; lean_object* v___x_5066_; 
v___x_5064_ = ((size_t)0ULL);
v___x_5065_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_5066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_5060_, v___x_5064_, v___x_5065_, v___x_5062_, v___y_5034_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_dec_ref(v___x_5066_);
v___y_5050_ = v_path_5058_;
v_a_5051_ = v___x_5059_;
goto v___jp_5049_;
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec_ref(v_path_5058_);
lean_dec_ref(v_b_5033_);
lean_dec_ref(v_scope_5028_);
lean_dec_ref(v_service_5027_);
lean_dec_ref(v_cache_5026_);
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_5066_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5066_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
}
else
{
size_t v___x_5075_; size_t v___x_5076_; lean_object* v___x_5077_; 
v___x_5075_ = ((size_t)0ULL);
v___x_5076_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_5077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_5060_, v___x_5075_, v___x_5076_, v___x_5062_, v___y_5034_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_dec_ref(v___x_5077_);
v___y_5050_ = v_path_5058_;
v_a_5051_ = v___x_5059_;
goto v___jp_5049_;
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
lean_dec_ref(v_path_5058_);
lean_dec_ref(v_b_5033_);
lean_dec_ref(v_scope_5028_);
lean_dec_ref(v_service_5027_);
lean_dec_ref(v_cache_5026_);
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
}
}
else
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lake_removeFileIfExists(v_path_5058_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_dec_ref(v___x_5086_);
v___y_5044_ = v_path_5058_;
goto v___jp_5043_;
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5099_; 
lean_dec_ref(v_path_5058_);
lean_dec_ref(v_b_5033_);
lean_dec_ref(v_scope_5028_);
lean_dec_ref(v_service_5027_);
lean_dec_ref(v_cache_5026_);
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5089_ = v___x_5086_;
v_isShared_5090_ = v_isSharedCheck_5099_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5086_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5099_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5091_; uint8_t v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5097_; 
v___x_5091_ = lean_io_error_to_string(v_a_5087_);
v___x_5092_ = 3;
v___x_5093_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5093_, 0, v___x_5091_);
lean_ctor_set_uint8(v___x_5093_, sizeof(void*)*1, v___x_5092_);
lean_inc_ref(v___y_5034_);
v___x_5094_ = lean_apply_2(v___y_5034_, v___x_5093_, lean_box(0));
v___x_5095_ = lean_box(0);
if (v_isShared_5090_ == 0)
{
lean_ctor_set(v___x_5089_, 0, v___x_5095_);
v___x_5097_ = v___x_5089_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v___x_5095_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
}
}
else
{
lean_object* v___x_5108_; 
lean_dec_ref(v_scope_5028_);
lean_dec_ref(v_service_5027_);
lean_dec_ref(v_cache_5026_);
v___x_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5108_, 0, v_b_5033_);
return v___x_5108_;
}
v___jp_5036_:
{
size_t v___x_5038_; size_t v___x_5039_; 
v___x_5038_ = ((size_t)1ULL);
v___x_5039_ = lean_usize_add(v_i_5031_, v___x_5038_);
v_i_5031_ = v___x_5039_;
v_b_5033_ = v_a_5037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object* v_cache_5109_, lean_object* v_service_5110_, lean_object* v_scope_5111_, lean_object* v_force_5112_, lean_object* v_as_5113_, lean_object* v_i_5114_, lean_object* v_stop_5115_, lean_object* v_b_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
uint8_t v_force_boxed_5119_; size_t v_i_boxed_5120_; size_t v_stop_boxed_5121_; lean_object* v_res_5122_; 
v_force_boxed_5119_ = lean_unbox(v_force_5112_);
v_i_boxed_5120_ = lean_unbox_usize(v_i_5114_);
lean_dec(v_i_5114_);
v_stop_boxed_5121_ = lean_unbox_usize(v_stop_5115_);
lean_dec(v_stop_5115_);
v_res_5122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(v_cache_5109_, v_service_5110_, v_scope_5111_, v_force_boxed_5119_, v_as_5113_, v_i_boxed_5120_, v_stop_boxed_5121_, v_b_5116_, v___y_5117_);
lean_dec_ref(v___y_5117_);
lean_dec_ref(v_as_5113_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_5129_, lean_object* v_cache_5130_, lean_object* v_service_5131_, lean_object* v_scope_5132_, uint8_t v_force_5133_, lean_object* v_a_5134_){
_start:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v_a_5139_; lean_object* v___y_5165_; uint8_t v___x_5175_; 
v___x_5136_ = lean_array_get_size(v_descrs_5129_);
v___x_5137_ = lean_unsigned_to_nat(0u);
v___x_5175_ = lean_nat_dec_eq(v___x_5136_, v___x_5137_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5176_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_5177_ = lean_nat_dec_lt(v___x_5137_, v___x_5136_);
if (v___x_5177_ == 0)
{
lean_dec_ref(v_service_5131_);
v_a_5139_ = v___x_5176_;
goto v___jp_5138_;
}
else
{
uint8_t v___x_5178_; 
v___x_5178_ = lean_nat_dec_le(v___x_5136_, v___x_5136_);
if (v___x_5178_ == 0)
{
if (v___x_5177_ == 0)
{
lean_dec_ref(v_service_5131_);
v_a_5139_ = v___x_5176_;
goto v___jp_5138_;
}
else
{
size_t v___x_5179_; size_t v___x_5180_; lean_object* v___x_5181_; 
v___x_5179_ = ((size_t)0ULL);
v___x_5180_ = lean_usize_of_nat(v___x_5136_);
lean_inc_ref(v_scope_5132_);
lean_inc_ref(v_cache_5130_);
v___x_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(v_cache_5130_, v_service_5131_, v_scope_5132_, v_force_5133_, v_descrs_5129_, v___x_5179_, v___x_5180_, v___x_5176_, v_a_5134_);
v___y_5165_ = v___x_5181_;
goto v___jp_5164_;
}
}
else
{
size_t v___x_5182_; size_t v___x_5183_; lean_object* v___x_5184_; 
v___x_5182_ = ((size_t)0ULL);
v___x_5183_ = lean_usize_of_nat(v___x_5136_);
lean_inc_ref(v_scope_5132_);
lean_inc_ref(v_cache_5130_);
v___x_5184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(v_cache_5130_, v_service_5131_, v_scope_5132_, v_force_5133_, v_descrs_5129_, v___x_5182_, v___x_5183_, v___x_5176_, v_a_5134_);
v___y_5165_ = v___x_5184_;
goto v___jp_5164_;
}
}
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
lean_dec_ref(v_scope_5132_);
lean_dec_ref(v_service_5131_);
lean_dec_ref(v_cache_5130_);
v___x_5185_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__2));
lean_inc_ref(v_a_5134_);
v___x_5186_ = lean_apply_2(v_a_5134_, v___x_5185_, lean_box(0));
v___x_5187_ = lean_box(0);
v___x_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5187_);
return v___x_5188_;
}
v___jp_5138_:
{
lean_object* v___x_5140_; uint8_t v___x_5141_; 
v___x_5140_ = lean_array_get_size(v_a_5139_);
v___x_5141_ = lean_nat_dec_eq(v___x_5140_, v___x_5137_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5142_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_5143_ = l_System_FilePath_join(v_cache_5130_, v___x_5142_);
v___x_5144_ = l_IO_FS_createDirAll(v___x_5143_);
if (lean_obj_tag(v___x_5144_) == 0)
{
uint8_t v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
lean_dec_ref(v___x_5144_);
v___x_5145_ = 0;
v___x_5146_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_5147_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5147_, 0, v_scope_5132_);
lean_ctor_set(v___x_5147_, 1, v_a_5139_);
lean_ctor_set(v___x_5147_, 2, v___x_5146_);
lean_ctor_set_uint8(v___x_5147_, sizeof(void*)*3, v___x_5145_);
v___x_5148_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_5134_, v___x_5147_);
return v___x_5148_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5161_; 
lean_dec_ref(v_a_5139_);
lean_dec_ref(v_scope_5132_);
v_a_5149_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5151_ = v___x_5144_;
v_isShared_5152_ = v_isSharedCheck_5161_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5144_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5161_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5153_; uint8_t v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5159_; 
v___x_5153_ = lean_io_error_to_string(v_a_5149_);
v___x_5154_ = 3;
v___x_5155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5155_, 0, v___x_5153_);
lean_ctor_set_uint8(v___x_5155_, sizeof(void*)*1, v___x_5154_);
lean_inc_ref(v_a_5134_);
v___x_5156_ = lean_apply_2(v_a_5134_, v___x_5155_, lean_box(0));
v___x_5157_ = lean_box(0);
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5157_);
v___x_5159_ = v___x_5151_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5157_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
else
{
lean_object* v___x_5162_; lean_object* v___x_5163_; 
lean_dec_ref(v_a_5139_);
lean_dec_ref(v_scope_5132_);
lean_dec_ref(v_cache_5130_);
v___x_5162_ = lean_box(0);
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5162_);
return v___x_5163_;
}
}
v___jp_5164_:
{
if (lean_obj_tag(v___y_5165_) == 0)
{
lean_object* v_a_5166_; 
v_a_5166_ = lean_ctor_get(v___y_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref(v___y_5165_);
v_a_5139_ = v_a_5166_;
goto v___jp_5138_;
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_dec_ref(v_scope_5132_);
lean_dec_ref(v_cache_5130_);
v_a_5167_ = lean_ctor_get(v___y_5165_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___y_5165_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___y_5165_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___y_5165_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_5189_, lean_object* v_cache_5190_, lean_object* v_service_5191_, lean_object* v_scope_5192_, lean_object* v_force_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_){
_start:
{
uint8_t v_force_boxed_5196_; lean_object* v_res_5197_; 
v_force_boxed_5196_ = lean_unbox(v_force_5193_);
v_res_5197_ = l_Lake_CacheService_downloadArtifacts(v_descrs_5189_, v_cache_5190_, v_service_5191_, v_scope_5192_, v_force_boxed_5196_, v_a_5194_);
lean_dec_ref(v_a_5194_);
lean_dec_ref(v_descrs_5189_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_5198_, lean_object* v_descrs_5199_, lean_object* v_cache_5200_, lean_object* v_service_5201_, lean_object* v_scope_5202_, uint8_t v_force_5203_){
_start:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v_a_5208_; lean_object* v___y_5234_; uint8_t v___x_5244_; 
v___x_5205_ = lean_array_get_size(v_descrs_5199_);
v___x_5206_ = lean_unsigned_to_nat(0u);
v___x_5244_ = lean_nat_dec_eq(v___x_5205_, v___x_5206_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; uint8_t v___x_5246_; 
v___x_5245_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_5246_ = lean_nat_dec_lt(v___x_5206_, v___x_5205_);
if (v___x_5246_ == 0)
{
lean_dec_ref(v_service_5201_);
v_a_5208_ = v___x_5245_;
goto v___jp_5207_;
}
else
{
uint8_t v___x_5247_; 
v___x_5247_ = lean_nat_dec_le(v___x_5205_, v___x_5205_);
if (v___x_5247_ == 0)
{
if (v___x_5246_ == 0)
{
lean_dec_ref(v_service_5201_);
v_a_5208_ = v___x_5245_;
goto v___jp_5207_;
}
else
{
size_t v___x_5248_; size_t v___x_5249_; lean_object* v___x_5250_; 
v___x_5248_ = ((size_t)0ULL);
v___x_5249_ = lean_usize_of_nat(v___x_5205_);
lean_inc_ref(v_scope_5202_);
lean_inc_ref(v_cache_5200_);
v___x_5250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(v_cache_5200_, v_service_5201_, v_scope_5202_, v_force_5203_, v_descrs_5199_, v___x_5248_, v___x_5249_, v___x_5245_, v_a_5198_);
v___y_5234_ = v___x_5250_;
goto v___jp_5233_;
}
}
else
{
size_t v___x_5251_; size_t v___x_5252_; lean_object* v___x_5253_; 
v___x_5251_ = ((size_t)0ULL);
v___x_5252_ = lean_usize_of_nat(v___x_5205_);
lean_inc_ref(v_scope_5202_);
lean_inc_ref(v_cache_5200_);
v___x_5253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__1(v_cache_5200_, v_service_5201_, v_scope_5202_, v_force_5203_, v_descrs_5199_, v___x_5251_, v___x_5252_, v___x_5245_, v_a_5198_);
v___y_5234_ = v___x_5253_;
goto v___jp_5233_;
}
}
}
else
{
lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
lean_dec_ref(v_scope_5202_);
lean_dec_ref(v_service_5201_);
lean_dec_ref(v_cache_5200_);
v___x_5254_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__2));
lean_inc_ref(v_a_5198_);
v___x_5255_ = lean_apply_2(v_a_5198_, v___x_5254_, lean_box(0));
v___x_5256_ = lean_box(0);
v___x_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5257_, 0, v___x_5256_);
return v___x_5257_;
}
v___jp_5207_:
{
lean_object* v___x_5209_; uint8_t v___x_5210_; 
v___x_5209_ = lean_array_get_size(v_a_5208_);
v___x_5210_ = lean_nat_dec_eq(v___x_5209_, v___x_5206_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5211_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_5212_ = l_System_FilePath_join(v_cache_5200_, v___x_5211_);
v___x_5213_ = l_IO_FS_createDirAll(v___x_5212_);
if (lean_obj_tag(v___x_5213_) == 0)
{
uint8_t v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
lean_dec_ref(v___x_5213_);
v___x_5214_ = 0;
v___x_5215_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_5216_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5216_, 0, v_scope_5202_);
lean_ctor_set(v___x_5216_, 1, v_a_5208_);
lean_ctor_set(v___x_5216_, 2, v___x_5215_);
lean_ctor_set_uint8(v___x_5216_, sizeof(void*)*3, v___x_5214_);
v___x_5217_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_5198_, v___x_5216_);
return v___x_5217_;
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5230_; 
lean_dec_ref(v_a_5208_);
lean_dec_ref(v_scope_5202_);
v_a_5218_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5220_ = v___x_5213_;
v_isShared_5221_ = v_isSharedCheck_5230_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5213_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5230_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5222_; uint8_t v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5228_; 
v___x_5222_ = lean_io_error_to_string(v_a_5218_);
v___x_5223_ = 3;
v___x_5224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5224_, 0, v___x_5222_);
lean_ctor_set_uint8(v___x_5224_, sizeof(void*)*1, v___x_5223_);
lean_inc_ref(v_a_5198_);
v___x_5225_ = lean_apply_2(v_a_5198_, v___x_5224_, lean_box(0));
v___x_5226_ = lean_box(0);
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 0, v___x_5226_);
v___x_5228_ = v___x_5220_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
else
{
lean_object* v___x_5231_; lean_object* v___x_5232_; 
lean_dec_ref(v_a_5208_);
lean_dec_ref(v_scope_5202_);
lean_dec_ref(v_cache_5200_);
v___x_5231_ = lean_box(0);
v___x_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
return v___x_5232_;
}
}
v___jp_5233_:
{
if (lean_obj_tag(v___y_5234_) == 0)
{
lean_object* v_a_5235_; 
v_a_5235_ = lean_ctor_get(v___y_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref(v___y_5234_);
v_a_5208_ = v_a_5235_;
goto v___jp_5207_;
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec_ref(v_scope_5202_);
lean_dec_ref(v_cache_5200_);
v_a_5236_ = lean_ctor_get(v___y_5234_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___y_5234_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___y_5234_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___y_5234_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_5258_, lean_object* v_descrs_5259_, lean_object* v_cache_5260_, lean_object* v_service_5261_, lean_object* v_scope_5262_, lean_object* v_force_5263_, lean_object* v_a_5264_){
_start:
{
uint8_t v_force_boxed_5265_; lean_object* v_res_5266_; 
v_force_boxed_5265_ = lean_unbox(v_force_5263_);
v_res_5266_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_5258_, v_descrs_5259_, v_cache_5260_, v_service_5261_, v_scope_5262_, v_force_boxed_5265_);
lean_dec_ref(v_descrs_5259_);
lean_dec_ref(v_a_5258_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_5267_, lean_object* v_cache_5268_, lean_object* v_service_5269_, lean_object* v_localScope_5270_, lean_object* v_remoteScope_5271_, uint8_t v_force_5272_, lean_object* v_a_5273_){
_start:
{
lean_object* v_name_x3f_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v_name_x3f_5278_ = lean_ctor_get(v_service_5269_, 0);
lean_inc_ref(v_remoteScope_5271_);
v___x_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5279_, 0, v_remoteScope_5271_);
lean_inc(v_name_x3f_5278_);
lean_inc_ref(v_cache_5268_);
v___x_5280_ = l_Lake_Cache_writeMap(v_cache_5268_, v_localScope_5270_, v_map_5267_, v_name_x3f_5278_, v___x_5279_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5318_; 
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v___x_5280_, 0);
lean_dec(v_unused_5319_);
v___x_5282_ = v___x_5280_;
v_isShared_5283_ = v_isSharedCheck_5318_;
goto v_resetjp_5281_;
}
else
{
lean_dec(v___x_5280_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5318_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5284_ = lean_unsigned_to_nat(0u);
v___x_5285_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5286_ = l_Lake_CacheMap_collectOutputDescrs(v_map_5267_, v___x_5285_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; lean_object* v_a_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
lean_del_object(v___x_5282_);
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc(v_a_5287_);
v_a_5288_ = lean_ctor_get(v___x_5286_, 1);
lean_inc(v_a_5288_);
lean_dec_ref(v___x_5286_);
v___x_5289_ = lean_array_get_size(v_a_5288_);
v___x_5290_ = lean_nat_dec_lt(v___x_5284_, v___x_5289_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; 
lean_dec(v_a_5288_);
v___x_5291_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_5273_, v_a_5287_, v_cache_5268_, v_service_5269_, v_remoteScope_5271_, v_force_5272_);
lean_dec(v_a_5287_);
return v___x_5291_;
}
else
{
lean_object* v___x_5292_; uint8_t v___x_5293_; 
v___x_5292_ = lean_box(0);
v___x_5293_ = lean_nat_dec_le(v___x_5289_, v___x_5289_);
if (v___x_5293_ == 0)
{
if (v___x_5290_ == 0)
{
lean_object* v___x_5294_; 
lean_dec(v_a_5288_);
v___x_5294_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_5273_, v_a_5287_, v_cache_5268_, v_service_5269_, v_remoteScope_5271_, v_force_5272_);
lean_dec(v_a_5287_);
return v___x_5294_;
}
else
{
size_t v___x_5295_; size_t v___x_5296_; lean_object* v___x_5297_; 
v___x_5295_ = ((size_t)0ULL);
v___x_5296_ = lean_usize_of_nat(v___x_5289_);
v___x_5297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5288_, v___x_5295_, v___x_5296_, v___x_5292_, v_a_5273_);
lean_dec(v_a_5288_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v___x_5298_; 
lean_dec_ref(v___x_5297_);
v___x_5298_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_5273_, v_a_5287_, v_cache_5268_, v_service_5269_, v_remoteScope_5271_, v_force_5272_);
lean_dec(v_a_5287_);
return v___x_5298_;
}
else
{
lean_dec(v_a_5287_);
lean_dec_ref(v_remoteScope_5271_);
lean_dec_ref(v_service_5269_);
lean_dec_ref(v_cache_5268_);
return v___x_5297_;
}
}
}
else
{
size_t v___x_5299_; size_t v___x_5300_; lean_object* v___x_5301_; 
v___x_5299_ = ((size_t)0ULL);
v___x_5300_ = lean_usize_of_nat(v___x_5289_);
v___x_5301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5288_, v___x_5299_, v___x_5300_, v___x_5292_, v_a_5273_);
lean_dec(v_a_5288_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v___x_5302_; 
lean_dec_ref(v___x_5301_);
v___x_5302_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_5273_, v_a_5287_, v_cache_5268_, v_service_5269_, v_remoteScope_5271_, v_force_5272_);
lean_dec(v_a_5287_);
return v___x_5302_;
}
else
{
lean_dec(v_a_5287_);
lean_dec_ref(v_remoteScope_5271_);
lean_dec_ref(v_service_5269_);
lean_dec_ref(v_cache_5268_);
return v___x_5301_;
}
}
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5304_; uint8_t v___x_5305_; 
lean_dec_ref(v_remoteScope_5271_);
lean_dec_ref(v_service_5269_);
lean_dec_ref(v_cache_5268_);
v_a_5303_ = lean_ctor_get(v___x_5286_, 1);
lean_inc(v_a_5303_);
lean_dec_ref(v___x_5286_);
v___x_5304_ = lean_array_get_size(v_a_5303_);
v___x_5305_ = lean_nat_dec_lt(v___x_5284_, v___x_5304_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; lean_object* v___x_5308_; 
lean_dec(v_a_5303_);
v___x_5306_ = lean_box(0);
if (v_isShared_5283_ == 0)
{
lean_ctor_set_tag(v___x_5282_, 1);
lean_ctor_set(v___x_5282_, 0, v___x_5306_);
v___x_5308_ = v___x_5282_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5306_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
else
{
lean_object* v___x_5310_; uint8_t v___x_5311_; 
lean_del_object(v___x_5282_);
v___x_5310_ = lean_box(0);
v___x_5311_ = lean_nat_dec_le(v___x_5304_, v___x_5304_);
if (v___x_5311_ == 0)
{
if (v___x_5305_ == 0)
{
lean_dec(v_a_5303_);
goto v___jp_5275_;
}
else
{
size_t v___x_5312_; size_t v___x_5313_; lean_object* v___x_5314_; 
v___x_5312_ = ((size_t)0ULL);
v___x_5313_ = lean_usize_of_nat(v___x_5304_);
v___x_5314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5303_, v___x_5312_, v___x_5313_, v___x_5310_, v_a_5273_);
lean_dec(v_a_5303_);
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_dec_ref(v___x_5314_);
goto v___jp_5275_;
}
else
{
return v___x_5314_;
}
}
}
else
{
size_t v___x_5315_; size_t v___x_5316_; lean_object* v___x_5317_; 
v___x_5315_ = ((size_t)0ULL);
v___x_5316_ = lean_usize_of_nat(v___x_5304_);
v___x_5317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5303_, v___x_5315_, v___x_5316_, v___x_5310_, v_a_5273_);
lean_dec(v_a_5303_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_dec_ref(v___x_5317_);
goto v___jp_5275_;
}
else
{
return v___x_5317_;
}
}
}
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5332_; 
lean_dec_ref(v_remoteScope_5271_);
lean_dec_ref(v_service_5269_);
lean_dec_ref(v_cache_5268_);
lean_dec_ref(v_map_5267_);
v_a_5320_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5322_ = v___x_5280_;
v_isShared_5323_ = v_isSharedCheck_5332_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5280_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5332_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5324_; uint8_t v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
v___x_5324_ = lean_io_error_to_string(v_a_5320_);
v___x_5325_ = 3;
v___x_5326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5326_, 0, v___x_5324_);
lean_ctor_set_uint8(v___x_5326_, sizeof(void*)*1, v___x_5325_);
lean_inc_ref(v_a_5273_);
v___x_5327_ = lean_apply_2(v_a_5273_, v___x_5326_, lean_box(0));
v___x_5328_ = lean_box(0);
if (v_isShared_5323_ == 0)
{
lean_ctor_set(v___x_5322_, 0, v___x_5328_);
v___x_5330_ = v___x_5322_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
v___jp_5275_:
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5276_ = lean_box(0);
v___x_5277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_5333_, lean_object* v_cache_5334_, lean_object* v_service_5335_, lean_object* v_localScope_5336_, lean_object* v_remoteScope_5337_, lean_object* v_force_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_){
_start:
{
uint8_t v_force_boxed_5341_; lean_object* v_res_5342_; 
v_force_boxed_5341_ = lean_unbox(v_force_5338_);
v_res_5342_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_5333_, v_cache_5334_, v_service_5335_, v_localScope_5336_, v_remoteScope_5337_, v_force_boxed_5341_, v_a_5339_);
lean_dec_ref(v_a_5339_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* v_descrs_5343_, lean_object* v_service_5344_, lean_object* v_scope_5345_, lean_object* v_paths_5346_, lean_object* v_n_5347_, lean_object* v_i_5348_, lean_object* v_a_5349_){
_start:
{
lean_object* v_zero_5351_; uint8_t v_isZero_5352_; 
v_zero_5351_ = lean_unsigned_to_nat(0u);
v_isZero_5352_ = lean_nat_dec_eq(v_i_5348_, v_zero_5351_);
if (v_isZero_5352_ == 1)
{
lean_object* v___x_5353_; 
lean_dec(v_i_5348_);
lean_dec_ref(v_scope_5345_);
lean_dec_ref(v_service_5344_);
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v_a_5349_);
return v___x_5353_;
}
else
{
lean_object* v_one_5354_; lean_object* v_n_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; uint64_t v_hash_5359_; lean_object* v_url_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; 
v_one_5354_ = lean_unsigned_to_nat(1u);
v_n_5355_ = lean_nat_sub(v_i_5348_, v_one_5354_);
lean_dec(v_i_5348_);
v___x_5356_ = lean_nat_sub(v_n_5347_, v_n_5355_);
v___x_5357_ = lean_nat_sub(v___x_5356_, v_one_5354_);
lean_dec(v___x_5356_);
v___x_5358_ = lean_array_fget_borrowed(v_descrs_5343_, v___x_5357_);
v_hash_5359_ = lean_ctor_get_uint64(v___x_5358_, sizeof(void*)*1);
lean_inc_ref(v_scope_5345_);
lean_inc_ref(v_service_5344_);
v_url_5360_ = l_Lake_CacheService_artifactUrl(v_hash_5359_, v_service_5344_, v_scope_5345_);
v___x_5361_ = lean_array_fget_borrowed(v_paths_5346_, v___x_5357_);
lean_dec(v___x_5357_);
lean_inc(v___x_5358_);
lean_inc(v___x_5361_);
v___x_5362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5362_, 0, v_url_5360_);
lean_ctor_set(v___x_5362_, 1, v___x_5361_);
lean_ctor_set(v___x_5362_, 2, v___x_5358_);
v___x_5363_ = lean_array_push(v_a_5349_, v___x_5362_);
v_i_5348_ = v_n_5355_;
v_a_5349_ = v___x_5363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* v_descrs_5365_, lean_object* v_service_5366_, lean_object* v_scope_5367_, lean_object* v_paths_5368_, lean_object* v_n_5369_, lean_object* v_i_5370_, lean_object* v_a_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_descrs_5365_, v_service_5366_, v_scope_5367_, v_paths_5368_, v_n_5369_, v_i_5370_, v_a_5371_);
lean_dec(v_n_5369_);
lean_dec_ref(v_paths_5368_);
lean_dec_ref(v_descrs_5365_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_5378_, lean_object* v_descrs_5379_, lean_object* v_paths_5380_, lean_object* v_service_5381_, lean_object* v_scope_5382_, lean_object* v_a_5383_){
_start:
{
lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5385_ = lean_unsigned_to_nat(0u);
v___x_5386_ = lean_nat_dec_eq(v_n_5378_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v_a_5389_; lean_object* v_key_5390_; uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5387_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
lean_inc(v_n_5378_);
lean_inc_ref(v_scope_5382_);
lean_inc_ref(v_service_5381_);
v___x_5388_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_descrs_5379_, v_service_5381_, v_scope_5382_, v_paths_5380_, v_n_5378_, v_n_5378_, v___x_5387_);
lean_dec(v_n_5378_);
v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
lean_inc(v_a_5389_);
lean_dec_ref(v___x_5388_);
v_key_5390_ = lean_ctor_get(v_service_5381_, 1);
lean_inc_ref(v_key_5390_);
lean_dec_ref(v_service_5381_);
v___x_5391_ = 1;
v___x_5392_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5392_, 0, v_scope_5382_);
lean_ctor_set(v___x_5392_, 1, v_a_5389_);
lean_ctor_set(v___x_5392_, 2, v_key_5390_);
lean_ctor_set_uint8(v___x_5392_, sizeof(void*)*3, v___x_5391_);
v___x_5393_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_5383_, v___x_5392_);
return v___x_5393_;
}
else
{
lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
lean_dec_ref(v_scope_5382_);
lean_dec_ref(v_service_5381_);
lean_dec(v_n_5378_);
v___x_5394_ = ((lean_object*)(l_Lake_CacheService_uploadArtifacts___closed__1));
lean_inc_ref(v_a_5383_);
v___x_5395_ = lean_apply_2(v_a_5383_, v___x_5394_, lean_box(0));
v___x_5396_ = lean_box(0);
v___x_5397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5396_);
return v___x_5397_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_5398_, lean_object* v_descrs_5399_, lean_object* v_paths_5400_, lean_object* v_service_5401_, lean_object* v_scope_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Lake_CacheService_uploadArtifacts(v_n_5398_, v_descrs_5399_, v_paths_5400_, v_service_5401_, v_scope_5402_, v_a_5403_);
lean_dec_ref(v_a_5403_);
lean_dec_ref(v_paths_5400_);
lean_dec_ref(v_descrs_5399_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object* v_descrs_5406_, lean_object* v_service_5407_, lean_object* v_scope_5408_, lean_object* v_paths_5409_, lean_object* v_n_5410_, lean_object* v_i_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v___y_5414_){
_start:
{
lean_object* v___x_5416_; 
v___x_5416_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_descrs_5406_, v_service_5407_, v_scope_5408_, v_paths_5409_, v_n_5410_, v_i_5411_, v_a_5413_);
return v___x_5416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* v_descrs_5417_, lean_object* v_service_5418_, lean_object* v_scope_5419_, lean_object* v_paths_5420_, lean_object* v_n_5421_, lean_object* v_i_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v_res_5427_; 
v_res_5427_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(v_descrs_5417_, v_service_5418_, v_scope_5419_, v_paths_5420_, v_n_5421_, v_i_5422_, v_a_5423_, v_a_5424_, v___y_5425_);
lean_dec_ref(v___y_5425_);
lean_dec(v_n_5421_);
lean_dec_ref(v_paths_5420_);
lean_dec_ref(v_descrs_5417_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_5432_, lean_object* v_service_5433_, lean_object* v_scope_5434_, lean_object* v_platform_5435_, lean_object* v_toolchain_5436_){
_start:
{
lean_object* v_url_5438_; lean_object* v_url_5445_; 
if (lean_obj_tag(v_scope_5434_) == 0)
{
lean_object* v_s_5454_; lean_object* v_revisionEndpoint_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
lean_dec_ref(v_platform_5435_);
v_s_5454_ = lean_ctor_get(v_scope_5434_, 0);
lean_inc_ref(v_s_5454_);
lean_dec_ref(v_scope_5434_);
v_revisionEndpoint_5455_ = lean_ctor_get(v_service_5433_, 3);
lean_inc_ref(v_revisionEndpoint_5455_);
lean_dec_ref(v_service_5433_);
v___x_5456_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_5455_, v_s_5454_);
v___x_5457_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_5458_ = lean_string_append(v___x_5457_, v_rev_5432_);
v___x_5459_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_5460_ = lean_string_append(v___x_5458_, v___x_5459_);
v___x_5461_ = lean_string_append(v___x_5456_, v___x_5460_);
lean_dec_ref(v___x_5460_);
return v___x_5461_;
}
else
{
lean_object* v_s_5462_; lean_object* v_revisionEndpoint_5463_; lean_object* v_url_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; uint8_t v___x_5467_; 
v_s_5462_ = lean_ctor_get(v_scope_5434_, 0);
lean_inc_ref(v_s_5462_);
lean_dec_ref(v_scope_5434_);
v_revisionEndpoint_5463_ = lean_ctor_get(v_service_5433_, 3);
lean_inc_ref(v_revisionEndpoint_5463_);
lean_dec_ref(v_service_5433_);
v_url_5464_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_5463_, v_s_5462_);
v___x_5465_ = lean_string_utf8_byte_size(v_platform_5435_);
v___x_5466_ = lean_unsigned_to_nat(0u);
v___x_5467_ = lean_nat_dec_eq(v___x_5465_, v___x_5466_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v_url_5470_; 
v___x_5468_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_5469_ = lean_string_append(v_url_5464_, v___x_5468_);
v_url_5470_ = l_Lake_uriEncode(v_platform_5435_, v___x_5469_);
v_url_5445_ = v_url_5470_;
goto v___jp_5444_;
}
else
{
lean_dec_ref(v_platform_5435_);
v_url_5445_ = v_url_5464_;
goto v___jp_5444_;
}
}
v___jp_5437_:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5439_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_5440_ = lean_string_append(v_url_5438_, v___x_5439_);
v___x_5441_ = lean_string_append(v___x_5440_, v_rev_5432_);
v___x_5442_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_5443_ = lean_string_append(v___x_5441_, v___x_5442_);
return v___x_5443_;
}
v___jp_5444_:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; uint8_t v___x_5448_; 
v___x_5446_ = lean_string_utf8_byte_size(v_toolchain_5436_);
v___x_5447_ = lean_unsigned_to_nat(0u);
v___x_5448_ = lean_nat_dec_eq(v___x_5446_, v___x_5447_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v_url_5453_; 
v___x_5449_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_5450_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_5436_, v___x_5449_, v___x_5447_);
v___x_5451_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_5452_ = lean_string_append(v_url_5445_, v___x_5451_);
v_url_5453_ = l_Lake_uriEncode(v___x_5450_, v___x_5452_);
v_url_5438_ = v_url_5453_;
goto v___jp_5437_;
}
else
{
v_url_5438_ = v_url_5445_;
goto v___jp_5437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_5471_, lean_object* v_service_5472_, lean_object* v_scope_5473_, lean_object* v_platform_5474_, lean_object* v_toolchain_5475_){
_start:
{
lean_object* v_res_5476_; 
v_res_5476_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_5471_, v_service_5472_, v_scope_5473_, v_platform_5474_, v_toolchain_5475_);
lean_dec_ref(v_toolchain_5475_);
lean_dec_ref(v_rev_5471_);
return v_res_5476_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_5480_, lean_object* v_service_5481_, lean_object* v_scope_5482_, lean_object* v_platform_5483_, lean_object* v_toolchain_5484_){
_start:
{
lean_object* v_url_5486_; lean_object* v___y_5494_; uint8_t v_isReservoir_5504_; 
v_isReservoir_5504_ = lean_ctor_get_uint8(v_service_5481_, sizeof(void*)*5);
if (v_isReservoir_5504_ == 0)
{
lean_object* v___x_5505_; 
v___x_5505_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_5480_, v_service_5481_, v_scope_5482_, v_platform_5483_, v_toolchain_5484_);
lean_dec_ref(v_toolchain_5484_);
return v___x_5505_;
}
else
{
if (lean_obj_tag(v_scope_5482_) == 0)
{
lean_object* v_apiEndpoint_5506_; lean_object* v_s_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v_apiEndpoint_5506_ = lean_ctor_get(v_service_5481_, 4);
lean_inc_ref(v_apiEndpoint_5506_);
lean_dec_ref(v_service_5481_);
v_s_5507_ = lean_ctor_get(v_scope_5482_, 0);
lean_inc_ref(v_s_5507_);
lean_dec_ref(v_scope_5482_);
v___x_5508_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_5509_ = lean_string_append(v_apiEndpoint_5506_, v___x_5508_);
v___x_5510_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_5509_, v_s_5507_);
v___y_5494_ = v___x_5510_;
goto v___jp_5493_;
}
else
{
lean_object* v_apiEndpoint_5511_; lean_object* v_s_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v_apiEndpoint_5511_ = lean_ctor_get(v_service_5481_, 4);
lean_inc_ref(v_apiEndpoint_5511_);
lean_dec_ref(v_service_5481_);
v_s_5512_ = lean_ctor_get(v_scope_5482_, 0);
lean_inc_ref(v_s_5512_);
lean_dec_ref(v_scope_5482_);
v___x_5513_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_5514_ = lean_string_append(v_apiEndpoint_5511_, v___x_5513_);
v___x_5515_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_5514_, v_s_5512_);
v___y_5494_ = v___x_5515_;
goto v___jp_5493_;
}
}
v___jp_5485_:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; uint8_t v___x_5489_; 
v___x_5487_ = lean_string_utf8_byte_size(v_toolchain_5484_);
v___x_5488_ = lean_unsigned_to_nat(0u);
v___x_5489_ = lean_nat_dec_eq(v___x_5487_, v___x_5488_);
if (v___x_5489_ == 0)
{
lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v_url_5492_; 
v___x_5490_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_5491_ = lean_string_append(v_url_5486_, v___x_5490_);
v_url_5492_ = l_Lake_uriEncode(v_toolchain_5484_, v___x_5491_);
return v_url_5492_;
}
else
{
lean_dec_ref(v_toolchain_5484_);
return v_url_5486_;
}
}
v___jp_5493_:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v_url_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; uint8_t v___x_5500_; 
v___x_5495_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_5496_ = lean_string_append(v___y_5494_, v___x_5495_);
v_url_5497_ = lean_string_append(v___x_5496_, v_rev_5480_);
v___x_5498_ = lean_string_utf8_byte_size(v_platform_5483_);
v___x_5499_ = lean_unsigned_to_nat(0u);
v___x_5500_ = lean_nat_dec_eq(v___x_5498_, v___x_5499_);
if (v___x_5500_ == 0)
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v_url_5503_; 
v___x_5501_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_5502_ = lean_string_append(v_url_5497_, v___x_5501_);
v_url_5503_ = l_Lake_uriEncode(v_platform_5483_, v___x_5502_);
v_url_5486_ = v_url_5503_;
goto v___jp_5485_;
}
else
{
lean_dec_ref(v_platform_5483_);
v_url_5486_ = v_url_5497_;
goto v___jp_5485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_5516_, lean_object* v_service_5517_, lean_object* v_scope_5518_, lean_object* v_platform_5519_, lean_object* v_toolchain_5520_){
_start:
{
lean_object* v_res_5521_; 
v_res_5521_ = l_Lake_CacheService_revisionUrl(v_rev_5516_, v_service_5517_, v_scope_5518_, v_platform_5519_, v_toolchain_5520_);
lean_dec_ref(v_rev_5516_);
return v_res_5521_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_5526_, lean_object* v_cache_5527_, lean_object* v_service_5528_, lean_object* v_localScope_5529_, lean_object* v_remoteScope_5530_, lean_object* v_platform_5531_, lean_object* v_toolchain_5532_, uint8_t v_force_5533_, lean_object* v_a_5534_){
_start:
{
lean_object* v_a_5540_; lean_object* v_a_5547_; lean_object* v___y_5551_; lean_object* v___y_5552_; lean_object* v_a_5560_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v_path_5569_; lean_object* v_a_5571_; lean_object* v___y_5673_; lean_object* v___y_5674_; uint8_t v___x_5723_; lean_object* v___x_5787_; uint8_t v___x_5788_; 
v___x_5564_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_5565_ = l_System_FilePath_join(v_cache_5527_, v___x_5564_);
lean_inc_ref(v_localScope_5529_);
v___x_5566_ = l_System_FilePath_join(v___x_5565_, v_localScope_5529_);
v___x_5567_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_5526_);
v___x_5568_ = lean_string_append(v_rev_5526_, v___x_5567_);
v_path_5569_ = l_System_FilePath_join(v___x_5566_, v___x_5568_);
v___x_5723_ = l_System_FilePath_pathExists(v_path_5569_);
v___x_5787_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5788_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_5788_ == 0)
{
goto v___jp_5724_;
}
else
{
lean_object* v___x_5789_; uint8_t v___x_5790_; 
v___x_5789_ = lean_box(0);
v___x_5790_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_5790_ == 0)
{
if (v___x_5788_ == 0)
{
goto v___jp_5724_;
}
else
{
size_t v___x_5791_; size_t v___x_5792_; lean_object* v___x_5793_; 
v___x_5791_ = ((size_t)0ULL);
v___x_5792_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_5793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_5787_, v___x_5791_, v___x_5792_, v___x_5789_, v_a_5534_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_dec_ref(v___x_5793_);
goto v___jp_5724_;
}
else
{
lean_object* v_a_5794_; lean_object* v___x_5796_; uint8_t v_isShared_5797_; uint8_t v_isSharedCheck_5801_; 
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_toolchain_5532_);
lean_dec_ref(v_platform_5531_);
lean_dec_ref(v_remoteScope_5530_);
lean_dec_ref(v_localScope_5529_);
lean_dec_ref(v_service_5528_);
lean_dec_ref(v_rev_5526_);
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5801_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5801_ == 0)
{
v___x_5796_ = v___x_5793_;
v_isShared_5797_ = v_isSharedCheck_5801_;
goto v_resetjp_5795_;
}
else
{
lean_inc(v_a_5794_);
lean_dec(v___x_5793_);
v___x_5796_ = lean_box(0);
v_isShared_5797_ = v_isSharedCheck_5801_;
goto v_resetjp_5795_;
}
v_resetjp_5795_:
{
lean_object* v___x_5799_; 
if (v_isShared_5797_ == 0)
{
v___x_5799_ = v___x_5796_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_a_5794_);
v___x_5799_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
return v___x_5799_;
}
}
}
}
}
else
{
size_t v___x_5802_; size_t v___x_5803_; lean_object* v___x_5804_; 
v___x_5802_ = ((size_t)0ULL);
v___x_5803_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_5804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_5787_, v___x_5802_, v___x_5803_, v___x_5789_, v_a_5534_);
if (lean_obj_tag(v___x_5804_) == 0)
{
lean_dec_ref(v___x_5804_);
goto v___jp_5724_;
}
else
{
lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5812_; 
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_toolchain_5532_);
lean_dec_ref(v_platform_5531_);
lean_dec_ref(v_remoteScope_5530_);
lean_dec_ref(v_localScope_5529_);
lean_dec_ref(v_service_5528_);
lean_dec_ref(v_rev_5526_);
v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v___x_5804_);
if (v_isSharedCheck_5812_ == 0)
{
v___x_5807_ = v___x_5804_;
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_a_5805_);
lean_dec(v___x_5804_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5810_; 
if (v_isShared_5808_ == 0)
{
v___x_5810_ = v___x_5807_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v_a_5805_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
}
}
}
v___jp_5536_:
{
lean_object* v___x_5537_; lean_object* v___x_5538_; 
v___x_5537_ = lean_box(0);
v___x_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5537_);
return v___x_5538_;
}
v___jp_5539_:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___x_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5541_, 0, v_a_5540_);
v___x_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5541_);
return v___x_5542_;
}
v___jp_5543_:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5544_ = lean_box(0);
v___x_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5544_);
return v___x_5545_;
}
v___jp_5546_:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5548_, 0, v_a_5547_);
v___x_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
v___jp_5550_:
{
lean_object* v___x_5553_; lean_object* v___x_5554_; uint8_t v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5553_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_5554_ = lean_string_append(v___y_5552_, v___x_5553_);
v___x_5555_ = 3;
v___x_5556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5556_, 0, v___x_5554_);
lean_ctor_set_uint8(v___x_5556_, sizeof(void*)*1, v___x_5555_);
lean_inc_ref(v_a_5534_);
v___x_5557_ = lean_apply_2(v_a_5534_, v___x_5556_, lean_box(0));
v___x_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5558_, 0, v___y_5551_);
return v___x_5558_;
}
v___jp_5559_:
{
lean_object* v_s_5561_; 
v_s_5561_ = lean_ctor_get(v_remoteScope_5530_, 0);
lean_inc_ref(v_s_5561_);
lean_dec_ref(v_remoteScope_5530_);
v___y_5551_ = v_a_5560_;
v___y_5552_ = v_s_5561_;
goto v___jp_5550_;
}
v___jp_5562_:
{
lean_object* v___x_5563_; 
v___x_5563_ = lean_box(0);
v_a_5560_ = v___x_5563_;
goto v___jp_5559_;
}
v___jp_5570_:
{
if (lean_obj_tag(v_a_5571_) == 1)
{
lean_object* v_val_5572_; lean_object* v___x_5573_; 
v_val_5572_ = lean_ctor_get(v_a_5571_, 0);
lean_inc(v_val_5572_);
lean_dec_ref(v_a_5571_);
lean_inc_ref(v_path_5569_);
v___x_5573_ = l_Lake_createParentDirs(v_path_5569_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v___x_5574_; 
lean_dec_ref(v___x_5573_);
v___x_5574_ = l_IO_FS_writeFile(v_path_5569_, v_val_5572_);
lean_dec(v_val_5572_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5642_; 
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5642_ == 0)
{
lean_object* v_unused_5643_; 
v_unused_5643_ = lean_ctor_get(v___x_5574_, 0);
lean_dec(v_unused_5643_);
v___x_5576_ = v___x_5574_;
v_isShared_5577_ = v_isSharedCheck_5642_;
goto v_resetjp_5575_;
}
else
{
lean_dec(v___x_5574_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5642_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; uint8_t v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5578_ = lean_string_utf8_byte_size(v_platform_5531_);
lean_dec_ref(v_platform_5531_);
v___x_5579_ = lean_unsigned_to_nat(0u);
v___x_5580_ = lean_nat_dec_eq(v___x_5578_, v___x_5579_);
v___x_5581_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5582_ = l_Lake_CacheMap_load(v_path_5569_, v___x_5580_, v___x_5581_);
if (lean_obj_tag(v___x_5582_) == 0)
{
lean_object* v_a_5583_; lean_object* v_a_5584_; lean_object* v___x_5585_; uint8_t v___x_5586_; 
lean_del_object(v___x_5576_);
v_a_5583_ = lean_ctor_get(v___x_5582_, 0);
lean_inc(v_a_5583_);
v_a_5584_ = lean_ctor_get(v___x_5582_, 1);
lean_inc(v_a_5584_);
lean_dec_ref(v___x_5582_);
v___x_5585_ = lean_array_get_size(v_a_5584_);
v___x_5586_ = lean_nat_dec_lt(v___x_5579_, v___x_5585_);
if (v___x_5586_ == 0)
{
lean_dec(v_a_5584_);
v_a_5547_ = v_a_5583_;
goto v___jp_5546_;
}
else
{
lean_object* v___x_5587_; uint8_t v___x_5588_; 
v___x_5587_ = lean_box(0);
v___x_5588_ = lean_nat_dec_le(v___x_5585_, v___x_5585_);
if (v___x_5588_ == 0)
{
if (v___x_5586_ == 0)
{
lean_dec(v_a_5584_);
v_a_5547_ = v_a_5583_;
goto v___jp_5546_;
}
else
{
size_t v___x_5589_; size_t v___x_5590_; lean_object* v___x_5591_; 
v___x_5589_ = ((size_t)0ULL);
v___x_5590_ = lean_usize_of_nat(v___x_5585_);
v___x_5591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5584_, v___x_5589_, v___x_5590_, v___x_5587_, v_a_5534_);
lean_dec(v_a_5584_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_dec_ref(v___x_5591_);
v_a_5547_ = v_a_5583_;
goto v___jp_5546_;
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_dec(v_a_5583_);
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5591_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5591_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
}
else
{
size_t v___x_5600_; size_t v___x_5601_; lean_object* v___x_5602_; 
v___x_5600_ = ((size_t)0ULL);
v___x_5601_ = lean_usize_of_nat(v___x_5585_);
v___x_5602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5584_, v___x_5600_, v___x_5601_, v___x_5587_, v_a_5534_);
lean_dec(v_a_5584_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_dec_ref(v___x_5602_);
v_a_5547_ = v_a_5583_;
goto v___jp_5546_;
}
else
{
lean_object* v_a_5603_; lean_object* v___x_5605_; uint8_t v_isShared_5606_; uint8_t v_isSharedCheck_5610_; 
lean_dec(v_a_5583_);
v_a_5603_ = lean_ctor_get(v___x_5602_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v___x_5602_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5605_ = v___x_5602_;
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
else
{
lean_inc(v_a_5603_);
lean_dec(v___x_5602_);
v___x_5605_ = lean_box(0);
v_isShared_5606_ = v_isSharedCheck_5610_;
goto v_resetjp_5604_;
}
v_resetjp_5604_:
{
lean_object* v___x_5608_; 
if (v_isShared_5606_ == 0)
{
v___x_5608_ = v___x_5605_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
}
}
}
else
{
lean_object* v_a_5611_; lean_object* v___x_5612_; uint8_t v___x_5613_; 
v_a_5611_ = lean_ctor_get(v___x_5582_, 1);
lean_inc(v_a_5611_);
lean_dec_ref(v___x_5582_);
v___x_5612_ = lean_array_get_size(v_a_5611_);
v___x_5613_ = lean_nat_dec_lt(v___x_5579_, v___x_5612_);
if (v___x_5613_ == 0)
{
lean_object* v___x_5614_; lean_object* v___x_5616_; 
lean_dec(v_a_5611_);
v___x_5614_ = lean_box(0);
if (v_isShared_5577_ == 0)
{
lean_ctor_set_tag(v___x_5576_, 1);
lean_ctor_set(v___x_5576_, 0, v___x_5614_);
v___x_5616_ = v___x_5576_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5614_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
else
{
lean_object* v___x_5618_; uint8_t v___x_5619_; 
lean_del_object(v___x_5576_);
v___x_5618_ = lean_box(0);
v___x_5619_ = lean_nat_dec_le(v___x_5612_, v___x_5612_);
if (v___x_5619_ == 0)
{
if (v___x_5613_ == 0)
{
lean_dec(v_a_5611_);
goto v___jp_5543_;
}
else
{
size_t v___x_5620_; size_t v___x_5621_; lean_object* v___x_5622_; 
v___x_5620_ = ((size_t)0ULL);
v___x_5621_ = lean_usize_of_nat(v___x_5612_);
v___x_5622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5611_, v___x_5620_, v___x_5621_, v___x_5618_, v_a_5534_);
lean_dec(v_a_5611_);
if (lean_obj_tag(v___x_5622_) == 0)
{
lean_dec_ref(v___x_5622_);
goto v___jp_5543_;
}
else
{
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5630_; 
v_a_5623_ = lean_ctor_get(v___x_5622_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5622_);
if (v_isSharedCheck_5630_ == 0)
{
v___x_5625_ = v___x_5622_;
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5622_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5628_; 
if (v_isShared_5626_ == 0)
{
v___x_5628_ = v___x_5625_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
}
else
{
size_t v___x_5631_; size_t v___x_5632_; lean_object* v___x_5633_; 
v___x_5631_ = ((size_t)0ULL);
v___x_5632_ = lean_usize_of_nat(v___x_5612_);
v___x_5633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5611_, v___x_5631_, v___x_5632_, v___x_5618_, v_a_5534_);
lean_dec(v_a_5611_);
if (lean_obj_tag(v___x_5633_) == 0)
{
lean_dec_ref(v___x_5633_);
goto v___jp_5543_;
}
else
{
lean_object* v_a_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5641_; 
v_a_5634_ = lean_ctor_get(v___x_5633_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5633_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5636_ = v___x_5633_;
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_a_5634_);
lean_dec(v___x_5633_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5637_ == 0)
{
v___x_5639_ = v___x_5636_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
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
lean_object* v_a_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5656_; 
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_platform_5531_);
v_a_5644_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5646_ = v___x_5574_;
v_isShared_5647_ = v_isSharedCheck_5656_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_a_5644_);
lean_dec(v___x_5574_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5656_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v___x_5648_; uint8_t v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5654_; 
v___x_5648_ = lean_io_error_to_string(v_a_5644_);
v___x_5649_ = 3;
v___x_5650_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5650_, 0, v___x_5648_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*1, v___x_5649_);
lean_inc_ref(v_a_5534_);
v___x_5651_ = lean_apply_2(v_a_5534_, v___x_5650_, lean_box(0));
v___x_5652_ = lean_box(0);
if (v_isShared_5647_ == 0)
{
lean_ctor_set(v___x_5646_, 0, v___x_5652_);
v___x_5654_ = v___x_5646_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
else
{
lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5669_; 
lean_dec(v_val_5572_);
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_platform_5531_);
v_a_5657_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5669_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5659_ = v___x_5573_;
v_isShared_5660_ = v_isSharedCheck_5669_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5573_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5669_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5661_; uint8_t v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5667_; 
v___x_5661_ = lean_io_error_to_string(v_a_5657_);
v___x_5662_ = 3;
v___x_5663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5663_, 0, v___x_5661_);
lean_ctor_set_uint8(v___x_5663_, sizeof(void*)*1, v___x_5662_);
lean_inc_ref(v_a_5534_);
v___x_5664_ = lean_apply_2(v_a_5534_, v___x_5663_, lean_box(0));
v___x_5665_ = lean_box(0);
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5665_);
v___x_5667_ = v___x_5659_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5665_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
else
{
lean_object* v___x_5670_; lean_object* v___x_5671_; 
lean_dec(v_a_5571_);
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_platform_5531_);
v___x_5670_ = lean_box(0);
v___x_5671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
return v___x_5671_;
}
}
v___jp_5672_:
{
lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; 
v___x_5675_ = lean_unsigned_to_nat(0u);
v___x_5676_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5677_ = l_Lake_getUrl_x3f(v___y_5673_, v___y_5674_, v___x_5676_);
lean_dec_ref(v___y_5674_);
if (lean_obj_tag(v___x_5677_) == 0)
{
lean_object* v_a_5678_; lean_object* v_a_5679_; lean_object* v___x_5680_; uint8_t v___x_5681_; 
v_a_5678_ = lean_ctor_get(v___x_5677_, 0);
lean_inc(v_a_5678_);
v_a_5679_ = lean_ctor_get(v___x_5677_, 1);
lean_inc(v_a_5679_);
lean_dec_ref(v___x_5677_);
v___x_5680_ = lean_array_get_size(v_a_5679_);
v___x_5681_ = lean_nat_dec_lt(v___x_5675_, v___x_5680_);
if (v___x_5681_ == 0)
{
lean_dec(v_a_5679_);
lean_dec_ref(v_remoteScope_5530_);
v_a_5571_ = v_a_5678_;
goto v___jp_5570_;
}
else
{
lean_object* v___x_5682_; uint8_t v___x_5683_; 
v___x_5682_ = lean_box(0);
v___x_5683_ = lean_nat_dec_le(v___x_5680_, v___x_5680_);
if (v___x_5683_ == 0)
{
if (v___x_5681_ == 0)
{
lean_dec(v_a_5679_);
lean_dec_ref(v_remoteScope_5530_);
v_a_5571_ = v_a_5678_;
goto v___jp_5570_;
}
else
{
size_t v___x_5684_; size_t v___x_5685_; lean_object* v___x_5686_; 
v___x_5684_ = ((size_t)0ULL);
v___x_5685_ = lean_usize_of_nat(v___x_5680_);
v___x_5686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5679_, v___x_5684_, v___x_5685_, v___x_5682_, v_a_5534_);
lean_dec(v_a_5679_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_dec_ref(v___x_5686_);
lean_dec_ref(v_remoteScope_5530_);
v_a_5571_ = v_a_5678_;
goto v___jp_5570_;
}
else
{
lean_object* v_a_5687_; 
lean_dec(v_a_5678_);
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_platform_5531_);
v_a_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_a_5687_);
lean_dec_ref(v___x_5686_);
v_a_5560_ = v_a_5687_;
goto v___jp_5559_;
}
}
}
else
{
size_t v___x_5688_; size_t v___x_5689_; lean_object* v___x_5690_; 
v___x_5688_ = ((size_t)0ULL);
v___x_5689_ = lean_usize_of_nat(v___x_5680_);
v___x_5690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5679_, v___x_5688_, v___x_5689_, v___x_5682_, v_a_5534_);
lean_dec(v_a_5679_);
if (lean_obj_tag(v___x_5690_) == 0)
{
lean_dec_ref(v___x_5690_);
lean_dec_ref(v_remoteScope_5530_);
v_a_5571_ = v_a_5678_;
goto v___jp_5570_;
}
else
{
lean_object* v_a_5691_; 
lean_dec(v_a_5678_);
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_platform_5531_);
v_a_5691_ = lean_ctor_get(v___x_5690_, 0);
lean_inc(v_a_5691_);
lean_dec_ref(v___x_5690_);
v_a_5560_ = v_a_5691_;
goto v___jp_5559_;
}
}
}
}
else
{
lean_object* v_a_5692_; lean_object* v___x_5693_; uint8_t v___x_5694_; 
lean_dec_ref(v_path_5569_);
lean_dec_ref(v_platform_5531_);
v_a_5692_ = lean_ctor_get(v___x_5677_, 1);
lean_inc(v_a_5692_);
lean_dec_ref(v___x_5677_);
v___x_5693_ = lean_array_get_size(v_a_5692_);
v___x_5694_ = lean_nat_dec_lt(v___x_5675_, v___x_5693_);
if (v___x_5694_ == 0)
{
lean_object* v___x_5695_; 
lean_dec(v_a_5692_);
v___x_5695_ = lean_box(0);
v_a_5560_ = v___x_5695_;
goto v___jp_5559_;
}
else
{
lean_object* v___x_5696_; uint8_t v___x_5697_; 
v___x_5696_ = lean_box(0);
v___x_5697_ = lean_nat_dec_le(v___x_5693_, v___x_5693_);
if (v___x_5697_ == 0)
{
if (v___x_5694_ == 0)
{
lean_dec(v_a_5692_);
goto v___jp_5562_;
}
else
{
size_t v___x_5698_; size_t v___x_5699_; lean_object* v___x_5700_; 
v___x_5698_ = ((size_t)0ULL);
v___x_5699_ = lean_usize_of_nat(v___x_5693_);
v___x_5700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5692_, v___x_5698_, v___x_5699_, v___x_5696_, v_a_5534_);
lean_dec(v_a_5692_);
if (lean_obj_tag(v___x_5700_) == 0)
{
lean_dec_ref(v___x_5700_);
goto v___jp_5562_;
}
else
{
lean_object* v_a_5701_; 
v_a_5701_ = lean_ctor_get(v___x_5700_, 0);
lean_inc(v_a_5701_);
lean_dec_ref(v___x_5700_);
v_a_5560_ = v_a_5701_;
goto v___jp_5559_;
}
}
}
else
{
size_t v___x_5702_; size_t v___x_5703_; lean_object* v___x_5704_; 
v___x_5702_ = ((size_t)0ULL);
v___x_5703_ = lean_usize_of_nat(v___x_5693_);
v___x_5704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5692_, v___x_5702_, v___x_5703_, v___x_5696_, v_a_5534_);
lean_dec(v_a_5692_);
if (lean_obj_tag(v___x_5704_) == 0)
{
lean_dec_ref(v___x_5704_);
goto v___jp_5562_;
}
else
{
lean_object* v_a_5705_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
lean_inc(v_a_5705_);
lean_dec_ref(v___x_5704_);
v_a_5560_ = v_a_5705_;
goto v___jp_5559_;
}
}
}
}
}
v___jp_5706_:
{
lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; uint8_t v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; uint8_t v_isReservoir_5720_; 
lean_inc_ref(v_platform_5531_);
lean_inc_ref(v_remoteScope_5530_);
lean_inc_ref(v_service_5528_);
v___x_5707_ = l_Lake_CacheService_revisionUrl(v_rev_5526_, v_service_5528_, v_remoteScope_5530_, v_platform_5531_, v_toolchain_5532_);
v___x_5708_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_5709_ = lean_string_append(v_localScope_5529_, v___x_5708_);
v___x_5710_ = lean_string_append(v___x_5709_, v_rev_5526_);
lean_dec_ref(v_rev_5526_);
v___x_5711_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_5712_ = lean_string_append(v___x_5710_, v___x_5711_);
v___x_5713_ = lean_string_append(v___x_5712_, v_path_5569_);
v___x_5714_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_5715_ = lean_string_append(v___x_5713_, v___x_5714_);
v___x_5716_ = lean_string_append(v___x_5715_, v___x_5707_);
v___x_5717_ = 1;
v___x_5718_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5718_, 0, v___x_5716_);
lean_ctor_set_uint8(v___x_5718_, sizeof(void*)*1, v___x_5717_);
lean_inc_ref(v_a_5534_);
v___x_5719_ = lean_apply_2(v_a_5534_, v___x_5718_, lean_box(0));
v_isReservoir_5720_ = lean_ctor_get_uint8(v_service_5528_, sizeof(void*)*5);
lean_dec_ref(v_service_5528_);
if (v_isReservoir_5720_ == 0)
{
lean_object* v___x_5721_; 
v___x_5721_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_5673_ = v___x_5707_;
v___y_5674_ = v___x_5721_;
goto v___jp_5672_;
}
else
{
lean_object* v___x_5722_; 
v___x_5722_ = l_Lake_Reservoir_lakeHeaders;
v___y_5673_ = v___x_5707_;
v___y_5674_ = v___x_5722_;
goto v___jp_5672_;
}
}
v___jp_5724_:
{
if (v___x_5723_ == 0)
{
goto v___jp_5706_;
}
else
{
if (v_force_5533_ == 0)
{
lean_object* v___x_5725_; lean_object* v___x_5726_; uint8_t v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; 
lean_dec_ref(v_toolchain_5532_);
lean_dec_ref(v_remoteScope_5530_);
lean_dec_ref(v_localScope_5529_);
lean_dec_ref(v_service_5528_);
lean_dec_ref(v_rev_5526_);
v___x_5725_ = lean_string_utf8_byte_size(v_platform_5531_);
lean_dec_ref(v_platform_5531_);
v___x_5726_ = lean_unsigned_to_nat(0u);
v___x_5727_ = lean_nat_dec_eq(v___x_5725_, v___x_5726_);
v___x_5728_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5729_ = l_Lake_CacheMap_load(v_path_5569_, v___x_5727_, v___x_5728_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; lean_object* v_a_5731_; lean_object* v___x_5732_; uint8_t v___x_5733_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_a_5730_);
v_a_5731_ = lean_ctor_get(v___x_5729_, 1);
lean_inc(v_a_5731_);
lean_dec_ref(v___x_5729_);
v___x_5732_ = lean_array_get_size(v_a_5731_);
v___x_5733_ = lean_nat_dec_lt(v___x_5726_, v___x_5732_);
if (v___x_5733_ == 0)
{
lean_dec(v_a_5731_);
v_a_5540_ = v_a_5730_;
goto v___jp_5539_;
}
else
{
lean_object* v___x_5734_; uint8_t v___x_5735_; 
v___x_5734_ = lean_box(0);
v___x_5735_ = lean_nat_dec_le(v___x_5732_, v___x_5732_);
if (v___x_5735_ == 0)
{
if (v___x_5733_ == 0)
{
lean_dec(v_a_5731_);
v_a_5540_ = v_a_5730_;
goto v___jp_5539_;
}
else
{
size_t v___x_5736_; size_t v___x_5737_; lean_object* v___x_5738_; 
v___x_5736_ = ((size_t)0ULL);
v___x_5737_ = lean_usize_of_nat(v___x_5732_);
v___x_5738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5731_, v___x_5736_, v___x_5737_, v___x_5734_, v_a_5534_);
lean_dec(v_a_5731_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_dec_ref(v___x_5738_);
v_a_5540_ = v_a_5730_;
goto v___jp_5539_;
}
else
{
lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5746_; 
lean_dec(v_a_5730_);
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5741_ = v___x_5738_;
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_dec(v___x_5738_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5744_; 
if (v_isShared_5742_ == 0)
{
v___x_5744_ = v___x_5741_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5739_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
}
}
else
{
size_t v___x_5747_; size_t v___x_5748_; lean_object* v___x_5749_; 
v___x_5747_ = ((size_t)0ULL);
v___x_5748_ = lean_usize_of_nat(v___x_5732_);
v___x_5749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5731_, v___x_5747_, v___x_5748_, v___x_5734_, v_a_5534_);
lean_dec(v_a_5731_);
if (lean_obj_tag(v___x_5749_) == 0)
{
lean_dec_ref(v___x_5749_);
v_a_5540_ = v_a_5730_;
goto v___jp_5539_;
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5757_; 
lean_dec(v_a_5730_);
v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5749_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5752_ = v___x_5749_;
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5749_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5755_; 
if (v_isShared_5753_ == 0)
{
v___x_5755_ = v___x_5752_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
}
}
else
{
lean_object* v_a_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; 
v_a_5758_ = lean_ctor_get(v___x_5729_, 1);
lean_inc(v_a_5758_);
lean_dec_ref(v___x_5729_);
v___x_5759_ = lean_array_get_size(v_a_5758_);
v___x_5760_ = lean_nat_dec_lt(v___x_5726_, v___x_5759_);
if (v___x_5760_ == 0)
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
lean_dec(v_a_5758_);
v___x_5761_ = lean_box(0);
v___x_5762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5761_);
return v___x_5762_;
}
else
{
lean_object* v___x_5763_; uint8_t v___x_5764_; 
v___x_5763_ = lean_box(0);
v___x_5764_ = lean_nat_dec_le(v___x_5759_, v___x_5759_);
if (v___x_5764_ == 0)
{
if (v___x_5760_ == 0)
{
lean_dec(v_a_5758_);
goto v___jp_5536_;
}
else
{
size_t v___x_5765_; size_t v___x_5766_; lean_object* v___x_5767_; 
v___x_5765_ = ((size_t)0ULL);
v___x_5766_ = lean_usize_of_nat(v___x_5759_);
v___x_5767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5758_, v___x_5765_, v___x_5766_, v___x_5763_, v_a_5534_);
lean_dec(v_a_5758_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_dec_ref(v___x_5767_);
goto v___jp_5536_;
}
else
{
lean_object* v_a_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_5775_; 
v_a_5768_ = lean_ctor_get(v___x_5767_, 0);
v_isSharedCheck_5775_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5775_ == 0)
{
v___x_5770_ = v___x_5767_;
v_isShared_5771_ = v_isSharedCheck_5775_;
goto v_resetjp_5769_;
}
else
{
lean_inc(v_a_5768_);
lean_dec(v___x_5767_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_5775_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
lean_object* v___x_5773_; 
if (v_isShared_5771_ == 0)
{
v___x_5773_ = v___x_5770_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_a_5768_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
}
}
}
else
{
size_t v___x_5776_; size_t v___x_5777_; lean_object* v___x_5778_; 
v___x_5776_ = ((size_t)0ULL);
v___x_5777_ = lean_usize_of_nat(v___x_5759_);
v___x_5778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_5758_, v___x_5776_, v___x_5777_, v___x_5763_, v_a_5534_);
lean_dec(v_a_5758_);
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_dec_ref(v___x_5778_);
goto v___jp_5536_;
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5786_; 
v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5781_ = v___x_5778_;
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5778_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5784_; 
if (v_isShared_5782_ == 0)
{
v___x_5784_ = v___x_5781_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
}
}
}
else
{
goto v___jp_5706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_5813_, lean_object* v_cache_5814_, lean_object* v_service_5815_, lean_object* v_localScope_5816_, lean_object* v_remoteScope_5817_, lean_object* v_platform_5818_, lean_object* v_toolchain_5819_, lean_object* v_force_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_){
_start:
{
uint8_t v_force_boxed_5823_; lean_object* v_res_5824_; 
v_force_boxed_5823_ = lean_unbox(v_force_5820_);
v_res_5824_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_5813_, v_cache_5814_, v_service_5815_, v_localScope_5816_, v_remoteScope_5817_, v_platform_5818_, v_toolchain_5819_, v_force_boxed_5823_, v_a_5821_);
lean_dec_ref(v_a_5821_);
return v_res_5824_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_5826_, lean_object* v_outputs_5827_, lean_object* v_service_5828_, lean_object* v_scope_5829_, lean_object* v_platform_5830_, lean_object* v_toolchain_5831_, lean_object* v_a_5832_){
_start:
{
lean_object* v_url_5834_; lean_object* v___y_5836_; lean_object* v_s_5852_; 
lean_inc_ref(v_scope_5829_);
lean_inc_ref(v_service_5828_);
v_url_5834_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_5826_, v_service_5828_, v_scope_5829_, v_platform_5830_, v_toolchain_5831_);
v_s_5852_ = lean_ctor_get(v_scope_5829_, 0);
lean_inc_ref(v_s_5852_);
lean_dec_ref(v_scope_5829_);
v___y_5836_ = v_s_5852_;
goto v___jp_5835_;
v___jp_5835_:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; uint8_t v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v_key_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5837_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_5838_ = lean_string_append(v___y_5836_, v___x_5837_);
v___x_5839_ = lean_string_append(v___x_5838_, v_rev_5826_);
v___x_5840_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_5841_ = lean_string_append(v___x_5839_, v___x_5840_);
v___x_5842_ = lean_string_append(v___x_5841_, v_outputs_5827_);
v___x_5843_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_5844_ = lean_string_append(v___x_5842_, v___x_5843_);
v___x_5845_ = lean_string_append(v___x_5844_, v_url_5834_);
v___x_5846_ = 1;
v___x_5847_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5847_, 0, v___x_5845_);
lean_ctor_set_uint8(v___x_5847_, sizeof(void*)*1, v___x_5846_);
lean_inc_ref(v_a_5832_);
v___x_5848_ = lean_apply_2(v_a_5832_, v___x_5847_, lean_box(0));
v_key_5849_ = lean_ctor_get(v_service_5828_, 1);
lean_inc_ref(v_key_5849_);
lean_dec_ref(v_service_5828_);
v___x_5850_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_5851_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_5832_, v_outputs_5827_, v___x_5850_, v_url_5834_, v_key_5849_);
return v___x_5851_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_5853_, lean_object* v_outputs_5854_, lean_object* v_service_5855_, lean_object* v_scope_5856_, lean_object* v_platform_5857_, lean_object* v_toolchain_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_){
_start:
{
lean_object* v_res_5861_; 
v_res_5861_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_5853_, v_outputs_5854_, v_service_5855_, v_scope_5856_, v_platform_5857_, v_toolchain_5858_, v_a_5859_);
lean_dec_ref(v_a_5859_);
lean_dec_ref(v_toolchain_5858_);
lean_dec_ref(v_rev_5853_);
return v_res_5861_;
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
