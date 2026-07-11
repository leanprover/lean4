// Lean compiler output
// Module: Lake.Config.Cache
// Imports: import Init.Control.Do public import Lake.Util.Git public import Lake.Util.Log public import Lake.Util.Version public import Lake.Config.Artifact import Lake.Config.InstallPath import Lake.Build.Actions import Lake.Util.Url import Lake.Util.Proc import Lake.Util.Reservoir import Lake.Util.JsonObject import Lake.Util.IO import Init.System.Platform import Init.Data.String.Lemmas
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lake_writeFileIfNew(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
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
lean_object* l_Lake_Date_fromJson_x3f(lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
extern lean_object* l_System_Platform_target;
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object*);
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
static const lean_string_object l_Lake_instInhabitedCache_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedCache_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCache_default = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCache = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
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
static const lean_string_object l_Lake_Cache_outputsDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "outputs"};
static const lean_object* l_Lake_Cache_outputsDir___closed__0 = (const lean_object*)&l_Lake_Cache_outputsDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object*);
static const lean_string_object l_Lake_Cache_outputsFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".json"};
static const lean_object* l_Lake_Cache_outputsFile___closed__0 = (const lean_object*)&l_Lake_Cache_outputsFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object*);
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
LEAN_EXPORT const lean_object* l_Lake_CachePlatform_none = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_system;
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CachePlatform_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lake_CachePlatform_toString___closed__0 = (const lean_object*)&l_Lake_CachePlatform_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CachePlatform_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheToolchain_none = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheToolchain_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value;
static const lean_array_object l_Lake_downloadArtifactCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_downloadArtifactCore___closed__0 = (const lean_object*)&l_Lake_downloadArtifactCore___closed__0_value;
static const lean_string_object l_Lake_downloadArtifactCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": downloaded artifact hash mismatch, got "};
static const lean_object* l_Lake_downloadArtifactCore___closed__1 = (const lean_object*)&l_Lake_downloadArtifactCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty;
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Hash_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(lean_object*, lean_object*, uint64_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "/artifacts"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object*);
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "property not found: status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "status: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "message: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "curl exited with code "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to fetch artifact URLs\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\n          \nInvalid curl JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "curl produced unexpected output:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "curl JSON:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstdout:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\n  Transfer error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to fetch artifact URLs"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "failed to fetch artifact URLs (status code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "\nIncorrect number of results: expected "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ")\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\nReservoir error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-d"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Content-Type: application/json"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "failed to copy artifact: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_downloadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "no artifacts to download"};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__0_value;
static const lean_ctor_object l_Lake_CacheService_downloadArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no artifacts to upload"};
static const lean_object* l_Lake_CacheService_uploadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__0_value;
static const lean_ctor_object l_Lake_CacheService_uploadArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheService_uploadArtifacts___closed__1 = (const lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_27_, 1);
v_a_15_ = v_a_28_;
goto v___jp_14_;
}
else
{
lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_29_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_27_, 1);
v___x_30_ = l_Lake_Date_fromJson_x3f(v_a_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v___x_30_, 1);
v_a_15_ = v_a_31_;
goto v___jp_14_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_a_32_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_30_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(size_t v_sz_201_, size_t v_i_202_, lean_object* v_bs_203_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0___boxed(lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_bs_215_){
_start:
{
size_t v_sz_boxed_216_; size_t v_i_boxed_217_; lean_object* v_res_218_; 
v_sz_boxed_216_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_217_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(v_sz_boxed_216_, v_i_boxed_217_, v_bs_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 4)
{
lean_object* v_elems_222_; size_t v_sz_223_; size_t v___x_224_; lean_object* v___x_225_; 
v_elems_222_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_elems_222_);
lean_dec_ref_known(v_x_221_, 1);
v_sz_223_ = lean_array_size(v_elems_222_);
v___x_224_ = ((size_t)0ULL);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(v_sz_223_, v___x_224_, v_elems_222_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_226_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_227_ = lean_unsigned_to_nat(80u);
v___x_228_ = l_Lean_Json_pretty(v_x_221_, v___x_227_);
v___x_229_ = lean_string_append(v___x_226_, v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
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
lean_dec_ref_known(v___x_242_, 1);
v___x_252_ = l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(v_a_251_);
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
lean_dec_ref_known(v___x_252_, 1);
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
lean_dec_ref_known(v___x_356_, 1);
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
lean_dec_ref_known(v___x_356_, 1);
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
lean_inc(v_b_447_);
return v_b_447_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg___boxed(lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_contents_463_, lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_461_, v___x_462_, v_contents_463_, v_a_464_, v_b_465_);
lean_dec(v_b_465_);
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
lean_dec_ref_known(v___x_496_, 3);
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
lean_dec_ref_known(v___x_499_, 1);
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
lean_dec_ref_known(v___x_486_, 1);
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
lean_inc(v_b_516_);
return v_b_516_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_contents_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_530_, v___x_531_, v_contents_532_, v_a_533_, v_b_534_);
lean_dec(v_b_534_);
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
lean_dec_ref_known(v___x_565_, 3);
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
lean_dec_ref_known(v___x_568_, 1);
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
lean_dec_ref_known(v___x_555_, 1);
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
lean_dec(v_b_596_);
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
lean_dec(v_b_614_);
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
lean_inc(v_b_642_);
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object* v___x_654_, lean_object* v_contents_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_654_, v_contents_655_, v_a_656_, v_b_657_);
lean_dec(v_b_657_);
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
lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; lean_object* v___y_698_; lean_object* v_searcher_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_searcher_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_string_utf8_byte_size(v_contents_665_);
lean_inc_ref(v_contents_665_);
v___x_736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_736_, 0, v_contents_665_);
lean_ctor_set(v___x_736_, 1, v_searcher_734_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = lean_box(0);
v___x_738_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_736_, v_contents_665_, v_searcher_734_, v___x_737_);
lean_dec_ref_known(v___x_736_, 3);
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
lean_dec_ref_known(v___x_738_, 1);
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
if (v___y_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = lean_unsigned_to_nat(2u);
v___x_677_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_674_);
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
lean_ctor_set(v___x_682_, 0, v___y_674_);
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
lean_dec_ref_known(v___y_688_, 1);
v___y_673_ = v___y_686_;
v___y_674_ = v___y_685_;
v___y_675_ = v___y_687_;
goto v___jp_672_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___y_686_);
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
lean_dec_ref_known(v___x_707_, 2);
v___x_711_ = lean_array_get_size(v_a_710_);
v___x_712_ = lean_nat_dec_lt(v___x_699_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec(v_a_710_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
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
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
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
lean_dec_ref_known(v___x_717_, 1);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___x_699_;
v___y_686_ = v___y_698_;
v___y_687_ = v___x_709_;
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
lean_dec_ref_known(v___x_720_, 1);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___x_699_;
v___y_686_ = v___y_698_;
v___y_687_ = v___x_709_;
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
lean_dec_ref_known(v___x_707_, 2);
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
lean_dec_ref_known(v___x_730_, 1);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___x_699_;
v___y_686_ = v___y_698_;
v___y_687_ = v___x_709_;
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
lean_dec_ref_known(v___x_733_, 1);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___x_699_;
v___y_686_ = v___y_698_;
v___y_687_ = v___x_709_;
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
lean_dec(v_b_760_);
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
lean_dec_ref_known(v___x_770_, 1);
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
lean_dec_ref_known(v___x_770_, 1);
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
lean_dec_ref_known(v___x_801_, 1);
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
lean_dec_ref_known(v___x_806_, 2);
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
lean_dec_ref_known(v___x_801_, 1);
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
lean_dec_ref_known(v___x_837_, 1);
lean_inc_ref(v_fileName_833_);
v___x_839_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_fileName_833_, v_a_838_, v_a_835_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_a_840_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 2);
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
lean_dec_ref_known(v___x_837_, 1);
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
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = 0;
v___x_876_ = lean_io_prim_handle_lock(v_a_874_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
lean_dec_ref_known(v___x_876_, 1);
v___x_877_ = lean_io_prim_handle_get_line(v_a_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
lean_inc_ref(v_file_868_);
v___x_879_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_868_, v_a_878_, v_a_870_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_879_, 1);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 2);
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
lean_dec_ref_known(v___x_877_, 1);
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
lean_dec_ref_known(v___x_876_, 1);
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
lean_dec_ref_known(v___x_873_, 1);
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
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = 0;
v___x_935_ = lean_io_prim_handle_lock(v_a_933_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
lean_dec_ref_known(v___x_935_, 1);
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
lean_dec_ref_known(v___x_941_, 2);
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
lean_dec_ref_known(v___x_945_, 2);
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
lean_dec_ref_known(v___x_941_, 2);
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
lean_dec_ref_known(v___x_936_, 1);
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
lean_dec_ref_known(v___x_935_, 1);
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
lean_dec_ref_known(v___x_932_, 1);
if (lean_obj_tag(v_a_976_) == 11)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec_ref_known(v_a_976_, 2);
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
lean_dec_ref_known(v_x_996_, 3);
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
v___x_1008_ = l_Lake_lowerHexUInt64(v___x_1007_);
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
lean_dec_ref_known(v___x_1016_, 1);
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
lean_dec_ref_known(v___x_1016_, 1);
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
lean_dec_ref_known(v___x_1045_, 2);
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
lean_dec_ref_known(v_x_1064_, 3);
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
lean_dec_ref_known(v_x_1064_, 3);
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
v___x_1080_ = l_Lake_lowerHexUInt64(v___x_1079_);
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
lean_dec_ref_known(v___x_1088_, 1);
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
lean_dec_ref_known(v___x_1088_, 1);
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
lean_dec_ref_known(v___x_1117_, 2);
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
lean_dec_ref_known(v_x_1193_, 3);
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
lean_dec_ref_known(v___x_1225_, 1);
v___x_1226_ = 4;
v___x_1227_ = lean_io_prim_handle_mk(v_file_1217_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
uint8_t v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1227_, 1);
v___x_1228_ = 3;
v___x_1229_ = lean_io_prim_handle_mk(v_file_1217_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = 1;
v___x_1232_ = lean_io_prim_handle_lock(v_a_1230_, v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref_known(v___x_1232_, 1);
v___x_1233_ = lean_io_prim_handle_get_line(v_a_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
lean_inc_ref(v_file_1217_);
v___x_1235_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_1217_, v_a_1234_, v_a_1219_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 2);
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
lean_dec_ref_known(v___x_1249_, 1);
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
lean_dec_ref_known(v___x_1249_, 1);
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
lean_dec_ref_known(v___x_1241_, 2);
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
lean_dec_ref_known(v___x_1235_, 2);
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
lean_dec_ref_known(v___x_1233_, 1);
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
lean_dec_ref_known(v___x_1232_, 1);
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
lean_dec_ref_known(v___x_1229_, 1);
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
lean_dec_ref_known(v___x_1227_, 1);
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
lean_dec_ref_known(v___x_1225_, 1);
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
lean_dec_ref_known(v___x_1328_, 1);
v___x_1329_ = 1;
v___x_1330_ = lean_io_prim_handle_mk(v_file_1323_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v_file_1323_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = 1;
v___x_1333_ = lean_io_prim_handle_lock(v_a_1331_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref_known(v___x_1333_, 1);
v___x_1334_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__2, &l_Lake_CacheMap_writeFile___closed__2_once, _init_l_Lake_CacheMap_writeFile___closed__2);
v___x_1335_ = l_IO_FS_Handle_putStrLn(v_a_1331_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1335_, 1);
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
lean_dec_ref_known(v___x_1335_, 1);
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
lean_dec_ref_known(v___x_1333_, 1);
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
lean_dec_ref_known(v___x_1330_, 1);
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
lean_dec_ref_known(v___x_1328_, 1);
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
lean_dec_ref_known(v_x_1494_, 5);
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1493_, v_l_1498_, v___y_1495_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1500_, 2);
v___x_1503_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1501_, v_v_1497_, v_a_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v_a_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
v_a_1505_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1503_, 2);
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
lean_dec_ref_known(v_o_1509_, 0);
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
lean_dec_ref_known(v_o_1509_, 1);
v___x_1517_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
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
lean_dec_ref_known(v___x_1517_, 1);
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
lean_dec_ref_known(v_o_1509_, 1);
v___x_1535_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
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
lean_dec_ref_known(v___x_1535_, 1);
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
lean_dec_ref_known(v_o_1509_, 1);
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
lean_dec_ref_known(v_o_1509_, 1);
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
lean_dec_ref_known(v___x_1568_, 2);
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
lean_dec_ref_known(v_x_1595_, 3);
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
lean_dec_ref_known(v___x_1602_, 2);
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
lean_dec_ref_known(v___x_1619_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1840_){
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
v___x_1872_ = l_Lean_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1863_);
v_obj_1873_ = l_Lake_JsonObject_insertJson(v___x_1870_, v___x_1871_, v___x_1872_);
if (lean_obj_tag(v_scope_x3f_1864_) == 1)
{
lean_object* v_val_1874_; lean_object* v___y_1876_; uint8_t v___x_1879_; 
v_val_1874_ = lean_ctor_get(v_scope_x3f_1864_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v_scope_x3f_1864_, 1);
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
lean_inc_ref(v___y_1876_);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1886_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
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
v___x_1931_ = lean_string_compare(v_k_1926_, v_k_1928_);
switch(v___x_1931_)
{
case 0:
{
v_t_1927_ = v_l_1929_;
goto _start;
}
case 1:
{
uint8_t v___x_1933_; 
v___x_1933_ = 1;
return v___x_1933_;
}
default: 
{
v_t_1927_ = v_r_1930_;
goto _start;
}
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
lean_dec_ref_known(v_json_1946_, 1);
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
lean_dec_ref_known(v___x_2052_, 1);
v___x_2055_ = l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_2054_);
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
lean_dec_ref_known(v___x_2055_, 1);
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
v___x_1979_ = l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1975_);
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
lean_dec_ref_known(v___x_1979_, 1);
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
v___x_2019_ = l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_2015_);
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
lean_dec_ref_known(v___x_2019_, 1);
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
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2093_ = l_System_FilePath_join(v_cache_2091_, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_2095_, uint64_t v_contentHash_2096_, lean_object* v_ext_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2098_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2099_ = l_System_FilePath_join(v_cache_2095_, v___x_2098_);
v___x_2100_ = lean_string_utf8_byte_size(v_ext_2097_);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_nat_dec_eq(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2103_ = l_Lake_lowerHexUInt64(v_contentHash_2096_);
v___x_2104_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2105_ = lean_string_append(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_string_append(v___x_2105_, v_ext_2097_);
v___x_2107_ = l_System_FilePath_join(v___x_2099_, v___x_2106_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = l_Lake_lowerHexUInt64(v_contentHash_2096_);
v___x_2109_ = l_System_FilePath_join(v___x_2099_, v___x_2108_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_2110_, lean_object* v_contentHash_2111_, lean_object* v_ext_2112_){
_start:
{
uint64_t v_contentHash_boxed_2113_; lean_object* v_res_2114_; 
v_contentHash_boxed_2113_ = lean_unbox_uint64(v_contentHash_2111_);
lean_dec_ref(v_contentHash_2111_);
v_res_2114_ = l_Lake_Cache_artifactPath(v_cache_2110_, v_contentHash_boxed_2113_, v_ext_2112_);
lean_dec_ref(v_ext_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_2115_, lean_object* v_descr_2116_){
_start:
{
uint64_t v_hash_2118_; lean_object* v_ext_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___y_2123_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_hash_2118_ = lean_ctor_get_uint64(v_descr_2116_, sizeof(void*)*1);
v_ext_2119_ = lean_ctor_get(v_descr_2116_, 0);
v___x_2120_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2121_ = l_System_FilePath_join(v_cache_2115_, v___x_2120_);
v___x_2137_ = lean_string_utf8_byte_size(v_ext_2119_);
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_nat_dec_eq(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = l_Lake_lowerHexUInt64(v_hash_2118_);
v___x_2141_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2142_ = lean_string_append(v___x_2140_, v___x_2141_);
v___x_2143_ = lean_string_append(v___x_2142_, v_ext_2119_);
v___y_2123_ = v___x_2143_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lake_lowerHexUInt64(v_hash_2118_);
v___y_2123_ = v___x_2144_;
goto v___jp_2122_;
}
v___jp_2122_:
{
lean_object* v_path_2124_; lean_object* v___x_2125_; 
v_path_2124_ = l_System_FilePath_join(v___x_2121_, v___y_2123_);
v___x_2125_ = lean_io_metadata(v_path_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2135_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_modified_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v_modified_2130_ = lean_ctor_get(v_a_2126_, 1);
lean_inc_ref(v_modified_2130_);
lean_dec(v_a_2126_);
lean_inc_ref(v_path_2124_);
v___x_2131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2131_, 0, v_descr_2116_);
lean_ctor_set(v___x_2131_, 1, v_path_2124_);
lean_ctor_set(v___x_2131_, 2, v_path_2124_);
lean_ctor_set(v___x_2131_, 3, v_modified_2130_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2131_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
else
{
lean_object* v___x_2136_; 
lean_dec_ref_known(v___x_2125_, 1);
lean_dec_ref(v_path_2124_);
lean_dec_ref(v_descr_2116_);
v___x_2136_ = lean_box(0);
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_2145_, lean_object* v_descr_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lake_Cache_getArtifact_x3f(v_cache_2145_, v_descr_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_2151_, lean_object* v_descr_2152_){
_start:
{
uint64_t v_hash_2154_; lean_object* v_ext_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___y_2159_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_hash_2154_ = lean_ctor_get_uint64(v_descr_2152_, sizeof(void*)*1);
v_ext_2155_ = lean_ctor_get(v_descr_2152_, 0);
v___x_2156_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2157_ = l_System_FilePath_join(v_cache_2151_, v___x_2156_);
v___x_2188_ = lean_string_utf8_byte_size(v_ext_2155_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_eq(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = l_Lake_lowerHexUInt64(v_hash_2154_);
v___x_2192_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2193_ = lean_string_append(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_string_append(v___x_2193_, v_ext_2155_);
v___y_2159_ = v___x_2194_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lake_lowerHexUInt64(v_hash_2154_);
v___y_2159_ = v___x_2195_;
goto v___jp_2158_;
}
v___jp_2158_:
{
lean_object* v_path_2160_; lean_object* v___x_2161_; 
v_path_2160_ = l_System_FilePath_join(v___x_2157_, v___y_2159_);
v___x_2161_ = lean_io_metadata(v_path_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2171_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_modified_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v_modified_2166_ = lean_ctor_get(v_a_2162_, 1);
lean_inc_ref(v_modified_2166_);
lean_dec(v_a_2162_);
lean_inc_ref(v_path_2160_);
v___x_2167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2167_, 0, v_descr_2152_);
lean_ctor_set(v___x_2167_, 1, v_path_2160_);
lean_ctor_set(v___x_2167_, 2, v_path_2160_);
lean_ctor_set(v___x_2167_, 3, v_modified_2166_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2167_);
v___x_2169_ = v___x_2164_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_descr_2152_);
v_a_2172_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2174_ = v___x_2161_;
v_isShared_2175_ = v_isSharedCheck_2187_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2161_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2187_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
if (lean_obj_tag(v_a_2172_) == 11)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
lean_dec_ref_known(v_a_2172_, 2);
v___x_2176_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2177_ = lean_string_append(v___x_2176_, v_path_2160_);
lean_dec_ref(v_path_2160_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2177_);
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec_ref(v_path_2160_);
v___x_2181_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_2182_ = lean_io_error_to_string(v_a_2172_);
v___x_2183_ = lean_string_append(v___x_2181_, v___x_2182_);
lean_dec_ref(v___x_2182_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2183_);
v___x_2185_ = v___x_2174_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_2196_, lean_object* v_descr_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lake_Cache_getArtifact(v_cache_2196_, v_descr_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2201_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2203_ = l_System_FilePath_join(v_cache_2201_, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2205_, lean_object* v_scope_2206_, uint64_t v_inputHash_2207_){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2208_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2209_ = l_System_FilePath_join(v_cache_2205_, v___x_2208_);
v___x_2210_ = l_System_FilePath_join(v___x_2209_, v_scope_2206_);
v___x_2211_ = l_Lake_lowerHexUInt64(v_inputHash_2207_);
v___x_2212_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
v___x_2214_ = l_System_FilePath_join(v___x_2210_, v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2215_, lean_object* v_scope_2216_, lean_object* v_inputHash_2217_){
_start:
{
uint64_t v_inputHash_boxed_2218_; lean_object* v_res_2219_; 
v_inputHash_boxed_2218_ = lean_unbox_uint64(v_inputHash_2217_);
lean_dec_ref(v_inputHash_2217_);
v_res_2219_ = l_Lake_Cache_outputsFile(v_cache_2215_, v_scope_2216_, v_inputHash_boxed_2218_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2220_, lean_object* v_scope_2221_, uint64_t v_inputHash_2222_, lean_object* v_out_2223_, lean_object* v_service_x3f_2224_, lean_object* v_remoteScope_x3f_2225_, uint8_t v_overwrite_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_file_2234_; lean_object* v___x_2235_; 
v___x_2228_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2229_ = l_System_FilePath_join(v_cache_2220_, v___x_2228_);
v___x_2230_ = l_System_FilePath_join(v___x_2229_, v_scope_2221_);
v___x_2231_ = l_Lake_lowerHexUInt64(v_inputHash_2222_);
v___x_2232_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2233_ = lean_string_append(v___x_2231_, v___x_2232_);
v_file_2234_ = l_System_FilePath_join(v___x_2230_, v___x_2233_);
lean_inc_ref(v_file_2234_);
v___x_2235_ = l_Lake_createParentDirs(v_file_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref_known(v___x_2235_, 1);
v___x_2236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2236_, 0, v_out_2223_);
lean_ctor_set(v___x_2236_, 1, v_service_x3f_2224_);
lean_ctor_set(v___x_2236_, 2, v_remoteScope_x3f_2225_);
v___x_2237_ = l_Lake_CacheOutput_toJson(v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(80u);
v___x_2239_ = l_Lean_Json_pretty(v___x_2237_, v___x_2238_);
if (v_overwrite_2226_ == 0)
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lake_writeFileIfNew(v_file_2234_, v___x_2239_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v_file_2234_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = l_IO_FS_writeFile(v_file_2234_, v___x_2239_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v_file_2234_);
return v___x_2241_;
}
}
else
{
lean_dec_ref(v_file_2234_);
lean_dec(v_remoteScope_x3f_2225_);
lean_dec(v_service_x3f_2224_);
lean_dec(v_out_2223_);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2242_, lean_object* v_scope_2243_, lean_object* v_inputHash_2244_, lean_object* v_out_2245_, lean_object* v_service_x3f_2246_, lean_object* v_remoteScope_x3f_2247_, lean_object* v_overwrite_2248_, lean_object* v_a_2249_){
_start:
{
uint64_t v_inputHash_boxed_2250_; uint8_t v_overwrite_boxed_2251_; lean_object* v_res_2252_; 
v_inputHash_boxed_2250_ = lean_unbox_uint64(v_inputHash_2244_);
lean_dec_ref(v_inputHash_2244_);
v_overwrite_boxed_2251_ = lean_unbox(v_overwrite_2248_);
v_res_2252_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2242_, v_scope_2243_, v_inputHash_boxed_2250_, v_out_2245_, v_service_x3f_2246_, v_remoteScope_x3f_2247_, v_overwrite_boxed_2251_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2253_, lean_object* v_cache_2254_, lean_object* v_scope_2255_, uint64_t v_inputHash_2256_, lean_object* v_outputs_2257_, lean_object* v_service_x3f_2258_, lean_object* v_remoteScope_x3f_2259_, uint8_t v_overwrite_2260_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_apply_1(v_inst_2253_, v_outputs_2257_);
v___x_2263_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2254_, v_scope_2255_, v_inputHash_2256_, v___x_2262_, v_service_x3f_2258_, v_remoteScope_x3f_2259_, v_overwrite_2260_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2264_, lean_object* v_cache_2265_, lean_object* v_scope_2266_, lean_object* v_inputHash_2267_, lean_object* v_outputs_2268_, lean_object* v_service_x3f_2269_, lean_object* v_remoteScope_x3f_2270_, lean_object* v_overwrite_2271_, lean_object* v_a_2272_){
_start:
{
uint64_t v_inputHash_boxed_2273_; uint8_t v_overwrite_boxed_2274_; lean_object* v_res_2275_; 
v_inputHash_boxed_2273_ = lean_unbox_uint64(v_inputHash_2267_);
lean_dec_ref(v_inputHash_2267_);
v_overwrite_boxed_2274_ = lean_unbox(v_overwrite_2271_);
v_res_2275_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2264_, v_cache_2265_, v_scope_2266_, v_inputHash_boxed_2273_, v_outputs_2268_, v_service_x3f_2269_, v_remoteScope_x3f_2270_, v_overwrite_boxed_2274_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2276_, lean_object* v_inst_2277_, lean_object* v_cache_2278_, lean_object* v_scope_2279_, uint64_t v_inputHash_2280_, lean_object* v_outputs_2281_, lean_object* v_service_x3f_2282_, lean_object* v_remoteScope_x3f_2283_, uint8_t v_overwrite_2284_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_apply_1(v_inst_2277_, v_outputs_2281_);
v___x_2287_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2278_, v_scope_2279_, v_inputHash_2280_, v___x_2286_, v_service_x3f_2282_, v_remoteScope_x3f_2283_, v_overwrite_2284_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2288_, lean_object* v_inst_2289_, lean_object* v_cache_2290_, lean_object* v_scope_2291_, lean_object* v_inputHash_2292_, lean_object* v_outputs_2293_, lean_object* v_service_x3f_2294_, lean_object* v_remoteScope_x3f_2295_, lean_object* v_overwrite_2296_, lean_object* v_a_2297_){
_start:
{
uint64_t v_inputHash_boxed_2298_; uint8_t v_overwrite_boxed_2299_; lean_object* v_res_2300_; 
v_inputHash_boxed_2298_ = lean_unbox_uint64(v_inputHash_2292_);
lean_dec_ref(v_inputHash_2292_);
v_overwrite_boxed_2299_ = lean_unbox(v_overwrite_2296_);
v_res_2300_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2288_, v_inst_2289_, v_cache_2290_, v_scope_2291_, v_inputHash_boxed_2298_, v_outputs_2293_, v_service_x3f_2294_, v_remoteScope_x3f_2295_, v_overwrite_boxed_2299_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2301_, lean_object* v_scope_2302_, lean_object* v_service_x3f_2303_, lean_object* v_remoteScope_x3f_2304_, uint8_t v_overwrite_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
if (lean_obj_tag(v_x_2307_) == 0)
{
lean_object* v___x_2309_; 
lean_dec(v_remoteScope_x3f_2304_);
lean_dec(v_service_x3f_2303_);
lean_dec_ref(v_scope_2302_);
lean_dec_ref(v_cache_2301_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_x_2306_);
return v___x_2309_;
}
else
{
lean_object* v_value_2310_; lean_object* v_key_2311_; lean_object* v_tail_2312_; lean_object* v_out_2313_; uint64_t v___x_2314_; lean_object* v___x_2315_; 
v_value_2310_ = lean_ctor_get(v_x_2307_, 1);
lean_inc(v_value_2310_);
v_key_2311_ = lean_ctor_get(v_x_2307_, 0);
lean_inc(v_key_2311_);
v_tail_2312_ = lean_ctor_get(v_x_2307_, 2);
lean_inc(v_tail_2312_);
lean_dec_ref_known(v_x_2307_, 3);
v_out_2313_ = lean_ctor_get(v_value_2310_, 0);
lean_inc(v_out_2313_);
lean_dec(v_value_2310_);
v___x_2314_ = lean_unbox_uint64(v_key_2311_);
lean_dec(v_key_2311_);
lean_inc(v_remoteScope_x3f_2304_);
lean_inc(v_service_x3f_2303_);
lean_inc_ref(v_scope_2302_);
lean_inc_ref(v_cache_2301_);
v___x_2315_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2301_, v_scope_2302_, v___x_2314_, v_out_2313_, v_service_x3f_2303_, v_remoteScope_x3f_2304_, v_overwrite_2305_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_x_2306_ = v_a_2316_;
v_x_2307_ = v_tail_2312_;
goto _start;
}
else
{
lean_dec(v_tail_2312_);
lean_dec(v_remoteScope_x3f_2304_);
lean_dec(v_service_x3f_2303_);
lean_dec_ref(v_scope_2302_);
lean_dec_ref(v_cache_2301_);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2318_, lean_object* v_scope_2319_, lean_object* v_service_x3f_2320_, lean_object* v_remoteScope_x3f_2321_, lean_object* v_overwrite_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v_overwrite_boxed_2326_; lean_object* v_res_2327_; 
v_overwrite_boxed_2326_ = lean_unbox(v_overwrite_2322_);
v_res_2327_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2318_, v_scope_2319_, v_service_x3f_2320_, v_remoteScope_x3f_2321_, v_overwrite_boxed_2326_, v_x_2323_, v_x_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2328_, lean_object* v_scope_2329_, lean_object* v_service_x3f_2330_, lean_object* v_remoteScope_x3f_2331_, uint8_t v_overwrite_2332_, lean_object* v_as_2333_, size_t v_i_2334_, size_t v_stop_2335_, lean_object* v_b_2336_){
_start:
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_usize_dec_eq(v_i_2334_, v_stop_2335_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = lean_array_uget_borrowed(v_as_2333_, v_i_2334_);
v___x_2340_ = lean_box(0);
lean_inc(v___x_2339_);
lean_inc(v_remoteScope_x3f_2331_);
lean_inc(v_service_x3f_2330_);
lean_inc_ref(v_scope_2329_);
lean_inc_ref(v_cache_2328_);
v___x_2341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2328_, v_scope_2329_, v_service_x3f_2330_, v_remoteScope_x3f_2331_, v_overwrite_2332_, v___x_2340_, v___x_2339_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; size_t v___x_2343_; size_t v___x_2344_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = ((size_t)1ULL);
v___x_2344_ = lean_usize_add(v_i_2334_, v___x_2343_);
v_i_2334_ = v___x_2344_;
v_b_2336_ = v_a_2342_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2331_);
lean_dec(v_service_x3f_2330_);
lean_dec_ref(v_scope_2329_);
lean_dec_ref(v_cache_2328_);
return v___x_2341_;
}
}
else
{
lean_object* v___x_2346_; 
lean_dec(v_remoteScope_x3f_2331_);
lean_dec(v_service_x3f_2330_);
lean_dec_ref(v_scope_2329_);
lean_dec_ref(v_cache_2328_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_b_2336_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2347_, lean_object* v_scope_2348_, lean_object* v_service_x3f_2349_, lean_object* v_remoteScope_x3f_2350_, lean_object* v_overwrite_2351_, lean_object* v_as_2352_, lean_object* v_i_2353_, lean_object* v_stop_2354_, lean_object* v_b_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v_overwrite_boxed_2357_; size_t v_i_boxed_2358_; size_t v_stop_boxed_2359_; lean_object* v_res_2360_; 
v_overwrite_boxed_2357_ = lean_unbox(v_overwrite_2351_);
v_i_boxed_2358_ = lean_unbox_usize(v_i_2353_);
lean_dec(v_i_2353_);
v_stop_boxed_2359_ = lean_unbox_usize(v_stop_2354_);
lean_dec(v_stop_2354_);
v_res_2360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2347_, v_scope_2348_, v_service_x3f_2349_, v_remoteScope_x3f_2350_, v_overwrite_boxed_2357_, v_as_2352_, v_i_boxed_2358_, v_stop_boxed_2359_, v_b_2355_);
lean_dec_ref(v_as_2352_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2361_, lean_object* v_scope_2362_, lean_object* v_map_2363_, lean_object* v_service_x3f_2364_, lean_object* v_remoteScope_x3f_2365_, uint8_t v_overwrite_2366_){
_start:
{
lean_object* v_buckets_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_buckets_2368_ = lean_ctor_get(v_map_2363_, 1);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_array_get_size(v_buckets_2368_);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_nat_dec_lt(v___x_2369_, v___x_2370_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_dec(v_remoteScope_x3f_2365_);
lean_dec(v_service_x3f_2364_);
lean_dec_ref(v_scope_2362_);
lean_dec_ref(v_cache_2361_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
return v___x_2373_;
}
else
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_nat_dec_le(v___x_2370_, v___x_2370_);
if (v___x_2374_ == 0)
{
if (v___x_2372_ == 0)
{
lean_object* v___x_2375_; 
lean_dec(v_remoteScope_x3f_2365_);
lean_dec(v_service_x3f_2364_);
lean_dec_ref(v_scope_2362_);
lean_dec_ref(v_cache_2361_);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2371_);
return v___x_2375_;
}
else
{
size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = lean_usize_of_nat(v___x_2370_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2361_, v_scope_2362_, v_service_x3f_2364_, v_remoteScope_x3f_2365_, v_overwrite_2366_, v_buckets_2368_, v___x_2376_, v___x_2377_, v___x_2371_);
return v___x_2378_;
}
}
else
{
size_t v___x_2379_; size_t v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = ((size_t)0ULL);
v___x_2380_ = lean_usize_of_nat(v___x_2370_);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2361_, v_scope_2362_, v_service_x3f_2364_, v_remoteScope_x3f_2365_, v_overwrite_2366_, v_buckets_2368_, v___x_2379_, v___x_2380_, v___x_2371_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2382_, lean_object* v_scope_2383_, lean_object* v_map_2384_, lean_object* v_service_x3f_2385_, lean_object* v_remoteScope_x3f_2386_, lean_object* v_overwrite_2387_, lean_object* v_a_2388_){
_start:
{
uint8_t v_overwrite_boxed_2389_; lean_object* v_res_2390_; 
v_overwrite_boxed_2389_ = lean_unbox(v_overwrite_2387_);
v_res_2390_ = l_Lake_Cache_writeMap(v_cache_2382_, v_scope_2383_, v_map_2384_, v_service_x3f_2385_, v_remoteScope_x3f_2386_, v_overwrite_boxed_2389_);
lean_dec_ref(v_map_2384_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2393_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lake_CacheOutput_fromJson_x3f(v_x_2393_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2412_; 
v_a_2404_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2406_ = v___x_2395_;
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2395_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_a_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2415_, lean_object* v_scope_2416_, uint64_t v_inputHash_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v_path_2426_; lean_object* v___x_2427_; 
v___x_2420_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2421_ = l_System_FilePath_join(v_cache_2415_, v___x_2420_);
v___x_2422_ = l_System_FilePath_join(v___x_2421_, v_scope_2416_);
v___x_2423_ = l_Lake_lowerHexUInt64(v_inputHash_2417_);
v___x_2424_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2425_ = lean_string_append(v___x_2423_, v___x_2424_);
v_path_2426_ = l_System_FilePath_join(v___x_2422_, v___x_2425_);
v___x_2427_ = l_IO_FS_readFile(v_path_2426_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v_a_2430_; lean_object* v___x_2439_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2439_ = l_Lean_Json_parse(v_a_2428_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v_a_2430_ = v_a_2440_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2442_ = l_Lean_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2441_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v_a_2430_ = v_a_2443_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
lean_dec_ref(v_path_2426_);
v_a_2444_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v_a_2444_);
lean_ctor_set(v___x_2445_, 1, v_a_2418_);
return v___x_2445_;
}
}
v___jp_2429_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2431_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2432_ = lean_string_append(v_path_2426_, v___x_2431_);
v___x_2433_ = lean_string_append(v___x_2432_, v_a_2430_);
lean_dec_ref(v_a_2430_);
v___x_2434_ = 2;
v___x_2435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*1, v___x_2434_);
v___x_2436_ = lean_array_push(v_a_2418_, v___x_2435_);
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2436_);
return v___x_2438_;
}
}
else
{
lean_object* v_a_2446_; 
v_a_2446_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2427_, 1);
if (lean_obj_tag(v_a_2446_) == 11)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref_known(v_a_2446_, 2);
lean_dec_ref(v_path_2426_);
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_a_2418_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2449_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2450_ = lean_string_append(v_path_2426_, v___x_2449_);
v___x_2451_ = lean_io_error_to_string(v_a_2446_);
v___x_2452_ = lean_string_append(v___x_2450_, v___x_2451_);
lean_dec_ref(v___x_2451_);
v___x_2453_ = 3;
v___x_2454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set_uint8(v___x_2454_, sizeof(void*)*1, v___x_2453_);
v___x_2455_ = lean_array_get_size(v_a_2418_);
v___x_2456_ = lean_array_push(v_a_2418_, v___x_2454_);
v___x_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2458_, lean_object* v_scope_2459_, lean_object* v_inputHash_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
uint64_t v_inputHash_boxed_2463_; lean_object* v_res_2464_; 
v_inputHash_boxed_2463_ = lean_unbox_uint64(v_inputHash_2460_);
lean_dec_ref(v_inputHash_2460_);
v_res_2464_ = l_Lake_Cache_readOutputs_x3f(v_cache_2458_, v_scope_2459_, v_inputHash_boxed_2463_, v_a_2461_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2468_ = l_System_FilePath_join(v_cache_2466_, v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2470_, lean_object* v_scope_2471_, lean_object* v_rev_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2473_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2474_ = l_System_FilePath_join(v_cache_2470_, v___x_2473_);
v___x_2475_ = l_System_FilePath_join(v___x_2474_, v_scope_2471_);
v___x_2476_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2477_ = lean_string_append(v_rev_2472_, v___x_2476_);
v___x_2478_ = l_System_FilePath_join(v___x_2475_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2481_ = lean_string_utf8_byte_size(v_self_2480_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_nat_dec_eq(v___x_2481_, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2484_){
_start:
{
uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_res_2485_ = l_Lake_CachePlatform_isNone(v_self_2484_);
lean_dec_ref(v_self_2484_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_System_Platform_target;
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2488_){
_start:
{
lean_inc_ref(v_s_2488_);
return v_s_2488_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lake_CachePlatform_ofString(v_s_2489_);
lean_dec_ref(v_s_2489_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(lean_object* v___x_2491_, lean_object* v___x_2492_, lean_object* v_a_2493_, lean_object* v_b_2494_){
_start:
{
lean_object* v_startInclusive_2495_; lean_object* v_endExclusive_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v_startInclusive_2495_ = lean_ctor_get(v___x_2491_, 1);
v_endExclusive_2496_ = lean_ctor_get(v___x_2491_, 2);
v___x_2497_ = lean_nat_sub(v_endExclusive_2496_, v_startInclusive_2495_);
v___x_2498_ = lean_nat_dec_eq(v_a_2493_, v___x_2497_);
lean_dec(v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_string_utf8_next_fast(v___x_2492_, v_a_2493_);
lean_dec(v_a_2493_);
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = lean_nat_add(v_b_2494_, v___x_2500_);
lean_dec(v_b_2494_);
v_a_2493_ = v___x_2499_;
v_b_2494_ = v___x_2501_;
goto _start;
}
else
{
lean_dec(v_a_2493_);
return v_b_2494_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg___boxed(lean_object* v___x_2503_, lean_object* v___x_2504_, lean_object* v_a_2505_, lean_object* v_b_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2503_, v___x_2504_, v_a_2505_, v_b_2506_);
lean_dec_ref(v___x_2504_);
lean_dec_ref(v___x_2503_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = lean_string_utf8_byte_size(v_self_2508_);
lean_inc_ref(v_self_2508_);
v___x_2511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2511_, 0, v_self_2508_);
lean_ctor_set(v___x_2511_, 1, v___x_2509_);
lean_ctor_set(v___x_2511_, 2, v___x_2510_);
v___x_2512_ = l_String_Slice_positions(v___x_2511_);
v___x_2513_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2511_, v_self_2508_, v___x_2512_, v___x_2509_);
lean_dec_ref(v_self_2508_);
lean_dec_ref_known(v___x_2511_, 3);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(lean_object* v___x_2514_, lean_object* v___x_2515_, lean_object* v_inst_2516_, lean_object* v_R_2517_, lean_object* v_a_2518_, lean_object* v_b_2519_, lean_object* v_c_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2514_, v___x_2515_, v_a_2518_, v_b_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___boxed(lean_object* v___x_2522_, lean_object* v___x_2523_, lean_object* v_inst_2524_, lean_object* v_R_2525_, lean_object* v_a_2526_, lean_object* v_b_2527_, lean_object* v_c_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(v___x_2522_, v___x_2523_, v_inst_2524_, v_R_2525_, v_a_2526_, v_b_2527_, v_c_2528_);
lean_dec_ref(v___x_2523_);
lean_dec_ref(v___x_2522_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2531_){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = lean_string_utf8_byte_size(v_self_2531_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_nat_dec_eq(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_inc_ref(v_self_2531_);
return v_self_2531_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lake_CachePlatform_toString(v_self_2536_);
lean_dec_ref(v_self_2536_);
return v_res_2537_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2541_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_string_utf8_byte_size(v_self_2541_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_nat_dec_eq(v___x_2542_, v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2545_){
_start:
{
uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_res_2546_ = l_Lake_CacheToolchain_isNone(v_self_2545_);
lean_dec_ref(v_self_2545_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lake_normalizeToolchain(v_s_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2550_){
_start:
{
lean_inc_ref(v_s_2550_);
return v_s_2550_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2551_);
lean_dec_ref(v_s_2551_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = lean_string_utf8_byte_size(v_self_2553_);
lean_inc_ref(v_self_2553_);
v___x_2556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2556_, 0, v_self_2553_);
lean_ctor_set(v___x_2556_, 1, v___x_2554_);
lean_ctor_set(v___x_2556_, 2, v___x_2555_);
v___x_2557_ = l_String_Slice_positions(v___x_2556_);
v___x_2558_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2556_, v_self_2553_, v___x_2557_, v___x_2554_);
lean_dec_ref(v_self_2553_);
lean_dec_ref_known(v___x_2556_, 3);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2559_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2560_ = lean_string_utf8_byte_size(v_self_2559_);
v___x_2561_ = lean_unsigned_to_nat(0u);
v___x_2562_ = lean_nat_dec_eq(v___x_2560_, v___x_2561_);
if (v___x_2562_ == 0)
{
lean_inc_ref(v_self_2559_);
return v_self_2559_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lake_CacheToolchain_toString(v_self_2564_);
lean_dec_ref(v_self_2564_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2571_, lean_object* v_url_2572_, lean_object* v_path_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2573_);
v___x_2577_ = l_Lake_download(v_url_2572_, v_path_2573_, v___x_2576_, v_a_2574_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2621_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2577_, 0);
lean_dec(v_unused_2622_);
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2621_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2621_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lake_computeBinFileHash(v_path_2573_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; uint64_t v___x_2584_; uint8_t v___x_2585_; uint8_t v___x_2586_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = lean_unbox_uint64(v_a_2583_);
v___x_2585_ = lean_uint64_dec_eq(v___x_2584_, v_hash_2571_);
v___x_2586_ = lean_bool_not(v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec(v_a_2583_);
lean_dec_ref(v_path_2573_);
v___x_2587_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2587_);
v___x_2589_ = v___x_2580_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_a_2578_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; uint64_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2591_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_2573_);
v___x_2592_ = lean_string_append(v_path_2573_, v___x_2591_);
v___x_2593_ = lean_unbox_uint64(v_a_2583_);
lean_dec(v_a_2583_);
v___x_2594_ = l_Lake_lowerHexUInt64(v___x_2593_);
v___x_2595_ = lean_string_append(v___x_2592_, v___x_2594_);
lean_dec_ref(v___x_2594_);
v___x_2596_ = 3;
v___x_2597_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*1, v___x_2596_);
lean_inc(v_a_2578_);
v___x_2598_ = lean_array_push(v_a_2578_, v___x_2597_);
v___x_2599_ = lean_io_remove_file(v_path_2573_);
lean_dec_ref(v_path_2573_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec_ref_known(v___x_2599_, 1);
v___x_2600_ = lean_array_get_size(v_a_2578_);
lean_dec(v_a_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2598_);
lean_ctor_set(v___x_2580_, 0, v___x_2600_);
v___x_2602_ = v___x_2580_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2598_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec(v_a_2578_);
v_a_2604_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2605_ = lean_io_error_to_string(v_a_2604_);
v___x_2606_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*1, v___x_2596_);
v___x_2607_ = lean_array_get_size(v___x_2598_);
v___x_2608_ = lean_array_push(v___x_2598_, v___x_2606_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2608_);
lean_ctor_set(v___x_2580_, 0, v___x_2607_);
v___x_2610_ = v___x_2580_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec_ref(v_path_2573_);
v_a_2612_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2613_ = lean_io_error_to_string(v_a_2612_);
v___x_2614_ = 3;
v___x_2615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1, v___x_2614_);
v___x_2616_ = lean_array_get_size(v_a_2578_);
v___x_2617_ = lean_array_push(v_a_2578_, v___x_2615_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2617_);
lean_ctor_set(v___x_2580_, 0, v___x_2616_);
v___x_2619_ = v___x_2580_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_dec_ref(v_path_2573_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2623_, lean_object* v_url_2624_, lean_object* v_path_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
uint64_t v_hash_boxed_2628_; lean_object* v_res_2629_; 
v_hash_boxed_2628_ = lean_unbox_uint64(v_hash_2623_);
lean_dec_ref(v_hash_2623_);
v_res_2629_ = l_Lake_downloadArtifactCore(v_hash_boxed_2628_, v_url_2624_, v_path_2625_, v_a_2626_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2632_){
_start:
{
if (lean_obj_tag(v_x_2632_) == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Json_getNat_x3f(v_x_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2651_; 
v_a_2643_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2645_ = v___x_2634_;
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2634_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2647_, 0, v_a_2643_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2647_);
v___x_2649_ = v___x_2645_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2674_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2675_ = lean_unsigned_to_nat(14u);
v___x_2676_ = lean_mk_empty_array_with_capacity(v___x_2675_);
v___x_2677_ = lean_array_push(v___x_2676_, v___x_2674_);
return v___x_2677_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2679_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2680_ = lean_array_push(v___x_2679_, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2682_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2683_ = lean_array_push(v___x_2682_, v___x_2681_);
return v___x_2683_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2685_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2686_ = lean_array_push(v___x_2685_, v___x_2684_);
return v___x_2686_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2688_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2689_ = lean_array_push(v___x_2688_, v___x_2687_);
return v___x_2689_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2691_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2692_ = lean_array_push(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2696_, lean_object* v_contentType_2697_, lean_object* v_url_2698_, lean_object* v_key_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___y_2703_; lean_object* v_a_2704_; lean_object* v_stderr_2717_; lean_object* v___y_2726_; lean_object* v___y_2729_; lean_object* v_a_2730_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v_stderr_2769_; lean_object* v_a_2770_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2784_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2785_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2786_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2787_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2788_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2789_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2790_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2791_ = lean_string_append(v___x_2790_, v_contentType_2697_);
v___x_2792_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2793_ = lean_array_push(v___x_2792_, v_key_2699_);
v___x_2794_ = lean_array_push(v___x_2793_, v___x_2786_);
v___x_2795_ = lean_array_push(v___x_2794_, v___x_2787_);
v___x_2796_ = lean_array_push(v___x_2795_, v___x_2788_);
v___x_2797_ = lean_array_push(v___x_2796_, v_file_2696_);
v___x_2798_ = lean_array_push(v___x_2797_, v_url_2698_);
v___x_2799_ = lean_array_push(v___x_2798_, v___x_2789_);
v___x_2800_ = lean_array_push(v___x_2799_, v___x_2791_);
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2804_ = 1;
v___x_2805_ = 0;
v___x_2806_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2806_, 0, v___x_2784_);
lean_ctor_set(v___x_2806_, 1, v___x_2785_);
lean_ctor_set(v___x_2806_, 2, v___x_2800_);
lean_ctor_set(v___x_2806_, 3, v___x_2801_);
lean_ctor_set(v___x_2806_, 4, v___x_2803_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*5, v___x_2804_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*5 + 1, v___x_2805_);
v___x_2807_ = l_Lake_captureProc_x27(v___x_2806_, v___x_2803_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v_a_2809_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
v_a_2809_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2807_, 2);
v___x_2823_ = lean_array_get_size(v_a_2809_);
v___x_2824_ = lean_nat_dec_lt(v___x_2802_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_dec(v_a_2809_);
goto v___jp_2810_;
}
else
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_nat_dec_le(v___x_2823_, v___x_2823_);
if (v___x_2826_ == 0)
{
if (v___x_2824_ == 0)
{
lean_dec(v_a_2809_);
goto v___jp_2810_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = lean_usize_of_nat(v___x_2823_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2809_, v___x_2827_, v___x_2828_, v___x_2825_, v_a_2700_);
lean_dec(v_a_2809_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_dec_ref_known(v___x_2829_, 1);
goto v___jp_2810_;
}
else
{
lean_dec(v_a_2808_);
return v___x_2829_;
}
}
}
else
{
size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = lean_usize_of_nat(v___x_2823_);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2809_, v___x_2830_, v___x_2831_, v___x_2825_, v_a_2700_);
lean_dec(v_a_2809_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_dec_ref_known(v___x_2832_, 1);
goto v___jp_2810_;
}
else
{
lean_dec(v_a_2808_);
return v___x_2832_;
}
}
}
v___jp_2810_:
{
lean_object* v_stderr_2811_; lean_object* v___x_2812_; 
v_stderr_2811_ = lean_ctor_get(v_a_2808_, 1);
lean_inc_ref(v_stderr_2811_);
v___x_2812_ = l_Lean_Json_parse(v_stderr_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; 
lean_inc_ref(v_stderr_2811_);
lean_dec(v_a_2808_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v_stderr_2769_ = v_stderr_2811_;
v_a_2770_ = v_a_2813_;
goto v___jp_2768_;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2815_; 
v_a_2814_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2815_ = l_Lean_Json_getObj_x3f(v_a_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
lean_inc_ref(v_stderr_2811_);
lean_dec(v_a_2808_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v_stderr_2769_ = v_stderr_2811_;
v_a_2770_ = v_a_2816_;
goto v___jp_2768_;
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2817_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2818_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2819_ = l_Lake_JsonObject_getJson_x3f(v_a_2817_, v___x_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_inc_ref(v_stderr_2811_);
lean_dec(v_a_2817_);
lean_dec(v_a_2808_);
v_stderr_2717_ = v_stderr_2811_;
goto v___jp_2716_;
}
else
{
lean_object* v_val_2820_; lean_object* v___x_2821_; 
v_val_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_val_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2820_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_dec_ref_known(v___x_2821_, 1);
v___y_2757_ = v_a_2817_;
v___y_2758_ = v_a_2808_;
goto v___jp_2756_;
}
else
{
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_dec_ref_known(v___x_2821_, 1);
v___y_2757_ = v_a_2817_;
v___y_2758_ = v_a_2808_;
goto v___jp_2756_;
}
else
{
lean_object* v_a_2822_; 
lean_dec(v_a_2817_);
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___y_2729_ = v_a_2808_;
v_a_2730_ = v_a_2822_;
goto v___jp_2728_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v_a_2833_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2807_, 2);
v___x_2834_ = lean_array_get_size(v_a_2833_);
v___x_2835_ = lean_nat_dec_lt(v___x_2802_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v_a_2833_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
else
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_nat_dec_le(v___x_2834_, v___x_2834_);
if (v___x_2839_ == 0)
{
if (v___x_2835_ == 0)
{
lean_dec(v_a_2833_);
goto v___jp_2781_;
}
else
{
size_t v___x_2840_; size_t v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = ((size_t)0ULL);
v___x_2841_ = lean_usize_of_nat(v___x_2834_);
v___x_2842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2833_, v___x_2840_, v___x_2841_, v___x_2838_, v_a_2700_);
lean_dec(v_a_2833_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref_known(v___x_2842_, 1);
goto v___jp_2781_;
}
else
{
return v___x_2842_;
}
}
}
else
{
size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = lean_usize_of_nat(v___x_2834_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2833_, v___x_2843_, v___x_2844_, v___x_2838_, v_a_2700_);
lean_dec(v_a_2833_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_dec_ref_known(v___x_2845_, 1);
goto v___jp_2781_;
}
else
{
return v___x_2845_;
}
}
}
}
v___jp_2702_:
{
lean_object* v_stderr_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_stderr_2705_ = lean_ctor_get(v___y_2703_, 1);
lean_inc_ref(v_stderr_2705_);
lean_dec_ref(v___y_2703_);
v___x_2706_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2707_ = lean_string_append(v___x_2706_, v_a_2704_);
lean_dec_ref(v_a_2704_);
v___x_2708_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2709_ = lean_string_append(v___x_2707_, v___x_2708_);
v___x_2710_ = lean_string_append(v___x_2709_, v_stderr_2705_);
lean_dec_ref(v_stderr_2705_);
v___x_2711_ = 3;
v___x_2712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*1, v___x_2711_);
lean_inc_ref(v_a_2700_);
v___x_2713_ = lean_apply_2(v_a_2700_, v___x_2712_, lean_box(0));
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2718_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2719_ = lean_string_append(v___x_2718_, v_stderr_2717_);
lean_dec_ref(v_stderr_2717_);
v___x_2720_ = 3;
v___x_2721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*1, v___x_2720_);
lean_inc_ref(v_a_2700_);
v___x_2722_ = lean_apply_2(v_a_2700_, v___x_2721_, lean_box(0));
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
v___jp_2725_:
{
lean_object* v_stderr_2727_; 
v_stderr_2727_ = lean_ctor_get(v___y_2726_, 1);
lean_inc_ref(v_stderr_2727_);
lean_dec_ref(v___y_2726_);
v_stderr_2717_ = v_stderr_2727_;
goto v___jp_2716_;
}
v___jp_2728_:
{
if (lean_obj_tag(v_a_2730_) == 0)
{
v___y_2726_ = v___y_2729_;
goto v___jp_2725_;
}
else
{
lean_object* v_val_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2755_; 
v_val_2731_ = lean_ctor_get(v_a_2730_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2733_ = v_a_2730_;
v_isShared_2734_ = v_isSharedCheck_2755_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_val_2731_);
lean_dec(v_a_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2755_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = lean_unsigned_to_nat(200u);
v___x_2736_ = lean_nat_dec_eq(v_val_2731_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v_stdout_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
v_stdout_2737_ = lean_ctor_get(v___y_2729_, 0);
lean_inc_ref(v_stdout_2737_);
lean_dec_ref(v___y_2729_);
v___x_2738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2739_ = l_Nat_reprFast(v_val_2731_);
v___x_2740_ = lean_string_append(v___x_2738_, v___x_2739_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2742_ = lean_string_append(v___x_2740_, v___x_2741_);
v___x_2743_ = lean_string_append(v___x_2742_, v_stdout_2737_);
lean_dec_ref(v_stdout_2737_);
v___x_2744_ = 3;
v___x_2745_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set_uint8(v___x_2745_, sizeof(void*)*1, v___x_2744_);
lean_inc_ref(v_a_2700_);
v___x_2746_ = lean_apply_2(v_a_2700_, v___x_2745_, lean_box(0));
v___x_2747_ = lean_box(0);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2747_);
v___x_2749_ = v___x_2733_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
lean_dec(v_val_2731_);
lean_dec_ref(v___y_2729_);
v___x_2751_ = lean_box(0);
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2751_);
v___x_2753_ = v___x_2733_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
v___jp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2760_ = l_Lake_JsonObject_getJson_x3f(v___y_2757_, v___x_2759_);
lean_dec(v___y_2757_);
if (lean_obj_tag(v___x_2760_) == 0)
{
v___y_2726_ = v___y_2758_;
goto v___jp_2725_;
}
else
{
lean_object* v_val_2761_; lean_object* v___x_2762_; 
v_val_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v___x_2762_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2765_ = lean_string_append(v___x_2764_, v_a_2763_);
lean_dec(v_a_2763_);
v___y_2703_ = v___y_2758_;
v_a_2704_ = v___x_2765_;
goto v___jp_2702_;
}
else
{
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2762_, 1);
v___y_2703_ = v___y_2758_;
v_a_2704_ = v_a_2766_;
goto v___jp_2702_;
}
else
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2762_, 1);
v___y_2729_ = v___y_2758_;
v_a_2730_ = v_a_2767_;
goto v___jp_2728_;
}
}
}
}
v___jp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2771_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2772_ = lean_string_append(v___x_2771_, v_a_2770_);
lean_dec_ref(v_a_2770_);
v___x_2773_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2774_ = lean_string_append(v___x_2772_, v___x_2773_);
v___x_2775_ = lean_string_append(v___x_2774_, v_stderr_2769_);
lean_dec_ref(v_stderr_2769_);
v___x_2776_ = 3;
v___x_2777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*1, v___x_2776_);
lean_inc_ref(v_a_2700_);
v___x_2778_ = lean_apply_2(v_a_2700_, v___x_2777_, lean_box(0));
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
return v___x_2780_;
}
v___jp_2781_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2846_, lean_object* v_contentType_2847_, lean_object* v_url_2848_, lean_object* v_key_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2846_, v_contentType_2847_, v_url_2848_, v_key_2849_, v_a_2850_);
lean_dec_ref(v_a_2850_);
lean_dec_ref(v_contentType_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2853_){
_start:
{
lean_object* v_name_x3f_2854_; 
v_name_x3f_2854_ = lean_ctor_get(v_service_2853_, 0);
lean_inc(v_name_x3f_2854_);
return v_name_x3f_2854_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lake_CacheService_name_x3f(v_service_2855_);
lean_dec_ref(v_service_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2857_){
_start:
{
uint8_t v_isReservoir_2858_; 
v_isReservoir_2858_ = lean_ctor_get_uint8(v_service_2857_, sizeof(void*)*5);
return v_isReservoir_2858_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2859_){
_start:
{
uint8_t v_res_2860_; lean_object* v_r_2861_; 
v_res_2860_ = l_Lake_CacheService_isReservoir(v_service_2859_);
lean_dec_ref(v_service_2859_);
v_r_2861_ = lean_box(v_res_2860_);
return v_r_2861_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2862_, lean_object* v_name_x3f_2863_){
_start:
{
lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2865_ = 1;
v___x_2866_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2866_, 0, v_name_x3f_2863_);
lean_ctor_set(v___x_2866_, 1, v___x_2864_);
lean_ctor_set(v___x_2866_, 2, v___x_2864_);
lean_ctor_set(v___x_2866_, 3, v___x_2864_);
lean_ctor_set(v___x_2866_, 4, v_apiEndpoint_2862_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*5, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2867_, lean_object* v_artifactEndpoint_2868_, lean_object* v_revisionEndpoint_2869_){
_start:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2870_ = lean_box(0);
v___x_2871_ = 0;
v___x_2872_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2873_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2873_, 0, v___x_2870_);
lean_ctor_set(v___x_2873_, 1, v_key_2867_);
lean_ctor_set(v___x_2873_, 2, v_artifactEndpoint_2868_);
lean_ctor_set(v___x_2873_, 3, v_revisionEndpoint_2869_);
lean_ctor_set(v___x_2873_, 4, v___x_2872_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*5, v___x_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2874_, lean_object* v_revisionEndpoint_2875_, lean_object* v_name_x3f_2876_){
_start:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2878_ = 0;
v___x_2879_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2879_, 0, v_name_x3f_2876_);
lean_ctor_set(v___x_2879_, 1, v___x_2877_);
lean_ctor_set(v___x_2879_, 2, v_artifactEndpoint_2874_);
lean_ctor_set(v___x_2879_, 3, v_revisionEndpoint_2875_);
lean_ctor_set(v___x_2879_, 4, v___x_2877_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*5, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2880_, lean_object* v_name_x3f_2881_){
_start:
{
lean_object* v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2883_ = 0;
v___x_2884_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2884_, 0, v_name_x3f_2881_);
lean_ctor_set(v___x_2884_, 1, v___x_2882_);
lean_ctor_set(v___x_2884_, 2, v_artifactEndpoint_2880_);
lean_ctor_set(v___x_2884_, 3, v___x_2882_);
lean_ctor_set(v___x_2884_, 4, v___x_2882_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*5, v___x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2885_, lean_object* v_key_2886_){
_start:
{
lean_object* v_name_x3f_2887_; lean_object* v_artifactEndpoint_2888_; lean_object* v_revisionEndpoint_2889_; uint8_t v_isReservoir_2890_; lean_object* v_apiEndpoint_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_name_x3f_2887_ = lean_ctor_get(v_service_2885_, 0);
v_artifactEndpoint_2888_ = lean_ctor_get(v_service_2885_, 2);
v_revisionEndpoint_2889_ = lean_ctor_get(v_service_2885_, 3);
v_isReservoir_2890_ = lean_ctor_get_uint8(v_service_2885_, sizeof(void*)*5);
v_apiEndpoint_2891_ = lean_ctor_get(v_service_2885_, 4);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_service_2885_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v_service_2885_, 1);
lean_dec(v_unused_2899_);
v___x_2893_ = v_service_2885_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_apiEndpoint_2891_);
lean_inc(v_revisionEndpoint_2889_);
lean_inc(v_artifactEndpoint_2888_);
lean_inc(v_name_x3f_2887_);
lean_dec(v_service_2885_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v_key_2886_);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_name_x3f_2887_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_key_2886_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_artifactEndpoint_2888_);
lean_ctor_set(v_reuseFailAlloc_2897_, 3, v_revisionEndpoint_2889_);
lean_ctor_set(v_reuseFailAlloc_2897_, 4, v_apiEndpoint_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2897_, sizeof(void*)*5, v_isReservoir_2890_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2906_);
lean_dec_ref(v_s_2906_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2908_, lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v_a_2911_, lean_object* v_b_2912_){
_start:
{
if (lean_obj_tag(v_a_2911_) == 0)
{
lean_object* v_currPos_2913_; lean_object* v_searcher_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2948_; 
v_currPos_2913_ = lean_ctor_get(v_a_2911_, 0);
v_searcher_2914_ = lean_ctor_get(v_a_2911_, 1);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_a_2911_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2916_ = v_a_2911_;
v_isShared_2917_ = v_isSharedCheck_2948_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_searcher_2914_);
lean_inc(v_currPos_2913_);
lean_dec(v_a_2911_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2948_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_startInclusive_2918_; lean_object* v_endExclusive_2919_; uint32_t v___x_2920_; lean_object* v_it_2922_; lean_object* v_startInclusive_2923_; lean_object* v_endExclusive_2924_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v_startInclusive_2918_ = lean_ctor_get(v___x_2909_, 1);
v_endExclusive_2919_ = lean_ctor_get(v___x_2909_, 2);
v___x_2920_ = 47;
v___x_2929_ = lean_nat_sub(v_endExclusive_2919_, v_startInclusive_2918_);
v___x_2930_ = lean_nat_dec_eq(v_searcher_2914_, v___x_2929_);
lean_dec(v___x_2929_);
if (v___x_2930_ == 0)
{
uint32_t v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = lean_string_utf8_get_fast(v_scope_2908_, v_searcher_2914_);
v___x_2932_ = lean_uint32_dec_eq(v___x_2931_, v___x_2920_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = lean_string_utf8_next_fast(v_scope_2908_, v_searcher_2914_);
lean_dec(v_searcher_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2933_);
v___x_2935_ = v___x_2916_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_currPos_2913_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
v_a_2911_ = v___x_2935_;
goto _start;
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_slice_2941_; lean_object* v_nextIt_2943_; 
v___x_2938_ = lean_string_utf8_next_fast(v_scope_2908_, v_searcher_2914_);
v___x_2939_ = lean_nat_sub(v___x_2938_, v_searcher_2914_);
v___x_2940_ = lean_nat_add(v_searcher_2914_, v___x_2939_);
lean_dec(v___x_2939_);
v_slice_2941_ = l_String_Slice_subslice_x21(v___x_2909_, v_currPos_2913_, v_searcher_2914_);
lean_inc(v___x_2940_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2940_);
lean_ctor_set(v___x_2916_, 0, v___x_2940_);
v_nextIt_2943_ = v___x_2916_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2940_);
v_nextIt_2943_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v_startInclusive_2944_; lean_object* v_endExclusive_2945_; 
v_startInclusive_2944_ = lean_ctor_get(v_slice_2941_, 0);
lean_inc(v_startInclusive_2944_);
v_endExclusive_2945_ = lean_ctor_get(v_slice_2941_, 1);
lean_inc(v_endExclusive_2945_);
lean_dec_ref(v_slice_2941_);
v_it_2922_ = v_nextIt_2943_;
v_startInclusive_2923_ = v_startInclusive_2944_;
v_endExclusive_2924_ = v_endExclusive_2945_;
goto v___jp_2921_;
}
}
}
else
{
lean_object* v___x_2947_; 
lean_del_object(v___x_2916_);
lean_dec(v_searcher_2914_);
v___x_2947_ = lean_box(1);
lean_inc(v___x_2910_);
v_it_2922_ = v___x_2947_;
v_startInclusive_2923_ = v_currPos_2913_;
v_endExclusive_2924_ = v___x_2910_;
goto v___jp_2921_;
}
v___jp_2921_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_string_utf8_extract(v_scope_2908_, v_startInclusive_2923_, v_endExclusive_2924_);
lean_dec(v_endExclusive_2924_);
lean_dec(v_startInclusive_2923_);
v___x_2926_ = lean_string_push(v_b_2912_, v___x_2920_);
v___x_2927_ = l_Lake_uriEncode(v___x_2925_, v___x_2926_);
v_a_2911_ = v_it_2922_;
v_b_2912_ = v___x_2927_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2910_);
return v_b_2912_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_2949_, lean_object* v___x_2950_, lean_object* v___x_2951_, lean_object* v_a_2952_, lean_object* v_b_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2949_, v___x_2950_, v___x_2951_, v_a_2952_, v_b_2953_);
lean_dec_ref(v___x_2950_);
lean_dec_ref(v_scope_2949_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_2955_, lean_object* v_scope_2956_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2957_ = lean_unsigned_to_nat(0u);
v___x_2958_ = lean_string_utf8_byte_size(v_scope_2956_);
lean_inc_ref(v_scope_2956_);
v___x_2959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2959_, 0, v_scope_2956_);
lean_ctor_set(v___x_2959_, 1, v___x_2957_);
lean_ctor_set(v___x_2959_, 2, v___x_2958_);
v___x_2960_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_2959_);
v___x_2961_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2956_, v___x_2959_, v___x_2958_, v___x_2960_, v_endpoint_2955_);
lean_dec_ref_known(v___x_2959_, 3);
lean_dec_ref(v_scope_2956_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_2962_, lean_object* v___x_2963_, lean_object* v___x_2964_, lean_object* v_inst_2965_, lean_object* v_R_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_, lean_object* v_c_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2962_, v___x_2963_, v___x_2964_, v_a_2967_, v_b_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_2971_, lean_object* v___x_2972_, lean_object* v___x_2973_, lean_object* v_inst_2974_, lean_object* v_R_2975_, lean_object* v_a_2976_, lean_object* v_b_2977_, lean_object* v_c_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_2971_, v___x_2972_, v___x_2973_, v_inst_2974_, v_R_2975_, v_a_2976_, v_b_2977_, v_c_2978_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_scope_2971_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_2980_, lean_object* v_scope_2981_){
_start:
{
lean_object* v_artifactEndpoint_2982_; lean_object* v___x_2983_; 
v_artifactEndpoint_2982_ = lean_ctor_get(v_service_2980_, 2);
lean_inc_ref(v_artifactEndpoint_2982_);
lean_dec_ref(v_service_2980_);
v___x_2983_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_2982_, v_scope_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_2986_, lean_object* v_service_2987_, lean_object* v_scope_2988_){
_start:
{
lean_object* v___y_2990_; lean_object* v_s_2997_; lean_object* v___x_2998_; 
v_s_2997_ = lean_ctor_get(v_scope_2988_, 0);
lean_inc_ref(v_s_2997_);
lean_dec_ref(v_scope_2988_);
v___x_2998_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_2987_, v_s_2997_);
v___y_2990_ = v___x_2998_;
goto v___jp_2989_;
v___jp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2991_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_2992_ = lean_string_append(v___y_2990_, v___x_2991_);
v___x_2993_ = l_Lake_lowerHexUInt64(v_contentHash_2986_);
v___x_2994_ = lean_string_append(v___x_2992_, v___x_2993_);
lean_dec_ref(v___x_2993_);
v___x_2995_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2996_ = lean_string_append(v___x_2994_, v___x_2995_);
return v___x_2996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_2999_, lean_object* v_service_3000_, lean_object* v_scope_3001_){
_start:
{
uint64_t v_contentHash_boxed_3002_; lean_object* v_res_3003_; 
v_contentHash_boxed_3002_ = lean_unbox_uint64(v_contentHash_2999_);
lean_dec_ref(v_contentHash_2999_);
v_res_3003_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_3002_, v_service_3000_, v_scope_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_3007_, lean_object* v_service_3008_, lean_object* v_scope_3009_){
_start:
{
lean_object* v___y_3011_; uint8_t v_isReservoir_3018_; 
v_isReservoir_3018_ = lean_ctor_get_uint8(v_service_3008_, sizeof(void*)*5);
if (v_isReservoir_3018_ == 0)
{
lean_object* v___x_3019_; 
v___x_3019_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3007_, v_service_3008_, v_scope_3009_);
return v___x_3019_;
}
else
{
if (lean_obj_tag(v_scope_3009_) == 0)
{
lean_object* v_apiEndpoint_3020_; lean_object* v_s_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_apiEndpoint_3020_ = lean_ctor_get(v_service_3008_, 4);
lean_inc_ref(v_apiEndpoint_3020_);
lean_dec_ref(v_service_3008_);
v_s_3021_ = lean_ctor_get(v_scope_3009_, 0);
lean_inc_ref(v_s_3021_);
lean_dec_ref_known(v_scope_3009_, 1);
v___x_3022_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_3023_ = lean_string_append(v_apiEndpoint_3020_, v___x_3022_);
v___x_3024_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3023_, v_s_3021_);
v___y_3011_ = v___x_3024_;
goto v___jp_3010_;
}
else
{
lean_object* v_apiEndpoint_3025_; lean_object* v_s_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v_apiEndpoint_3025_ = lean_ctor_get(v_service_3008_, 4);
lean_inc_ref(v_apiEndpoint_3025_);
lean_dec_ref(v_service_3008_);
v_s_3026_ = lean_ctor_get(v_scope_3009_, 0);
lean_inc_ref(v_s_3026_);
lean_dec_ref_known(v_scope_3009_, 1);
v___x_3027_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3028_ = lean_string_append(v_apiEndpoint_3025_, v___x_3027_);
v___x_3029_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3028_, v_s_3026_);
v___y_3011_ = v___x_3029_;
goto v___jp_3010_;
}
}
v___jp_3010_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3012_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_3013_ = lean_string_append(v___y_3011_, v___x_3012_);
v___x_3014_ = l_Lake_lowerHexUInt64(v_contentHash_3007_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_3030_, lean_object* v_service_3031_, lean_object* v_scope_3032_){
_start:
{
uint64_t v_contentHash_boxed_3033_; lean_object* v_res_3034_; 
v_contentHash_boxed_3033_ = lean_unbox_uint64(v_contentHash_3030_);
lean_dec_ref(v_contentHash_3030_);
v_res_3034_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_3033_, v_service_3031_, v_scope_3032_);
return v_res_3034_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3039_ = lean_array_get_size(v___x_3038_);
return v___x_3039_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3040_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = lean_nat_dec_lt(v___x_3041_, v___x_3040_);
return v___x_3042_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3044_ = lean_nat_dec_le(v___x_3043_, v___x_3043_);
return v___x_3044_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_3045_; size_t v___x_3046_; 
v___x_3045_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3046_ = lean_usize_of_nat(v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_3047_, lean_object* v_cache_3048_, lean_object* v_service_3049_, lean_object* v_scope_3050_, uint8_t v_force_3051_, lean_object* v_a_3052_){
_start:
{
uint64_t v_hash_3057_; lean_object* v_ext_3058_; lean_object* v_url_3059_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3123_; lean_object* v___y_3126_; uint8_t v_a_3127_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___y_3134_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_hash_3057_ = lean_ctor_get_uint64(v_descr_3047_, sizeof(void*)*1);
v_ext_3058_ = lean_ctor_get(v_descr_3047_, 0);
lean_inc_ref(v_scope_3050_);
v_url_3059_ = l_Lake_CacheService_artifactUrl(v_hash_3057_, v_service_3049_, v_scope_3050_);
v___x_3131_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3132_ = l_System_FilePath_join(v_cache_3048_, v___x_3131_);
v___x_3147_ = lean_string_utf8_byte_size(v_ext_3058_);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_nat_dec_eq(v___x_3147_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3150_ = l_Lake_lowerHexUInt64(v_hash_3057_);
v___x_3151_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3152_ = lean_string_append(v___x_3150_, v___x_3151_);
v___x_3153_ = lean_string_append(v___x_3152_, v_ext_3058_);
v___y_3134_ = v___x_3153_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lake_lowerHexUInt64(v_hash_3057_);
v___y_3134_ = v___x_3154_;
goto v___jp_3133_;
}
v___jp_3054_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
v___jp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3063_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3064_ = lean_string_append(v___y_3062_, v___x_3063_);
v___x_3065_ = l_Lake_lowerHexUInt64(v_hash_3057_);
v___x_3066_ = lean_string_append(v___x_3064_, v___x_3065_);
lean_dec_ref(v___x_3065_);
v___x_3067_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3068_ = lean_string_append(v___x_3066_, v___x_3067_);
v___x_3069_ = lean_string_append(v___x_3068_, v___y_3061_);
v___x_3070_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3071_ = lean_string_append(v___x_3069_, v___x_3070_);
v___x_3072_ = lean_string_append(v___x_3071_, v_url_3059_);
v___x_3073_ = 1;
v___x_3074_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set_uint8(v___x_3074_, sizeof(void*)*1, v___x_3073_);
lean_inc_ref(v_a_3052_);
v___x_3075_ = lean_apply_2(v_a_3052_, v___x_3074_, lean_box(0));
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3078_ = l_Lake_downloadArtifactCore(v_hash_3057_, v_url_3059_, v___y_3061_, v___x_3077_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v_a_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
v_a_3080_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3078_, 2);
v___x_3081_ = lean_array_get_size(v_a_3080_);
v___x_3082_ = lean_nat_dec_lt(v___x_3076_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec(v_a_3080_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v_a_3079_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_nat_dec_le(v___x_3081_, v___x_3081_);
if (v___x_3085_ == 0)
{
if (v___x_3082_ == 0)
{
lean_object* v___x_3086_; 
lean_dec(v_a_3080_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_a_3079_);
return v___x_3086_;
}
else
{
size_t v___x_3087_; size_t v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = lean_usize_of_nat(v___x_3081_);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3080_, v___x_3087_, v___x_3088_, v___x_3084_, v_a_3052_);
lean_dec(v_a_3080_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v___x_3089_, 0);
lean_dec(v_unused_3097_);
v___x_3091_ = v___x_3089_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v___x_3089_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v_a_3079_);
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3079_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
else
{
lean_dec(v_a_3079_);
return v___x_3089_;
}
}
}
else
{
size_t v___x_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = lean_usize_of_nat(v___x_3081_);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3080_, v___x_3098_, v___x_3099_, v___x_3084_, v_a_3052_);
lean_dec(v_a_3080_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v___x_3100_, 0);
lean_dec(v_unused_3108_);
v___x_3102_ = v___x_3100_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_dec(v___x_3100_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v_a_3079_);
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3079_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_dec(v_a_3079_);
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_a_3109_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3078_, 2);
v___x_3110_ = lean_array_get_size(v_a_3109_);
v___x_3111_ = lean_nat_dec_lt(v___x_3076_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec(v_a_3109_);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = lean_box(0);
v___x_3115_ = lean_nat_dec_le(v___x_3110_, v___x_3110_);
if (v___x_3115_ == 0)
{
if (v___x_3111_ == 0)
{
lean_dec(v_a_3109_);
goto v___jp_3054_;
}
else
{
size_t v___x_3116_; size_t v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = ((size_t)0ULL);
v___x_3117_ = lean_usize_of_nat(v___x_3110_);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3109_, v___x_3116_, v___x_3117_, v___x_3114_, v_a_3052_);
lean_dec(v_a_3109_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref_known(v___x_3118_, 1);
goto v___jp_3054_;
}
else
{
return v___x_3118_;
}
}
}
else
{
size_t v___x_3119_; size_t v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = ((size_t)0ULL);
v___x_3120_ = lean_usize_of_nat(v___x_3110_);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3109_, v___x_3119_, v___x_3120_, v___x_3114_, v_a_3052_);
lean_dec(v_a_3109_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_dec_ref_known(v___x_3121_, 1);
goto v___jp_3054_;
}
else
{
return v___x_3121_;
}
}
}
}
}
v___jp_3122_:
{
lean_object* v_s_3124_; 
v_s_3124_ = lean_ctor_get(v_scope_3050_, 0);
lean_inc_ref(v_s_3124_);
lean_dec_ref(v_scope_3050_);
v___y_3061_ = v___y_3123_;
v___y_3062_ = v_s_3124_;
goto v___jp_3060_;
}
v___jp_3125_:
{
if (v_a_3127_ == 0)
{
v___y_3123_ = v___y_3126_;
goto v___jp_3122_;
}
else
{
uint8_t v___x_3128_; 
v___x_3128_ = lean_bool_not(v_force_3051_);
if (v___x_3128_ == 0)
{
v___y_3123_ = v___y_3126_;
goto v___jp_3122_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v___y_3126_);
lean_dec_ref(v_url_3059_);
lean_dec_ref(v_scope_3050_);
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
}
}
v___jp_3133_:
{
lean_object* v_path_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v_path_3135_ = l_System_FilePath_join(v___x_3132_, v___y_3134_);
v___x_3136_ = l_System_FilePath_pathExists(v_path_3135_);
v___x_3137_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3138_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3138_ == 0)
{
v___y_3126_ = v_path_3135_;
v_a_3127_ = v___x_3136_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3139_ = lean_box(0);
v___x_3140_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3140_ == 0)
{
if (v___x_3138_ == 0)
{
v___y_3126_ = v_path_3135_;
v_a_3127_ = v___x_3136_;
goto v___jp_3125_;
}
else
{
size_t v___x_3141_; size_t v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = ((size_t)0ULL);
v___x_3142_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3137_, v___x_3141_, v___x_3142_, v___x_3139_, v_a_3052_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_dec_ref_known(v___x_3143_, 1);
v___y_3126_ = v_path_3135_;
v_a_3127_ = v___x_3136_;
goto v___jp_3125_;
}
else
{
lean_dec_ref(v_path_3135_);
lean_dec_ref(v_url_3059_);
lean_dec_ref(v_scope_3050_);
return v___x_3143_;
}
}
}
else
{
size_t v___x_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((size_t)0ULL);
v___x_3145_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3137_, v___x_3144_, v___x_3145_, v___x_3139_, v_a_3052_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_dec_ref_known(v___x_3146_, 1);
v___y_3126_ = v_path_3135_;
v_a_3127_ = v___x_3136_;
goto v___jp_3125_;
}
else
{
lean_dec_ref(v_path_3135_);
lean_dec_ref(v_url_3059_);
lean_dec_ref(v_scope_3050_);
return v___x_3146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3155_, lean_object* v_cache_3156_, lean_object* v_service_3157_, lean_object* v_scope_3158_, lean_object* v_force_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
uint8_t v_force_boxed_3162_; lean_object* v_res_3163_; 
v_force_boxed_3162_ = lean_unbox(v_force_3159_);
v_res_3163_ = l_Lake_CacheService_downloadArtifact(v_descr_3155_, v_cache_3156_, v_service_3157_, v_scope_3158_, v_force_boxed_3162_, v_a_3160_);
lean_dec_ref(v_a_3160_);
lean_dec_ref(v_descr_3155_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3164_, lean_object* v_file_3165_, lean_object* v_contentType_3166_, lean_object* v_url_3167_, lean_object* v_key_3168_){
_start:
{
lean_object* v___y_3171_; lean_object* v_a_3172_; lean_object* v_stderr_3185_; lean_object* v___y_3194_; lean_object* v___y_3197_; lean_object* v_a_3198_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v_stderr_3237_; lean_object* v_a_3238_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3252_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3253_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3254_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3255_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3256_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3257_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3258_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3259_ = lean_string_append(v___x_3258_, v_contentType_3166_);
v___x_3260_ = lean_unsigned_to_nat(14u);
v___x_3261_ = lean_mk_empty_array_with_capacity(v___x_3260_);
lean_dec_ref(v___x_3261_);
v___x_3262_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3263_ = lean_array_push(v___x_3262_, v_key_3168_);
v___x_3264_ = lean_array_push(v___x_3263_, v___x_3254_);
v___x_3265_ = lean_array_push(v___x_3264_, v___x_3255_);
v___x_3266_ = lean_array_push(v___x_3265_, v___x_3256_);
v___x_3267_ = lean_array_push(v___x_3266_, v_file_3165_);
v___x_3268_ = lean_array_push(v___x_3267_, v_url_3167_);
v___x_3269_ = lean_array_push(v___x_3268_, v___x_3257_);
v___x_3270_ = lean_array_push(v___x_3269_, v___x_3259_);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3274_ = 1;
v___x_3275_ = 0;
v___x_3276_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3276_, 0, v___x_3252_);
lean_ctor_set(v___x_3276_, 1, v___x_3253_);
lean_ctor_set(v___x_3276_, 2, v___x_3270_);
lean_ctor_set(v___x_3276_, 3, v___x_3271_);
lean_ctor_set(v___x_3276_, 4, v___x_3273_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*5, v___x_3274_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*5 + 1, v___x_3275_);
v___x_3277_ = l_Lake_captureProc_x27(v___x_3276_, v___x_3273_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v_a_3279_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
v_a_3279_ = lean_ctor_get(v___x_3277_, 1);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3277_, 2);
v___x_3293_ = lean_array_get_size(v_a_3279_);
v___x_3294_ = lean_nat_dec_lt(v___x_3272_, v___x_3293_);
if (v___x_3294_ == 0)
{
lean_dec(v_a_3279_);
goto v___jp_3280_;
}
else
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_nat_dec_le(v___x_3293_, v___x_3293_);
if (v___x_3296_ == 0)
{
if (v___x_3294_ == 0)
{
lean_dec(v_a_3279_);
goto v___jp_3280_;
}
else
{
size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = ((size_t)0ULL);
v___x_3298_ = lean_usize_of_nat(v___x_3293_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3279_, v___x_3297_, v___x_3298_, v___x_3295_, v_a_3164_);
lean_dec(v_a_3279_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_dec_ref_known(v___x_3299_, 1);
goto v___jp_3280_;
}
else
{
lean_dec(v_a_3278_);
return v___x_3299_;
}
}
}
else
{
size_t v___x_3300_; size_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = lean_usize_of_nat(v___x_3293_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3279_, v___x_3300_, v___x_3301_, v___x_3295_, v_a_3164_);
lean_dec(v_a_3279_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_dec_ref_known(v___x_3302_, 1);
goto v___jp_3280_;
}
else
{
lean_dec(v_a_3278_);
return v___x_3302_;
}
}
}
v___jp_3280_:
{
lean_object* v_stderr_3281_; lean_object* v___x_3282_; 
v_stderr_3281_ = lean_ctor_get(v_a_3278_, 1);
lean_inc_ref(v_stderr_3281_);
v___x_3282_ = l_Lean_Json_parse(v_stderr_3281_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; 
lean_inc_ref(v_stderr_3281_);
lean_dec(v_a_3278_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v_stderr_3237_ = v_stderr_3281_;
v_a_3238_ = v_a_3283_;
goto v___jp_3236_;
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3285_; 
v_a_3284_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3285_ = l_Lean_Json_getObj_x3f(v_a_3284_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; 
lean_inc_ref(v_stderr_3281_);
lean_dec(v_a_3278_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
v_stderr_3237_ = v_stderr_3281_;
v_a_3238_ = v_a_3286_;
goto v___jp_3236_;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3287_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3288_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3289_ = l_Lake_JsonObject_getJson_x3f(v_a_3287_, v___x_3288_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_inc_ref(v_stderr_3281_);
lean_dec(v_a_3287_);
lean_dec(v_a_3278_);
v_stderr_3185_ = v_stderr_3281_;
goto v___jp_3184_;
}
else
{
lean_object* v_val_3290_; lean_object* v___x_3291_; 
v_val_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3291_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_dec_ref_known(v___x_3291_, 1);
v___y_3225_ = v_a_3287_;
v___y_3226_ = v_a_3278_;
goto v___jp_3224_;
}
else
{
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_dec_ref_known(v___x_3291_, 1);
v___y_3225_ = v_a_3287_;
v___y_3226_ = v_a_3278_;
goto v___jp_3224_;
}
else
{
lean_object* v_a_3292_; 
lean_dec(v_a_3287_);
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___y_3197_ = v_a_3278_;
v_a_3198_ = v_a_3292_;
goto v___jp_3196_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_a_3303_ = lean_ctor_get(v___x_3277_, 1);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3277_, 2);
v___x_3304_ = lean_array_get_size(v_a_3303_);
v___x_3305_ = lean_nat_dec_lt(v___x_3272_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_a_3303_);
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
else
{
lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_nat_dec_le(v___x_3304_, v___x_3304_);
if (v___x_3309_ == 0)
{
if (v___x_3305_ == 0)
{
lean_dec(v_a_3303_);
goto v___jp_3249_;
}
else
{
size_t v___x_3310_; size_t v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = ((size_t)0ULL);
v___x_3311_ = lean_usize_of_nat(v___x_3304_);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3303_, v___x_3310_, v___x_3311_, v___x_3308_, v_a_3164_);
lean_dec(v_a_3303_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
goto v___jp_3249_;
}
else
{
return v___x_3312_;
}
}
}
else
{
size_t v___x_3313_; size_t v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = ((size_t)0ULL);
v___x_3314_ = lean_usize_of_nat(v___x_3304_);
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3303_, v___x_3313_, v___x_3314_, v___x_3308_, v_a_3164_);
lean_dec(v_a_3303_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_dec_ref_known(v___x_3315_, 1);
goto v___jp_3249_;
}
else
{
return v___x_3315_;
}
}
}
}
v___jp_3170_:
{
lean_object* v_stderr_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_stderr_3173_ = lean_ctor_get(v___y_3171_, 1);
lean_inc_ref(v_stderr_3173_);
lean_dec_ref(v___y_3171_);
v___x_3174_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3175_ = lean_string_append(v___x_3174_, v_a_3172_);
lean_dec_ref(v_a_3172_);
v___x_3176_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3177_ = lean_string_append(v___x_3175_, v___x_3176_);
v___x_3178_ = lean_string_append(v___x_3177_, v_stderr_3173_);
lean_dec_ref(v_stderr_3173_);
v___x_3179_ = 3;
v___x_3180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*1, v___x_3179_);
lean_inc_ref(v_a_3164_);
v___x_3181_ = lean_apply_2(v_a_3164_, v___x_3180_, lean_box(0));
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
v___jp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3186_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3187_ = lean_string_append(v___x_3186_, v_stderr_3185_);
lean_dec_ref(v_stderr_3185_);
v___x_3188_ = 3;
v___x_3189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*1, v___x_3188_);
lean_inc_ref(v_a_3164_);
v___x_3190_ = lean_apply_2(v_a_3164_, v___x_3189_, lean_box(0));
v___x_3191_ = lean_box(0);
v___x_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
v___jp_3193_:
{
lean_object* v_stderr_3195_; 
v_stderr_3195_ = lean_ctor_get(v___y_3194_, 1);
lean_inc_ref(v_stderr_3195_);
lean_dec_ref(v___y_3194_);
v_stderr_3185_ = v_stderr_3195_;
goto v___jp_3184_;
}
v___jp_3196_:
{
if (lean_obj_tag(v_a_3198_) == 0)
{
v___y_3194_ = v___y_3197_;
goto v___jp_3193_;
}
else
{
lean_object* v_val_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3223_; 
v_val_3199_ = lean_ctor_get(v_a_3198_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3201_ = v_a_3198_;
v_isShared_3202_ = v_isSharedCheck_3223_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_val_3199_);
lean_dec(v_a_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3223_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = lean_unsigned_to_nat(200u);
v___x_3204_ = lean_nat_dec_eq(v_val_3199_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_object* v_stdout_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v_stdout_3205_ = lean_ctor_get(v___y_3197_, 0);
lean_inc_ref(v_stdout_3205_);
lean_dec_ref(v___y_3197_);
v___x_3206_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3207_ = l_Nat_reprFast(v_val_3199_);
v___x_3208_ = lean_string_append(v___x_3206_, v___x_3207_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3210_ = lean_string_append(v___x_3208_, v___x_3209_);
v___x_3211_ = lean_string_append(v___x_3210_, v_stdout_3205_);
lean_dec_ref(v_stdout_3205_);
v___x_3212_ = 3;
v___x_3213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*1, v___x_3212_);
lean_inc_ref(v_a_3164_);
v___x_3214_ = lean_apply_2(v_a_3164_, v___x_3213_, lean_box(0));
v___x_3215_ = lean_box(0);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3215_);
v___x_3217_ = v___x_3201_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_dec(v_val_3199_);
lean_dec_ref(v___y_3197_);
v___x_3219_ = lean_box(0);
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3219_);
v___x_3221_ = v___x_3201_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
v___jp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3228_ = l_Lake_JsonObject_getJson_x3f(v___y_3225_, v___x_3227_);
lean_dec(v___y_3225_);
if (lean_obj_tag(v___x_3228_) == 0)
{
v___y_3194_ = v___y_3226_;
goto v___jp_3193_;
}
else
{
lean_object* v_val_3229_; lean_object* v___x_3230_; 
v_val_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3229_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3233_ = lean_string_append(v___x_3232_, v_a_3231_);
lean_dec(v_a_3231_);
v___y_3171_ = v___y_3226_;
v_a_3172_ = v___x_3233_;
goto v___jp_3170_;
}
else
{
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3234_; 
v_a_3234_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3230_, 1);
v___y_3171_ = v___y_3226_;
v_a_3172_ = v_a_3234_;
goto v___jp_3170_;
}
else
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3230_, 1);
v___y_3197_ = v___y_3226_;
v_a_3198_ = v_a_3235_;
goto v___jp_3196_;
}
}
}
}
v___jp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3239_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3240_ = lean_string_append(v___x_3239_, v_a_3238_);
lean_dec_ref(v_a_3238_);
v___x_3241_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
v___x_3243_ = lean_string_append(v___x_3242_, v_stderr_3237_);
lean_dec_ref(v_stderr_3237_);
v___x_3244_ = 3;
v___x_3245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*1, v___x_3244_);
lean_inc_ref(v_a_3164_);
v___x_3246_ = lean_apply_2(v_a_3164_, v___x_3245_, lean_box(0));
v___x_3247_ = lean_box(0);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
return v___x_3248_;
}
v___jp_3249_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_box(0);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3316_, lean_object* v_file_3317_, lean_object* v_contentType_3318_, lean_object* v_url_3319_, lean_object* v_key_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3316_, v_file_3317_, v_contentType_3318_, v_url_3319_, v_key_3320_);
lean_dec_ref(v_contentType_3318_);
lean_dec_ref(v_a_3316_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3324_, lean_object* v_art_3325_, lean_object* v_service_3326_, lean_object* v_scope_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v_url_3330_; lean_object* v___y_3332_; lean_object* v_s_3349_; 
lean_inc_ref(v_scope_3327_);
lean_inc_ref(v_service_3326_);
v_url_3330_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3324_, v_service_3326_, v_scope_3327_);
v_s_3349_ = lean_ctor_get(v_scope_3327_, 0);
lean_inc_ref(v_s_3349_);
lean_dec_ref(v_scope_3327_);
v___y_3332_ = v_s_3349_;
goto v___jp_3331_;
v___jp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v_key_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3333_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3334_ = lean_string_append(v___y_3332_, v___x_3333_);
v___x_3335_ = l_Lake_lowerHexUInt64(v_contentHash_3324_);
v___x_3336_ = lean_string_append(v___x_3334_, v___x_3335_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3338_ = lean_string_append(v___x_3336_, v___x_3337_);
v___x_3339_ = lean_string_append(v___x_3338_, v_art_3325_);
v___x_3340_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = lean_string_append(v___x_3341_, v_url_3330_);
v___x_3343_ = 1;
v___x_3344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*1, v___x_3343_);
lean_inc_ref(v_a_3328_);
v___x_3345_ = lean_apply_2(v_a_3328_, v___x_3344_, lean_box(0));
v_key_3346_ = lean_ctor_get(v_service_3326_, 1);
lean_inc_ref(v_key_3346_);
lean_dec_ref(v_service_3326_);
v___x_3347_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3348_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3328_, v_art_3325_, v___x_3347_, v_url_3330_, v_key_3346_);
return v___x_3348_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3350_, lean_object* v_art_3351_, lean_object* v_service_3352_, lean_object* v_scope_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
uint64_t v_contentHash_boxed_3356_; lean_object* v_res_3357_; 
v_contentHash_boxed_3356_ = lean_unbox_uint64(v_contentHash_3350_);
lean_dec_ref(v_contentHash_3350_);
v_res_3357_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3356_, v_art_3351_, v_service_3352_, v_scope_3353_, v_a_3354_);
lean_dec_ref(v_a_3354_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(uint8_t v_x_3358_){
_start:
{
if (v_x_3358_ == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_unsigned_to_nat(0u);
return v___x_3359_;
}
else
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_unsigned_to_nat(1u);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___boxed(lean_object* v_x_3361_){
_start:
{
uint8_t v_x_boxed_3362_; lean_object* v_res_3363_; 
v_x_boxed_3362_ = lean_unbox(v_x_3361_);
v_res_3363_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_boxed_3362_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(uint8_t v_x_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx___boxed(lean_object* v_x_3366_){
_start:
{
uint8_t v_x_4__boxed_3367_; lean_object* v_res_3368_; 
v_x_4__boxed_3367_ = lean_unbox(v_x_3366_);
v_res_3368_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(v_x_4__boxed_3367_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object* v_k_3369_){
_start:
{
lean_inc(v_k_3369_);
return v_k_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object* v_k_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(v_k_3370_);
lean_dec(v_k_3370_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object* v_motive_3372_, lean_object* v_ctorIdx_3373_, uint8_t v_t_3374_, lean_object* v_h_3375_, lean_object* v_k_3376_){
_start:
{
lean_inc(v_k_3376_);
return v_k_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object* v_motive_3377_, lean_object* v_ctorIdx_3378_, lean_object* v_t_3379_, lean_object* v_h_3380_, lean_object* v_k_3381_){
_start:
{
uint8_t v_t_boxed_3382_; lean_object* v_res_3383_; 
v_t_boxed_3382_ = lean_unbox(v_t_3379_);
v_res_3383_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(v_motive_3377_, v_ctorIdx_3378_, v_t_boxed_3382_, v_h_3380_, v_k_3381_);
lean_dec(v_k_3381_);
lean_dec(v_ctorIdx_3378_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object* v_get_3384_){
_start:
{
lean_inc(v_get_3384_);
return v_get_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object* v_get_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(v_get_3385_);
lean_dec(v_get_3385_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object* v_motive_3387_, uint8_t v_t_3388_, lean_object* v_h_3389_, lean_object* v_get_3390_){
_start:
{
lean_inc(v_get_3390_);
return v_get_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object* v_motive_3391_, lean_object* v_t_3392_, lean_object* v_h_3393_, lean_object* v_get_3394_){
_start:
{
uint8_t v_t_boxed_3395_; lean_object* v_res_3396_; 
v_t_boxed_3395_ = lean_unbox(v_t_3392_);
v_res_3396_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(v_motive_3391_, v_t_boxed_3395_, v_h_3393_, v_get_3394_);
lean_dec(v_get_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object* v_put_3397_){
_start:
{
lean_inc(v_put_3397_);
return v_put_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object* v_put_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(v_put_3398_);
lean_dec(v_put_3398_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object* v_motive_3400_, uint8_t v_t_3401_, lean_object* v_h_3402_, lean_object* v_put_3403_){
_start:
{
lean_inc(v_put_3403_);
return v_put_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object* v_motive_3404_, lean_object* v_t_3405_, lean_object* v_h_3406_, lean_object* v_put_3407_){
_start:
{
uint8_t v_t_boxed_3408_; lean_object* v_res_3409_; 
v_t_boxed_3408_ = lean_unbox(v_t_3405_);
v_res_3409_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(v_motive_3404_, v_t_boxed_3408_, v_h_3406_, v_put_3407_);
lean_dec(v_put_3407_);
return v_res_3409_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object* v_n_3410_){
_start:
{
lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = lean_nat_dec_le(v_n_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
uint8_t v___x_3413_; 
v___x_3413_ = 1;
return v___x_3413_;
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = 0;
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object* v_n_3415_){
_start:
{
uint8_t v_res_3416_; lean_object* v_r_3417_; 
v_res_3416_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(v_n_3415_);
lean_dec(v_n_3415_);
v_r_3417_ = lean_box(v_res_3416_);
return v_r_3417_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t v_x_3418_, uint8_t v_y_3419_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3418_);
v___x_3421_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_y_3419_);
v___x_3422_ = lean_nat_dec_eq(v___x_3420_, v___x_3421_);
lean_dec(v___x_3421_);
lean_dec(v___x_3420_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object* v_x_3423_, lean_object* v_y_3424_){
_start:
{
uint8_t v_x_13__boxed_3425_; uint8_t v_y_14__boxed_3426_; uint8_t v_res_3427_; lean_object* v_r_3428_; 
v_x_13__boxed_3425_ = lean_unbox(v_x_3423_);
v_y_14__boxed_3426_ = lean_unbox(v_y_3424_);
v_res_3427_ = l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(v_x_13__boxed_3425_, v_y_14__boxed_3426_);
v_r_3428_ = lean_box(v_res_3427_);
return v_r_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(lean_object* v_self_3429_, lean_object* v_path_3430_, uint8_t v_extra_3431_){
_start:
{
if (v_extra_3431_ == 0)
{
lean_object* v_url_3432_; uint64_t v_hash_3433_; lean_object* v_path_3434_; lean_object* v_extraPaths_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3443_; 
v_url_3432_ = lean_ctor_get(v_self_3429_, 0);
v_hash_3433_ = lean_ctor_get_uint64(v_self_3429_, sizeof(void*)*3);
v_path_3434_ = lean_ctor_get(v_self_3429_, 1);
v_extraPaths_3435_ = lean_ctor_get(v_self_3429_, 2);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_self_3429_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3437_ = v_self_3429_;
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_extraPaths_3435_);
lean_inc(v_path_3434_);
lean_inc(v_url_3432_);
lean_dec(v_self_3429_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = lean_array_push(v_extraPaths_3435_, v_path_3434_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 2, v___x_3439_);
lean_ctor_set(v___x_3437_, 1, v_path_3430_);
v___x_3441_ = v___x_3437_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_url_3432_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_path_3430_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v___x_3439_);
lean_ctor_set_uint64(v_reuseFailAlloc_3442_, sizeof(void*)*3, v_hash_3433_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
else
{
lean_object* v_url_3444_; uint64_t v_hash_3445_; lean_object* v_path_3446_; lean_object* v_extraPaths_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3455_; 
v_url_3444_ = lean_ctor_get(v_self_3429_, 0);
v_hash_3445_ = lean_ctor_get_uint64(v_self_3429_, sizeof(void*)*3);
v_path_3446_ = lean_ctor_get(v_self_3429_, 1);
v_extraPaths_3447_ = lean_ctor_get(v_self_3429_, 2);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_self_3429_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3449_ = v_self_3429_;
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_extraPaths_3447_);
lean_inc(v_path_3446_);
lean_inc(v_url_3444_);
lean_dec(v_self_3429_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = lean_array_push(v_extraPaths_3447_, v_path_3430_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 2, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_url_3444_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_path_3446_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v___x_3451_);
lean_ctor_set_uint64(v_reuseFailAlloc_3454_, sizeof(void*)*3, v_hash_3445_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath___boxed(lean_object* v_self_3456_, lean_object* v_path_3457_, lean_object* v_extra_3458_){
_start:
{
uint8_t v_extra_boxed_3459_; lean_object* v_res_3460_; 
v_extra_boxed_3459_ = lean_unbox(v_extra_3458_);
v_res_3460_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(v_self_3456_, v_path_3457_, v_extra_boxed_3459_);
return v_res_3460_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_3464_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v___x_3463_);
return v___x_3465_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty(void){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
return v___x_3466_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___f_3469_; 
v___x_3468_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_3469_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3469_, 0, v___x_3468_);
return v___f_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(lean_object* v_self_3470_, lean_object* v_url_3471_, uint64_t v_hash_3472_, lean_object* v_path_3473_){
_start:
{
lean_object* v_infos_3474_; lean_object* v_indices_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3490_; 
v_infos_3474_ = lean_ctor_get(v_self_3470_, 0);
v_indices_3475_ = lean_ctor_get(v_self_3470_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_self_3470_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3477_ = v_self_3470_;
v_isShared_3478_ = v_isSharedCheck_3490_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_indices_3475_);
lean_inc(v_infos_3474_);
lean_dec(v_self_3470_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3490_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___f_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___f_3479_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___x_3480_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3481_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3481_, 0, v_url_3471_);
lean_ctor_set(v___x_3481_, 1, v_path_3473_);
lean_ctor_set(v___x_3481_, 2, v___x_3480_);
lean_ctor_set_uint64(v___x_3481_, sizeof(void*)*3, v_hash_3472_);
lean_inc_ref(v_infos_3474_);
v___x_3482_ = lean_array_push(v_infos_3474_, v___x_3481_);
v___f_3483_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3484_ = lean_array_get_size(v_infos_3474_);
lean_dec_ref(v_infos_3474_);
v___x_3485_ = lean_box_uint64(v_hash_3472_);
v___x_3486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3483_, v___f_3479_, v_indices_3475_, v___x_3485_, v___x_3484_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 1, v___x_3486_);
lean_ctor_set(v___x_3477_, 0, v___x_3482_);
v___x_3488_ = v___x_3477_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___boxed(lean_object* v_self_3491_, lean_object* v_url_3492_, lean_object* v_hash_3493_, lean_object* v_path_3494_){
_start:
{
uint64_t v_hash_boxed_3495_; lean_object* v_res_3496_; 
v_hash_boxed_3495_ = lean_unbox_uint64(v_hash_3493_);
lean_dec_ref(v_hash_3493_);
v_res_3496_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(v_self_3491_, v_url_3492_, v_hash_boxed_3495_, v_path_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(lean_object* v_self_3497_, lean_object* v_url_3498_, uint64_t v_hash_3499_, lean_object* v_path_3500_){
_start:
{
lean_object* v_infos_3501_; lean_object* v_indices_3502_; lean_object* v___f_3503_; lean_object* v___f_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_infos_3501_ = lean_ctor_get(v_self_3497_, 0);
v_indices_3502_ = lean_ctor_get(v_self_3497_, 1);
v___f_3503_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___f_3504_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3505_ = lean_box_uint64(v_hash_3499_);
v___x_3506_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_3504_, v___f_3503_, v_indices_3502_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3519_; 
lean_inc_ref(v_indices_3502_);
lean_inc_ref(v_infos_3501_);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_self_3497_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; lean_object* v_unused_3521_; 
v_unused_3520_ = lean_ctor_get(v_self_3497_, 1);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v_self_3497_, 0);
lean_dec(v_unused_3521_);
v___x_3508_ = v_self_3497_;
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v_self_3497_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3510_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3511_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3511_, 0, v_url_3498_);
lean_ctor_set(v___x_3511_, 1, v_path_3500_);
lean_ctor_set(v___x_3511_, 2, v___x_3510_);
lean_ctor_set_uint64(v___x_3511_, sizeof(void*)*3, v_hash_3499_);
lean_inc_ref(v_infos_3501_);
v___x_3512_ = lean_array_push(v_infos_3501_, v___x_3511_);
v___x_3513_ = lean_array_get_size(v_infos_3501_);
lean_dec_ref(v_infos_3501_);
v___x_3514_ = lean_box_uint64(v_hash_3499_);
v___x_3515_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3504_, v___f_3503_, v_indices_3502_, v___x_3514_, v___x_3513_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v___x_3515_);
lean_ctor_set(v___x_3508_, 0, v___x_3512_);
v___x_3517_ = v___x_3508_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_dec_ref(v_path_3500_);
lean_dec_ref(v_url_3498_);
return v_self_3497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew___boxed(lean_object* v_self_3522_, lean_object* v_url_3523_, lean_object* v_hash_3524_, lean_object* v_path_3525_){
_start:
{
uint64_t v_hash_boxed_3526_; lean_object* v_res_3527_; 
v_hash_boxed_3526_ = lean_unbox_uint64(v_hash_3524_);
lean_dec_ref(v_hash_3524_);
v_res_3527_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(v_self_3522_, v_url_3523_, v_hash_boxed_3526_, v_path_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(lean_object* v_self_3528_, lean_object* v_url_3529_, uint64_t v_hash_3530_, lean_object* v_path_3531_, uint8_t v_extra_3532_){
_start:
{
lean_object* v_infos_3533_; lean_object* v_indices_3534_; lean_object* v___f_3535_; lean_object* v___f_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v_infos_3533_ = lean_ctor_get(v_self_3528_, 0);
v_indices_3534_ = lean_ctor_get(v_self_3528_, 1);
v___f_3535_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___f_3536_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3537_ = lean_box_uint64(v_hash_3530_);
v___x_3538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3536_, v___f_3535_, v_indices_3534_, v___x_3537_);
if (lean_obj_tag(v___x_3538_) == 1)
{
lean_object* v_val_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
lean_dec_ref(v_url_3529_);
v_val_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_val_3539_);
lean_dec_ref_known(v___x_3538_, 1);
v___x_3540_ = lean_array_get_size(v_infos_3533_);
v___x_3541_ = lean_nat_dec_lt(v_val_3539_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_dec(v_val_3539_);
lean_dec_ref(v_path_3531_);
return v_self_3528_;
}
else
{
lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3578_; 
lean_inc_ref(v_indices_3534_);
lean_inc_ref(v_infos_3533_);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_self_3528_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; lean_object* v_unused_3580_; 
v_unused_3579_ = lean_ctor_get(v_self_3528_, 1);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_self_3528_, 0);
lean_dec(v_unused_3580_);
v___x_3543_ = v_self_3528_;
v_isShared_3544_ = v_isSharedCheck_3578_;
goto v_resetjp_3542_;
}
else
{
lean_dec(v_self_3528_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3578_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_v_3545_; lean_object* v___x_3546_; lean_object* v_xs_x27_3547_; lean_object* v___y_3549_; 
v_v_3545_ = lean_array_fget(v_infos_3533_, v_val_3539_);
v___x_3546_ = lean_box(0);
v_xs_x27_3547_ = lean_array_fset(v_infos_3533_, v_val_3539_, v___x_3546_);
if (v_extra_3532_ == 0)
{
lean_object* v_url_3554_; uint64_t v_hash_3555_; lean_object* v_path_3556_; lean_object* v_extraPaths_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3565_; 
v_url_3554_ = lean_ctor_get(v_v_3545_, 0);
v_hash_3555_ = lean_ctor_get_uint64(v_v_3545_, sizeof(void*)*3);
v_path_3556_ = lean_ctor_get(v_v_3545_, 1);
v_extraPaths_3557_ = lean_ctor_get(v_v_3545_, 2);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_v_3545_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3559_ = v_v_3545_;
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_extraPaths_3557_);
lean_inc(v_path_3556_);
lean_inc(v_url_3554_);
lean_dec(v_v_3545_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3561_ = lean_array_push(v_extraPaths_3557_, v_path_3556_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 2, v___x_3561_);
lean_ctor_set(v___x_3559_, 1, v_path_3531_);
v___x_3563_ = v___x_3559_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_url_3554_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_path_3531_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v___x_3561_);
lean_ctor_set_uint64(v_reuseFailAlloc_3564_, sizeof(void*)*3, v_hash_3555_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
v___y_3549_ = v___x_3563_;
goto v___jp_3548_;
}
}
}
else
{
lean_object* v_url_3566_; uint64_t v_hash_3567_; lean_object* v_path_3568_; lean_object* v_extraPaths_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3577_; 
v_url_3566_ = lean_ctor_get(v_v_3545_, 0);
v_hash_3567_ = lean_ctor_get_uint64(v_v_3545_, sizeof(void*)*3);
v_path_3568_ = lean_ctor_get(v_v_3545_, 1);
v_extraPaths_3569_ = lean_ctor_get(v_v_3545_, 2);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_v_3545_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3571_ = v_v_3545_;
v_isShared_3572_ = v_isSharedCheck_3577_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_extraPaths_3569_);
lean_inc(v_path_3568_);
lean_inc(v_url_3566_);
lean_dec(v_v_3545_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3577_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3573_ = lean_array_push(v_extraPaths_3569_, v_path_3531_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 2, v___x_3573_);
v___x_3575_ = v___x_3571_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_url_3566_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_path_3568_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v___x_3573_);
lean_ctor_set_uint64(v_reuseFailAlloc_3576_, sizeof(void*)*3, v_hash_3567_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
v___y_3549_ = v___x_3575_;
goto v___jp_3548_;
}
}
}
v___jp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3550_ = lean_array_fset(v_xs_x27_3547_, v_val_3539_, v___y_3549_);
lean_dec(v_val_3539_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 0, v___x_3550_);
v___x_3552_ = v___x_3543_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_indices_3534_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
else
{
lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3593_; 
lean_inc_ref(v_indices_3534_);
lean_inc_ref(v_infos_3533_);
lean_dec(v___x_3538_);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_self_3528_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; lean_object* v_unused_3595_; 
v_unused_3594_ = lean_ctor_get(v_self_3528_, 1);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_self_3528_, 0);
lean_dec(v_unused_3595_);
v___x_3582_ = v_self_3528_;
v_isShared_3583_ = v_isSharedCheck_3593_;
goto v_resetjp_3581_;
}
else
{
lean_dec(v_self_3528_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3593_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3584_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3585_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3585_, 0, v_url_3529_);
lean_ctor_set(v___x_3585_, 1, v_path_3531_);
lean_ctor_set(v___x_3585_, 2, v___x_3584_);
lean_ctor_set_uint64(v___x_3585_, sizeof(void*)*3, v_hash_3530_);
lean_inc_ref(v_infos_3533_);
v___x_3586_ = lean_array_push(v_infos_3533_, v___x_3585_);
v___x_3587_ = lean_array_get_size(v_infos_3533_);
lean_dec_ref(v_infos_3533_);
v___x_3588_ = lean_box_uint64(v_hash_3530_);
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3536_, v___f_3535_, v_indices_3534_, v___x_3588_, v___x_3587_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v___x_3589_);
lean_ctor_set(v___x_3582_, 0, v___x_3586_);
v___x_3591_ = v___x_3582_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add___boxed(lean_object* v_self_3596_, lean_object* v_url_3597_, lean_object* v_hash_3598_, lean_object* v_path_3599_, lean_object* v_extra_3600_){
_start:
{
uint64_t v_hash_boxed_3601_; uint8_t v_extra_boxed_3602_; lean_object* v_res_3603_; 
v_hash_boxed_3601_ = lean_unbox_uint64(v_hash_3598_);
lean_dec_ref(v_hash_3598_);
v_extra_boxed_3602_ = lean_unbox(v_extra_3600_);
v_res_3603_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(v_self_3596_, v_url_3597_, v_hash_boxed_3601_, v_path_3599_, v_extra_boxed_3602_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(lean_object* v_a_3604_, lean_object* v_as_3605_, size_t v_sz_3606_, size_t v_i_3607_, lean_object* v_b_3608_){
_start:
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_usize_dec_lt(v_i_3607_, v_sz_3606_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v_b_3608_);
return v___x_3611_;
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3613_; 
v_a_3612_ = lean_array_uget_borrowed(v_as_3605_, v_i_3607_);
v___x_3613_ = l_IO_FS_writeBinFile(v_a_3612_, v_a_3604_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; size_t v___x_3615_; size_t v___x_3616_; 
lean_dec_ref_known(v___x_3613_, 1);
v___x_3614_ = lean_box(0);
v___x_3615_ = ((size_t)1ULL);
v___x_3616_ = lean_usize_add(v_i_3607_, v___x_3615_);
v_i_3607_ = v___x_3616_;
v_b_3608_ = v___x_3614_;
goto _start;
}
else
{
return v___x_3613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0___boxed(lean_object* v_a_3618_, lean_object* v_as_3619_, lean_object* v_sz_3620_, lean_object* v_i_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_){
_start:
{
size_t v_sz_boxed_3624_; size_t v_i_boxed_3625_; lean_object* v_res_3626_; 
v_sz_boxed_3624_ = lean_unbox_usize(v_sz_3620_);
lean_dec(v_sz_3620_);
v_i_boxed_3625_ = lean_unbox_usize(v_i_3621_);
lean_dec(v_i_3621_);
v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(v_a_3618_, v_as_3619_, v_sz_boxed_3624_, v_i_boxed_3625_, v_b_3622_);
lean_dec_ref(v_as_3619_);
lean_dec_ref(v_a_3618_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(lean_object* v_path_3627_, lean_object* v_extraPaths_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_IO_FS_readBinFile(v_path_3627_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3632_; size_t v_sz_3633_; size_t v___x_3634_; lean_object* v___x_3635_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v___x_3632_ = lean_box(0);
v_sz_3633_ = lean_array_size(v_extraPaths_3628_);
v___x_3634_ = ((size_t)0ULL);
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(v_a_3631_, v_extraPaths_3628_, v_sz_3633_, v___x_3634_, v___x_3632_);
lean_dec(v_a_3631_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; 
v_unused_3643_ = lean_ctor_get(v___x_3635_, 0);
lean_dec(v_unused_3643_);
v___x_3637_ = v___x_3635_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_dec(v___x_3635_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v___x_3632_);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3632_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
else
{
return v___x_3635_;
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3630_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3630_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths___boxed(lean_object* v_path_3652_, lean_object* v_extraPaths_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(v_path_3652_, v_extraPaths_3653_);
lean_dec_ref(v_extraPaths_3653_);
lean_dec_ref(v_path_3652_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object* v_cfg_3657_, lean_object* v_out_3658_){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0));
v___x_3660_ = l_Lake_JsonObject_getJson_x3f(v_out_3658_, v___x_3659_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_box(0);
return v___x_3661_;
}
else
{
lean_object* v_val_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3678_; 
v_val_3662_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3664_ = v___x_3660_;
v_isShared_3665_ = v_isSharedCheck_3678_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_val_3662_);
lean_dec(v___x_3660_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3678_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_Json_getNat_x3f(v_val_3662_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3667_; 
lean_dec_ref_known(v___x_3666_, 1);
lean_del_object(v___x_3664_);
v___x_3667_ = lean_box(0);
return v___x_3667_;
}
else
{
if (lean_obj_tag(v___x_3666_) == 1)
{
lean_object* v_a_3668_; lean_object* v_infos_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_a_3668_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3666_, 1);
v_infos_3669_ = lean_ctor_get(v_cfg_3657_, 1);
v___x_3670_ = lean_array_get_size(v_infos_3669_);
v___x_3671_ = lean_nat_dec_lt(v_a_3668_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
lean_dec(v_a_3668_);
lean_del_object(v___x_3664_);
v___x_3672_ = lean_box(0);
return v___x_3672_;
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = lean_array_fget_borrowed(v_infos_3669_, v_a_3668_);
lean_dec(v_a_3668_);
lean_inc(v___x_3673_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3673_);
v___x_3675_ = v___x_3664_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
else
{
lean_object* v___x_3677_; 
lean_dec_ref_known(v___x_3666_, 1);
lean_del_object(v___x_3664_);
v___x_3677_ = lean_box(0);
return v___x_3677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object* v_cfg_3679_, lean_object* v_out_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3679_, v_out_3680_);
lean_dec(v_out_3680_);
lean_dec_ref(v_cfg_3679_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object* v_s_3682_, lean_object* v_pos_3683_){
_start:
{
lean_object* v_str_3684_; lean_object* v_startInclusive_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_str_3684_ = lean_ctor_get(v_s_3682_, 0);
v_startInclusive_3685_ = lean_ctor_get(v_s_3682_, 1);
v___x_3686_ = lean_nat_add(v_startInclusive_3685_, v_pos_3683_);
v___x_3687_ = lean_nat_sub(v___x_3686_, v_startInclusive_3685_);
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = lean_nat_dec_eq(v___x_3687_, v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___y_3698_; lean_object* v___x_3699_; uint32_t v___x_3700_; uint8_t v___y_3702_; uint32_t v___x_3707_; uint8_t v___x_3708_; 
lean_inc(v_startInclusive_3685_);
lean_inc_ref(v_str_3684_);
v___x_3690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3690_, 0, v_str_3684_);
lean_ctor_set(v___x_3690_, 1, v_startInclusive_3685_);
lean_ctor_set(v___x_3690_, 2, v___x_3686_);
v___x_3691_ = lean_unsigned_to_nat(1u);
v___x_3692_ = lean_nat_sub(v___x_3687_, v___x_3691_);
lean_dec(v___x_3687_);
v___x_3693_ = l_String_Slice_posLE(v___x_3690_, v___x_3692_);
lean_dec_ref_known(v___x_3690_, 3);
v___x_3699_ = lean_nat_add(v_startInclusive_3685_, v___x_3693_);
v___x_3700_ = lean_string_utf8_get_fast(v_str_3684_, v___x_3699_);
lean_dec(v___x_3699_);
v___x_3707_ = 32;
v___x_3708_ = lean_uint32_dec_eq(v___x_3700_, v___x_3707_);
if (v___x_3708_ == 0)
{
uint32_t v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = 9;
v___x_3710_ = lean_uint32_dec_eq(v___x_3700_, v___x_3709_);
v___y_3702_ = v___x_3710_;
goto v___jp_3701_;
}
else
{
v___y_3702_ = v___x_3708_;
goto v___jp_3701_;
}
v___jp_3694_:
{
uint8_t v___x_3695_; 
v___x_3695_ = lean_nat_dec_lt(v___x_3693_, v_pos_3683_);
if (v___x_3695_ == 0)
{
lean_dec(v___x_3693_);
return v_pos_3683_;
}
else
{
lean_dec(v_pos_3683_);
v_pos_3683_ = v___x_3693_;
goto _start;
}
}
v___jp_3697_:
{
if (v___y_3698_ == 0)
{
lean_dec(v___x_3693_);
return v_pos_3683_;
}
else
{
goto v___jp_3694_;
}
}
v___jp_3701_:
{
if (v___y_3702_ == 0)
{
uint32_t v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = 13;
v___x_3704_ = lean_uint32_dec_eq(v___x_3700_, v___x_3703_);
if (v___x_3704_ == 0)
{
uint32_t v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = 10;
v___x_3706_ = lean_uint32_dec_eq(v___x_3700_, v___x_3705_);
v___y_3698_ = v___x_3706_;
goto v___jp_3697_;
}
else
{
v___y_3698_ = v___x_3704_;
goto v___jp_3697_;
}
}
else
{
goto v___jp_3694_;
}
}
}
else
{
lean_dec(v___x_3687_);
lean_dec(v___x_3686_);
return v_pos_3683_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object* v_s_3711_, lean_object* v_pos_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v_s_3711_, v_pos_3712_);
lean_dec_ref(v_s_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object* v_cfg_3726_, lean_object* v_hOut_3727_, lean_object* v_info_3728_, lean_object* v_code_x3f_3729_, lean_object* v_out_3730_, lean_object* v_line_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_msg_3735_; lean_object* v___y_3736_; lean_object* v___y_3753_; lean_object* v_msg_3754_; lean_object* v___y_3755_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v_a_3774_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v_val_3785_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; uint8_t v_kind_3829_; lean_object* v_scope_3830_; lean_object* v_msg_3832_; lean_object* v___y_3833_; lean_object* v_msg_3874_; lean_object* v___y_3875_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3903_; 
v_kind_3829_ = lean_ctor_get_uint8(v_cfg_3726_, sizeof(void*)*3);
v_scope_3830_ = lean_ctor_get(v_cfg_3726_, 0);
lean_inc_ref(v_scope_3830_);
lean_dec_ref(v_cfg_3726_);
if (v_kind_3829_ == 0)
{
lean_object* v___x_3905_; 
v___x_3905_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___y_3903_ = v___x_3905_;
goto v___jp_3902_;
}
else
{
lean_object* v___x_3906_; 
v___x_3906_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___y_3903_ = v___x_3906_;
goto v___jp_3902_;
}
v___jp_3734_:
{
uint8_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3737_ = 3;
v___x_3738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3738_, 0, v_msg_3735_);
lean_ctor_set_uint8(v___x_3738_, sizeof(void*)*1, v___x_3737_);
lean_inc_ref_n(v___y_3736_, 2);
v___x_3739_ = lean_apply_2(v___y_3736_, v___x_3738_, lean_box(0));
v___x_3740_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0));
v___x_3741_ = lean_unsigned_to_nat(0u);
v___x_3742_ = lean_string_utf8_byte_size(v_line_3731_);
lean_inc_ref(v_line_3731_);
v___x_3743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3743_, 0, v_line_3731_);
lean_ctor_set(v___x_3743_, 1, v___x_3741_);
lean_ctor_set(v___x_3743_, 2, v___x_3742_);
v___x_3744_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_3743_, v___x_3742_);
lean_dec_ref_known(v___x_3743_, 3);
v___x_3745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3745_, 0, v_line_3731_);
lean_ctor_set(v___x_3745_, 1, v___x_3741_);
lean_ctor_set(v___x_3745_, 2, v___x_3744_);
v___x_3746_ = l_String_Slice_toString(v___x_3745_);
lean_dec_ref_known(v___x_3745_, 3);
v___x_3747_ = lean_string_append(v___x_3740_, v___x_3746_);
lean_dec_ref(v___x_3746_);
v___x_3748_ = 0;
v___x_3749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set_uint8(v___x_3749_, sizeof(void*)*1, v___x_3748_);
v___x_3750_ = lean_apply_2(v___y_3736_, v___x_3749_, lean_box(0));
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
v___jp_3752_:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lake_removeFileIfExists(v___y_3753_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_dec_ref_known(v___x_3756_, 1);
v_msg_3735_ = v_msg_3754_;
v___y_3736_ = v___y_3755_;
goto v___jp_3734_;
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_msg_3754_);
lean_dec_ref(v_line_3731_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3769_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3769_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3761_ = lean_io_error_to_string(v_a_3757_);
v___x_3762_ = 3;
v___x_3763_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*1, v___x_3762_);
lean_inc_ref(v___y_3755_);
v___x_3764_ = lean_apply_2(v___y_3755_, v___x_3763_, lean_box(0));
v___x_3765_ = lean_box(0);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3765_);
v___x_3767_ = v___x_3759_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
v___jp_3770_:
{
if (lean_obj_tag(v_a_3774_) == 1)
{
lean_object* v_a_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_a_3775_ = lean_ctor_get(v_a_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v_a_3774_, 1);
v___x_3776_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3777_ = lean_string_append(v___y_3773_, v___x_3776_);
v___x_3778_ = lean_string_append(v___x_3777_, v_a_3775_);
lean_dec(v_a_3775_);
v___y_3753_ = v___y_3771_;
v_msg_3754_ = v___x_3778_;
v___y_3755_ = v___y_3772_;
goto v___jp_3752_;
}
else
{
lean_dec_ref(v_a_3774_);
v___y_3753_ = v___y_3771_;
v_msg_3754_ = v___y_3773_;
v___y_3755_ = v___y_3772_;
goto v___jp_3752_;
}
}
v___jp_3779_:
{
lean_object* v___x_3786_; uint8_t v___x_3787_; 
v___x_3786_ = lean_array_get_size(v___y_3784_);
v___x_3787_ = lean_nat_dec_lt(v___y_3780_, v___x_3786_);
if (v___x_3787_ == 0)
{
v___y_3771_ = v___y_3781_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3782_;
v_a_3774_ = v_val_3785_;
goto v___jp_3770_;
}
else
{
lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_nat_dec_le(v___x_3786_, v___x_3786_);
if (v___x_3789_ == 0)
{
if (v___x_3787_ == 0)
{
v___y_3771_ = v___y_3781_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3782_;
v_a_3774_ = v_val_3785_;
goto v___jp_3770_;
}
else
{
size_t v___x_3790_; size_t v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = ((size_t)0ULL);
v___x_3791_ = lean_usize_of_nat(v___x_3786_);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3784_, v___x_3790_, v___x_3791_, v___x_3788_, v___y_3783_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_dec_ref_known(v___x_3792_, 1);
v___y_3771_ = v___y_3781_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3782_;
v_a_3774_ = v_val_3785_;
goto v___jp_3770_;
}
else
{
lean_dec_ref(v_val_3785_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v_line_3731_);
return v___x_3792_;
}
}
}
else
{
size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = ((size_t)0ULL);
v___x_3794_ = lean_usize_of_nat(v___x_3786_);
v___x_3795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3784_, v___x_3793_, v___x_3794_, v___x_3788_, v___y_3783_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref_known(v___x_3795_, 1);
v___y_3771_ = v___y_3781_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3782_;
v_a_3774_ = v_val_3785_;
goto v___jp_3770_;
}
else
{
lean_dec_ref(v_val_3785_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v_line_3731_);
return v___x_3795_;
}
}
}
}
v___jp_3796_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3801_ = l_Lake_JsonObject_getJson_x3f(v_out_3730_, v___x_3800_);
if (lean_obj_tag(v___x_3801_) == 0)
{
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
else
{
lean_object* v_val_3802_; lean_object* v___x_3803_; 
v_val_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = l_Lean_Json_getNat_x3f(v_val_3802_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_dec_ref_known(v___x_3803_, 1);
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
else
{
if (lean_obj_tag(v___x_3803_) == 1)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = lean_nat_dec_lt(v___x_3805_, v_a_3804_);
lean_dec(v_a_3804_);
if (v___x_3806_ == 0)
{
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3));
v___x_3808_ = l_Lake_JsonObject_getJson_x3f(v_out_3730_, v___x_3807_);
if (lean_obj_tag(v___x_3808_) == 0)
{
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
else
{
lean_object* v_val_3809_; lean_object* v___x_3810_; 
v_val_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v___x_3810_ = l_Lean_Json_getStr_x3f(v_val_3809_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_dec_ref_known(v___x_3810_, 1);
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
else
{
if (lean_obj_tag(v___x_3810_) == 1)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3828_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3828_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3828_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; uint8_t v___x_3816_; uint8_t v___x_3817_; 
v___x_3815_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3816_ = lean_string_dec_eq(v_a_3811_, v___x_3815_);
lean_dec(v_a_3811_);
v___x_3817_ = lean_bool_not(v___x_3816_);
if (v___x_3817_ == 0)
{
lean_del_object(v___x_3813_);
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3819_ = l_IO_FS_readFile(v___y_3797_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v_a_3820_);
v___x_3822_ = v___x_3813_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
v___y_3780_ = v___x_3805_;
v___y_3781_ = v___y_3797_;
v___y_3782_ = v___y_3799_;
v___y_3783_ = v___y_3798_;
v___y_3784_ = v___x_3818_;
v_val_3785_ = v___x_3822_;
goto v___jp_3779_;
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; 
v_a_3824_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3819_, 1);
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 0);
lean_ctor_set(v___x_3813_, 0, v_a_3824_);
v___x_3826_ = v___x_3813_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
v___y_3780_ = v___x_3805_;
v___y_3781_ = v___y_3797_;
v___y_3782_ = v___y_3799_;
v___y_3783_ = v___y_3798_;
v___y_3784_ = v___x_3818_;
v_val_3785_ = v___x_3826_;
goto v___jp_3779_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3810_, 1);
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3803_, 1);
v___y_3753_ = v___y_3797_;
v_msg_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
goto v___jp_3752_;
}
}
}
}
v___jp_3831_:
{
lean_object* v_url_3834_; lean_object* v_path_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v_msg_3841_; 
v_url_3834_ = lean_ctor_get(v_info_3728_, 0);
v_path_3835_ = lean_ctor_get(v_info_3728_, 1);
v___x_3836_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3837_ = lean_string_append(v_msg_3832_, v___x_3836_);
v___x_3838_ = lean_string_append(v___x_3837_, v_path_3835_);
v___x_3839_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3840_ = lean_string_append(v___x_3838_, v___x_3839_);
v_msg_3841_ = lean_string_append(v___x_3840_, v_url_3834_);
if (v_kind_3829_ == 0)
{
if (lean_obj_tag(v_code_x3f_3729_) == 1)
{
lean_object* v_a_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v_a_3842_ = lean_ctor_get(v_code_x3f_3729_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v_code_x3f_3729_, 1);
v___x_3843_ = lean_unsigned_to_nat(404u);
v___x_3844_ = lean_nat_dec_eq(v_a_3842_, v___x_3843_);
lean_dec(v_a_3842_);
if (v___x_3844_ == 0)
{
v___y_3797_ = v_path_3835_;
v___y_3798_ = v___y_3833_;
v___y_3799_ = v_msg_3841_;
goto v___jp_3796_;
}
else
{
v___y_3753_ = v_path_3835_;
v_msg_3754_ = v_msg_3841_;
v___y_3755_ = v___y_3833_;
goto v___jp_3752_;
}
}
else
{
lean_dec_ref(v_code_x3f_3729_);
v___y_3797_ = v_path_3835_;
v___y_3798_ = v___y_3833_;
v___y_3799_ = v_msg_3841_;
goto v___jp_3796_;
}
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec_ref(v_code_x3f_3729_);
v___x_3845_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3846_ = l_Lake_JsonObject_getJson_x3f(v_out_3730_, v___x_3845_);
if (lean_obj_tag(v___x_3846_) == 0)
{
v_msg_3735_ = v_msg_3841_;
v___y_3736_ = v___y_3833_;
goto v___jp_3734_;
}
else
{
lean_object* v_val_3847_; lean_object* v___x_3848_; 
v_val_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_val_3847_);
lean_dec_ref_known(v___x_3846_, 1);
v___x_3848_ = l_Lean_Json_getNat_x3f(v_val_3847_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_dec_ref_known(v___x_3848_, 1);
v_msg_3735_ = v_msg_3841_;
v___y_3736_ = v___y_3833_;
goto v___jp_3734_;
}
else
{
if (lean_obj_tag(v___x_3848_) == 1)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3850_ = lean_unsigned_to_nat(0u);
v___x_3851_ = lean_nat_dec_lt(v___x_3850_, v_a_3849_);
if (v___x_3851_ == 0)
{
lean_dec(v_a_3849_);
v_msg_3735_ = v_msg_3841_;
v___y_3736_ = v___y_3833_;
goto v___jp_3734_;
}
else
{
size_t v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_usize_of_nat(v_a_3849_);
lean_dec(v_a_3849_);
v___x_3853_ = lean_io_prim_handle_read(v_hOut_3727_, v___x_3852_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; uint8_t v___x_3855_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3855_ = lean_string_validate_utf8(v_a_3854_);
if (v___x_3855_ == 0)
{
lean_dec(v_a_3854_);
v_msg_3735_ = v_msg_3841_;
v___y_3736_ = v___y_3833_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3856_ = lean_string_from_utf8_unchecked(v_a_3854_);
v___x_3857_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3858_ = lean_string_append(v_msg_3841_, v___x_3857_);
v___x_3859_ = lean_string_append(v___x_3858_, v___x_3856_);
lean_dec_ref(v___x_3856_);
v_msg_3735_ = v___x_3859_;
v___y_3736_ = v___y_3833_;
goto v___jp_3734_;
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v_msg_3841_);
lean_dec_ref(v_line_3731_);
v_a_3860_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3862_ = v___x_3853_;
v_isShared_3863_ = v_isSharedCheck_3872_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3853_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3872_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3864_; uint8_t v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3864_ = lean_io_error_to_string(v_a_3860_);
v___x_3865_ = 3;
v___x_3866_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
lean_ctor_set_uint8(v___x_3866_, sizeof(void*)*1, v___x_3865_);
lean_inc_ref(v___y_3833_);
v___x_3867_ = lean_apply_2(v___y_3833_, v___x_3866_, lean_box(0));
v___x_3868_ = lean_box(0);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3868_);
v___x_3870_ = v___x_3862_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3848_, 1);
v_msg_3735_ = v_msg_3841_;
v___y_3736_ = v___y_3833_;
goto v___jp_3734_;
}
}
}
}
}
v___jp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_3877_ = l_Lake_JsonObject_getJson_x3f(v_out_3730_, v___x_3876_);
if (lean_obj_tag(v___x_3877_) == 0)
{
v_msg_3832_ = v_msg_3874_;
v___y_3833_ = v___y_3875_;
goto v___jp_3831_;
}
else
{
lean_object* v_val_3878_; lean_object* v___x_3879_; 
v_val_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_val_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = l_Lean_Json_getStr_x3f(v_val_3878_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_dec_ref_known(v___x_3879_, 1);
v_msg_3832_ = v_msg_3874_;
v___y_3833_ = v___y_3875_;
goto v___jp_3831_;
}
else
{
if (lean_obj_tag(v___x_3879_) == 1)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_msg_3883_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5));
v___x_3882_ = lean_string_append(v_msg_3874_, v___x_3881_);
v_msg_3883_ = lean_string_append(v___x_3882_, v_a_3880_);
lean_dec(v_a_3880_);
v_msg_3832_ = v_msg_3883_;
v___y_3833_ = v___y_3875_;
goto v___jp_3831_;
}
else
{
lean_dec_ref_known(v___x_3879_, 1);
v_msg_3832_ = v_msg_3874_;
v___y_3833_ = v___y_3875_;
goto v___jp_3831_;
}
}
}
}
v___jp_3884_:
{
uint64_t v_hash_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v_msg_3894_; 
v_hash_3887_ = lean_ctor_get_uint64(v_info_3728_, sizeof(void*)*3);
v___x_3888_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_3889_ = lean_string_append(v___y_3886_, v___x_3888_);
v___x_3890_ = lean_string_append(v___x_3889_, v___y_3885_);
v___x_3891_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7));
v___x_3892_ = lean_string_append(v___x_3890_, v___x_3891_);
v___x_3893_ = l_Lake_lowerHexUInt64(v_hash_3887_);
v_msg_3894_ = lean_string_append(v___x_3892_, v___x_3893_);
lean_dec_ref(v___x_3893_);
if (lean_obj_tag(v_code_x3f_3729_) == 1)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v_msg_3901_; 
v_a_3895_ = lean_ctor_get(v_code_x3f_3729_, 0);
v___x_3896_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8));
v___x_3897_ = lean_string_append(v_msg_3894_, v___x_3896_);
lean_inc(v_a_3895_);
v___x_3898_ = l_Nat_reprFast(v_a_3895_);
v___x_3899_ = lean_string_append(v___x_3897_, v___x_3898_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v_msg_3901_ = lean_string_append(v___x_3899_, v___x_3900_);
v_msg_3874_ = v_msg_3901_;
v___y_3875_ = v_a_3732_;
goto v___jp_3873_;
}
else
{
v_msg_3874_ = v_msg_3894_;
v___y_3875_ = v_a_3732_;
goto v___jp_3873_;
}
}
v___jp_3902_:
{
lean_object* v_s_3904_; 
v_s_3904_ = lean_ctor_get(v_scope_3830_, 0);
lean_inc_ref(v_s_3904_);
lean_dec_ref(v_scope_3830_);
v___y_3885_ = v___y_3903_;
v___y_3886_ = v_s_3904_;
goto v___jp_3884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object* v_cfg_3907_, lean_object* v_hOut_3908_, lean_object* v_info_3909_, lean_object* v_code_x3f_3910_, lean_object* v_out_3911_, lean_object* v_line_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3907_, v_hOut_3908_, v_info_3909_, v_code_x3f_3910_, v_out_3911_, v_line_3912_, v_a_3913_);
lean_dec_ref(v_a_3913_);
lean_dec(v_out_3911_);
lean_dec_ref(v_info_3909_);
lean_dec(v_hOut_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object* v_cfg_3916_, lean_object* v_hOut_3917_, lean_object* v_val_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, uint8_t v___x_3921_, lean_object* v_code_x3f_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3916_, v_hOut_3917_, v_val_3918_, v_code_x3f_3922_, v_a_3919_, v_a_3920_, v___y_3924_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3943_; 
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; 
v_unused_3944_ = lean_ctor_get(v___x_3926_, 0);
lean_dec(v_unused_3944_);
v___x_3928_ = v___x_3926_;
v_isShared_3929_ = v_isSharedCheck_3943_;
goto v_resetjp_3927_;
}
else
{
lean_dec(v___x_3926_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3943_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v_numSuccesses_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3942_; 
v_numSuccesses_3930_ = lean_ctor_get(v___y_3923_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___y_3923_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3932_ = v___y_3923_;
v_isShared_3933_ = v_isSharedCheck_3942_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_numSuccesses_3930_);
lean_dec(v___y_3923_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3942_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3934_ = lean_box(0);
if (v_isShared_3933_ == 0)
{
v___x_3936_ = v___x_3932_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_numSuccesses_3930_);
v___x_3936_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*1, v___x_3921_);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3934_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3937_);
v___x_3939_ = v___x_3928_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v___y_3923_);
v_a_3945_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3926_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3926_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object* v_cfg_3953_, lean_object* v_hOut_3954_, lean_object* v_val_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v___x_3958_, lean_object* v_code_x3f_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint8_t v___x_33626__boxed_3963_; lean_object* v_res_3964_; 
v___x_33626__boxed_3963_ = lean_unbox(v___x_3958_);
v_res_3964_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_3953_, v_hOut_3954_, v_val_3955_, v_a_3956_, v_a_3957_, v___x_33626__boxed_3963_, v_code_x3f_3959_, v___y_3960_, v___y_3961_);
lean_dec_ref(v___y_3961_);
lean_dec(v_a_3956_);
lean_dec_ref(v_val_3955_);
lean_dec(v_hOut_3954_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object* v_cfg_3967_, uint64_t v_hash_3968_, lean_object* v_path_3969_, lean_object* v_url_3970_, lean_object* v_extraPaths_3971_, lean_object* v___x_3972_, uint8_t v___x_3973_, lean_object* v_00___3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___y_3979_; lean_object* v___y_3995_; lean_object* v___y_4083_; uint8_t v_kind_4111_; 
v_kind_4111_ = lean_ctor_get_uint8(v_cfg_3967_, sizeof(void*)*3);
if (v_kind_4111_ == 0)
{
lean_object* v_scope_4112_; lean_object* v_s_4113_; 
v_scope_4112_ = lean_ctor_get(v_cfg_3967_, 0);
lean_inc_ref(v_scope_4112_);
lean_dec_ref(v_cfg_3967_);
v_s_4113_ = lean_ctor_get(v_scope_4112_, 0);
lean_inc_ref(v_s_4113_);
lean_dec_ref(v_scope_4112_);
v___y_3995_ = v_s_4113_;
goto v___jp_3994_;
}
else
{
lean_object* v_scope_4114_; lean_object* v_s_4115_; 
v_scope_4114_ = lean_ctor_get(v_cfg_3967_, 0);
lean_inc_ref(v_scope_4114_);
lean_dec_ref(v_cfg_3967_);
v_s_4115_ = lean_ctor_get(v_scope_4114_, 0);
lean_inc_ref(v_s_4115_);
lean_dec_ref(v_scope_4114_);
v___y_4083_ = v_s_4115_;
goto v___jp_4082_;
}
v___jp_3978_:
{
uint8_t v_didError_3980_; lean_object* v_numSuccesses_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3993_; 
v_didError_3980_ = lean_ctor_get_uint8(v___y_3979_, sizeof(void*)*1);
v_numSuccesses_3981_ = lean_ctor_get(v___y_3979_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___y_3979_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3983_ = v___y_3979_;
v_isShared_3984_ = v_isSharedCheck_3993_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_numSuccesses_3981_);
lean_dec(v___y_3979_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3993_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3989_; 
v___x_3985_ = lean_box(0);
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = lean_nat_add(v_numSuccesses_3981_, v___x_3986_);
lean_dec(v_numSuccesses_3981_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3987_);
v___x_3989_ = v___x_3983_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, sizeof(void*)*1, v_didError_3980_);
v___x_3989_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3985_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
}
}
v___jp_3994_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_3996_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0));
v___x_3997_ = lean_string_append(v___y_3995_, v___x_3996_);
v___x_3998_ = l_Lake_lowerHexUInt64(v_hash_3968_);
v___x_3999_ = lean_string_append(v___x_3997_, v___x_3998_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4001_ = lean_string_append(v___x_3999_, v___x_4000_);
v___x_4002_ = lean_string_append(v___x_4001_, v_path_3969_);
v___x_4003_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4004_ = lean_string_append(v___x_4002_, v___x_4003_);
v___x_4005_ = lean_string_append(v___x_4004_, v_url_3970_);
v___x_4006_ = 1;
v___x_4007_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4007_, 0, v___x_4005_);
lean_ctor_set_uint8(v___x_4007_, sizeof(void*)*1, v___x_4006_);
lean_inc_ref(v___y_3976_);
v___x_4008_ = lean_apply_2(v___y_3976_, v___x_4007_, lean_box(0));
v___x_4009_ = l_Lake_computeBinFileHash(v_path_3969_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; uint64_t v___x_4011_; uint8_t v___x_4012_; uint8_t v___x_4013_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v___x_4011_ = lean_unbox_uint64(v_a_4010_);
v___x_4012_ = lean_uint64_dec_eq(v___x_4011_, v_hash_3968_);
v___x_4013_ = lean_bool_not(v___x_4012_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; uint8_t v___x_4015_; 
lean_dec(v_a_4010_);
v___x_4014_ = lean_array_get_size(v_extraPaths_3971_);
v___x_4015_ = lean_nat_dec_eq(v___x_4014_, v___x_3972_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; 
v___x_4016_ = l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(v_path_3969_, v_extraPaths_3971_);
lean_dec_ref(v_path_3969_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_dec_ref_known(v___x_4016_, 1);
v___y_3979_ = v___y_3975_;
goto v___jp_3978_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4029_; 
lean_dec_ref(v___y_3975_);
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4029_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4029_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4021_ = lean_io_error_to_string(v_a_4017_);
v___x_4022_ = 3;
v___x_4023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4023_, 0, v___x_4021_);
lean_ctor_set_uint8(v___x_4023_, sizeof(void*)*1, v___x_4022_);
lean_inc_ref(v___y_3976_);
v___x_4024_ = lean_apply_2(v___y_3976_, v___x_4023_, lean_box(0));
v___x_4025_ = lean_box(0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4025_);
v___x_4027_ = v___x_4019_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
else
{
lean_dec_ref(v_path_3969_);
v___y_3979_ = v___y_3975_;
goto v___jp_3978_;
}
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; uint64_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; uint8_t v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4030_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_3969_);
v___x_4031_ = lean_string_append(v_path_3969_, v___x_4030_);
v___x_4032_ = lean_unbox_uint64(v_a_4010_);
lean_dec(v_a_4010_);
v___x_4033_ = l_Lake_lowerHexUInt64(v___x_4032_);
v___x_4034_ = lean_string_append(v___x_4031_, v___x_4033_);
lean_dec_ref(v___x_4033_);
v___x_4035_ = 3;
v___x_4036_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*1, v___x_4035_);
lean_inc_ref(v___y_3976_);
v___x_4037_ = lean_apply_2(v___y_3976_, v___x_4036_, lean_box(0));
v___x_4038_ = lean_io_remove_file(v_path_3969_);
lean_dec_ref(v_path_3969_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4055_; 
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; 
v_unused_4056_ = lean_ctor_get(v___x_4038_, 0);
lean_dec(v_unused_4056_);
v___x_4040_ = v___x_4038_;
v_isShared_4041_ = v_isSharedCheck_4055_;
goto v_resetjp_4039_;
}
else
{
lean_dec(v___x_4038_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4055_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v_numSuccesses_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4054_; 
v_numSuccesses_4042_ = lean_ctor_get(v___y_3975_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___y_3975_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4044_ = v___y_3975_;
v_isShared_4045_ = v_isSharedCheck_4054_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_numSuccesses_4042_);
lean_dec(v___y_3975_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4054_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4046_ = lean_box(0);
if (v_isShared_4045_ == 0)
{
v___x_4048_ = v___x_4044_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_numSuccesses_4042_);
v___x_4048_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*1, v___x_3973_);
v___x_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4046_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4049_);
v___x_4051_ = v___x_4040_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v___y_3975_);
v_a_4057_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4059_ = v___x_4038_;
v_isShared_4060_ = v_isSharedCheck_4068_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4038_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4068_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4061_ = lean_io_error_to_string(v_a_4057_);
v___x_4062_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set_uint8(v___x_4062_, sizeof(void*)*1, v___x_4035_);
lean_inc_ref(v___y_3976_);
v___x_4063_ = lean_apply_2(v___y_3976_, v___x_4062_, lean_box(0));
v___x_4064_ = lean_box(0);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4064_);
v___x_4066_ = v___x_4059_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v___y_3975_);
lean_dec_ref(v_path_3969_);
v_a_4069_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4071_ = v___x_4009_;
v_isShared_4072_ = v_isSharedCheck_4081_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4009_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4081_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4073_ = lean_io_error_to_string(v_a_4069_);
v___x_4074_ = 3;
v___x_4075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4075_, 0, v___x_4073_);
lean_ctor_set_uint8(v___x_4075_, sizeof(void*)*1, v___x_4074_);
lean_inc_ref(v___y_3976_);
v___x_4076_ = lean_apply_2(v___y_3976_, v___x_4075_, lean_box(0));
v___x_4077_ = lean_box(0);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v___x_4077_);
v___x_4079_ = v___x_4071_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
v___jp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v_didError_4097_; lean_object* v_numSuccesses_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4110_; 
v___x_4084_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1));
v___x_4085_ = lean_string_append(v___y_4083_, v___x_4084_);
v___x_4086_ = l_Lake_lowerHexUInt64(v_hash_3968_);
v___x_4087_ = lean_string_append(v___x_4085_, v___x_4086_);
lean_dec_ref(v___x_4086_);
v___x_4088_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4089_ = lean_string_append(v___x_4087_, v___x_4088_);
v___x_4090_ = lean_string_append(v___x_4089_, v_path_3969_);
lean_dec_ref(v_path_3969_);
v___x_4091_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4092_ = lean_string_append(v___x_4090_, v___x_4091_);
v___x_4093_ = lean_string_append(v___x_4092_, v_url_3970_);
v___x_4094_ = 1;
v___x_4095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*1, v___x_4094_);
lean_inc_ref(v___y_3976_);
v___x_4096_ = lean_apply_2(v___y_3976_, v___x_4095_, lean_box(0));
v_didError_4097_ = lean_ctor_get_uint8(v___y_3975_, sizeof(void*)*1);
v_numSuccesses_4098_ = lean_ctor_get(v___y_3975_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___y_3975_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4100_ = v___y_3975_;
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_numSuccesses_4098_);
lean_dec(v___y_3975_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v___x_4102_ = lean_box(0);
v___x_4103_ = lean_unsigned_to_nat(1u);
v___x_4104_ = lean_nat_add(v_numSuccesses_4098_, v___x_4103_);
lean_dec(v_numSuccesses_4098_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4104_);
v___x_4106_ = v___x_4100_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4104_);
lean_ctor_set_uint8(v_reuseFailAlloc_4109_, sizeof(void*)*1, v_didError_4097_);
v___x_4106_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4102_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object* v_cfg_4116_, lean_object* v_hash_4117_, lean_object* v_path_4118_, lean_object* v_url_4119_, lean_object* v_extraPaths_4120_, lean_object* v___x_4121_, lean_object* v___x_4122_, lean_object* v_00___4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
uint64_t v_hash_33705__boxed_4127_; uint8_t v___x_33710__boxed_4128_; lean_object* v_res_4129_; 
v_hash_33705__boxed_4127_ = lean_unbox_uint64(v_hash_4117_);
lean_dec_ref(v_hash_4117_);
v___x_33710__boxed_4128_ = lean_unbox(v___x_4122_);
v_res_4129_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4116_, v_hash_33705__boxed_4127_, v_path_4118_, v_url_4119_, v_extraPaths_4120_, v___x_4121_, v___x_33710__boxed_4128_, v_00___4123_, v___y_4124_, v___y_4125_);
lean_dec_ref(v___y_4125_);
lean_dec(v___x_4121_);
lean_dec_ref(v_extraPaths_4120_);
lean_dec_ref(v_url_4119_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object* v_a_4136_, lean_object* v_cfg_4137_, lean_object* v_h_4138_, lean_object* v_hOut_4139_, lean_object* v_s_4140_){
_start:
{
lean_object* v___y_4143_; lean_object* v___x_4155_; 
v___x_4155_ = lean_io_prim_handle_get_line(v_h_4138_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4255_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4255_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4255_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v_startInclusive_4168_; lean_object* v_endExclusive_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4164_ = lean_unsigned_to_nat(0u);
v___x_4165_ = lean_string_utf8_byte_size(v_a_4156_);
lean_inc(v_a_4156_);
v___x_4166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4166_, 0, v_a_4156_);
lean_ctor_set(v___x_4166_, 1, v___x_4164_);
lean_ctor_set(v___x_4166_, 2, v___x_4165_);
v___x_4167_ = l_String_Slice_trimAscii(v___x_4166_);
v_startInclusive_4168_ = lean_ctor_get(v___x_4167_, 1);
lean_inc(v_startInclusive_4168_);
v_endExclusive_4169_ = lean_ctor_get(v___x_4167_, 2);
lean_inc(v_endExclusive_4169_);
v___x_4170_ = lean_nat_sub(v_endExclusive_4169_, v_startInclusive_4168_);
lean_dec(v_startInclusive_4168_);
lean_dec(v_endExclusive_4169_);
v___x_4171_ = lean_nat_dec_eq(v___x_4170_, v___x_4164_);
lean_dec(v___x_4170_);
if (v___x_4171_ == 0)
{
uint8_t v___x_4172_; lean_object* v___y_4174_; lean_object* v_a_4192_; lean_object* v___x_4211_; 
lean_del_object(v___x_4158_);
v___x_4172_ = 1;
lean_inc(v_a_4156_);
v___x_4211_ = l_Lean_Json_parse(v_a_4156_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; 
lean_dec(v_a_4156_);
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4211_, 1);
v_a_4192_ = v_a_4212_;
goto v___jp_4191_;
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4214_; 
v_a_4213_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4211_, 1);
v___x_4214_ = l_Lean_Json_getObj_x3f(v_a_4213_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; 
lean_dec(v_a_4156_);
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v_a_4192_ = v_a_4215_;
goto v___jp_4191_;
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4217_; 
v_a_4216_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4217_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4137_, v_a_4216_);
if (lean_obj_tag(v___x_4217_) == 1)
{
lean_object* v_val_4218_; lean_object* v_url_4219_; uint64_t v_hash_4220_; lean_object* v_path_4221_; lean_object* v_extraPaths_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
lean_dec_ref(v___x_4167_);
v_val_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc_n(v_val_4218_, 2);
lean_dec_ref_known(v___x_4217_, 1);
v_url_4219_ = lean_ctor_get(v_val_4218_, 0);
v_hash_4220_ = lean_ctor_get_uint64(v_val_4218_, sizeof(void*)*3);
v_path_4221_ = lean_ctor_get(v_val_4218_, 1);
v_extraPaths_4222_ = lean_ctor_get(v_val_4218_, 2);
v___x_4223_ = lean_box(v___x_4172_);
lean_inc(v_a_4156_);
lean_inc(v_a_4216_);
lean_inc(v_hOut_4139_);
lean_inc_ref(v_cfg_4137_);
v___f_4224_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed), 10, 6);
lean_closure_set(v___f_4224_, 0, v_cfg_4137_);
lean_closure_set(v___f_4224_, 1, v_hOut_4139_);
lean_closure_set(v___f_4224_, 2, v_val_4218_);
lean_closure_set(v___f_4224_, 3, v_a_4216_);
lean_closure_set(v___f_4224_, 4, v_a_4156_);
lean_closure_set(v___f_4224_, 5, v___x_4223_);
v___x_4225_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4226_ = l_Lake_JsonObject_getJson_x3f(v_a_4216_, v___x_4225_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; 
lean_dec(v_val_4218_);
lean_dec(v_a_4216_);
lean_dec(v_a_4156_);
v___x_4227_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_4161_ = v___f_4224_;
v___y_4162_ = v___x_4227_;
goto v___jp_4160_;
}
else
{
lean_object* v_val_4228_; lean_object* v___x_4229_; 
v_val_4228_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_val_4228_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4229_ = l_Lean_Json_getNat_x3f(v_val_4228_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4239_; 
lean_dec(v_val_4218_);
lean_dec(v_a_4216_);
lean_dec(v_a_4156_);
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4239_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4239_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4234_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4235_ = lean_string_append(v___x_4234_, v_a_4230_);
lean_dec(v_a_4230_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4235_);
v___x_4237_ = v___x_4232_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
v___y_4161_ = v___f_4224_;
v___y_4162_ = v___x_4237_;
goto v___jp_4160_;
}
}
}
else
{
if (lean_obj_tag(v___x_4229_) == 1)
{
lean_object* v_a_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
lean_dec_ref(v___f_4224_);
v_a_4240_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4240_);
v___x_4241_ = lean_unsigned_to_nat(200u);
v___x_4242_ = lean_nat_dec_eq(v_a_4240_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; uint8_t v___x_4244_; 
v___x_4243_ = lean_unsigned_to_nat(201u);
v___x_4244_ = lean_nat_dec_eq(v_a_4240_, v___x_4243_);
lean_dec(v_a_4240_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
lean_inc_ref(v_cfg_4137_);
v___x_4245_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4137_, v_hOut_4139_, v_val_4218_, v_a_4216_, v_a_4156_, v___x_4172_, v___x_4229_, v_s_4140_, v_a_4136_);
lean_dec(v_a_4216_);
lean_dec(v_val_4218_);
v___y_4143_ = v___x_4245_;
goto v___jp_4142_;
}
else
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_inc_ref(v_extraPaths_4222_);
lean_inc_ref(v_path_4221_);
lean_inc_ref(v_url_4219_);
lean_dec_ref_known(v___x_4229_, 1);
lean_dec(v_val_4218_);
lean_dec(v_a_4216_);
lean_dec(v_a_4156_);
v___x_4246_ = lean_box(0);
lean_inc_ref(v_cfg_4137_);
v___x_4247_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4137_, v_hash_4220_, v_path_4221_, v_url_4219_, v_extraPaths_4222_, v___x_4164_, v___x_4172_, v___x_4246_, v_s_4140_, v_a_4136_);
lean_dec_ref(v_extraPaths_4222_);
lean_dec_ref(v_url_4219_);
v___y_4143_ = v___x_4247_;
goto v___jp_4142_;
}
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_inc_ref(v_extraPaths_4222_);
lean_inc_ref(v_path_4221_);
lean_inc_ref(v_url_4219_);
lean_dec_ref_known(v___x_4229_, 1);
lean_dec(v_a_4240_);
lean_dec(v_val_4218_);
lean_dec(v_a_4216_);
lean_dec(v_a_4156_);
v___x_4248_ = lean_box(0);
lean_inc_ref(v_cfg_4137_);
v___x_4249_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4137_, v_hash_4220_, v_path_4221_, v_url_4219_, v_extraPaths_4222_, v___x_4164_, v___x_4172_, v___x_4248_, v_s_4140_, v_a_4136_);
lean_dec_ref(v_extraPaths_4222_);
lean_dec_ref(v_url_4219_);
v___y_4143_ = v___x_4249_;
goto v___jp_4142_;
}
}
else
{
lean_dec(v_val_4218_);
lean_dec(v_a_4216_);
lean_dec(v_a_4156_);
v___y_4161_ = v___f_4224_;
v___y_4162_ = v___x_4229_;
goto v___jp_4160_;
}
}
}
}
else
{
lean_object* v_scope_4250_; lean_object* v_s_4251_; 
lean_dec(v___x_4217_);
lean_dec(v_a_4216_);
lean_dec(v_a_4156_);
v_scope_4250_ = lean_ctor_get(v_cfg_4137_, 0);
v_s_4251_ = lean_ctor_get(v_scope_4250_, 0);
lean_inc_ref(v_s_4251_);
v___y_4174_ = v_s_4251_;
goto v___jp_4173_;
}
}
}
v___jp_4173_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v_numSuccesses_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4190_; 
v___x_4175_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4176_ = lean_string_append(v___y_4174_, v___x_4175_);
v___x_4177_ = l_String_Slice_toString(v___x_4167_);
lean_dec_ref(v___x_4167_);
v___x_4178_ = lean_string_append(v___x_4176_, v___x_4177_);
lean_dec_ref(v___x_4177_);
v___x_4179_ = 3;
v___x_4180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4180_, 0, v___x_4178_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*1, v___x_4179_);
lean_inc_ref(v_a_4136_);
v___x_4181_ = lean_apply_2(v_a_4136_, v___x_4180_, lean_box(0));
v_numSuccesses_4182_ = lean_ctor_get(v_s_4140_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_s_4140_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4184_ = v_s_4140_;
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_numSuccesses_4182_);
lean_dec(v_s_4140_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_numSuccesses_4182_);
v___x_4187_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_ctor_set_uint8(v___x_4187_, sizeof(void*)*1, v___x_4172_);
v_s_4140_ = v___x_4187_;
goto _start;
}
}
}
v___jp_4191_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v_numSuccesses_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4210_; 
v___x_4193_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4194_ = lean_string_append(v___x_4193_, v_a_4192_);
lean_dec_ref(v_a_4192_);
v___x_4195_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4196_ = lean_string_append(v___x_4194_, v___x_4195_);
v___x_4197_ = l_String_Slice_toString(v___x_4167_);
lean_dec_ref(v___x_4167_);
v___x_4198_ = lean_string_append(v___x_4196_, v___x_4197_);
lean_dec_ref(v___x_4197_);
v___x_4199_ = 3;
v___x_4200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4200_, 0, v___x_4198_);
lean_ctor_set_uint8(v___x_4200_, sizeof(void*)*1, v___x_4199_);
lean_inc_ref(v_a_4136_);
v___x_4201_ = lean_apply_2(v_a_4136_, v___x_4200_, lean_box(0));
v_numSuccesses_4202_ = lean_ctor_get(v_s_4140_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_s_4140_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4204_ = v_s_4140_;
v_isShared_4205_ = v_isSharedCheck_4210_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_numSuccesses_4202_);
lean_dec(v_s_4140_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4210_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_numSuccesses_4202_);
v___x_4207_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_ctor_set_uint8(v___x_4207_, sizeof(void*)*1, v___x_4172_);
v_s_4140_ = v___x_4207_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4253_; 
lean_dec_ref(v___x_4167_);
lean_dec(v_a_4156_);
lean_dec(v_hOut_4139_);
lean_dec_ref(v_cfg_4137_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v_s_4140_);
v___x_4253_ = v___x_4158_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_s_4140_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
v___jp_4160_:
{
lean_object* v___x_4163_; 
lean_inc_ref(v_a_4136_);
v___x_4163_ = lean_apply_4(v___y_4161_, v___y_4162_, v_s_4140_, v_a_4136_, lean_box(0));
v___y_4143_ = v___x_4163_;
goto v___jp_4142_;
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_s_4140_);
lean_dec(v_hOut_4139_);
lean_dec_ref(v_cfg_4137_);
v_a_4256_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4258_ = v___x_4155_;
v_isShared_4259_ = v_isSharedCheck_4268_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4155_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4268_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4260_; uint8_t v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4260_ = lean_io_error_to_string(v_a_4256_);
v___x_4261_ = 3;
v___x_4262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set_uint8(v___x_4262_, sizeof(void*)*1, v___x_4261_);
lean_inc_ref(v_a_4136_);
v___x_4263_ = lean_apply_2(v_a_4136_, v___x_4262_, lean_box(0));
v___x_4264_ = lean_box(0);
if (v_isShared_4259_ == 0)
{
lean_ctor_set(v___x_4258_, 0, v___x_4264_);
v___x_4266_ = v___x_4258_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
v___jp_4142_:
{
if (lean_obj_tag(v___y_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v_snd_4145_; 
v_a_4144_ = lean_ctor_get(v___y_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___y_4143_, 1);
v_snd_4145_ = lean_ctor_get(v_a_4144_, 1);
lean_inc(v_snd_4145_);
lean_dec(v_a_4144_);
v_s_4140_ = v_snd_4145_;
goto _start;
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_hOut_4139_);
lean_dec_ref(v_cfg_4137_);
v_a_4147_ = lean_ctor_get(v___y_4143_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___y_4143_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___y_4143_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___y_4143_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object* v_a_4269_, lean_object* v_cfg_4270_, lean_object* v_h_4271_, lean_object* v_hOut_4272_, lean_object* v_s_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4269_, v_cfg_4270_, v_h_4271_, v_hOut_4272_, v_s_4273_);
lean_dec(v_h_4271_);
lean_dec_ref(v_a_4269_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object* v_cfg_4276_, lean_object* v_h_4277_, lean_object* v_hOut_4278_, lean_object* v_s_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v___y_4283_; lean_object* v___x_4295_; 
v___x_4295_ = lean_io_prim_handle_get_line(v_h_4277_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4392_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4298_ = v___x_4295_;
v_isShared_4299_ = v_isSharedCheck_4392_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4295_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4392_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_startInclusive_4304_; lean_object* v_endExclusive_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4300_ = lean_unsigned_to_nat(0u);
v___x_4301_ = lean_string_utf8_byte_size(v_a_4296_);
lean_inc(v_a_4296_);
v___x_4302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4302_, 0, v_a_4296_);
lean_ctor_set(v___x_4302_, 1, v___x_4300_);
lean_ctor_set(v___x_4302_, 2, v___x_4301_);
v___x_4303_ = l_String_Slice_trimAscii(v___x_4302_);
v_startInclusive_4304_ = lean_ctor_get(v___x_4303_, 1);
lean_inc(v_startInclusive_4304_);
v_endExclusive_4305_ = lean_ctor_get(v___x_4303_, 2);
lean_inc(v_endExclusive_4305_);
v___x_4306_ = lean_nat_sub(v_endExclusive_4305_, v_startInclusive_4304_);
lean_dec(v_startInclusive_4304_);
lean_dec(v_endExclusive_4305_);
v___x_4307_ = lean_nat_dec_eq(v___x_4306_, v___x_4300_);
lean_dec(v___x_4306_);
if (v___x_4307_ == 0)
{
uint8_t v___x_4308_; lean_object* v___y_4310_; lean_object* v_a_4328_; lean_object* v___x_4347_; 
lean_del_object(v___x_4298_);
v___x_4308_ = 1;
lean_inc(v_a_4296_);
v___x_4347_ = l_Lean_Json_parse(v_a_4296_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; 
lean_dec(v_a_4296_);
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
v_a_4328_ = v_a_4348_;
goto v___jp_4327_;
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4350_; 
v_a_4349_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4347_, 1);
v___x_4350_ = l_Lean_Json_getObj_x3f(v_a_4349_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; 
lean_dec(v_a_4296_);
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v_a_4328_ = v_a_4351_;
goto v___jp_4327_;
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4353_; 
v_a_4352_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4353_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4276_, v_a_4352_);
if (lean_obj_tag(v___x_4353_) == 1)
{
lean_object* v_val_4354_; lean_object* v_url_4355_; uint64_t v_hash_4356_; lean_object* v_path_4357_; lean_object* v_extraPaths_4358_; lean_object* v___y_4360_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
lean_dec_ref(v___x_4303_);
v_val_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_val_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v_url_4355_ = lean_ctor_get(v_val_4354_, 0);
v_hash_4356_ = lean_ctor_get_uint64(v_val_4354_, sizeof(void*)*3);
v_path_4357_ = lean_ctor_get(v_val_4354_, 1);
v_extraPaths_4358_ = lean_ctor_get(v_val_4354_, 2);
v___x_4362_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4363_ = l_Lake_JsonObject_getJson_x3f(v_a_4352_, v___x_4362_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v___x_4364_; 
v___x_4364_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_4360_ = v___x_4364_;
goto v___jp_4359_;
}
else
{
lean_object* v_val_4365_; lean_object* v___x_4366_; 
v_val_4365_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_val_4365_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4366_ = l_Lean_Json_getNat_x3f(v_val_4365_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4376_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4369_ = v___x_4366_;
v_isShared_4370_ = v_isSharedCheck_4376_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4376_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4371_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4372_ = lean_string_append(v___x_4371_, v_a_4367_);
lean_dec(v_a_4367_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4372_);
v___x_4374_ = v___x_4369_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
v___y_4360_ = v___x_4374_;
goto v___jp_4359_;
}
}
}
else
{
if (lean_obj_tag(v___x_4366_) == 1)
{
lean_object* v_a_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v_a_4377_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4377_);
v___x_4378_ = lean_unsigned_to_nat(200u);
v___x_4379_ = lean_nat_dec_eq(v_a_4377_, v___x_4378_);
if (v___x_4379_ == 0)
{
lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4380_ = lean_unsigned_to_nat(201u);
v___x_4381_ = lean_nat_dec_eq(v_a_4377_, v___x_4380_);
lean_dec(v_a_4377_);
if (v___x_4381_ == 0)
{
lean_object* v___x_4382_; 
lean_inc_ref(v_cfg_4276_);
v___x_4382_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4276_, v_hOut_4278_, v_val_4354_, v_a_4352_, v_a_4296_, v___x_4308_, v___x_4366_, v_s_4279_, v_a_4280_);
lean_dec(v_a_4352_);
lean_dec(v_val_4354_);
v___y_4283_ = v___x_4382_;
goto v___jp_4282_;
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_inc_ref(v_extraPaths_4358_);
lean_inc_ref(v_path_4357_);
lean_inc_ref(v_url_4355_);
lean_dec_ref_known(v___x_4366_, 1);
lean_dec(v_val_4354_);
lean_dec(v_a_4352_);
lean_dec(v_a_4296_);
v___x_4383_ = lean_box(0);
lean_inc_ref(v_cfg_4276_);
v___x_4384_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4276_, v_hash_4356_, v_path_4357_, v_url_4355_, v_extraPaths_4358_, v___x_4300_, v___x_4308_, v___x_4383_, v_s_4279_, v_a_4280_);
lean_dec_ref(v_extraPaths_4358_);
lean_dec_ref(v_url_4355_);
v___y_4283_ = v___x_4384_;
goto v___jp_4282_;
}
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_inc_ref(v_extraPaths_4358_);
lean_inc_ref(v_path_4357_);
lean_inc_ref(v_url_4355_);
lean_dec_ref_known(v___x_4366_, 1);
lean_dec(v_a_4377_);
lean_dec(v_val_4354_);
lean_dec(v_a_4352_);
lean_dec(v_a_4296_);
v___x_4385_ = lean_box(0);
lean_inc_ref(v_cfg_4276_);
v___x_4386_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4276_, v_hash_4356_, v_path_4357_, v_url_4355_, v_extraPaths_4358_, v___x_4300_, v___x_4308_, v___x_4385_, v_s_4279_, v_a_4280_);
lean_dec_ref(v_extraPaths_4358_);
lean_dec_ref(v_url_4355_);
v___y_4283_ = v___x_4386_;
goto v___jp_4282_;
}
}
else
{
v___y_4360_ = v___x_4366_;
goto v___jp_4359_;
}
}
}
v___jp_4359_:
{
lean_object* v___x_4361_; 
lean_inc_ref(v_cfg_4276_);
v___x_4361_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4276_, v_hOut_4278_, v_val_4354_, v_a_4352_, v_a_4296_, v___x_4308_, v___y_4360_, v_s_4279_, v_a_4280_);
lean_dec(v_a_4352_);
lean_dec(v_val_4354_);
v___y_4283_ = v___x_4361_;
goto v___jp_4282_;
}
}
else
{
lean_object* v_scope_4387_; lean_object* v_s_4388_; 
lean_dec(v___x_4353_);
lean_dec(v_a_4352_);
lean_dec(v_a_4296_);
v_scope_4387_ = lean_ctor_get(v_cfg_4276_, 0);
v_s_4388_ = lean_ctor_get(v_scope_4387_, 0);
lean_inc_ref(v_s_4388_);
v___y_4310_ = v_s_4388_;
goto v___jp_4309_;
}
}
}
v___jp_4309_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v_numSuccesses_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4326_; 
v___x_4311_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4312_ = lean_string_append(v___y_4310_, v___x_4311_);
v___x_4313_ = l_String_Slice_toString(v___x_4303_);
lean_dec_ref(v___x_4303_);
v___x_4314_ = lean_string_append(v___x_4312_, v___x_4313_);
lean_dec_ref(v___x_4313_);
v___x_4315_ = 3;
v___x_4316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set_uint8(v___x_4316_, sizeof(void*)*1, v___x_4315_);
lean_inc_ref(v_a_4280_);
v___x_4317_ = lean_apply_2(v_a_4280_, v___x_4316_, lean_box(0));
v_numSuccesses_4318_ = lean_ctor_get(v_s_4279_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_s_4279_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4320_ = v_s_4279_;
v_isShared_4321_ = v_isSharedCheck_4326_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_numSuccesses_4318_);
lean_dec(v_s_4279_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4326_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_numSuccesses_4318_);
v___x_4323_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; 
lean_ctor_set_uint8(v___x_4323_, sizeof(void*)*1, v___x_4308_);
v___x_4324_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4280_, v_cfg_4276_, v_h_4277_, v_hOut_4278_, v___x_4323_);
return v___x_4324_;
}
}
}
v___jp_4327_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v_numSuccesses_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4346_; 
v___x_4329_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4330_ = lean_string_append(v___x_4329_, v_a_4328_);
lean_dec_ref(v_a_4328_);
v___x_4331_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4332_ = lean_string_append(v___x_4330_, v___x_4331_);
v___x_4333_ = l_String_Slice_toString(v___x_4303_);
lean_dec_ref(v___x_4303_);
v___x_4334_ = lean_string_append(v___x_4332_, v___x_4333_);
lean_dec_ref(v___x_4333_);
v___x_4335_ = 3;
v___x_4336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*1, v___x_4335_);
lean_inc_ref(v_a_4280_);
v___x_4337_ = lean_apply_2(v_a_4280_, v___x_4336_, lean_box(0));
v_numSuccesses_4338_ = lean_ctor_get(v_s_4279_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_s_4279_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4340_ = v_s_4279_;
v_isShared_4341_ = v_isSharedCheck_4346_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_numSuccesses_4338_);
lean_dec(v_s_4279_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4346_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_numSuccesses_4338_);
v___x_4343_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
lean_object* v___x_4344_; 
lean_ctor_set_uint8(v___x_4343_, sizeof(void*)*1, v___x_4308_);
v___x_4344_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4280_, v_cfg_4276_, v_h_4277_, v_hOut_4278_, v___x_4343_);
return v___x_4344_;
}
}
}
}
else
{
lean_object* v___x_4390_; 
lean_dec_ref(v___x_4303_);
lean_dec(v_a_4296_);
lean_dec(v_hOut_4278_);
lean_dec_ref(v_cfg_4276_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 0, v_s_4279_);
v___x_4390_ = v___x_4298_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_s_4279_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4405_; 
lean_dec_ref(v_s_4279_);
lean_dec(v_hOut_4278_);
lean_dec_ref(v_cfg_4276_);
v_a_4393_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4395_ = v___x_4295_;
v_isShared_4396_ = v_isSharedCheck_4405_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4295_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4405_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4397_ = lean_io_error_to_string(v_a_4393_);
v___x_4398_ = 3;
v___x_4399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set_uint8(v___x_4399_, sizeof(void*)*1, v___x_4398_);
lean_inc_ref(v_a_4280_);
v___x_4400_ = lean_apply_2(v_a_4280_, v___x_4399_, lean_box(0));
v___x_4401_ = lean_box(0);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4401_);
v___x_4403_ = v___x_4395_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
v___jp_4282_:
{
if (lean_obj_tag(v___y_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v_snd_4285_; lean_object* v___x_4286_; 
v_a_4284_ = lean_ctor_get(v___y_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___y_4283_, 1);
v_snd_4285_ = lean_ctor_get(v_a_4284_, 1);
lean_inc(v_snd_4285_);
lean_dec(v_a_4284_);
v___x_4286_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4280_, v_cfg_4276_, v_h_4277_, v_hOut_4278_, v_snd_4285_);
return v___x_4286_;
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v_hOut_4278_);
lean_dec_ref(v_cfg_4276_);
v_a_4287_ = lean_ctor_get(v___y_4283_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___y_4283_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___y_4283_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___y_4283_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object* v_cfg_4406_, lean_object* v_h_4407_, lean_object* v_hOut_4408_, lean_object* v_s_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4406_, v_h_4407_, v_hOut_4408_, v_s_4409_, v_a_4410_);
lean_dec_ref(v_a_4410_);
lean_dec(v_h_4407_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object* v_snd_4413_, lean_object* v___y_4414_, lean_object* v_a_x3f_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_io_remove_file(v_snd_4413_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4417_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4438_; 
v_a_4426_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4428_ = v___x_4417_;
v_isShared_4429_ = v_isSharedCheck_4438_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4417_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4438_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; uint8_t v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v___x_4430_ = lean_io_error_to_string(v_a_4426_);
v___x_4431_ = 3;
v___x_4432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4432_, 0, v___x_4430_);
lean_ctor_set_uint8(v___x_4432_, sizeof(void*)*1, v___x_4431_);
lean_inc_ref(v___y_4414_);
v___x_4433_ = lean_apply_2(v___y_4414_, v___x_4432_, lean_box(0));
v___x_4434_ = lean_box(0);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4434_);
v___x_4436_ = v___x_4428_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object* v_snd_4439_, lean_object* v___y_4440_, lean_object* v_a_x3f_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4439_, v___y_4440_, v_a_x3f_4441_);
lean_dec(v_a_x3f_4441_);
lean_dec_ref(v___y_4440_);
lean_dec_ref(v_snd_4439_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object* v_f_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v_fst_4449_; lean_object* v_snd_4450_; lean_object* v_r_4451_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
v_fst_4449_ = lean_ctor_get(v_a_4448_, 0);
lean_inc(v_fst_4449_);
v_snd_4450_ = lean_ctor_get(v_a_4448_, 1);
lean_inc_n(v_snd_4450_, 2);
lean_dec(v_a_4448_);
lean_inc_ref(v___y_4445_);
v_r_4451_ = lean_apply_4(v_f_4444_, v_fst_4449_, v_snd_4450_, v___y_4445_, lean_box(0));
if (lean_obj_tag(v_r_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4476_; 
v_a_4452_ = lean_ctor_get(v_r_4451_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_r_4451_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4454_ = v_r_4451_;
v_isShared_4455_ = v_isSharedCheck_4476_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v_r_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4476_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
lean_inc(v_a_4452_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set_tag(v___x_4454_, 1);
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4450_, v___y_4445_, v___x_4457_);
lean_dec_ref(v___x_4457_);
lean_dec(v_snd_4450_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4465_ == 0)
{
lean_object* v_unused_4466_; 
v_unused_4466_ = lean_ctor_get(v___x_4458_, 0);
lean_dec(v_unused_4466_);
v___x_4460_ = v___x_4458_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_dec(v___x_4458_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v_a_4452_);
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4452_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec(v_a_4452_);
v_a_4467_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4458_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4458_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v_a_4477_ = lean_ctor_get(v_r_4451_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v_r_4451_, 1);
v___x_4478_ = lean_box(0);
v___x_4479_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4450_, v___y_4445_, v___x_4478_);
lean_dec(v_snd_4450_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4486_ == 0)
{
lean_object* v_unused_4487_; 
v_unused_4487_ = lean_ctor_get(v___x_4479_, 0);
lean_dec(v_unused_4487_);
v___x_4481_ = v___x_4479_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_dec(v___x_4479_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set_tag(v___x_4481_, 1);
lean_ctor_set(v___x_4481_, 0, v_a_4477_);
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4477_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_a_4477_);
v_a_4488_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4479_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4479_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v_f_4444_);
v_a_4496_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4498_ = v___x_4447_;
v_isShared_4499_ = v_isSharedCheck_4508_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4447_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4508_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4500_; uint8_t v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4500_ = lean_io_error_to_string(v_a_4496_);
v___x_4501_ = 3;
v___x_4502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set_uint8(v___x_4502_, sizeof(void*)*1, v___x_4501_);
lean_inc_ref(v___y_4445_);
v___x_4503_ = lean_apply_2(v___y_4445_, v___x_4502_, lean_box(0));
v___x_4504_ = lean_box(0);
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 0, v___x_4504_);
v___x_4506_ = v___x_4498_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object* v_f_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4509_, v___y_4510_);
lean_dec_ref(v___y_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object* v_00_u03b1_4513_, lean_object* v_f_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4514_, v___y_4515_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object* v_00_u03b1_4518_, lean_object* v_f_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(v_00_u03b1_4518_, v_f_4519_, v___y_4520_);
lean_dec_ref(v___y_4520_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object* v_h_4525_, lean_object* v_as_4526_, size_t v_i_4527_, size_t v_stop_4528_, lean_object* v_b_4529_, lean_object* v___y_4530_){
_start:
{
uint8_t v___x_4532_; 
v___x_4532_ = lean_usize_dec_eq(v_i_4527_, v_stop_4528_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; lean_object* v_url_4534_; lean_object* v_path_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4533_ = lean_array_uget_borrowed(v_as_4526_, v_i_4527_);
v_url_4534_ = lean_ctor_get(v___x_4533_, 0);
v_path_4535_ = lean_ctor_get(v___x_4533_, 1);
v___x_4536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4534_);
v___x_4537_ = l_String_quote(v_url_4534_);
v___x_4538_ = lean_string_append(v___x_4536_, v___x_4537_);
lean_dec_ref(v___x_4537_);
v___x_4539_ = l_IO_FS_Handle_putStrLn(v_h_4525_, v___x_4538_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec_ref_known(v___x_4539_, 1);
v___x_4540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1));
lean_inc_ref(v_path_4535_);
v___x_4541_ = l_String_quote(v_path_4535_);
v___x_4542_ = lean_string_append(v___x_4540_, v___x_4541_);
lean_dec_ref(v___x_4541_);
v___x_4543_ = l_IO_FS_Handle_putStrLn(v_h_4525_, v___x_4542_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; size_t v___x_4545_; size_t v___x_4546_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc(v_a_4544_);
lean_dec_ref_known(v___x_4543_, 1);
v___x_4545_ = ((size_t)1ULL);
v___x_4546_ = lean_usize_add(v_i_4527_, v___x_4545_);
v_i_4527_ = v___x_4546_;
v_b_4529_ = v_a_4544_;
goto _start;
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4560_; 
v_a_4548_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4550_ = v___x_4543_;
v_isShared_4551_ = v_isSharedCheck_4560_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4543_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4560_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4552_ = lean_io_error_to_string(v_a_4548_);
v___x_4553_ = 3;
v___x_4554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set_uint8(v___x_4554_, sizeof(void*)*1, v___x_4553_);
lean_inc_ref(v___y_4530_);
v___x_4555_ = lean_apply_2(v___y_4530_, v___x_4554_, lean_box(0));
v___x_4556_ = lean_box(0);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4556_);
v___x_4558_ = v___x_4550_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4573_; 
v_a_4561_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4563_ = v___x_4539_;
v_isShared_4564_ = v_isSharedCheck_4573_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4539_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4573_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; uint8_t v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4571_; 
v___x_4565_ = lean_io_error_to_string(v_a_4561_);
v___x_4566_ = 3;
v___x_4567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set_uint8(v___x_4567_, sizeof(void*)*1, v___x_4566_);
lean_inc_ref(v___y_4530_);
v___x_4568_ = lean_apply_2(v___y_4530_, v___x_4567_, lean_box(0));
v___x_4569_ = lean_box(0);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4569_);
v___x_4571_ = v___x_4563_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
else
{
lean_object* v___x_4574_; 
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v_b_4529_);
return v___x_4574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object* v_h_4575_, lean_object* v_as_4576_, lean_object* v_i_4577_, lean_object* v_stop_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
size_t v_i_boxed_4582_; size_t v_stop_boxed_4583_; lean_object* v_res_4584_; 
v_i_boxed_4582_ = lean_unbox_usize(v_i_4577_);
lean_dec(v_i_4577_);
v_stop_boxed_4583_ = lean_unbox_usize(v_stop_4578_);
lean_dec(v_stop_4578_);
v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4575_, v_as_4576_, v_i_boxed_4582_, v_stop_boxed_4583_, v_b_4579_, v___y_4580_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v_as_4576_);
lean_dec(v_h_4575_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object* v_h_4586_, lean_object* v_as_4587_, size_t v_i_4588_, size_t v_stop_4589_, lean_object* v_b_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v___x_4593_; 
v___x_4593_ = lean_usize_dec_eq(v_i_4588_, v_stop_4589_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; lean_object* v_url_4595_; lean_object* v_path_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4594_ = lean_array_uget_borrowed(v_as_4587_, v_i_4588_);
v_url_4595_ = lean_ctor_get(v___x_4594_, 0);
v_path_4596_ = lean_ctor_get(v___x_4594_, 1);
v___x_4597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0));
lean_inc_ref(v_path_4596_);
v___x_4598_ = l_String_quote(v_path_4596_);
v___x_4599_ = lean_string_append(v___x_4597_, v___x_4598_);
lean_dec_ref(v___x_4598_);
v___x_4600_ = l_IO_FS_Handle_putStrLn(v_h_4586_, v___x_4599_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
lean_dec_ref_known(v___x_4600_, 1);
v___x_4601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4595_);
v___x_4602_ = l_String_quote(v_url_4595_);
v___x_4603_ = lean_string_append(v___x_4601_, v___x_4602_);
lean_dec_ref(v___x_4602_);
v___x_4604_ = l_IO_FS_Handle_putStrLn(v_h_4586_, v___x_4603_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; size_t v___x_4606_; size_t v___x_4607_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref_known(v___x_4604_, 1);
v___x_4606_ = ((size_t)1ULL);
v___x_4607_ = lean_usize_add(v_i_4588_, v___x_4606_);
v_i_4588_ = v___x_4607_;
v_b_4590_ = v_a_4605_;
goto _start;
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4621_; 
v_a_4609_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4611_ = v___x_4604_;
v_isShared_4612_ = v_isSharedCheck_4621_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4604_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4621_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; uint8_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4613_ = lean_io_error_to_string(v_a_4609_);
v___x_4614_ = 3;
v___x_4615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
lean_ctor_set_uint8(v___x_4615_, sizeof(void*)*1, v___x_4614_);
lean_inc_ref(v___y_4591_);
v___x_4616_ = lean_apply_2(v___y_4591_, v___x_4615_, lean_box(0));
v___x_4617_ = lean_box(0);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4617_);
v___x_4619_ = v___x_4611_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4634_; 
v_a_4622_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4624_ = v___x_4600_;
v_isShared_4625_ = v_isSharedCheck_4634_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4600_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4634_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; uint8_t v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4626_ = lean_io_error_to_string(v_a_4622_);
v___x_4627_ = 3;
v___x_4628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4628_, 0, v___x_4626_);
lean_ctor_set_uint8(v___x_4628_, sizeof(void*)*1, v___x_4627_);
lean_inc_ref(v___y_4591_);
v___x_4629_ = lean_apply_2(v___y_4591_, v___x_4628_, lean_box(0));
v___x_4630_ = lean_box(0);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4630_);
v___x_4632_ = v___x_4624_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
else
{
lean_object* v___x_4635_; 
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v_b_4590_);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object* v_h_4636_, lean_object* v_as_4637_, lean_object* v_i_4638_, lean_object* v_stop_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
size_t v_i_boxed_4643_; size_t v_stop_boxed_4644_; lean_object* v_res_4645_; 
v_i_boxed_4643_ = lean_unbox_usize(v_i_4638_);
lean_dec(v_i_4638_);
v_stop_boxed_4644_ = lean_unbox_usize(v_stop_4639_);
lean_dec(v_stop_4639_);
v_res_4645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4636_, v_as_4637_, v_i_boxed_4643_, v_stop_boxed_4644_, v_b_4640_, v___y_4641_);
lean_dec_ref(v___y_4641_);
lean_dec_ref(v_as_4637_);
lean_dec(v_h_4636_);
return v_res_4645_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4662_ = lean_unsigned_to_nat(11u);
v___x_4663_ = lean_mk_empty_array_with_capacity(v___x_4662_);
v___x_4664_ = lean_array_push(v___x_4663_, v___x_4661_);
return v___x_4664_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4666_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11);
v___x_4667_ = lean_array_push(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4668_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6));
v___x_4669_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12);
v___x_4670_ = lean_array_push(v___x_4669_, v___x_4668_);
return v___x_4670_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4672_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13);
v___x_4673_ = lean_array_push(v___x_4672_, v___x_4671_);
return v___x_4673_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4675_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14);
v___x_4676_ = lean_array_push(v___x_4675_, v___x_4674_);
return v___x_4676_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4678_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15);
v___x_4679_ = lean_array_push(v___x_4678_, v___x_4677_);
return v___x_4679_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4680_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4681_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16);
v___x_4682_ = lean_array_push(v___x_4681_, v___x_4680_);
return v___x_4682_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18(void){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4683_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4684_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17);
v___x_4685_ = lean_array_push(v___x_4684_, v___x_4683_);
return v___x_4685_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4687_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18);
v___x_4688_ = lean_array_push(v___x_4687_, v___x_4686_);
return v___x_4688_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4689_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4690_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19);
v___x_4691_ = lean_array_push(v___x_4690_, v___x_4689_);
return v___x_4691_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4693_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4694_ = lean_unsigned_to_nat(17u);
v___x_4695_ = lean_mk_empty_array_with_capacity(v___x_4694_);
v___x_4696_ = lean_array_push(v___x_4695_, v___x_4693_);
return v___x_4696_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23(void){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4697_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4698_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22);
v___x_4699_ = lean_array_push(v___x_4698_, v___x_4697_);
return v___x_4699_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24(void){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4700_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_4701_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23);
v___x_4702_ = lean_array_push(v___x_4701_, v___x_4700_);
return v___x_4702_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4703_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4704_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24);
v___x_4705_ = lean_array_push(v___x_4704_, v___x_4703_);
return v___x_4705_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_4707_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25);
v___x_4708_ = lean_array_push(v___x_4707_, v___x_4706_);
return v___x_4708_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27(void){
_start:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4709_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21));
v___x_4710_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26);
v___x_4711_ = lean_array_push(v___x_4710_, v___x_4709_);
return v___x_4711_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28(void){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4712_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4713_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27);
v___x_4714_ = lean_array_push(v___x_4713_, v___x_4712_);
return v___x_4714_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29(void){
_start:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4716_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28);
v___x_4717_ = lean_array_push(v___x_4716_, v___x_4715_);
return v___x_4717_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30(void){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4718_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_4719_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29);
v___x_4720_ = lean_array_push(v___x_4719_, v___x_4718_);
return v___x_4720_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4721_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_4722_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30);
v___x_4723_ = lean_array_push(v___x_4722_, v___x_4721_);
return v___x_4723_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4724_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_4725_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31);
v___x_4726_ = lean_array_push(v___x_4725_, v___x_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object* v_cfg_4727_, lean_object* v_h_4728_, lean_object* v_path_4729_, lean_object* v___y_4730_){
_start:
{
uint8_t v___y_4733_; uint32_t v___y_4739_; lean_object* v___y_4740_; uint8_t v___y_4741_; lean_object* v___y_4742_; uint8_t v_kind_4751_; lean_object* v_scope_4752_; lean_object* v_infos_4753_; lean_object* v_key_4754_; uint32_t v___y_4756_; uint8_t v___y_4757_; lean_object* v___y_4758_; uint32_t v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; uint8_t v___y_4769_; lean_object* v___y_4770_; uint32_t v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; uint8_t v___y_4785_; lean_object* v___y_4786_; uint32_t v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4794_; uint8_t v___y_4795_; lean_object* v___y_4796_; uint32_t v___y_4806_; lean_object* v___y_4807_; lean_object* v___y_4808_; uint8_t v___y_4809_; lean_object* v___y_4810_; lean_object* v_a_4813_; lean_object* v___y_4907_; lean_object* v___y_4935_; 
v_kind_4751_ = lean_ctor_get_uint8(v_cfg_4727_, sizeof(void*)*3);
v_scope_4752_ = lean_ctor_get(v_cfg_4727_, 0);
lean_inc_ref(v_scope_4752_);
v_infos_4753_ = lean_ctor_get(v_cfg_4727_, 1);
lean_inc_ref(v_infos_4753_);
v_key_4754_ = lean_ctor_get(v_cfg_4727_, 2);
if (v_kind_4751_ == 0)
{
lean_object* v___x_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4936_ = lean_unsigned_to_nat(0u);
v___x_4937_ = lean_array_get_size(v_infos_4753_);
v___x_4938_ = lean_nat_dec_lt(v___x_4936_, v___x_4937_);
if (v___x_4938_ == 0)
{
goto v___jp_4889_;
}
else
{
lean_object* v___x_4939_; uint8_t v___x_4940_; 
v___x_4939_ = lean_box(0);
v___x_4940_ = lean_nat_dec_le(v___x_4937_, v___x_4937_);
if (v___x_4940_ == 0)
{
if (v___x_4938_ == 0)
{
goto v___jp_4889_;
}
else
{
size_t v___x_4941_; size_t v___x_4942_; lean_object* v___x_4943_; 
v___x_4941_ = ((size_t)0ULL);
v___x_4942_ = lean_usize_of_nat(v___x_4937_);
v___x_4943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4728_, v_infos_4753_, v___x_4941_, v___x_4942_, v___x_4939_, v___y_4730_);
v___y_4907_ = v___x_4943_;
goto v___jp_4906_;
}
}
else
{
size_t v___x_4944_; size_t v___x_4945_; lean_object* v___x_4946_; 
v___x_4944_ = ((size_t)0ULL);
v___x_4945_ = lean_usize_of_nat(v___x_4937_);
v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4728_, v_infos_4753_, v___x_4944_, v___x_4945_, v___x_4939_, v___y_4730_);
v___y_4907_ = v___x_4946_;
goto v___jp_4906_;
}
}
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4947_ = lean_unsigned_to_nat(0u);
v___x_4948_ = lean_array_get_size(v_infos_4753_);
v___x_4949_ = lean_nat_dec_lt(v___x_4947_, v___x_4948_);
if (v___x_4949_ == 0)
{
goto v___jp_4908_;
}
else
{
lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4950_ = lean_box(0);
v___x_4951_ = lean_nat_dec_le(v___x_4948_, v___x_4948_);
if (v___x_4951_ == 0)
{
if (v___x_4949_ == 0)
{
goto v___jp_4908_;
}
else
{
size_t v___x_4952_; size_t v___x_4953_; lean_object* v___x_4954_; 
v___x_4952_ = ((size_t)0ULL);
v___x_4953_ = lean_usize_of_nat(v___x_4948_);
v___x_4954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4728_, v_infos_4753_, v___x_4952_, v___x_4953_, v___x_4950_, v___y_4730_);
v___y_4935_ = v___x_4954_;
goto v___jp_4934_;
}
}
else
{
size_t v___x_4955_; size_t v___x_4956_; lean_object* v___x_4957_; 
v___x_4955_ = ((size_t)0ULL);
v___x_4956_ = lean_usize_of_nat(v___x_4948_);
v___x_4957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4728_, v_infos_4753_, v___x_4955_, v___x_4956_, v___x_4950_, v___y_4730_);
v___y_4935_ = v___x_4957_;
goto v___jp_4934_;
}
}
}
v___jp_4732_:
{
if (v___y_4733_ == 0)
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = lean_box(0);
v___x_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
return v___x_4735_;
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
return v___x_4737_;
}
}
v___jp_4738_:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4743_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_4744_ = lean_string_append(v___y_4742_, v___x_4743_);
v___x_4745_ = lean_uint32_to_nat(v___y_4739_);
v___x_4746_ = l_Nat_reprFast(v___x_4745_);
v___x_4747_ = lean_string_append(v___x_4744_, v___x_4746_);
lean_dec_ref(v___x_4746_);
v___x_4748_ = 3;
v___x_4749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4749_, 0, v___x_4747_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1, v___x_4748_);
lean_inc_ref(v___y_4740_);
v___x_4750_ = lean_apply_2(v___y_4740_, v___x_4749_, lean_box(0));
v___y_4733_ = v___y_4741_;
goto v___jp_4732_;
}
v___jp_4755_:
{
uint32_t v___x_4759_; uint8_t v___x_4760_; uint8_t v___x_4761_; 
v___x_4759_ = 0;
v___x_4760_ = lean_uint32_dec_eq(v___y_4756_, v___x_4759_);
v___x_4761_ = lean_bool_not(v___x_4760_);
if (v___x_4761_ == 0)
{
lean_dec_ref(v_scope_4752_);
v___y_4733_ = v___y_4757_;
goto v___jp_4732_;
}
else
{
lean_object* v_s_4762_; 
v_s_4762_ = lean_ctor_get(v_scope_4752_, 0);
lean_inc_ref(v_s_4762_);
lean_dec_ref(v_scope_4752_);
v___y_4739_ = v___y_4756_;
v___y_4740_ = v___y_4758_;
v___y_4741_ = v___y_4757_;
v___y_4742_ = v_s_4762_;
goto v___jp_4738_;
}
}
v___jp_4763_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; uint8_t v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4771_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_4772_ = lean_string_append(v___y_4770_, v___x_4771_);
lean_inc(v___y_4766_);
lean_inc(v___y_4767_);
lean_inc_ref(v___y_4768_);
v___x_4773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4773_, 0, v___y_4768_);
lean_ctor_set(v___x_4773_, 1, v___y_4767_);
lean_ctor_set(v___x_4773_, 2, v___y_4766_);
v___x_4774_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_4773_, v___y_4766_);
lean_dec_ref_known(v___x_4773_, 3);
v___x_4775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4775_, 0, v___y_4768_);
lean_ctor_set(v___x_4775_, 1, v___y_4767_);
lean_ctor_set(v___x_4775_, 2, v___x_4774_);
v___x_4776_ = l_String_Slice_toString(v___x_4775_);
lean_dec_ref_known(v___x_4775_, 3);
v___x_4777_ = lean_string_append(v___x_4772_, v___x_4776_);
lean_dec_ref(v___x_4776_);
v___x_4778_ = 2;
v___x_4779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4779_, 0, v___x_4777_);
lean_ctor_set_uint8(v___x_4779_, sizeof(void*)*1, v___x_4778_);
lean_inc_ref(v___y_4765_);
v___x_4780_ = lean_apply_2(v___y_4765_, v___x_4779_, lean_box(0));
v___y_4756_ = v___y_4764_;
v___y_4757_ = v___y_4769_;
v___y_4758_ = v___y_4765_;
goto v___jp_4755_;
}
v___jp_4781_:
{
lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4787_ = lean_string_utf8_byte_size(v___y_4784_);
v___x_4788_ = lean_nat_dec_eq(v___x_4787_, v___y_4783_);
if (v___x_4788_ == 0)
{
lean_object* v_s_4789_; 
v_s_4789_ = lean_ctor_get(v_scope_4752_, 0);
lean_inc_ref(v_s_4789_);
v___y_4764_ = v___y_4782_;
v___y_4765_ = v___y_4786_;
v___y_4766_ = v___x_4787_;
v___y_4767_ = v___y_4783_;
v___y_4768_ = v___y_4784_;
v___y_4769_ = v___y_4785_;
v___y_4770_ = v_s_4789_;
goto v___jp_4763_;
}
else
{
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
v___y_4756_ = v___y_4782_;
v___y_4757_ = v___y_4785_;
v___y_4758_ = v___y_4786_;
goto v___jp_4755_;
}
}
v___jp_4790_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4797_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_4798_ = lean_string_append(v___y_4796_, v___x_4797_);
v___x_4799_ = lean_string_append(v___x_4798_, v___y_4792_);
v___x_4800_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_4801_ = lean_string_append(v___x_4799_, v___x_4800_);
v___x_4802_ = 3;
v___x_4803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4803_, 0, v___x_4801_);
lean_ctor_set_uint8(v___x_4803_, sizeof(void*)*1, v___x_4802_);
lean_inc_ref(v___y_4730_);
v___x_4804_ = lean_apply_2(v___y_4730_, v___x_4803_, lean_box(0));
v___y_4782_ = v___y_4791_;
v___y_4783_ = v___y_4793_;
v___y_4784_ = v___y_4794_;
v___y_4785_ = v___y_4795_;
v___y_4786_ = v___y_4730_;
goto v___jp_4781_;
}
v___jp_4805_:
{
lean_object* v_s_4811_; 
v_s_4811_ = lean_ctor_get(v_scope_4752_, 0);
lean_inc_ref(v_s_4811_);
v___y_4791_ = v___y_4806_;
v___y_4792_ = v___y_4810_;
v___y_4793_ = v___y_4807_;
v___y_4794_ = v___y_4808_;
v___y_4795_ = v___y_4809_;
v___y_4796_ = v_s_4811_;
goto v___jp_4790_;
}
v___jp_4812_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; uint8_t v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4814_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_4815_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_4816_ = lean_box(0);
v___x_4817_ = lean_unsigned_to_nat(0u);
v___x_4818_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_4819_ = 1;
v___x_4820_ = 0;
v___x_4821_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4821_, 0, v___x_4814_);
lean_ctor_set(v___x_4821_, 1, v___x_4815_);
lean_ctor_set(v___x_4821_, 2, v_a_4813_);
lean_ctor_set(v___x_4821_, 3, v___x_4816_);
lean_ctor_set(v___x_4821_, 4, v___x_4818_);
lean_ctor_set_uint8(v___x_4821_, sizeof(void*)*5, v___x_4819_);
lean_ctor_set_uint8(v___x_4821_, sizeof(void*)*5 + 1, v___x_4820_);
v___x_4822_ = lean_io_process_spawn(v___x_4821_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v_stdout_4824_; lean_object* v_stderr_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v_stdout_4824_ = lean_ctor_get(v_a_4823_, 1);
lean_inc_n(v_stdout_4824_, 2);
v_stderr_4825_ = lean_ctor_get(v_a_4823_, 2);
v___x_4826_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_4827_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4727_, v_stderr_4825_, v_stdout_4824_, v___x_4826_, v___y_4730_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4829_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
v___x_4829_ = lean_io_process_child_wait(v___x_4814_, v_a_4823_);
lean_dec(v_a_4823_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref_known(v___x_4829_, 1);
v___x_4831_ = l_IO_FS_Handle_readToEnd(v_stdout_4824_);
lean_dec(v_stdout_4824_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; uint8_t v_didError_4833_; lean_object* v_numSuccesses_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref_known(v___x_4831_, 1);
v_didError_4833_ = lean_ctor_get_uint8(v_a_4828_, sizeof(void*)*1);
v_numSuccesses_4834_ = lean_ctor_get(v_a_4828_, 0);
lean_inc(v_numSuccesses_4834_);
lean_dec(v_a_4828_);
v___x_4835_ = lean_array_get_size(v_infos_4753_);
lean_dec_ref(v_infos_4753_);
v___x_4836_ = lean_nat_dec_lt(v_numSuccesses_4834_, v___x_4835_);
lean_dec(v_numSuccesses_4834_);
if (v___x_4836_ == 0)
{
uint32_t v___x_4837_; 
v___x_4837_ = lean_unbox_uint32(v_a_4830_);
lean_dec(v_a_4830_);
v___y_4782_ = v___x_4837_;
v___y_4783_ = v___x_4817_;
v___y_4784_ = v_a_4832_;
v___y_4785_ = v_didError_4833_;
v___y_4786_ = v___y_4730_;
goto v___jp_4781_;
}
else
{
if (v_kind_4751_ == 0)
{
lean_object* v___x_4838_; uint32_t v___x_4839_; 
v___x_4838_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_4839_ = lean_unbox_uint32(v_a_4830_);
lean_dec(v_a_4830_);
v___y_4806_ = v___x_4839_;
v___y_4807_ = v___x_4817_;
v___y_4808_ = v_a_4832_;
v___y_4809_ = v_didError_4833_;
v___y_4810_ = v___x_4838_;
goto v___jp_4805_;
}
else
{
lean_object* v___x_4840_; uint32_t v___x_4841_; 
v___x_4840_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_4841_ = lean_unbox_uint32(v_a_4830_);
lean_dec(v_a_4830_);
v___y_4806_ = v___x_4841_;
v___y_4807_ = v___x_4817_;
v___y_4808_ = v_a_4832_;
v___y_4809_ = v_didError_4833_;
v___y_4810_ = v___x_4840_;
goto v___jp_4805_;
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4854_; 
lean_dec(v_a_4830_);
lean_dec(v_a_4828_);
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
v_a_4842_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4844_ = v___x_4831_;
v_isShared_4845_ = v_isSharedCheck_4854_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4831_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4854_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4846_; uint8_t v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4846_ = lean_io_error_to_string(v_a_4842_);
v___x_4847_ = 3;
v___x_4848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set_uint8(v___x_4848_, sizeof(void*)*1, v___x_4847_);
lean_inc_ref(v___y_4730_);
v___x_4849_ = lean_apply_2(v___y_4730_, v___x_4848_, lean_box(0));
v___x_4850_ = lean_box(0);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 0, v___x_4850_);
v___x_4852_ = v___x_4844_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4867_; 
lean_dec(v_a_4828_);
lean_dec(v_stdout_4824_);
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
v_a_4855_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4857_ = v___x_4829_;
v_isShared_4858_ = v_isSharedCheck_4867_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4829_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4867_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; uint8_t v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4859_ = lean_io_error_to_string(v_a_4855_);
v___x_4860_ = 3;
v___x_4861_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4861_, 0, v___x_4859_);
lean_ctor_set_uint8(v___x_4861_, sizeof(void*)*1, v___x_4860_);
lean_inc_ref(v___y_4730_);
v___x_4862_ = lean_apply_2(v___y_4730_, v___x_4861_, lean_box(0));
v___x_4863_ = lean_box(0);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4863_);
v___x_4865_ = v___x_4857_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec(v_stdout_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
v_a_4868_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4827_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4827_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4888_; 
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
lean_dec_ref(v_cfg_4727_);
v_a_4876_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4878_ = v___x_4822_;
v_isShared_4879_ = v_isSharedCheck_4888_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4822_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4888_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; uint8_t v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4880_ = lean_io_error_to_string(v_a_4876_);
v___x_4881_ = 3;
v___x_4882_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4882_, 0, v___x_4880_);
lean_ctor_set_uint8(v___x_4882_, sizeof(void*)*1, v___x_4881_);
lean_inc_ref(v___y_4730_);
v___x_4883_ = lean_apply_2(v___y_4730_, v___x_4882_, lean_box(0));
v___x_4884_ = lean_box(0);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4884_);
v___x_4886_ = v___x_4878_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
v___jp_4889_:
{
lean_object* v___x_4890_; 
v___x_4890_ = lean_io_prim_handle_flush(v_h_4728_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
lean_dec_ref_known(v___x_4890_, 1);
v___x_4891_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_4892_ = lean_array_push(v___x_4891_, v_path_4729_);
v_a_4813_ = v___x_4892_;
goto v___jp_4812_;
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4905_; 
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
lean_dec_ref(v_path_4729_);
lean_dec_ref(v_cfg_4727_);
v_a_4893_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4895_ = v___x_4890_;
v_isShared_4896_ = v_isSharedCheck_4905_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4890_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4905_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4897_; uint8_t v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4903_; 
v___x_4897_ = lean_io_error_to_string(v_a_4893_);
v___x_4898_ = 3;
v___x_4899_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4899_, 0, v___x_4897_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*1, v___x_4898_);
lean_inc_ref(v___y_4730_);
v___x_4900_ = lean_apply_2(v___y_4730_, v___x_4899_, lean_box(0));
v___x_4901_ = lean_box(0);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 0, v___x_4901_);
v___x_4903_ = v___x_4895_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
v___jp_4906_:
{
if (lean_obj_tag(v___y_4907_) == 0)
{
lean_dec_ref_known(v___y_4907_, 1);
goto v___jp_4889_;
}
else
{
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
lean_dec_ref(v_path_4729_);
lean_dec_ref(v_cfg_4727_);
return v___y_4907_;
}
}
v___jp_4908_:
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_io_prim_handle_flush(v_h_4728_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_dec_ref_known(v___x_4909_, 1);
v___x_4910_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4911_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4912_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4913_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4914_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_4754_);
v___x_4915_ = lean_array_push(v___x_4914_, v_key_4754_);
v___x_4916_ = lean_array_push(v___x_4915_, v___x_4910_);
v___x_4917_ = lean_array_push(v___x_4916_, v___x_4911_);
v___x_4918_ = lean_array_push(v___x_4917_, v___x_4912_);
v___x_4919_ = lean_array_push(v___x_4918_, v___x_4913_);
v___x_4920_ = lean_array_push(v___x_4919_, v_path_4729_);
v_a_4813_ = v___x_4920_;
goto v___jp_4812_;
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4933_; 
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
lean_dec_ref(v_path_4729_);
lean_dec_ref(v_cfg_4727_);
v_a_4921_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4923_ = v___x_4909_;
v_isShared_4924_ = v_isSharedCheck_4933_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4909_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4933_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; uint8_t v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4925_ = lean_io_error_to_string(v_a_4921_);
v___x_4926_ = 3;
v___x_4927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set_uint8(v___x_4927_, sizeof(void*)*1, v___x_4926_);
lean_inc_ref(v___y_4730_);
v___x_4928_ = lean_apply_2(v___y_4730_, v___x_4927_, lean_box(0));
v___x_4929_ = lean_box(0);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4929_);
v___x_4931_ = v___x_4923_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4929_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
v___jp_4934_:
{
if (lean_obj_tag(v___y_4935_) == 0)
{
lean_dec_ref_known(v___y_4935_, 1);
goto v___jp_4908_;
}
else
{
lean_dec_ref(v_infos_4753_);
lean_dec_ref(v_scope_4752_);
lean_dec_ref(v_path_4729_);
lean_dec_ref(v_cfg_4727_);
return v___y_4935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object* v_cfg_4958_, lean_object* v_h_4959_, lean_object* v_path_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(v_cfg_4958_, v_h_4959_, v_path_4960_, v___y_4961_);
lean_dec_ref(v___y_4961_);
lean_dec(v_h_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object* v_cfg_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v___f_4967_; lean_object* v___x_4968_; 
v___f_4967_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4967_, 0, v_cfg_4964_);
v___x_4968_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_4967_, v_a_4965_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object* v_cfg_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(v_cfg_4969_, v_a_4970_);
lean_dec_ref(v_a_4970_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(lean_object* v_service_4974_, lean_object* v_scope_4975_){
_start:
{
lean_object* v___y_4977_; 
if (lean_obj_tag(v_scope_4975_) == 0)
{
lean_object* v_s_4980_; lean_object* v_apiEndpoint_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v_s_4980_ = lean_ctor_get(v_scope_4975_, 0);
lean_inc_ref(v_s_4980_);
lean_dec_ref_known(v_scope_4975_, 1);
v_apiEndpoint_4981_ = lean_ctor_get(v_service_4974_, 4);
lean_inc_ref(v_apiEndpoint_4981_);
lean_dec_ref(v_service_4974_);
v___x_4982_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_4983_ = lean_string_append(v_apiEndpoint_4981_, v___x_4982_);
v___x_4984_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4983_, v_s_4980_);
v___y_4977_ = v___x_4984_;
goto v___jp_4976_;
}
else
{
lean_object* v_s_4985_; lean_object* v_apiEndpoint_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v_s_4985_ = lean_ctor_get(v_scope_4975_, 0);
lean_inc_ref(v_s_4985_);
lean_dec_ref_known(v_scope_4975_, 1);
v_apiEndpoint_4986_ = lean_ctor_get(v_service_4974_, 4);
lean_inc_ref(v_apiEndpoint_4986_);
lean_dec_ref(v_service_4974_);
v___x_4987_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_4988_ = lean_string_append(v_apiEndpoint_4986_, v___x_4987_);
v___x_4989_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4988_, v_s_4985_);
v___y_4977_ = v___x_4989_;
goto v___jp_4976_;
}
v___jp_4976_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0));
v___x_4979_ = lean_string_append(v___y_4977_, v___x_4978_);
return v___x_4979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(size_t v_sz_4990_, size_t v_i_4991_, lean_object* v_bs_4992_){
_start:
{
uint8_t v___x_4993_; 
v___x_4993_ = lean_usize_dec_lt(v_i_4991_, v_sz_4990_);
if (v___x_4993_ == 0)
{
return v_bs_4992_;
}
else
{
lean_object* v_v_4994_; uint64_t v_hash_4995_; lean_object* v___x_4996_; lean_object* v_bs_x27_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; size_t v___x_5000_; size_t v___x_5001_; lean_object* v___x_5002_; 
v_v_4994_ = lean_array_uget_borrowed(v_bs_4992_, v_i_4991_);
v_hash_4995_ = lean_ctor_get_uint64(v_v_4994_, sizeof(void*)*3);
v___x_4996_ = lean_unsigned_to_nat(0u);
v_bs_x27_4997_ = lean_array_uset(v_bs_4992_, v_i_4991_, v___x_4996_);
v___x_4998_ = l_Lake_lowerHexUInt64(v_hash_4995_);
v___x_4999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
v___x_5000_ = ((size_t)1ULL);
v___x_5001_ = lean_usize_add(v_i_4991_, v___x_5000_);
v___x_5002_ = lean_array_uset(v_bs_x27_4997_, v_i_4991_, v___x_4999_);
v_i_4991_ = v___x_5001_;
v_bs_4992_ = v___x_5002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0___boxed(lean_object* v_sz_5004_, lean_object* v_i_5005_, lean_object* v_bs_5006_){
_start:
{
size_t v_sz_boxed_5007_; size_t v_i_boxed_5008_; lean_object* v_res_5009_; 
v_sz_boxed_5007_ = lean_unbox_usize(v_sz_5004_);
lean_dec(v_sz_5004_);
v_i_boxed_5008_ = lean_unbox_usize(v_i_5005_);
lean_dec(v_i_5005_);
v_res_5009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_boxed_5007_, v_i_boxed_5008_, v_bs_5006_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(lean_object* v_a_5010_, lean_object* v_n_5011_, lean_object* v_j_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v_zero_5014_; uint8_t v_isZero_5015_; 
v_zero_5014_ = lean_unsigned_to_nat(0u);
v_isZero_5015_ = lean_nat_dec_eq(v_j_5012_, v_zero_5014_);
if (v_isZero_5015_ == 1)
{
lean_dec(v_j_5012_);
return v_a_5013_;
}
else
{
lean_object* v___x_5016_; lean_object* v___x_5017_; uint64_t v_hash_5018_; lean_object* v_path_5019_; lean_object* v_extraPaths_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5032_; 
v___x_5016_ = lean_nat_sub(v_n_5011_, v_j_5012_);
v___x_5017_ = lean_array_fget(v_a_5013_, v___x_5016_);
v_hash_5018_ = lean_ctor_get_uint64(v___x_5017_, sizeof(void*)*3);
v_path_5019_ = lean_ctor_get(v___x_5017_, 1);
v_extraPaths_5020_ = lean_ctor_get(v___x_5017_, 2);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5032_ == 0)
{
lean_object* v_unused_5033_; 
v_unused_5033_ = lean_ctor_get(v___x_5017_, 0);
lean_dec(v_unused_5033_);
v___x_5022_ = v___x_5017_;
v_isShared_5023_ = v_isSharedCheck_5032_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_extraPaths_5020_);
lean_inc(v_path_5019_);
lean_dec(v___x_5017_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5032_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v_one_5024_; lean_object* v_n_5025_; lean_object* v___x_5026_; lean_object* v___x_5028_; 
v_one_5024_ = lean_unsigned_to_nat(1u);
v_n_5025_ = lean_nat_sub(v_j_5012_, v_one_5024_);
lean_dec(v_j_5012_);
v___x_5026_ = lean_array_fget_borrowed(v_a_5010_, v___x_5016_);
lean_inc(v___x_5026_);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5026_);
v___x_5028_ = v___x_5022_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5026_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_path_5019_);
lean_ctor_set(v_reuseFailAlloc_5031_, 2, v_extraPaths_5020_);
lean_ctor_set_uint64(v_reuseFailAlloc_5031_, sizeof(void*)*3, v_hash_5018_);
v___x_5028_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
lean_object* v___x_5029_; 
v___x_5029_ = lean_array_fset(v_a_5013_, v___x_5016_, v___x_5028_);
lean_dec(v___x_5016_);
v_j_5012_ = v_n_5025_;
v_a_5013_ = v___x_5029_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg___boxed(lean_object* v_a_5034_, lean_object* v_n_5035_, lean_object* v_j_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5034_, v_n_5035_, v_j_5036_, v_a_5037_);
lean_dec(v_n_5035_);
lean_dec_ref(v_a_5034_);
return v_res_5038_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5039_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5040_ = lean_unsigned_to_nat(2u);
v___x_5041_ = lean_mk_empty_array_with_capacity(v___x_5040_);
v___x_5042_ = lean_array_push(v___x_5041_, v___x_5039_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(lean_object* v_as_5043_, size_t v_i_5044_, size_t v_stop_5045_, lean_object* v_b_5046_){
_start:
{
uint8_t v___x_5047_; 
v___x_5047_ = lean_usize_dec_eq(v_i_5044_, v_stop_5045_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; size_t v___x_5052_; size_t v___x_5053_; 
v___x_5048_ = lean_array_uget_borrowed(v_as_5043_, v_i_5044_);
v___x_5049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0);
lean_inc(v___x_5048_);
v___x_5050_ = lean_array_push(v___x_5049_, v___x_5048_);
v___x_5051_ = l_Array_append___redArg(v_b_5046_, v___x_5050_);
lean_dec_ref(v___x_5050_);
v___x_5052_ = ((size_t)1ULL);
v___x_5053_ = lean_usize_add(v_i_5044_, v___x_5052_);
v_i_5044_ = v___x_5053_;
v_b_5046_ = v___x_5051_;
goto _start;
}
else
{
return v_b_5046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___boxed(lean_object* v_as_5055_, lean_object* v_i_5056_, lean_object* v_stop_5057_, lean_object* v_b_5058_){
_start:
{
size_t v_i_boxed_5059_; size_t v_stop_boxed_5060_; lean_object* v_res_5061_; 
v_i_boxed_5059_ = lean_unbox_usize(v_i_5056_);
lean_dec(v_i_5056_);
v_stop_boxed_5060_ = lean_unbox_usize(v_stop_5057_);
lean_dec(v_stop_5057_);
v_res_5061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v_as_5055_, v_i_boxed_5059_, v_stop_boxed_5060_, v_b_5058_);
lean_dec_ref(v_as_5055_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object* v_x_5064_){
_start:
{
if (lean_obj_tag(v_x_5064_) == 0)
{
lean_object* v___x_5065_; 
v___x_5065_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0));
return v___x_5065_;
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5066_, 0, v_x_5064_);
v___x_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
return v___x_5067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object* v_x_5070_){
_start:
{
if (lean_obj_tag(v_x_5070_) == 0)
{
lean_object* v___x_5071_; 
v___x_5071_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0));
return v___x_5071_;
}
else
{
lean_object* v___x_5072_; 
v___x_5072_ = l_Lean_Json_getObj_x3f(v_x_5070_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5072_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5072_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5089_; 
v_a_5081_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5083_ = v___x_5072_;
v_isShared_5084_ = v_isSharedCheck_5089_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5072_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5089_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5085_; lean_object* v___x_5087_; 
v___x_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5085_, 0, v_a_5081_);
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 0, v___x_5085_);
v___x_5087_ = v___x_5083_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5085_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t v_sz_5090_, size_t v_i_5091_, lean_object* v_bs_5092_){
_start:
{
uint8_t v___x_5093_; 
v___x_5093_ = lean_usize_dec_lt(v_i_5091_, v_sz_5090_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; 
v___x_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5094_, 0, v_bs_5092_);
return v___x_5094_;
}
else
{
lean_object* v_v_5095_; lean_object* v___x_5096_; 
v_v_5095_ = lean_array_uget_borrowed(v_bs_5092_, v_i_5091_);
lean_inc(v_v_5095_);
v___x_5096_ = l_Lean_Json_getStr_x3f(v_v_5095_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_dec_ref(v_bs_5092_);
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
else
{
lean_object* v_a_5105_; lean_object* v___x_5106_; lean_object* v_bs_x27_5107_; size_t v___x_5108_; size_t v___x_5109_; lean_object* v___x_5110_; 
v_a_5105_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5096_, 1);
v___x_5106_ = lean_unsigned_to_nat(0u);
v_bs_x27_5107_ = lean_array_uset(v_bs_5092_, v_i_5091_, v___x_5106_);
v___x_5108_ = ((size_t)1ULL);
v___x_5109_ = lean_usize_add(v_i_5091_, v___x_5108_);
v___x_5110_ = lean_array_uset(v_bs_x27_5107_, v_i_5091_, v_a_5105_);
v_i_5091_ = v___x_5109_;
v_bs_5092_ = v___x_5110_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_5112_, lean_object* v_i_5113_, lean_object* v_bs_5114_){
_start:
{
size_t v_sz_boxed_5115_; size_t v_i_boxed_5116_; lean_object* v_res_5117_; 
v_sz_boxed_5115_ = lean_unbox_usize(v_sz_5112_);
lean_dec(v_sz_5112_);
v_i_boxed_5116_ = lean_unbox_usize(v_i_5113_);
lean_dec(v_i_5113_);
v_res_5117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_boxed_5115_, v_i_boxed_5116_, v_bs_5114_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object* v_x_5118_){
_start:
{
if (lean_obj_tag(v_x_5118_) == 4)
{
lean_object* v_elems_5119_; size_t v_sz_5120_; size_t v___x_5121_; lean_object* v___x_5122_; 
v_elems_5119_ = lean_ctor_get(v_x_5118_, 0);
lean_inc_ref(v_elems_5119_);
lean_dec_ref_known(v_x_5118_, 1);
v_sz_5120_ = lean_array_size(v_elems_5119_);
v___x_5121_ = ((size_t)0ULL);
v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_5120_, v___x_5121_, v_elems_5119_);
return v___x_5122_;
}
else
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5123_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_5124_ = lean_unsigned_to_nat(80u);
v___x_5125_ = l_Lean_Json_pretty(v_x_5118_, v___x_5124_);
v___x_5126_ = lean_string_append(v___x_5123_, v___x_5125_);
lean_dec_ref(v___x_5125_);
v___x_5127_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
v___x_5128_ = lean_string_append(v___x_5126_, v___x_5127_);
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
return v___x_5129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(lean_object* v_val_5142_){
_start:
{
lean_object* v_a_5144_; lean_object* v___x_5188_; 
lean_inc(v_val_5142_);
v___x_5188_ = l_Lean_Json_getObj_x3f(v_val_5142_);
if (lean_obj_tag(v___x_5188_) == 1)
{
lean_object* v_a_5189_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref_known(v___x_5188_, 1);
v___x_5196_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0));
v___x_5197_ = l_Lake_JsonObject_getJson_x3f(v_a_5189_, v___x_5196_);
if (lean_obj_tag(v___x_5197_) == 0)
{
goto v___jp_5190_;
}
else
{
lean_object* v_val_5198_; lean_object* v___x_5199_; 
v_val_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_val_5198_);
lean_dec_ref_known(v___x_5197_, 1);
v___x_5199_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(v_val_5198_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5209_; 
lean_dec(v_a_5189_);
lean_dec(v_val_5142_);
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5209_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5209_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5207_; 
v___x_5204_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1));
v___x_5205_ = lean_string_append(v___x_5204_, v_a_5200_);
lean_dec(v_a_5200_);
if (v_isShared_5203_ == 0)
{
lean_ctor_set(v___x_5202_, 0, v___x_5205_);
v___x_5207_ = v___x_5202_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5205_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
else
{
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_dec(v_a_5189_);
lean_dec(v_val_5142_);
v_a_5210_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5199_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5199_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set_tag(v___x_5212_, 0);
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
else
{
lean_object* v_a_5218_; 
v_a_5218_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5199_, 1);
if (lean_obj_tag(v_a_5218_) == 1)
{
lean_object* v_val_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_dec(v_a_5189_);
lean_dec(v_val_5142_);
v_val_5219_ = lean_ctor_get(v_a_5218_, 0);
lean_inc(v_val_5219_);
lean_dec_ref_known(v_a_5218_, 1);
v___x_5220_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2));
v___x_5221_ = l_Lake_JsonObject_getJson_x3f(v_val_5219_, v___x_5220_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v___x_5222_; 
lean_dec(v_val_5219_);
v___x_5222_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4));
return v___x_5222_;
}
else
{
lean_object* v_val_5223_; lean_object* v___x_5224_; 
v_val_5223_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_val_5223_);
lean_dec_ref_known(v___x_5221_, 1);
v___x_5224_ = l_Lean_Json_getNat_x3f(v_val_5223_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5234_; 
lean_dec(v_val_5219_);
v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5227_ = v___x_5224_;
v_isShared_5228_ = v_isSharedCheck_5234_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5224_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5234_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5232_; 
v___x_5229_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5));
v___x_5230_ = lean_string_append(v___x_5229_, v_a_5225_);
lean_dec(v_a_5225_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 0, v___x_5230_);
v___x_5232_ = v___x_5227_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
else
{
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
lean_dec(v_val_5219_);
v_a_5235_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5224_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5224_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
lean_ctor_set_tag(v___x_5237_, 0);
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; 
v_a_5243_ = lean_ctor_get(v___x_5224_, 0);
lean_inc(v_a_5243_);
lean_dec_ref_known(v___x_5224_, 1);
v___x_5244_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6));
v___x_5245_ = l_Lake_JsonObject_getJson_x3f(v_val_5219_, v___x_5244_);
lean_dec(v_val_5219_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v___x_5246_; 
lean_dec(v_a_5243_);
v___x_5246_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8));
return v___x_5246_;
}
else
{
lean_object* v_val_5247_; lean_object* v___x_5248_; 
v_val_5247_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_val_5247_);
lean_dec_ref_known(v___x_5245_, 1);
v___x_5248_ = l_Lean_Json_getStr_x3f(v_val_5247_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5258_; 
lean_dec(v_a_5243_);
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5251_ = v___x_5248_;
v_isShared_5252_ = v_isSharedCheck_5258_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5248_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5258_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5256_; 
v___x_5253_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9));
v___x_5254_ = lean_string_append(v___x_5253_, v_a_5249_);
lean_dec(v_a_5249_);
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 0, v___x_5254_);
v___x_5256_ = v___x_5251_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v___x_5254_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
else
{
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
lean_dec(v_a_5243_);
v_a_5259_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5248_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5248_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
lean_ctor_set_tag(v___x_5261_, 0);
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5275_; 
v_a_5267_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5269_ = v___x_5248_;
v_isShared_5270_ = v_isSharedCheck_5275_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5248_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5275_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5271_; lean_object* v___x_5273_; 
v___x_5271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5271_, 0, v_a_5243_);
lean_ctor_set(v___x_5271_, 1, v_a_5267_);
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 0, v___x_5271_);
v___x_5273_ = v___x_5269_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5271_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
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
lean_dec(v_a_5218_);
goto v___jp_5190_;
}
}
}
}
v___jp_5190_:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5191_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_5192_ = l_Lake_JsonObject_getJson_x3f(v_a_5189_, v___x_5191_);
lean_dec(v_a_5189_);
if (lean_obj_tag(v___x_5192_) == 0)
{
v_a_5144_ = v___x_5192_;
goto v___jp_5143_;
}
else
{
lean_object* v_val_5193_; lean_object* v___x_5194_; lean_object* v_a_5195_; 
v_val_5193_ = lean_ctor_get(v___x_5192_, 0);
lean_inc(v_val_5193_);
lean_dec_ref_known(v___x_5192_, 1);
v___x_5194_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(v_val_5193_);
v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc(v_a_5195_);
lean_dec_ref(v___x_5194_);
v_a_5144_ = v_a_5195_;
goto v___jp_5143_;
}
}
}
else
{
lean_object* v___x_5276_; 
lean_dec_ref(v___x_5188_);
v___x_5276_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5142_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5293_; 
v_a_5285_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5287_ = v___x_5276_;
v_isShared_5288_ = v_isSharedCheck_5293_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5276_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5293_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5289_, 0, v_a_5285_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5289_);
v___x_5291_ = v___x_5287_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
v___jp_5143_:
{
if (lean_obj_tag(v_a_5144_) == 1)
{
lean_object* v_val_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5169_; 
lean_dec(v_val_5142_);
v_val_5145_ = lean_ctor_get(v_a_5144_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v_a_5144_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5147_ = v_a_5144_;
v_isShared_5148_ = v_isSharedCheck_5169_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_val_5145_);
lean_dec(v_a_5144_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5169_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5145_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
lean_del_object(v___x_5147_);
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5149_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5149_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
else
{
lean_object* v_a_5158_; lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5168_; 
v_a_5158_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5160_ = v___x_5149_;
v_isShared_5161_ = v_isSharedCheck_5168_;
goto v_resetjp_5159_;
}
else
{
lean_inc(v_a_5158_);
lean_dec(v___x_5149_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5168_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5163_; 
if (v_isShared_5148_ == 0)
{
lean_ctor_set_tag(v___x_5147_, 0);
lean_ctor_set(v___x_5147_, 0, v_a_5158_);
v___x_5163_ = v___x_5147_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5158_);
v___x_5163_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5165_; 
if (v_isShared_5161_ == 0)
{
lean_ctor_set(v___x_5160_, 0, v___x_5163_);
v___x_5165_ = v___x_5160_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5163_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
}
}
}
else
{
lean_object* v___x_5170_; 
lean_dec(v_a_5144_);
v___x_5170_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5142_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5170_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5170_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5187_; 
v_a_5179_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5181_ = v___x_5170_;
v_isShared_5182_ = v_isSharedCheck_5187_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5170_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5187_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5183_; lean_object* v___x_5185_; 
v___x_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5183_, 0, v_a_5179_);
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 0, v___x_5183_);
v___x_5185_ = v___x_5181_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18(void){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5312_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_5313_ = lean_unsigned_to_nat(12u);
v___x_5314_ = lean_mk_empty_array_with_capacity(v___x_5313_);
v___x_5315_ = lean_array_push(v___x_5314_, v___x_5312_);
return v___x_5315_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19(void){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14));
v___x_5317_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18);
v___x_5318_ = lean_array_push(v___x_5317_, v___x_5316_);
return v___x_5318_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20(void){
_start:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5319_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_5320_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19);
v___x_5321_ = lean_array_push(v___x_5320_, v___x_5319_);
return v___x_5321_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21(void){
_start:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5322_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15));
v___x_5323_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20);
v___x_5324_ = lean_array_push(v___x_5323_, v___x_5322_);
return v___x_5324_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22(void){
_start:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; 
v___x_5325_ = l_Lake_Reservoir_lakeHeaders;
v___x_5326_ = lean_array_get_size(v___x_5325_);
return v___x_5326_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23(void){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; uint8_t v___x_5329_; 
v___x_5327_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5328_ = lean_unsigned_to_nat(0u);
v___x_5329_ = lean_nat_dec_lt(v___x_5328_, v___x_5327_);
return v___x_5329_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24(void){
_start:
{
lean_object* v___x_5330_; uint8_t v___x_5331_; 
v___x_5330_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5331_ = lean_nat_dec_le(v___x_5330_, v___x_5330_);
return v___x_5331_;
}
}
static size_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25(void){
_start:
{
lean_object* v___x_5332_; size_t v___x_5333_; 
v___x_5332_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5333_ = lean_usize_of_nat(v___x_5332_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(lean_object* v_infos_5334_, lean_object* v_url_5335_, lean_object* v_h_5336_, lean_object* v_path_5337_, lean_object* v___y_5338_){
_start:
{
uint32_t v___y_5341_; lean_object* v___y_5342_; lean_object* v___y_5353_; lean_object* v___y_5354_; uint32_t v___y_5355_; lean_object* v___y_5356_; lean_object* v_a_5357_; lean_object* v___y_5385_; uint8_t v___y_5386_; uint32_t v___y_5387_; lean_object* v___y_5388_; lean_object* v_msg_5389_; lean_object* v___y_5390_; lean_object* v___y_5404_; lean_object* v___y_5405_; uint8_t v___y_5406_; uint32_t v___y_5407_; lean_object* v___y_5408_; lean_object* v_msg_5409_; lean_object* v___y_5410_; lean_object* v___y_5421_; lean_object* v___y_5422_; uint8_t v___y_5423_; lean_object* v___y_5424_; uint32_t v___y_5425_; lean_object* v___y_5426_; lean_object* v_msg_5427_; lean_object* v___y_5428_; lean_object* v___y_5441_; lean_object* v___y_5442_; uint8_t v___y_5443_; uint32_t v___y_5444_; lean_object* v___y_5445_; size_t v_sz_5463_; size_t v___x_5464_; lean_object* v___x_5465_; lean_object* v_body_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
v_sz_5463_ = lean_array_size(v_infos_5334_);
v___x_5464_ = ((size_t)0ULL);
lean_inc_ref(v_infos_5334_);
v___x_5465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_5463_, v___x_5464_, v_infos_5334_);
v_body_5466_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_5466_, 0, v___x_5465_);
v___x_5467_ = l_Lean_Json_compress(v_body_5466_);
v___x_5468_ = lean_io_prim_handle_put_str(v_h_5336_, v___x_5467_);
lean_dec_ref(v___x_5467_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v___x_5469_; 
lean_dec_ref_known(v___x_5468_, 1);
v___x_5469_ = lean_io_prim_handle_flush(v_h_5336_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v___y_5471_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; uint8_t v___x_5573_; 
lean_dec_ref_known(v___x_5469_, 1);
v___x_5554_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_5555_ = lean_string_append(v___x_5554_, v_path_5337_);
v___x_5556_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_5557_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_5558_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5559_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5560_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5561_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5562_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_5563_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_5564_ = lean_array_push(v___x_5563_, v___x_5555_);
v___x_5565_ = lean_array_push(v___x_5564_, v___x_5556_);
v___x_5566_ = lean_array_push(v___x_5565_, v___x_5557_);
v___x_5567_ = lean_array_push(v___x_5566_, v___x_5558_);
v___x_5568_ = lean_array_push(v___x_5567_, v___x_5559_);
v___x_5569_ = lean_array_push(v___x_5568_, v___x_5560_);
v___x_5570_ = lean_array_push(v___x_5569_, v___x_5561_);
v___x_5571_ = lean_array_push(v___x_5570_, v___x_5562_);
v___x_5572_ = l_Lake_Reservoir_lakeHeaders;
v___x_5573_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_5573_ == 0)
{
v___y_5471_ = v___x_5571_;
goto v___jp_5470_;
}
else
{
uint8_t v___x_5574_; 
v___x_5574_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
if (v___x_5574_ == 0)
{
if (v___x_5573_ == 0)
{
v___y_5471_ = v___x_5571_;
goto v___jp_5470_;
}
else
{
size_t v___x_5575_; lean_object* v___x_5576_; 
v___x_5575_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5572_, v___x_5464_, v___x_5575_, v___x_5571_);
v___y_5471_ = v___x_5576_;
goto v___jp_5470_;
}
}
else
{
size_t v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5572_, v___x_5464_, v___x_5577_, v___x_5571_);
v___y_5471_ = v___x_5578_;
goto v___jp_5470_;
}
}
v___jp_5470_:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; uint8_t v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; uint8_t v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5472_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5473_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
lean_inc_ref(v_url_5335_);
v___x_5474_ = lean_array_push(v___y_5471_, v_url_5335_);
v___x_5475_ = lean_box(0);
v___x_5476_ = lean_unsigned_to_nat(0u);
v___x_5477_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5478_ = 1;
v___x_5479_ = 0;
v___x_5480_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5480_, 0, v___x_5472_);
lean_ctor_set(v___x_5480_, 1, v___x_5473_);
lean_ctor_set(v___x_5480_, 2, v___x_5474_);
lean_ctor_set(v___x_5480_, 3, v___x_5475_);
lean_ctor_set(v___x_5480_, 4, v___x_5477_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*5, v___x_5478_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*5 + 1, v___x_5479_);
lean_inc_ref(v___x_5480_);
v___x_5481_ = l_Lake_mkCmdLog(v___x_5480_);
v___x_5482_ = 0;
v___x_5483_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5483_, 0, v___x_5481_);
lean_ctor_set_uint8(v___x_5483_, sizeof(void*)*1, v___x_5482_);
lean_inc_ref(v___y_5338_);
v___x_5484_ = lean_apply_2(v___y_5338_, v___x_5483_, lean_box(0));
v___x_5485_ = l_IO_Process_output(v___x_5480_, v___x_5475_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5540_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5488_ = v___x_5485_;
v_isShared_5489_ = v_isSharedCheck_5540_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___x_5485_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5540_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
uint32_t v_exitCode_5490_; lean_object* v_stdout_5491_; lean_object* v_stderr_5492_; lean_object* v___x_5493_; 
v_exitCode_5490_ = lean_ctor_get_uint32(v_a_5486_, sizeof(void*)*2);
v_stdout_5491_ = lean_ctor_get(v_a_5486_, 0);
lean_inc_ref_n(v_stdout_5491_, 2);
v_stderr_5492_ = lean_ctor_get(v_a_5486_, 1);
lean_inc_ref(v_stderr_5492_);
lean_dec(v_a_5486_);
v___x_5493_ = l_Lean_Json_parse(v_stdout_5491_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_dec_ref_known(v___x_5493_, 1);
lean_del_object(v___x_5488_);
lean_dec_ref(v_infos_5334_);
v___y_5441_ = v_stdout_5491_;
v___y_5442_ = v_stderr_5492_;
v___y_5443_ = v___x_5482_;
v___y_5444_ = v_exitCode_5490_;
v___y_5445_ = v___x_5476_;
goto v___jp_5440_;
}
else
{
lean_object* v_a_5494_; lean_object* v___x_5495_; 
v_a_5494_ = lean_ctor_get(v___x_5493_, 0);
lean_inc(v_a_5494_);
lean_dec_ref_known(v___x_5493_, 1);
v___x_5495_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_5494_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_dec_ref_known(v___x_5495_, 1);
lean_del_object(v___x_5488_);
lean_dec_ref(v_infos_5334_);
v___y_5441_ = v_stdout_5491_;
v___y_5442_ = v_stderr_5492_;
v___y_5443_ = v___x_5482_;
v___y_5444_ = v_exitCode_5490_;
v___y_5445_ = v___x_5476_;
goto v___jp_5440_;
}
else
{
lean_object* v_a_5496_; 
lean_dec_ref(v_stderr_5492_);
lean_dec_ref(v_stdout_5491_);
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
lean_dec_ref_known(v___x_5495_, 1);
if (lean_obj_tag(v_a_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; uint8_t v___x_5500_; 
v_a_5497_ = lean_ctor_get(v_a_5496_, 0);
lean_inc(v_a_5497_);
lean_dec_ref_known(v_a_5496_, 1);
v___x_5498_ = lean_array_get_size(v_infos_5334_);
v___x_5499_ = lean_array_get_size(v_a_5497_);
v___x_5500_ = lean_nat_dec_eq(v___x_5498_, v___x_5499_);
if (v___x_5500_ == 0)
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; uint8_t v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5516_; 
lean_dec(v_a_5497_);
lean_dec_ref(v_infos_5334_);
v___x_5501_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5502_ = lean_string_append(v___x_5501_, v_url_5335_);
lean_dec_ref(v_url_5335_);
v___x_5503_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_5504_ = lean_string_append(v___x_5502_, v___x_5503_);
v___x_5505_ = l_Nat_reprFast(v___x_5498_);
v___x_5506_ = lean_string_append(v___x_5504_, v___x_5505_);
lean_dec_ref(v___x_5505_);
v___x_5507_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_5508_ = lean_string_append(v___x_5506_, v___x_5507_);
v___x_5509_ = l_Nat_reprFast(v___x_5499_);
v___x_5510_ = lean_string_append(v___x_5508_, v___x_5509_);
lean_dec_ref(v___x_5509_);
v___x_5511_ = 3;
v___x_5512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5512_, 0, v___x_5510_);
lean_ctor_set_uint8(v___x_5512_, sizeof(void*)*1, v___x_5511_);
lean_inc_ref(v___y_5338_);
v___x_5513_ = lean_apply_2(v___y_5338_, v___x_5512_, lean_box(0));
v___x_5514_ = lean_box(0);
if (v_isShared_5489_ == 0)
{
lean_ctor_set_tag(v___x_5488_, 1);
lean_ctor_set(v___x_5488_, 0, v___x_5514_);
v___x_5516_ = v___x_5488_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5514_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
else
{
lean_object* v___x_5518_; lean_object* v___x_5520_; 
lean_dec_ref(v_url_5335_);
v___x_5518_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5497_, v___x_5498_, v___x_5498_, v_infos_5334_);
lean_dec(v_a_5497_);
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 0, v___x_5518_);
v___x_5520_ = v___x_5488_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5518_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
else
{
lean_object* v_status_5522_; lean_object* v_message_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5538_; 
lean_dec_ref(v_infos_5334_);
v_status_5522_ = lean_ctor_get(v_a_5496_, 0);
lean_inc(v_status_5522_);
v_message_5523_ = lean_ctor_get(v_a_5496_, 1);
lean_inc_ref(v_message_5523_);
lean_dec_ref_known(v_a_5496_, 2);
v___x_5524_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5525_ = l_Nat_reprFast(v_status_5522_);
v___x_5526_ = lean_string_append(v___x_5524_, v___x_5525_);
lean_dec_ref(v___x_5525_);
v___x_5527_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_5528_ = lean_string_append(v___x_5526_, v___x_5527_);
v___x_5529_ = lean_string_append(v___x_5528_, v_url_5335_);
lean_dec_ref(v_url_5335_);
v___x_5530_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_5531_ = lean_string_append(v___x_5529_, v___x_5530_);
v___x_5532_ = lean_string_append(v___x_5531_, v_message_5523_);
lean_dec_ref(v_message_5523_);
v___x_5533_ = 3;
v___x_5534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5534_, 0, v___x_5532_);
lean_ctor_set_uint8(v___x_5534_, sizeof(void*)*1, v___x_5533_);
lean_inc_ref(v___y_5338_);
v___x_5535_ = lean_apply_2(v___y_5338_, v___x_5534_, lean_box(0));
v___x_5536_ = lean_box(0);
if (v_isShared_5489_ == 0)
{
lean_ctor_set_tag(v___x_5488_, 1);
lean_ctor_set(v___x_5488_, 0, v___x_5536_);
v___x_5538_ = v___x_5488_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
}
}
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5553_; 
lean_dec_ref(v_url_5335_);
lean_dec_ref(v_infos_5334_);
v_a_5541_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5543_ = v___x_5485_;
v_isShared_5544_ = v_isSharedCheck_5553_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5485_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5553_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5545_; uint8_t v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5545_ = lean_io_error_to_string(v_a_5541_);
v___x_5546_ = 3;
v___x_5547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5547_, 0, v___x_5545_);
lean_ctor_set_uint8(v___x_5547_, sizeof(void*)*1, v___x_5546_);
lean_inc_ref(v___y_5338_);
v___x_5548_ = lean_apply_2(v___y_5338_, v___x_5547_, lean_box(0));
v___x_5549_ = lean_box(0);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 0, v___x_5549_);
v___x_5551_ = v___x_5543_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v___x_5549_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
}
}
}
else
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5591_; 
lean_dec_ref(v_url_5335_);
lean_dec_ref(v_infos_5334_);
v_a_5579_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5581_ = v___x_5469_;
v_isShared_5582_ = v_isSharedCheck_5591_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5469_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5591_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5583_; uint8_t v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5589_; 
v___x_5583_ = lean_io_error_to_string(v_a_5579_);
v___x_5584_ = 3;
v___x_5585_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5585_, 0, v___x_5583_);
lean_ctor_set_uint8(v___x_5585_, sizeof(void*)*1, v___x_5584_);
lean_inc_ref(v___y_5338_);
v___x_5586_ = lean_apply_2(v___y_5338_, v___x_5585_, lean_box(0));
v___x_5587_ = lean_box(0);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 0, v___x_5587_);
v___x_5589_ = v___x_5581_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5587_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5604_; 
lean_dec_ref(v_url_5335_);
lean_dec_ref(v_infos_5334_);
v_a_5592_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5594_ = v___x_5468_;
v_isShared_5595_ = v_isSharedCheck_5604_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5468_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5604_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5596_; uint8_t v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5602_; 
v___x_5596_ = lean_io_error_to_string(v_a_5592_);
v___x_5597_ = 3;
v___x_5598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5598_, 0, v___x_5596_);
lean_ctor_set_uint8(v___x_5598_, sizeof(void*)*1, v___x_5597_);
lean_inc_ref(v___y_5338_);
v___x_5599_ = lean_apply_2(v___y_5338_, v___x_5598_, lean_box(0));
v___x_5600_ = lean_box(0);
if (v_isShared_5595_ == 0)
{
lean_ctor_set(v___x_5594_, 0, v___x_5600_);
v___x_5602_ = v___x_5594_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
v___jp_5340_:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; uint8_t v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; 
v___x_5343_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_5344_ = lean_uint32_to_nat(v___y_5341_);
v___x_5345_ = l_Nat_reprFast(v___x_5344_);
v___x_5346_ = lean_string_append(v___x_5343_, v___x_5345_);
lean_dec_ref(v___x_5345_);
v___x_5347_ = 3;
v___x_5348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5348_, 0, v___x_5346_);
lean_ctor_set_uint8(v___x_5348_, sizeof(void*)*1, v___x_5347_);
lean_inc_ref(v___y_5342_);
v___x_5349_ = lean_apply_2(v___y_5342_, v___x_5348_, lean_box(0));
v___x_5350_ = lean_box(0);
v___x_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5351_, 0, v___x_5350_);
return v___x_5351_;
}
v___jp_5352_:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; uint8_t v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; 
v___x_5358_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5359_ = lean_string_append(v___x_5358_, v_url_5335_);
lean_dec_ref(v_url_5335_);
v___x_5360_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_5361_ = lean_string_append(v___x_5359_, v___x_5360_);
v___x_5362_ = lean_string_append(v___x_5361_, v_a_5357_);
lean_dec_ref(v_a_5357_);
v___x_5363_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_5364_ = lean_string_append(v___x_5362_, v___x_5363_);
v___x_5365_ = lean_string_utf8_byte_size(v___y_5354_);
lean_inc(v___y_5356_);
v___x_5366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5366_, 0, v___y_5354_);
lean_ctor_set(v___x_5366_, 1, v___y_5356_);
lean_ctor_set(v___x_5366_, 2, v___x_5365_);
v___x_5367_ = l_String_Slice_trimAscii(v___x_5366_);
v___x_5368_ = l_String_Slice_toString(v___x_5367_);
lean_dec_ref(v___x_5367_);
v___x_5369_ = lean_string_append(v___x_5364_, v___x_5368_);
lean_dec_ref(v___x_5368_);
v___x_5370_ = 3;
v___x_5371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5371_, 0, v___x_5369_);
lean_ctor_set_uint8(v___x_5371_, sizeof(void*)*1, v___x_5370_);
lean_inc_ref(v___y_5338_);
v___x_5372_ = lean_apply_2(v___y_5338_, v___x_5371_, lean_box(0));
v___x_5373_ = lean_string_utf8_byte_size(v___y_5353_);
v___x_5374_ = lean_nat_dec_eq(v___x_5373_, v___y_5356_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; uint8_t v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5375_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
lean_inc(v___y_5356_);
lean_inc_ref(v___y_5353_);
v___x_5376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5376_, 0, v___y_5353_);
lean_ctor_set(v___x_5376_, 1, v___y_5356_);
lean_ctor_set(v___x_5376_, 2, v___x_5373_);
v___x_5377_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5376_, v___x_5373_);
lean_dec_ref_known(v___x_5376_, 3);
v___x_5378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5378_, 0, v___y_5353_);
lean_ctor_set(v___x_5378_, 1, v___y_5356_);
lean_ctor_set(v___x_5378_, 2, v___x_5377_);
v___x_5379_ = l_String_Slice_toString(v___x_5378_);
lean_dec_ref_known(v___x_5378_, 3);
v___x_5380_ = lean_string_append(v___x_5375_, v___x_5379_);
lean_dec_ref(v___x_5379_);
v___x_5381_ = 2;
v___x_5382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5382_, 0, v___x_5380_);
lean_ctor_set_uint8(v___x_5382_, sizeof(void*)*1, v___x_5381_);
lean_inc_ref(v___y_5338_);
v___x_5383_ = lean_apply_2(v___y_5338_, v___x_5382_, lean_box(0));
v___y_5341_ = v___y_5355_;
v___y_5342_ = v___y_5338_;
goto v___jp_5340_;
}
else
{
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5353_);
v___y_5341_ = v___y_5355_;
v___y_5342_ = v___y_5338_;
goto v___jp_5340_;
}
}
v___jp_5384_:
{
uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5391_ = 3;
v___x_5392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5392_, 0, v_msg_5389_);
lean_ctor_set_uint8(v___x_5392_, sizeof(void*)*1, v___x_5391_);
lean_inc_ref_n(v___y_5390_, 2);
v___x_5393_ = lean_apply_2(v___y_5390_, v___x_5392_, lean_box(0));
v___x_5394_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_5395_ = lean_string_utf8_byte_size(v___y_5385_);
lean_inc(v___y_5388_);
lean_inc_ref(v___y_5385_);
v___x_5396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5396_, 0, v___y_5385_);
lean_ctor_set(v___x_5396_, 1, v___y_5388_);
lean_ctor_set(v___x_5396_, 2, v___x_5395_);
v___x_5397_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5396_, v___x_5395_);
lean_dec_ref_known(v___x_5396_, 3);
v___x_5398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5398_, 0, v___y_5385_);
lean_ctor_set(v___x_5398_, 1, v___y_5388_);
lean_ctor_set(v___x_5398_, 2, v___x_5397_);
v___x_5399_ = l_String_Slice_toString(v___x_5398_);
lean_dec_ref_known(v___x_5398_, 3);
v___x_5400_ = lean_string_append(v___x_5394_, v___x_5399_);
lean_dec_ref(v___x_5399_);
v___x_5401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5401_, 0, v___x_5400_);
lean_ctor_set_uint8(v___x_5401_, sizeof(void*)*1, v___y_5386_);
v___x_5402_ = lean_apply_2(v___y_5390_, v___x_5401_, lean_box(0));
v___y_5341_ = v___y_5387_;
v___y_5342_ = v___y_5390_;
goto v___jp_5340_;
}
v___jp_5403_:
{
lean_object* v___x_5411_; uint8_t v___x_5412_; 
v___x_5411_ = lean_string_utf8_byte_size(v___y_5404_);
v___x_5412_ = lean_nat_dec_eq(v___x_5411_, v___y_5408_);
if (v___x_5412_ == 0)
{
lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5413_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5414_ = lean_string_append(v_msg_5409_, v___x_5413_);
lean_inc_n(v___y_5408_, 2);
lean_inc_ref(v___y_5404_);
v___x_5415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5415_, 0, v___y_5404_);
lean_ctor_set(v___x_5415_, 1, v___y_5408_);
lean_ctor_set(v___x_5415_, 2, v___x_5411_);
v___x_5416_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5415_, v___x_5411_);
lean_dec_ref_known(v___x_5415_, 3);
v___x_5417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5417_, 0, v___y_5404_);
lean_ctor_set(v___x_5417_, 1, v___y_5408_);
lean_ctor_set(v___x_5417_, 2, v___x_5416_);
v___x_5418_ = l_String_Slice_toString(v___x_5417_);
lean_dec_ref_known(v___x_5417_, 3);
v___x_5419_ = lean_string_append(v___x_5414_, v___x_5418_);
lean_dec_ref(v___x_5418_);
v___y_5385_ = v___y_5405_;
v___y_5386_ = v___y_5406_;
v___y_5387_ = v___y_5407_;
v___y_5388_ = v___y_5408_;
v_msg_5389_ = v___x_5419_;
v___y_5390_ = v___y_5410_;
goto v___jp_5384_;
}
else
{
lean_dec_ref(v___y_5404_);
v___y_5385_ = v___y_5405_;
v___y_5386_ = v___y_5406_;
v___y_5387_ = v___y_5407_;
v___y_5388_ = v___y_5408_;
v_msg_5389_ = v_msg_5409_;
v___y_5390_ = v___y_5410_;
goto v___jp_5384_;
}
}
v___jp_5420_:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5429_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_5430_ = lean_string_append(v_msg_5427_, v___x_5429_);
v___x_5431_ = lean_string_append(v___x_5430_, v_url_5335_);
lean_dec_ref(v_url_5335_);
v___x_5432_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_5433_ = l_Lake_JsonObject_getJson_x3f(v___y_5424_, v___x_5432_);
lean_dec(v___y_5424_);
if (lean_obj_tag(v___x_5433_) == 0)
{
v___y_5404_ = v___y_5421_;
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5425_;
v___y_5408_ = v___y_5426_;
v_msg_5409_ = v___x_5431_;
v___y_5410_ = v___y_5428_;
goto v___jp_5403_;
}
else
{
lean_object* v_val_5434_; lean_object* v___x_5435_; 
v_val_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_val_5434_);
lean_dec_ref_known(v___x_5433_, 1);
v___x_5435_ = l_Lean_Json_getStr_x3f(v_val_5434_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_dec_ref_known(v___x_5435_, 1);
v___y_5404_ = v___y_5421_;
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5425_;
v___y_5408_ = v___y_5426_;
v_msg_5409_ = v___x_5431_;
v___y_5410_ = v___y_5428_;
goto v___jp_5403_;
}
else
{
if (lean_obj_tag(v___x_5435_) == 1)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref_known(v___x_5435_, 1);
v___x_5437_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
v___x_5438_ = lean_string_append(v___x_5431_, v___x_5437_);
v___x_5439_ = lean_string_append(v___x_5438_, v_a_5436_);
lean_dec(v_a_5436_);
v___y_5404_ = v___y_5421_;
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5425_;
v___y_5408_ = v___y_5426_;
v_msg_5409_ = v___x_5439_;
v___y_5410_ = v___y_5428_;
goto v___jp_5403_;
}
else
{
lean_dec_ref_known(v___x_5435_, 1);
v___y_5404_ = v___y_5421_;
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5425_;
v___y_5408_ = v___y_5426_;
v_msg_5409_ = v___x_5431_;
v___y_5410_ = v___y_5428_;
goto v___jp_5403_;
}
}
}
}
v___jp_5440_:
{
lean_object* v___x_5446_; 
lean_inc_ref(v___y_5442_);
v___x_5446_ = l_Lean_Json_parse(v___y_5442_);
if (lean_obj_tag(v___x_5446_) == 0)
{
lean_object* v_a_5447_; 
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
lean_inc(v_a_5447_);
lean_dec_ref_known(v___x_5446_, 1);
v___y_5353_ = v___y_5441_;
v___y_5354_ = v___y_5442_;
v___y_5355_ = v___y_5444_;
v___y_5356_ = v___y_5445_;
v_a_5357_ = v_a_5447_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5449_; 
v_a_5448_ = lean_ctor_get(v___x_5446_, 0);
lean_inc(v_a_5448_);
lean_dec_ref_known(v___x_5446_, 1);
v___x_5449_ = l_Lean_Json_getObj_x3f(v_a_5448_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5450_);
lean_dec_ref_known(v___x_5449_, 1);
v___y_5353_ = v___y_5441_;
v___y_5354_ = v___y_5442_;
v___y_5355_ = v___y_5444_;
v___y_5356_ = v___y_5445_;
v_a_5357_ = v_a_5450_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; 
v_a_5451_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5451_);
lean_dec_ref_known(v___x_5449_, 1);
v___x_5452_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_5453_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_5454_ = l_Lake_JsonObject_getJson_x3f(v_a_5451_, v___x_5453_);
if (lean_obj_tag(v___x_5454_) == 0)
{
v___y_5421_ = v___y_5441_;
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v_a_5451_;
v___y_5425_ = v___y_5444_;
v___y_5426_ = v___y_5445_;
v_msg_5427_ = v___x_5452_;
v___y_5428_ = v___y_5338_;
goto v___jp_5420_;
}
else
{
lean_object* v_val_5455_; lean_object* v___x_5456_; 
v_val_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_val_5455_);
lean_dec_ref_known(v___x_5454_, 1);
v___x_5456_ = l_Lean_Json_getNat_x3f(v_val_5455_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_dec_ref_known(v___x_5456_, 1);
v___y_5421_ = v___y_5441_;
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v_a_5451_;
v___y_5425_ = v___y_5444_;
v___y_5426_ = v___y_5445_;
v_msg_5427_ = v___x_5452_;
v___y_5428_ = v___y_5338_;
goto v___jp_5420_;
}
else
{
if (lean_obj_tag(v___x_5456_) == 1)
{
lean_object* v_a_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5456_, 1);
v___x_5458_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5459_ = l_Nat_reprFast(v_a_5457_);
v___x_5460_ = lean_string_append(v___x_5458_, v___x_5459_);
lean_dec_ref(v___x_5459_);
v___x_5461_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_5462_ = lean_string_append(v___x_5460_, v___x_5461_);
v___y_5421_ = v___y_5441_;
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v_a_5451_;
v___y_5425_ = v___y_5444_;
v___y_5426_ = v___y_5445_;
v_msg_5427_ = v___x_5462_;
v___y_5428_ = v___y_5338_;
goto v___jp_5420_;
}
else
{
lean_dec_ref_known(v___x_5456_, 1);
v___y_5421_ = v___y_5441_;
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v_a_5451_;
v___y_5425_ = v___y_5444_;
v___y_5426_ = v___y_5445_;
v_msg_5427_ = v___x_5452_;
v___y_5428_ = v___y_5338_;
goto v___jp_5420_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed(lean_object* v_infos_5605_, lean_object* v_url_5606_, lean_object* v_h_5607_, lean_object* v_path_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
lean_object* v_res_5611_; 
v_res_5611_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(v_infos_5605_, v_url_5606_, v_h_5607_, v_path_5608_, v___y_5609_);
lean_dec_ref(v___y_5609_);
lean_dec_ref(v_path_5608_);
lean_dec(v_h_5607_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(lean_object* v_url_5612_, lean_object* v_infos_5613_, lean_object* v_a_5614_){
_start:
{
lean_object* v___f_5616_; lean_object* v___x_5617_; 
v___f_5616_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5616_, 0, v_infos_5613_);
lean_closure_set(v___f_5616_, 1, v_url_5612_);
v___x_5617_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5616_, v_a_5614_);
return v___x_5617_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___boxed(lean_object* v_url_5618_, lean_object* v_infos_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(v_url_5618_, v_infos_5619_, v_a_5620_);
lean_dec_ref(v_a_5620_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(lean_object* v_a_5623_, lean_object* v___x_5624_, lean_object* v_n_5625_, lean_object* v_j_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_){
_start:
{
lean_object* v___x_5629_; 
v___x_5629_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5623_, v_n_5625_, v_j_5626_, v_a_5628_);
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___boxed(lean_object* v_a_5630_, lean_object* v___x_5631_, lean_object* v_n_5632_, lean_object* v_j_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(v_a_5630_, v___x_5631_, v_n_5632_, v_j_5633_, v_a_5634_, v_a_5635_);
lean_dec(v_n_5632_);
lean_dec(v___x_5631_);
lean_dec_ref(v_a_5630_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object* v_cfg_5637_, lean_object* v_h_5638_, lean_object* v_path_5639_, lean_object* v___y_5640_){
_start:
{
uint8_t v___y_5643_; uint32_t v___y_5649_; lean_object* v___y_5650_; uint8_t v___y_5651_; lean_object* v___y_5652_; uint8_t v_kind_5661_; lean_object* v_scope_5662_; lean_object* v_infos_5663_; lean_object* v_key_5664_; uint32_t v___y_5666_; uint8_t v___y_5667_; lean_object* v___y_5668_; lean_object* v___y_5674_; lean_object* v___y_5675_; lean_object* v___y_5676_; uint32_t v___y_5677_; lean_object* v___y_5678_; uint8_t v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5692_; lean_object* v___y_5693_; uint32_t v___y_5694_; uint8_t v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5701_; uint32_t v___y_5702_; lean_object* v___y_5703_; uint8_t v___y_5704_; lean_object* v___y_5705_; lean_object* v___y_5706_; lean_object* v___y_5716_; lean_object* v___y_5717_; uint32_t v___y_5718_; uint8_t v___y_5719_; lean_object* v___y_5720_; lean_object* v_a_5723_; lean_object* v___y_5819_; lean_object* v___y_5849_; 
v_kind_5661_ = lean_ctor_get_uint8(v_cfg_5637_, sizeof(void*)*3);
v_scope_5662_ = lean_ctor_get(v_cfg_5637_, 0);
lean_inc_ref(v_scope_5662_);
v_infos_5663_ = lean_ctor_get(v_cfg_5637_, 1);
lean_inc_ref(v_infos_5663_);
v_key_5664_ = lean_ctor_get(v_cfg_5637_, 2);
if (v_kind_5661_ == 0)
{
lean_object* v___x_5850_; lean_object* v___x_5851_; uint8_t v___x_5852_; 
v___x_5850_ = lean_unsigned_to_nat(0u);
v___x_5851_ = lean_array_get_size(v_infos_5663_);
v___x_5852_ = lean_nat_dec_lt(v___x_5850_, v___x_5851_);
if (v___x_5852_ == 0)
{
goto v___jp_5799_;
}
else
{
lean_object* v___x_5853_; uint8_t v___x_5854_; 
v___x_5853_ = lean_box(0);
v___x_5854_ = lean_nat_dec_le(v___x_5851_, v___x_5851_);
if (v___x_5854_ == 0)
{
if (v___x_5852_ == 0)
{
goto v___jp_5799_;
}
else
{
size_t v___x_5855_; size_t v___x_5856_; lean_object* v___x_5857_; 
v___x_5855_ = ((size_t)0ULL);
v___x_5856_ = lean_usize_of_nat(v___x_5851_);
v___x_5857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5638_, v_infos_5663_, v___x_5855_, v___x_5856_, v___x_5853_, v___y_5640_);
v___y_5819_ = v___x_5857_;
goto v___jp_5818_;
}
}
else
{
size_t v___x_5858_; size_t v___x_5859_; lean_object* v___x_5860_; 
v___x_5858_ = ((size_t)0ULL);
v___x_5859_ = lean_usize_of_nat(v___x_5851_);
v___x_5860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5638_, v_infos_5663_, v___x_5858_, v___x_5859_, v___x_5853_, v___y_5640_);
v___y_5819_ = v___x_5860_;
goto v___jp_5818_;
}
}
}
else
{
lean_object* v___x_5861_; lean_object* v___x_5862_; uint8_t v___x_5863_; 
v___x_5861_ = lean_unsigned_to_nat(0u);
v___x_5862_ = lean_array_get_size(v_infos_5663_);
v___x_5863_ = lean_nat_dec_lt(v___x_5861_, v___x_5862_);
if (v___x_5863_ == 0)
{
goto v___jp_5820_;
}
else
{
lean_object* v___x_5864_; uint8_t v___x_5865_; 
v___x_5864_ = lean_box(0);
v___x_5865_ = lean_nat_dec_le(v___x_5862_, v___x_5862_);
if (v___x_5865_ == 0)
{
if (v___x_5863_ == 0)
{
goto v___jp_5820_;
}
else
{
size_t v___x_5866_; size_t v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = ((size_t)0ULL);
v___x_5867_ = lean_usize_of_nat(v___x_5862_);
v___x_5868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5638_, v_infos_5663_, v___x_5866_, v___x_5867_, v___x_5864_, v___y_5640_);
v___y_5849_ = v___x_5868_;
goto v___jp_5848_;
}
}
else
{
size_t v___x_5869_; size_t v___x_5870_; lean_object* v___x_5871_; 
v___x_5869_ = ((size_t)0ULL);
v___x_5870_ = lean_usize_of_nat(v___x_5862_);
v___x_5871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5638_, v_infos_5663_, v___x_5869_, v___x_5870_, v___x_5864_, v___y_5640_);
v___y_5849_ = v___x_5871_;
goto v___jp_5848_;
}
}
}
v___jp_5642_:
{
if (v___y_5643_ == 0)
{
lean_object* v___x_5644_; lean_object* v___x_5645_; 
v___x_5644_ = lean_box(0);
v___x_5645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
return v___x_5645_;
}
else
{
lean_object* v___x_5646_; lean_object* v___x_5647_; 
v___x_5646_ = lean_box(0);
v___x_5647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
return v___x_5647_;
}
}
v___jp_5648_:
{
lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; uint8_t v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; 
v___x_5653_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_5654_ = lean_string_append(v___y_5652_, v___x_5653_);
v___x_5655_ = lean_uint32_to_nat(v___y_5649_);
v___x_5656_ = l_Nat_reprFast(v___x_5655_);
v___x_5657_ = lean_string_append(v___x_5654_, v___x_5656_);
lean_dec_ref(v___x_5656_);
v___x_5658_ = 3;
v___x_5659_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5659_, 0, v___x_5657_);
lean_ctor_set_uint8(v___x_5659_, sizeof(void*)*1, v___x_5658_);
lean_inc_ref(v___y_5650_);
v___x_5660_ = lean_apply_2(v___y_5650_, v___x_5659_, lean_box(0));
v___y_5643_ = v___y_5651_;
goto v___jp_5642_;
}
v___jp_5665_:
{
uint32_t v___x_5669_; uint8_t v___x_5670_; uint8_t v___x_5671_; 
v___x_5669_ = 0;
v___x_5670_ = lean_uint32_dec_eq(v___y_5666_, v___x_5669_);
v___x_5671_ = lean_bool_not(v___x_5670_);
if (v___x_5671_ == 0)
{
lean_dec_ref(v_scope_5662_);
v___y_5643_ = v___y_5667_;
goto v___jp_5642_;
}
else
{
lean_object* v_s_5672_; 
v_s_5672_ = lean_ctor_get(v_scope_5662_, 0);
lean_inc_ref(v_s_5672_);
lean_dec_ref(v_scope_5662_);
v___y_5649_ = v___y_5666_;
v___y_5650_ = v___y_5668_;
v___y_5651_ = v___y_5667_;
v___y_5652_ = v_s_5672_;
goto v___jp_5648_;
}
}
v___jp_5673_:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; uint8_t v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5681_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_5682_ = lean_string_append(v___y_5680_, v___x_5681_);
lean_inc(v___y_5674_);
lean_inc(v___y_5678_);
lean_inc_ref(v___y_5675_);
v___x_5683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5683_, 0, v___y_5675_);
lean_ctor_set(v___x_5683_, 1, v___y_5678_);
lean_ctor_set(v___x_5683_, 2, v___y_5674_);
v___x_5684_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5683_, v___y_5674_);
lean_dec_ref_known(v___x_5683_, 3);
v___x_5685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5685_, 0, v___y_5675_);
lean_ctor_set(v___x_5685_, 1, v___y_5678_);
lean_ctor_set(v___x_5685_, 2, v___x_5684_);
v___x_5686_ = l_String_Slice_toString(v___x_5685_);
lean_dec_ref_known(v___x_5685_, 3);
v___x_5687_ = lean_string_append(v___x_5682_, v___x_5686_);
lean_dec_ref(v___x_5686_);
v___x_5688_ = 2;
v___x_5689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5689_, 0, v___x_5687_);
lean_ctor_set_uint8(v___x_5689_, sizeof(void*)*1, v___x_5688_);
lean_inc_ref(v___y_5676_);
v___x_5690_ = lean_apply_2(v___y_5676_, v___x_5689_, lean_box(0));
v___y_5666_ = v___y_5677_;
v___y_5667_ = v___y_5679_;
v___y_5668_ = v___y_5676_;
goto v___jp_5665_;
}
v___jp_5691_:
{
lean_object* v___x_5697_; uint8_t v___x_5698_; 
v___x_5697_ = lean_string_utf8_byte_size(v___y_5692_);
v___x_5698_ = lean_nat_dec_eq(v___x_5697_, v___y_5693_);
if (v___x_5698_ == 0)
{
lean_object* v_s_5699_; 
v_s_5699_ = lean_ctor_get(v_scope_5662_, 0);
lean_inc_ref(v_s_5699_);
v___y_5674_ = v___x_5697_;
v___y_5675_ = v___y_5692_;
v___y_5676_ = v___y_5696_;
v___y_5677_ = v___y_5694_;
v___y_5678_ = v___y_5693_;
v___y_5679_ = v___y_5695_;
v___y_5680_ = v_s_5699_;
goto v___jp_5673_;
}
else
{
lean_dec(v___y_5693_);
lean_dec_ref(v___y_5692_);
v___y_5666_ = v___y_5694_;
v___y_5667_ = v___y_5695_;
v___y_5668_ = v___y_5696_;
goto v___jp_5665_;
}
}
v___jp_5700_:
{
lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; uint8_t v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
v___x_5707_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_5708_ = lean_string_append(v___y_5706_, v___x_5707_);
v___x_5709_ = lean_string_append(v___x_5708_, v___y_5705_);
v___x_5710_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_5711_ = lean_string_append(v___x_5709_, v___x_5710_);
v___x_5712_ = 3;
v___x_5713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*1, v___x_5712_);
lean_inc_ref(v___y_5640_);
v___x_5714_ = lean_apply_2(v___y_5640_, v___x_5713_, lean_box(0));
v___y_5692_ = v___y_5701_;
v___y_5693_ = v___y_5703_;
v___y_5694_ = v___y_5702_;
v___y_5695_ = v___y_5704_;
v___y_5696_ = v___y_5640_;
goto v___jp_5691_;
}
v___jp_5715_:
{
lean_object* v_s_5721_; 
v_s_5721_ = lean_ctor_get(v_scope_5662_, 0);
lean_inc_ref(v_s_5721_);
v___y_5701_ = v___y_5716_;
v___y_5702_ = v___y_5718_;
v___y_5703_ = v___y_5717_;
v___y_5704_ = v___y_5719_;
v___y_5705_ = v___y_5720_;
v___y_5706_ = v_s_5721_;
goto v___jp_5700_;
}
v___jp_5722_:
{
lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; uint8_t v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5724_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5725_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_5726_ = lean_box(0);
v___x_5727_ = lean_unsigned_to_nat(0u);
v___x_5728_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5729_ = 1;
v___x_5730_ = 0;
v___x_5731_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5731_, 0, v___x_5724_);
lean_ctor_set(v___x_5731_, 1, v___x_5725_);
lean_ctor_set(v___x_5731_, 2, v_a_5723_);
lean_ctor_set(v___x_5731_, 3, v___x_5726_);
lean_ctor_set(v___x_5731_, 4, v___x_5728_);
lean_ctor_set_uint8(v___x_5731_, sizeof(void*)*5, v___x_5729_);
lean_ctor_set_uint8(v___x_5731_, sizeof(void*)*5 + 1, v___x_5730_);
v___x_5732_ = lean_io_process_spawn(v___x_5731_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; lean_object* v_stdout_5734_; lean_object* v_stderr_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc(v_a_5733_);
lean_dec_ref_known(v___x_5732_, 1);
v_stdout_5734_ = lean_ctor_get(v_a_5733_, 1);
lean_inc_n(v_stdout_5734_, 2);
v_stderr_5735_ = lean_ctor_get(v_a_5733_, 2);
v___x_5736_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_5737_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_5637_, v_stderr_5735_, v_stdout_5734_, v___x_5736_, v___y_5640_);
if (lean_obj_tag(v___x_5737_) == 0)
{
lean_object* v_a_5738_; lean_object* v___x_5739_; 
v_a_5738_ = lean_ctor_get(v___x_5737_, 0);
lean_inc(v_a_5738_);
lean_dec_ref_known(v___x_5737_, 1);
v___x_5739_ = lean_io_process_child_wait(v___x_5724_, v_a_5733_);
lean_dec(v_a_5733_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_object* v_a_5740_; lean_object* v___x_5741_; 
v_a_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_a_5740_);
lean_dec_ref_known(v___x_5739_, 1);
v___x_5741_ = l_IO_FS_Handle_readToEnd(v_stdout_5734_);
lean_dec(v_stdout_5734_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_object* v_a_5742_; uint8_t v_didError_5743_; lean_object* v_numSuccesses_5744_; lean_object* v___x_5745_; uint8_t v___x_5746_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref_known(v___x_5741_, 1);
v_didError_5743_ = lean_ctor_get_uint8(v_a_5738_, sizeof(void*)*1);
v_numSuccesses_5744_ = lean_ctor_get(v_a_5738_, 0);
lean_inc(v_numSuccesses_5744_);
lean_dec(v_a_5738_);
v___x_5745_ = lean_array_get_size(v_infos_5663_);
lean_dec_ref(v_infos_5663_);
v___x_5746_ = lean_nat_dec_lt(v_numSuccesses_5744_, v___x_5745_);
lean_dec(v_numSuccesses_5744_);
if (v___x_5746_ == 0)
{
uint32_t v___x_5747_; 
v___x_5747_ = lean_unbox_uint32(v_a_5740_);
lean_dec(v_a_5740_);
v___y_5692_ = v_a_5742_;
v___y_5693_ = v___x_5727_;
v___y_5694_ = v___x_5747_;
v___y_5695_ = v_didError_5743_;
v___y_5696_ = v___y_5640_;
goto v___jp_5691_;
}
else
{
if (v_kind_5661_ == 0)
{
lean_object* v___x_5748_; uint32_t v___x_5749_; 
v___x_5748_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_5749_ = lean_unbox_uint32(v_a_5740_);
lean_dec(v_a_5740_);
v___y_5716_ = v_a_5742_;
v___y_5717_ = v___x_5727_;
v___y_5718_ = v___x_5749_;
v___y_5719_ = v_didError_5743_;
v___y_5720_ = v___x_5748_;
goto v___jp_5715_;
}
else
{
lean_object* v___x_5750_; uint32_t v___x_5751_; 
v___x_5750_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_5751_ = lean_unbox_uint32(v_a_5740_);
lean_dec(v_a_5740_);
v___y_5716_ = v_a_5742_;
v___y_5717_ = v___x_5727_;
v___y_5718_ = v___x_5751_;
v___y_5719_ = v_didError_5743_;
v___y_5720_ = v___x_5750_;
goto v___jp_5715_;
}
}
}
else
{
lean_object* v_a_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5764_; 
lean_dec(v_a_5740_);
lean_dec(v_a_5738_);
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
v_a_5752_ = lean_ctor_get(v___x_5741_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5741_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5754_ = v___x_5741_;
v_isShared_5755_ = v_isSharedCheck_5764_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_a_5752_);
lean_dec(v___x_5741_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5764_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5756_; uint8_t v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5762_; 
v___x_5756_ = lean_io_error_to_string(v_a_5752_);
v___x_5757_ = 3;
v___x_5758_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5758_, 0, v___x_5756_);
lean_ctor_set_uint8(v___x_5758_, sizeof(void*)*1, v___x_5757_);
lean_inc_ref(v___y_5640_);
v___x_5759_ = lean_apply_2(v___y_5640_, v___x_5758_, lean_box(0));
v___x_5760_ = lean_box(0);
if (v_isShared_5755_ == 0)
{
lean_ctor_set(v___x_5754_, 0, v___x_5760_);
v___x_5762_ = v___x_5754_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v___x_5760_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
else
{
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5777_; 
lean_dec(v_a_5738_);
lean_dec(v_stdout_5734_);
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
v_a_5765_ = lean_ctor_get(v___x_5739_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5767_ = v___x_5739_;
v_isShared_5768_ = v_isSharedCheck_5777_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5739_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5777_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5769_; uint8_t v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5775_; 
v___x_5769_ = lean_io_error_to_string(v_a_5765_);
v___x_5770_ = 3;
v___x_5771_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5771_, 0, v___x_5769_);
lean_ctor_set_uint8(v___x_5771_, sizeof(void*)*1, v___x_5770_);
lean_inc_ref(v___y_5640_);
v___x_5772_ = lean_apply_2(v___y_5640_, v___x_5771_, lean_box(0));
v___x_5773_ = lean_box(0);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 0, v___x_5773_);
v___x_5775_ = v___x_5767_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v___x_5773_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
}
else
{
lean_object* v_a_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5785_; 
lean_dec(v_stdout_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
v_a_5778_ = lean_ctor_get(v___x_5737_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5737_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5780_ = v___x_5737_;
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_a_5778_);
lean_dec(v___x_5737_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5783_; 
if (v_isShared_5781_ == 0)
{
v___x_5783_ = v___x_5780_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5798_; 
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
lean_dec_ref(v_cfg_5637_);
v_a_5786_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5788_ = v___x_5732_;
v_isShared_5789_ = v_isSharedCheck_5798_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5732_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5798_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5790_; uint8_t v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5796_; 
v___x_5790_ = lean_io_error_to_string(v_a_5786_);
v___x_5791_ = 3;
v___x_5792_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5792_, 0, v___x_5790_);
lean_ctor_set_uint8(v___x_5792_, sizeof(void*)*1, v___x_5791_);
lean_inc_ref(v___y_5640_);
v___x_5793_ = lean_apply_2(v___y_5640_, v___x_5792_, lean_box(0));
v___x_5794_ = lean_box(0);
if (v_isShared_5789_ == 0)
{
lean_ctor_set(v___x_5788_, 0, v___x_5794_);
v___x_5796_ = v___x_5788_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5794_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
}
v___jp_5799_:
{
lean_object* v___x_5800_; 
v___x_5800_ = lean_io_prim_handle_flush(v_h_5638_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; 
lean_dec_ref_known(v___x_5800_, 1);
v___x_5801_ = lean_unsigned_to_nat(11u);
v___x_5802_ = lean_mk_empty_array_with_capacity(v___x_5801_);
lean_dec_ref(v___x_5802_);
v___x_5803_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_5804_ = lean_array_push(v___x_5803_, v_path_5639_);
v_a_5723_ = v___x_5804_;
goto v___jp_5722_;
}
else
{
lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5817_; 
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
lean_dec_ref(v_path_5639_);
lean_dec_ref(v_cfg_5637_);
v_a_5805_ = lean_ctor_get(v___x_5800_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v___x_5800_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5807_ = v___x_5800_;
v_isShared_5808_ = v_isSharedCheck_5817_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_a_5805_);
lean_dec(v___x_5800_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5817_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5809_; uint8_t v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5815_; 
v___x_5809_ = lean_io_error_to_string(v_a_5805_);
v___x_5810_ = 3;
v___x_5811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5811_, 0, v___x_5809_);
lean_ctor_set_uint8(v___x_5811_, sizeof(void*)*1, v___x_5810_);
lean_inc_ref(v___y_5640_);
v___x_5812_ = lean_apply_2(v___y_5640_, v___x_5811_, lean_box(0));
v___x_5813_ = lean_box(0);
if (v_isShared_5808_ == 0)
{
lean_ctor_set(v___x_5807_, 0, v___x_5813_);
v___x_5815_ = v___x_5807_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
v___jp_5818_:
{
if (lean_obj_tag(v___y_5819_) == 0)
{
lean_dec_ref_known(v___y_5819_, 1);
goto v___jp_5799_;
}
else
{
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
lean_dec_ref(v_path_5639_);
lean_dec_ref(v_cfg_5637_);
return v___y_5819_;
}
}
v___jp_5820_:
{
lean_object* v___x_5821_; 
v___x_5821_ = lean_io_prim_handle_flush(v_h_5638_);
if (lean_obj_tag(v___x_5821_) == 0)
{
lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
lean_dec_ref_known(v___x_5821_, 1);
v___x_5822_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5823_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5824_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5825_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_5826_ = lean_unsigned_to_nat(17u);
v___x_5827_ = lean_mk_empty_array_with_capacity(v___x_5826_);
lean_dec_ref(v___x_5827_);
v___x_5828_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_5664_);
v___x_5829_ = lean_array_push(v___x_5828_, v_key_5664_);
v___x_5830_ = lean_array_push(v___x_5829_, v___x_5822_);
v___x_5831_ = lean_array_push(v___x_5830_, v___x_5823_);
v___x_5832_ = lean_array_push(v___x_5831_, v___x_5824_);
v___x_5833_ = lean_array_push(v___x_5832_, v___x_5825_);
v___x_5834_ = lean_array_push(v___x_5833_, v_path_5639_);
v_a_5723_ = v___x_5834_;
goto v___jp_5722_;
}
else
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5847_; 
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
lean_dec_ref(v_path_5639_);
lean_dec_ref(v_cfg_5637_);
v_a_5835_ = lean_ctor_get(v___x_5821_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5837_ = v___x_5821_;
v_isShared_5838_ = v_isSharedCheck_5847_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5821_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5847_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5839_; uint8_t v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5845_; 
v___x_5839_ = lean_io_error_to_string(v_a_5835_);
v___x_5840_ = 3;
v___x_5841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5841_, 0, v___x_5839_);
lean_ctor_set_uint8(v___x_5841_, sizeof(void*)*1, v___x_5840_);
lean_inc_ref(v___y_5640_);
v___x_5842_ = lean_apply_2(v___y_5640_, v___x_5841_, lean_box(0));
v___x_5843_ = lean_box(0);
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 0, v___x_5843_);
v___x_5845_ = v___x_5837_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5843_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
}
v___jp_5848_:
{
if (lean_obj_tag(v___y_5849_) == 0)
{
lean_dec_ref_known(v___y_5849_, 1);
goto v___jp_5820_;
}
else
{
lean_dec_ref(v_infos_5663_);
lean_dec_ref(v_scope_5662_);
lean_dec_ref(v_path_5639_);
lean_dec_ref(v_cfg_5637_);
return v___y_5849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object* v_cfg_5872_, lean_object* v_h_5873_, lean_object* v_path_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(v_cfg_5872_, v_h_5873_, v_path_5874_, v___y_5875_);
lean_dec_ref(v___y_5875_);
lean_dec(v_h_5873_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object* v_a_5878_, lean_object* v_cfg_5879_){
_start:
{
lean_object* v___f_5881_; lean_object* v___x_5882_; 
v___f_5881_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed), 5, 1);
lean_closure_set(v___f_5881_, 0, v_cfg_5879_);
v___x_5882_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5881_, v_a_5878_);
return v___x_5882_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object* v_a_5883_, lean_object* v_cfg_5884_, lean_object* v_a_5885_){
_start:
{
lean_object* v_res_5886_; 
v_res_5886_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_5883_, v_cfg_5884_);
lean_dec_ref(v_a_5883_);
return v_res_5886_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(lean_object* v_infos_5887_, lean_object* v_url_5888_, lean_object* v_h_5889_, lean_object* v_path_5890_, lean_object* v___y_5891_){
_start:
{
uint32_t v___y_5894_; lean_object* v___y_5895_; lean_object* v___y_5906_; lean_object* v___y_5907_; lean_object* v___y_5908_; uint32_t v___y_5909_; lean_object* v_a_5910_; uint8_t v___y_5938_; lean_object* v___y_5939_; lean_object* v___y_5940_; uint32_t v___y_5941_; lean_object* v_msg_5942_; lean_object* v___y_5943_; lean_object* v___y_5957_; uint8_t v___y_5958_; lean_object* v___y_5959_; lean_object* v___y_5960_; uint32_t v___y_5961_; lean_object* v_msg_5962_; lean_object* v___y_5963_; lean_object* v___y_5974_; lean_object* v___y_5975_; uint8_t v___y_5976_; lean_object* v___y_5977_; uint32_t v___y_5978_; lean_object* v___y_5979_; lean_object* v_msg_5980_; lean_object* v___y_5981_; lean_object* v___y_5994_; uint8_t v___y_5995_; lean_object* v___y_5996_; lean_object* v___y_5997_; uint32_t v___y_5998_; size_t v_sz_6016_; size_t v___x_6017_; lean_object* v___x_6018_; lean_object* v_body_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v_sz_6016_ = lean_array_size(v_infos_5887_);
v___x_6017_ = ((size_t)0ULL);
lean_inc_ref(v_infos_5887_);
v___x_6018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_6016_, v___x_6017_, v_infos_5887_);
v_body_6019_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_6019_, 0, v___x_6018_);
v___x_6020_ = l_Lean_Json_compress(v_body_6019_);
v___x_6021_ = lean_io_prim_handle_put_str(v_h_5889_, v___x_6020_);
lean_dec_ref(v___x_6020_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_object* v___x_6022_; 
lean_dec_ref_known(v___x_6021_, 1);
v___x_6022_ = lean_io_prim_handle_flush(v_h_5889_);
if (lean_obj_tag(v___x_6022_) == 0)
{
lean_object* v___y_6024_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; uint8_t v___x_6128_; 
lean_dec_ref_known(v___x_6022_, 1);
v___x_6107_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_6108_ = lean_string_append(v___x_6107_, v_path_5890_);
v___x_6109_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_6110_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_6111_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_6112_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_6113_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_6114_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_6115_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_6116_ = lean_unsigned_to_nat(12u);
v___x_6117_ = lean_mk_empty_array_with_capacity(v___x_6116_);
lean_dec_ref(v___x_6117_);
v___x_6118_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_6119_ = lean_array_push(v___x_6118_, v___x_6108_);
v___x_6120_ = lean_array_push(v___x_6119_, v___x_6109_);
v___x_6121_ = lean_array_push(v___x_6120_, v___x_6110_);
v___x_6122_ = lean_array_push(v___x_6121_, v___x_6111_);
v___x_6123_ = lean_array_push(v___x_6122_, v___x_6112_);
v___x_6124_ = lean_array_push(v___x_6123_, v___x_6113_);
v___x_6125_ = lean_array_push(v___x_6124_, v___x_6114_);
v___x_6126_ = lean_array_push(v___x_6125_, v___x_6115_);
v___x_6127_ = l_Lake_Reservoir_lakeHeaders;
v___x_6128_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_6128_ == 0)
{
v___y_6024_ = v___x_6126_;
goto v___jp_6023_;
}
else
{
uint8_t v___x_6129_; 
v___x_6129_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
if (v___x_6129_ == 0)
{
if (v___x_6128_ == 0)
{
v___y_6024_ = v___x_6126_;
goto v___jp_6023_;
}
else
{
size_t v___x_6130_; lean_object* v___x_6131_; 
v___x_6130_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_6131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_6127_, v___x_6017_, v___x_6130_, v___x_6126_);
v___y_6024_ = v___x_6131_;
goto v___jp_6023_;
}
}
else
{
size_t v___x_6132_; lean_object* v___x_6133_; 
v___x_6132_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_6133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_6127_, v___x_6017_, v___x_6132_, v___x_6126_);
v___y_6024_ = v___x_6133_;
goto v___jp_6023_;
}
}
v___jp_6023_:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; uint8_t v___x_6031_; uint8_t v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; uint8_t v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6025_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_6026_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
lean_inc_ref(v_url_5888_);
v___x_6027_ = lean_array_push(v___y_6024_, v_url_5888_);
v___x_6028_ = lean_box(0);
v___x_6029_ = lean_unsigned_to_nat(0u);
v___x_6030_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_6031_ = 1;
v___x_6032_ = 0;
v___x_6033_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_6033_, 0, v___x_6025_);
lean_ctor_set(v___x_6033_, 1, v___x_6026_);
lean_ctor_set(v___x_6033_, 2, v___x_6027_);
lean_ctor_set(v___x_6033_, 3, v___x_6028_);
lean_ctor_set(v___x_6033_, 4, v___x_6030_);
lean_ctor_set_uint8(v___x_6033_, sizeof(void*)*5, v___x_6031_);
lean_ctor_set_uint8(v___x_6033_, sizeof(void*)*5 + 1, v___x_6032_);
lean_inc_ref(v___x_6033_);
v___x_6034_ = l_Lake_mkCmdLog(v___x_6033_);
v___x_6035_ = 0;
v___x_6036_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6036_, 0, v___x_6034_);
lean_ctor_set_uint8(v___x_6036_, sizeof(void*)*1, v___x_6035_);
lean_inc_ref(v___y_5891_);
v___x_6037_ = lean_apply_2(v___y_5891_, v___x_6036_, lean_box(0));
v___x_6038_ = l_IO_Process_output(v___x_6033_, v___x_6028_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; lean_object* v___x_6041_; uint8_t v_isShared_6042_; uint8_t v_isSharedCheck_6093_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6093_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6093_ == 0)
{
v___x_6041_ = v___x_6038_;
v_isShared_6042_ = v_isSharedCheck_6093_;
goto v_resetjp_6040_;
}
else
{
lean_inc(v_a_6039_);
lean_dec(v___x_6038_);
v___x_6041_ = lean_box(0);
v_isShared_6042_ = v_isSharedCheck_6093_;
goto v_resetjp_6040_;
}
v_resetjp_6040_:
{
uint32_t v_exitCode_6043_; lean_object* v_stdout_6044_; lean_object* v_stderr_6045_; lean_object* v___x_6046_; 
v_exitCode_6043_ = lean_ctor_get_uint32(v_a_6039_, sizeof(void*)*2);
v_stdout_6044_ = lean_ctor_get(v_a_6039_, 0);
lean_inc_ref_n(v_stdout_6044_, 2);
v_stderr_6045_ = lean_ctor_get(v_a_6039_, 1);
lean_inc_ref(v_stderr_6045_);
lean_dec(v_a_6039_);
v___x_6046_ = l_Lean_Json_parse(v_stdout_6044_);
if (lean_obj_tag(v___x_6046_) == 0)
{
lean_dec_ref_known(v___x_6046_, 1);
lean_del_object(v___x_6041_);
lean_dec_ref(v_infos_5887_);
v___y_5994_ = v_stdout_6044_;
v___y_5995_ = v___x_6035_;
v___y_5996_ = v___x_6029_;
v___y_5997_ = v_stderr_6045_;
v___y_5998_ = v_exitCode_6043_;
goto v___jp_5993_;
}
else
{
lean_object* v_a_6047_; lean_object* v___x_6048_; 
v_a_6047_ = lean_ctor_get(v___x_6046_, 0);
lean_inc(v_a_6047_);
lean_dec_ref_known(v___x_6046_, 1);
v___x_6048_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_6047_);
if (lean_obj_tag(v___x_6048_) == 0)
{
lean_dec_ref_known(v___x_6048_, 1);
lean_del_object(v___x_6041_);
lean_dec_ref(v_infos_5887_);
v___y_5994_ = v_stdout_6044_;
v___y_5995_ = v___x_6035_;
v___y_5996_ = v___x_6029_;
v___y_5997_ = v_stderr_6045_;
v___y_5998_ = v_exitCode_6043_;
goto v___jp_5993_;
}
else
{
lean_object* v_a_6049_; 
lean_dec_ref(v_stderr_6045_);
lean_dec_ref(v_stdout_6044_);
v_a_6049_ = lean_ctor_get(v___x_6048_, 0);
lean_inc(v_a_6049_);
lean_dec_ref_known(v___x_6048_, 1);
if (lean_obj_tag(v_a_6049_) == 0)
{
lean_object* v_a_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; uint8_t v___x_6053_; 
v_a_6050_ = lean_ctor_get(v_a_6049_, 0);
lean_inc(v_a_6050_);
lean_dec_ref_known(v_a_6049_, 1);
v___x_6051_ = lean_array_get_size(v_infos_5887_);
v___x_6052_ = lean_array_get_size(v_a_6050_);
v___x_6053_ = lean_nat_dec_eq(v___x_6051_, v___x_6052_);
if (v___x_6053_ == 0)
{
lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; uint8_t v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6069_; 
lean_dec(v_a_6050_);
lean_dec_ref(v_infos_5887_);
v___x_6054_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_6055_ = lean_string_append(v___x_6054_, v_url_5888_);
lean_dec_ref(v_url_5888_);
v___x_6056_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_6057_ = lean_string_append(v___x_6055_, v___x_6056_);
v___x_6058_ = l_Nat_reprFast(v___x_6051_);
v___x_6059_ = lean_string_append(v___x_6057_, v___x_6058_);
lean_dec_ref(v___x_6058_);
v___x_6060_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_6061_ = lean_string_append(v___x_6059_, v___x_6060_);
v___x_6062_ = l_Nat_reprFast(v___x_6052_);
v___x_6063_ = lean_string_append(v___x_6061_, v___x_6062_);
lean_dec_ref(v___x_6062_);
v___x_6064_ = 3;
v___x_6065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6065_, 0, v___x_6063_);
lean_ctor_set_uint8(v___x_6065_, sizeof(void*)*1, v___x_6064_);
lean_inc_ref(v___y_5891_);
v___x_6066_ = lean_apply_2(v___y_5891_, v___x_6065_, lean_box(0));
v___x_6067_ = lean_box(0);
if (v_isShared_6042_ == 0)
{
lean_ctor_set_tag(v___x_6041_, 1);
lean_ctor_set(v___x_6041_, 0, v___x_6067_);
v___x_6069_ = v___x_6041_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v___x_6067_);
v___x_6069_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
return v___x_6069_;
}
}
else
{
lean_object* v___x_6071_; lean_object* v___x_6073_; 
lean_dec_ref(v_url_5888_);
v___x_6071_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_6050_, v___x_6051_, v___x_6051_, v_infos_5887_);
lean_dec(v_a_6050_);
if (v_isShared_6042_ == 0)
{
lean_ctor_set(v___x_6041_, 0, v___x_6071_);
v___x_6073_ = v___x_6041_;
goto v_reusejp_6072_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v___x_6071_);
v___x_6073_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6072_;
}
v_reusejp_6072_:
{
return v___x_6073_;
}
}
}
else
{
lean_object* v_status_6075_; lean_object* v_message_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; uint8_t v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6091_; 
lean_dec_ref(v_infos_5887_);
v_status_6075_ = lean_ctor_get(v_a_6049_, 0);
lean_inc(v_status_6075_);
v_message_6076_ = lean_ctor_get(v_a_6049_, 1);
lean_inc_ref(v_message_6076_);
lean_dec_ref_known(v_a_6049_, 2);
v___x_6077_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_6078_ = l_Nat_reprFast(v_status_6075_);
v___x_6079_ = lean_string_append(v___x_6077_, v___x_6078_);
lean_dec_ref(v___x_6078_);
v___x_6080_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_6081_ = lean_string_append(v___x_6079_, v___x_6080_);
v___x_6082_ = lean_string_append(v___x_6081_, v_url_5888_);
lean_dec_ref(v_url_5888_);
v___x_6083_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_6084_ = lean_string_append(v___x_6082_, v___x_6083_);
v___x_6085_ = lean_string_append(v___x_6084_, v_message_6076_);
lean_dec_ref(v_message_6076_);
v___x_6086_ = 3;
v___x_6087_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6087_, 0, v___x_6085_);
lean_ctor_set_uint8(v___x_6087_, sizeof(void*)*1, v___x_6086_);
lean_inc_ref(v___y_5891_);
v___x_6088_ = lean_apply_2(v___y_5891_, v___x_6087_, lean_box(0));
v___x_6089_ = lean_box(0);
if (v_isShared_6042_ == 0)
{
lean_ctor_set_tag(v___x_6041_, 1);
lean_ctor_set(v___x_6041_, 0, v___x_6089_);
v___x_6091_ = v___x_6041_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6092_; 
v_reuseFailAlloc_6092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6092_, 0, v___x_6089_);
v___x_6091_ = v_reuseFailAlloc_6092_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
return v___x_6091_;
}
}
}
}
}
}
else
{
lean_object* v_a_6094_; lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6106_; 
lean_dec_ref(v_url_5888_);
lean_dec_ref(v_infos_5887_);
v_a_6094_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6096_ = v___x_6038_;
v_isShared_6097_ = v_isSharedCheck_6106_;
goto v_resetjp_6095_;
}
else
{
lean_inc(v_a_6094_);
lean_dec(v___x_6038_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6106_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
lean_object* v___x_6098_; uint8_t v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6104_; 
v___x_6098_ = lean_io_error_to_string(v_a_6094_);
v___x_6099_ = 3;
v___x_6100_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6100_, 0, v___x_6098_);
lean_ctor_set_uint8(v___x_6100_, sizeof(void*)*1, v___x_6099_);
lean_inc_ref(v___y_5891_);
v___x_6101_ = lean_apply_2(v___y_5891_, v___x_6100_, lean_box(0));
v___x_6102_ = lean_box(0);
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 0, v___x_6102_);
v___x_6104_ = v___x_6096_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6102_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
}
else
{
lean_object* v_a_6134_; lean_object* v___x_6136_; uint8_t v_isShared_6137_; uint8_t v_isSharedCheck_6146_; 
lean_dec_ref(v_url_5888_);
lean_dec_ref(v_infos_5887_);
v_a_6134_ = lean_ctor_get(v___x_6022_, 0);
v_isSharedCheck_6146_ = !lean_is_exclusive(v___x_6022_);
if (v_isSharedCheck_6146_ == 0)
{
v___x_6136_ = v___x_6022_;
v_isShared_6137_ = v_isSharedCheck_6146_;
goto v_resetjp_6135_;
}
else
{
lean_inc(v_a_6134_);
lean_dec(v___x_6022_);
v___x_6136_ = lean_box(0);
v_isShared_6137_ = v_isSharedCheck_6146_;
goto v_resetjp_6135_;
}
v_resetjp_6135_:
{
lean_object* v___x_6138_; uint8_t v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6144_; 
v___x_6138_ = lean_io_error_to_string(v_a_6134_);
v___x_6139_ = 3;
v___x_6140_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set_uint8(v___x_6140_, sizeof(void*)*1, v___x_6139_);
lean_inc_ref(v___y_5891_);
v___x_6141_ = lean_apply_2(v___y_5891_, v___x_6140_, lean_box(0));
v___x_6142_ = lean_box(0);
if (v_isShared_6137_ == 0)
{
lean_ctor_set(v___x_6136_, 0, v___x_6142_);
v___x_6144_ = v___x_6136_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v___x_6142_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
}
}
else
{
lean_object* v_a_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6159_; 
lean_dec_ref(v_url_5888_);
lean_dec_ref(v_infos_5887_);
v_a_6147_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6159_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6159_ == 0)
{
v___x_6149_ = v___x_6021_;
v_isShared_6150_ = v_isSharedCheck_6159_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_a_6147_);
lean_dec(v___x_6021_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6159_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v___x_6151_; uint8_t v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6157_; 
v___x_6151_ = lean_io_error_to_string(v_a_6147_);
v___x_6152_ = 3;
v___x_6153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6153_, 0, v___x_6151_);
lean_ctor_set_uint8(v___x_6153_, sizeof(void*)*1, v___x_6152_);
lean_inc_ref(v___y_5891_);
v___x_6154_ = lean_apply_2(v___y_5891_, v___x_6153_, lean_box(0));
v___x_6155_ = lean_box(0);
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 0, v___x_6155_);
v___x_6157_ = v___x_6149_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6155_);
v___x_6157_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
return v___x_6157_;
}
}
}
v___jp_5893_:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; uint8_t v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5896_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_5897_ = lean_uint32_to_nat(v___y_5894_);
v___x_5898_ = l_Nat_reprFast(v___x_5897_);
v___x_5899_ = lean_string_append(v___x_5896_, v___x_5898_);
lean_dec_ref(v___x_5898_);
v___x_5900_ = 3;
v___x_5901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5901_, 0, v___x_5899_);
lean_ctor_set_uint8(v___x_5901_, sizeof(void*)*1, v___x_5900_);
lean_inc_ref(v___y_5895_);
v___x_5902_ = lean_apply_2(v___y_5895_, v___x_5901_, lean_box(0));
v___x_5903_ = lean_box(0);
v___x_5904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5903_);
return v___x_5904_;
}
v___jp_5905_:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; uint8_t v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; uint8_t v___x_5927_; 
v___x_5911_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5912_ = lean_string_append(v___x_5911_, v_url_5888_);
lean_dec_ref(v_url_5888_);
v___x_5913_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_5914_ = lean_string_append(v___x_5912_, v___x_5913_);
v___x_5915_ = lean_string_append(v___x_5914_, v_a_5910_);
lean_dec_ref(v_a_5910_);
v___x_5916_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_5917_ = lean_string_append(v___x_5915_, v___x_5916_);
v___x_5918_ = lean_string_utf8_byte_size(v___y_5908_);
lean_inc(v___y_5907_);
v___x_5919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5919_, 0, v___y_5908_);
lean_ctor_set(v___x_5919_, 1, v___y_5907_);
lean_ctor_set(v___x_5919_, 2, v___x_5918_);
v___x_5920_ = l_String_Slice_trimAscii(v___x_5919_);
v___x_5921_ = l_String_Slice_toString(v___x_5920_);
lean_dec_ref(v___x_5920_);
v___x_5922_ = lean_string_append(v___x_5917_, v___x_5921_);
lean_dec_ref(v___x_5921_);
v___x_5923_ = 3;
v___x_5924_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5924_, 0, v___x_5922_);
lean_ctor_set_uint8(v___x_5924_, sizeof(void*)*1, v___x_5923_);
lean_inc_ref(v___y_5891_);
v___x_5925_ = lean_apply_2(v___y_5891_, v___x_5924_, lean_box(0));
v___x_5926_ = lean_string_utf8_byte_size(v___y_5906_);
v___x_5927_ = lean_nat_dec_eq(v___x_5926_, v___y_5907_);
if (v___x_5927_ == 0)
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; uint8_t v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5928_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
lean_inc(v___y_5907_);
lean_inc_ref(v___y_5906_);
v___x_5929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5929_, 0, v___y_5906_);
lean_ctor_set(v___x_5929_, 1, v___y_5907_);
lean_ctor_set(v___x_5929_, 2, v___x_5926_);
v___x_5930_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5929_, v___x_5926_);
lean_dec_ref_known(v___x_5929_, 3);
v___x_5931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5931_, 0, v___y_5906_);
lean_ctor_set(v___x_5931_, 1, v___y_5907_);
lean_ctor_set(v___x_5931_, 2, v___x_5930_);
v___x_5932_ = l_String_Slice_toString(v___x_5931_);
lean_dec_ref_known(v___x_5931_, 3);
v___x_5933_ = lean_string_append(v___x_5928_, v___x_5932_);
lean_dec_ref(v___x_5932_);
v___x_5934_ = 2;
v___x_5935_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set_uint8(v___x_5935_, sizeof(void*)*1, v___x_5934_);
lean_inc_ref(v___y_5891_);
v___x_5936_ = lean_apply_2(v___y_5891_, v___x_5935_, lean_box(0));
v___y_5894_ = v___y_5909_;
v___y_5895_ = v___y_5891_;
goto v___jp_5893_;
}
else
{
lean_dec(v___y_5907_);
lean_dec_ref(v___y_5906_);
v___y_5894_ = v___y_5909_;
v___y_5895_ = v___y_5891_;
goto v___jp_5893_;
}
}
v___jp_5937_:
{
uint8_t v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5944_ = 3;
v___x_5945_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5945_, 0, v_msg_5942_);
lean_ctor_set_uint8(v___x_5945_, sizeof(void*)*1, v___x_5944_);
lean_inc_ref_n(v___y_5943_, 2);
v___x_5946_ = lean_apply_2(v___y_5943_, v___x_5945_, lean_box(0));
v___x_5947_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_5948_ = lean_string_utf8_byte_size(v___y_5940_);
lean_inc(v___y_5939_);
lean_inc_ref(v___y_5940_);
v___x_5949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5949_, 0, v___y_5940_);
lean_ctor_set(v___x_5949_, 1, v___y_5939_);
lean_ctor_set(v___x_5949_, 2, v___x_5948_);
v___x_5950_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5949_, v___x_5948_);
lean_dec_ref_known(v___x_5949_, 3);
v___x_5951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5951_, 0, v___y_5940_);
lean_ctor_set(v___x_5951_, 1, v___y_5939_);
lean_ctor_set(v___x_5951_, 2, v___x_5950_);
v___x_5952_ = l_String_Slice_toString(v___x_5951_);
lean_dec_ref_known(v___x_5951_, 3);
v___x_5953_ = lean_string_append(v___x_5947_, v___x_5952_);
lean_dec_ref(v___x_5952_);
v___x_5954_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set_uint8(v___x_5954_, sizeof(void*)*1, v___y_5938_);
v___x_5955_ = lean_apply_2(v___y_5943_, v___x_5954_, lean_box(0));
v___y_5894_ = v___y_5941_;
v___y_5895_ = v___y_5943_;
goto v___jp_5893_;
}
v___jp_5956_:
{
lean_object* v___x_5964_; uint8_t v___x_5965_; 
v___x_5964_ = lean_string_utf8_byte_size(v___y_5957_);
v___x_5965_ = lean_nat_dec_eq(v___x_5964_, v___y_5959_);
if (v___x_5965_ == 0)
{
lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5966_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5967_ = lean_string_append(v_msg_5962_, v___x_5966_);
lean_inc_n(v___y_5959_, 2);
lean_inc_ref(v___y_5957_);
v___x_5968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5968_, 0, v___y_5957_);
lean_ctor_set(v___x_5968_, 1, v___y_5959_);
lean_ctor_set(v___x_5968_, 2, v___x_5964_);
v___x_5969_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5968_, v___x_5964_);
lean_dec_ref_known(v___x_5968_, 3);
v___x_5970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5970_, 0, v___y_5957_);
lean_ctor_set(v___x_5970_, 1, v___y_5959_);
lean_ctor_set(v___x_5970_, 2, v___x_5969_);
v___x_5971_ = l_String_Slice_toString(v___x_5970_);
lean_dec_ref_known(v___x_5970_, 3);
v___x_5972_ = lean_string_append(v___x_5967_, v___x_5971_);
lean_dec_ref(v___x_5971_);
v___y_5938_ = v___y_5958_;
v___y_5939_ = v___y_5959_;
v___y_5940_ = v___y_5960_;
v___y_5941_ = v___y_5961_;
v_msg_5942_ = v___x_5972_;
v___y_5943_ = v___y_5963_;
goto v___jp_5937_;
}
else
{
lean_dec_ref(v___y_5957_);
v___y_5938_ = v___y_5958_;
v___y_5939_ = v___y_5959_;
v___y_5940_ = v___y_5960_;
v___y_5941_ = v___y_5961_;
v_msg_5942_ = v_msg_5962_;
v___y_5943_ = v___y_5963_;
goto v___jp_5937_;
}
}
v___jp_5973_:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
v___x_5982_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_5983_ = lean_string_append(v_msg_5980_, v___x_5982_);
v___x_5984_ = lean_string_append(v___x_5983_, v_url_5888_);
lean_dec_ref(v_url_5888_);
v___x_5985_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_5986_ = l_Lake_JsonObject_getJson_x3f(v___y_5979_, v___x_5985_);
lean_dec(v___y_5979_);
if (lean_obj_tag(v___x_5986_) == 0)
{
v___y_5957_ = v___y_5974_;
v___y_5958_ = v___y_5976_;
v___y_5959_ = v___y_5975_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5978_;
v_msg_5962_ = v___x_5984_;
v___y_5963_ = v___y_5981_;
goto v___jp_5956_;
}
else
{
lean_object* v_val_5987_; lean_object* v___x_5988_; 
v_val_5987_ = lean_ctor_get(v___x_5986_, 0);
lean_inc(v_val_5987_);
lean_dec_ref_known(v___x_5986_, 1);
v___x_5988_ = l_Lean_Json_getStr_x3f(v_val_5987_);
if (lean_obj_tag(v___x_5988_) == 0)
{
lean_dec_ref_known(v___x_5988_, 1);
v___y_5957_ = v___y_5974_;
v___y_5958_ = v___y_5976_;
v___y_5959_ = v___y_5975_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5978_;
v_msg_5962_ = v___x_5984_;
v___y_5963_ = v___y_5981_;
goto v___jp_5956_;
}
else
{
if (lean_obj_tag(v___x_5988_) == 1)
{
lean_object* v_a_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v_a_5989_ = lean_ctor_get(v___x_5988_, 0);
lean_inc(v_a_5989_);
lean_dec_ref_known(v___x_5988_, 1);
v___x_5990_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
v___x_5991_ = lean_string_append(v___x_5984_, v___x_5990_);
v___x_5992_ = lean_string_append(v___x_5991_, v_a_5989_);
lean_dec(v_a_5989_);
v___y_5957_ = v___y_5974_;
v___y_5958_ = v___y_5976_;
v___y_5959_ = v___y_5975_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5978_;
v_msg_5962_ = v___x_5992_;
v___y_5963_ = v___y_5981_;
goto v___jp_5956_;
}
else
{
lean_dec_ref_known(v___x_5988_, 1);
v___y_5957_ = v___y_5974_;
v___y_5958_ = v___y_5976_;
v___y_5959_ = v___y_5975_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5978_;
v_msg_5962_ = v___x_5984_;
v___y_5963_ = v___y_5981_;
goto v___jp_5956_;
}
}
}
}
v___jp_5993_:
{
lean_object* v___x_5999_; 
lean_inc_ref(v___y_5997_);
v___x_5999_ = l_Lean_Json_parse(v___y_5997_);
if (lean_obj_tag(v___x_5999_) == 0)
{
lean_object* v_a_6000_; 
v_a_6000_ = lean_ctor_get(v___x_5999_, 0);
lean_inc(v_a_6000_);
lean_dec_ref_known(v___x_5999_, 1);
v___y_5906_ = v___y_5994_;
v___y_5907_ = v___y_5996_;
v___y_5908_ = v___y_5997_;
v___y_5909_ = v___y_5998_;
v_a_5910_ = v_a_6000_;
goto v___jp_5905_;
}
else
{
lean_object* v_a_6001_; lean_object* v___x_6002_; 
v_a_6001_ = lean_ctor_get(v___x_5999_, 0);
lean_inc(v_a_6001_);
lean_dec_ref_known(v___x_5999_, 1);
v___x_6002_ = l_Lean_Json_getObj_x3f(v_a_6001_);
if (lean_obj_tag(v___x_6002_) == 0)
{
lean_object* v_a_6003_; 
v_a_6003_ = lean_ctor_get(v___x_6002_, 0);
lean_inc(v_a_6003_);
lean_dec_ref_known(v___x_6002_, 1);
v___y_5906_ = v___y_5994_;
v___y_5907_ = v___y_5996_;
v___y_5908_ = v___y_5997_;
v___y_5909_ = v___y_5998_;
v_a_5910_ = v_a_6003_;
goto v___jp_5905_;
}
else
{
lean_object* v_a_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v_a_6004_ = lean_ctor_get(v___x_6002_, 0);
lean_inc(v_a_6004_);
lean_dec_ref_known(v___x_6002_, 1);
v___x_6005_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_6006_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_6007_ = l_Lake_JsonObject_getJson_x3f(v_a_6004_, v___x_6006_);
if (lean_obj_tag(v___x_6007_) == 0)
{
v___y_5974_ = v___y_5994_;
v___y_5975_ = v___y_5996_;
v___y_5976_ = v___y_5995_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v___y_5998_;
v___y_5979_ = v_a_6004_;
v_msg_5980_ = v___x_6005_;
v___y_5981_ = v___y_5891_;
goto v___jp_5973_;
}
else
{
lean_object* v_val_6008_; lean_object* v___x_6009_; 
v_val_6008_ = lean_ctor_get(v___x_6007_, 0);
lean_inc(v_val_6008_);
lean_dec_ref_known(v___x_6007_, 1);
v___x_6009_ = l_Lean_Json_getNat_x3f(v_val_6008_);
if (lean_obj_tag(v___x_6009_) == 0)
{
lean_dec_ref_known(v___x_6009_, 1);
v___y_5974_ = v___y_5994_;
v___y_5975_ = v___y_5996_;
v___y_5976_ = v___y_5995_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v___y_5998_;
v___y_5979_ = v_a_6004_;
v_msg_5980_ = v___x_6005_;
v___y_5981_ = v___y_5891_;
goto v___jp_5973_;
}
else
{
if (lean_obj_tag(v___x_6009_) == 1)
{
lean_object* v_a_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
v_a_6010_ = lean_ctor_get(v___x_6009_, 0);
lean_inc(v_a_6010_);
lean_dec_ref_known(v___x_6009_, 1);
v___x_6011_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_6012_ = l_Nat_reprFast(v_a_6010_);
v___x_6013_ = lean_string_append(v___x_6011_, v___x_6012_);
lean_dec_ref(v___x_6012_);
v___x_6014_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_6015_ = lean_string_append(v___x_6013_, v___x_6014_);
v___y_5974_ = v___y_5994_;
v___y_5975_ = v___y_5996_;
v___y_5976_ = v___y_5995_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v___y_5998_;
v___y_5979_ = v_a_6004_;
v_msg_5980_ = v___x_6015_;
v___y_5981_ = v___y_5891_;
goto v___jp_5973_;
}
else
{
lean_dec_ref_known(v___x_6009_, 1);
v___y_5974_ = v___y_5994_;
v___y_5975_ = v___y_5996_;
v___y_5976_ = v___y_5995_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v___y_5998_;
v___y_5979_ = v_a_6004_;
v_msg_5980_ = v___x_6005_;
v___y_5981_ = v___y_5891_;
goto v___jp_5973_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed(lean_object* v_infos_6160_, lean_object* v_url_6161_, lean_object* v_h_6162_, lean_object* v_path_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
lean_object* v_res_6166_; 
v_res_6166_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(v_infos_6160_, v_url_6161_, v_h_6162_, v_path_6163_, v___y_6164_);
lean_dec_ref(v___y_6164_);
lean_dec_ref(v_path_6163_);
lean_dec(v_h_6162_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object* v_a_6167_, lean_object* v_url_6168_, lean_object* v_infos_6169_){
_start:
{
lean_object* v___f_6171_; lean_object* v___x_6172_; 
v___f_6171_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_6171_, 0, v_infos_6169_);
lean_closure_set(v___f_6171_, 1, v_url_6168_);
v___x_6172_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_6171_, v_a_6167_);
return v___x_6172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object* v_a_6173_, lean_object* v_url_6174_, lean_object* v_infos_6175_, lean_object* v_a_6176_){
_start:
{
lean_object* v_res_6177_; 
v_res_6177_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6173_, v_url_6174_, v_infos_6175_);
lean_dec_ref(v_a_6173_);
return v_res_6177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(lean_object* v_service_6178_, lean_object* v_scope_6179_, lean_object* v_cache_6180_, uint8_t v_force_6181_, lean_object* v_as_6182_, size_t v_i_6183_, size_t v_stop_6184_, lean_object* v_b_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v_a_6189_; lean_object* v___y_6194_; lean_object* v___y_6205_; lean_object* v___y_6216_; uint8_t v___x_6226_; 
v___x_6226_ = lean_usize_dec_eq(v_i_6183_, v_stop_6184_);
if (v___x_6226_ == 0)
{
lean_object* v___x_6227_; uint64_t v_hash_6228_; lean_object* v_ext_6229_; lean_object* v_url_6230_; lean_object* v___y_6232_; uint8_t v_a_6233_; lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___y_6309_; lean_object* v___x_6388_; lean_object* v___x_6389_; uint8_t v___x_6390_; 
v___x_6227_ = lean_array_uget_borrowed(v_as_6182_, v_i_6183_);
v_hash_6228_ = lean_ctor_get_uint64(v___x_6227_, sizeof(void*)*1);
v_ext_6229_ = lean_ctor_get(v___x_6227_, 0);
lean_inc_ref(v_scope_6179_);
lean_inc_ref(v_service_6178_);
v_url_6230_ = l_Lake_CacheService_artifactUrl(v_hash_6228_, v_service_6178_, v_scope_6179_);
v___x_6306_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
lean_inc_ref(v_cache_6180_);
v___x_6307_ = l_System_FilePath_join(v_cache_6180_, v___x_6306_);
v___x_6388_ = lean_string_utf8_byte_size(v_ext_6229_);
v___x_6389_ = lean_unsigned_to_nat(0u);
v___x_6390_ = lean_nat_dec_eq(v___x_6388_, v___x_6389_);
if (v___x_6390_ == 0)
{
lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; 
v___x_6391_ = l_Lake_lowerHexUInt64(v_hash_6228_);
v___x_6392_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_6393_ = lean_string_append(v___x_6391_, v___x_6392_);
v___x_6394_ = lean_string_append(v___x_6393_, v_ext_6229_);
v___y_6309_ = v___x_6394_;
goto v___jp_6308_;
}
else
{
lean_object* v___x_6395_; 
v___x_6395_ = l_Lake_lowerHexUInt64(v_hash_6228_);
v___y_6309_ = v___x_6395_;
goto v___jp_6308_;
}
v___jp_6231_:
{
if (v_a_6233_ == 0)
{
lean_object* v_infos_6234_; lean_object* v_indices_6235_; lean_object* v___x_6236_; 
v_infos_6234_ = lean_ctor_get(v_b_6185_, 0);
v_indices_6235_ = lean_ctor_get(v_b_6185_, 1);
v___x_6236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_indices_6235_, v_hash_6228_);
if (lean_obj_tag(v___x_6236_) == 1)
{
lean_object* v_val_6237_; lean_object* v___x_6238_; uint8_t v___x_6239_; 
lean_dec_ref(v_url_6230_);
v_val_6237_ = lean_ctor_get(v___x_6236_, 0);
lean_inc(v_val_6237_);
lean_dec_ref_known(v___x_6236_, 1);
v___x_6238_ = lean_array_get_size(v_infos_6234_);
v___x_6239_ = lean_nat_dec_lt(v_val_6237_, v___x_6238_);
if (v___x_6239_ == 0)
{
lean_dec(v_val_6237_);
lean_dec_ref(v___y_6232_);
lean_inc_ref(v_infos_6234_);
v___y_6205_ = v_infos_6234_;
goto v___jp_6204_;
}
else
{
lean_object* v_v_6240_; lean_object* v_url_6241_; uint64_t v_hash_6242_; lean_object* v_path_6243_; lean_object* v_extraPaths_6244_; lean_object* v___x_6246_; uint8_t v_isShared_6247_; uint8_t v_isSharedCheck_6255_; 
v_v_6240_ = lean_array_fget(v_infos_6234_, v_val_6237_);
v_url_6241_ = lean_ctor_get(v_v_6240_, 0);
v_hash_6242_ = lean_ctor_get_uint64(v_v_6240_, sizeof(void*)*3);
v_path_6243_ = lean_ctor_get(v_v_6240_, 1);
v_extraPaths_6244_ = lean_ctor_get(v_v_6240_, 2);
v_isSharedCheck_6255_ = !lean_is_exclusive(v_v_6240_);
if (v_isSharedCheck_6255_ == 0)
{
v___x_6246_ = v_v_6240_;
v_isShared_6247_ = v_isSharedCheck_6255_;
goto v_resetjp_6245_;
}
else
{
lean_inc(v_extraPaths_6244_);
lean_inc(v_path_6243_);
lean_inc(v_url_6241_);
lean_dec(v_v_6240_);
v___x_6246_ = lean_box(0);
v_isShared_6247_ = v_isSharedCheck_6255_;
goto v_resetjp_6245_;
}
v_resetjp_6245_:
{
lean_object* v___x_6248_; lean_object* v_xs_x27_6249_; lean_object* v___x_6250_; lean_object* v___x_6252_; 
v___x_6248_ = lean_box(0);
lean_inc_ref(v_infos_6234_);
v_xs_x27_6249_ = lean_array_fset(v_infos_6234_, v_val_6237_, v___x_6248_);
v___x_6250_ = lean_array_push(v_extraPaths_6244_, v___y_6232_);
if (v_isShared_6247_ == 0)
{
lean_ctor_set(v___x_6246_, 2, v___x_6250_);
v___x_6252_ = v___x_6246_;
goto v_reusejp_6251_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_url_6241_);
lean_ctor_set(v_reuseFailAlloc_6254_, 1, v_path_6243_);
lean_ctor_set(v_reuseFailAlloc_6254_, 2, v___x_6250_);
lean_ctor_set_uint64(v_reuseFailAlloc_6254_, sizeof(void*)*3, v_hash_6242_);
v___x_6252_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6251_;
}
v_reusejp_6251_:
{
lean_object* v___x_6253_; 
v___x_6253_ = lean_array_fset(v_xs_x27_6249_, v_val_6237_, v___x_6252_);
lean_dec(v_val_6237_);
v___y_6205_ = v___x_6253_;
goto v___jp_6204_;
}
}
}
}
else
{
lean_object* v___x_6257_; uint8_t v_isShared_6258_; uint8_t v_isSharedCheck_6267_; 
lean_inc_ref(v_indices_6235_);
lean_inc_ref(v_infos_6234_);
lean_dec(v___x_6236_);
v_isSharedCheck_6267_ = !lean_is_exclusive(v_b_6185_);
if (v_isSharedCheck_6267_ == 0)
{
lean_object* v_unused_6268_; lean_object* v_unused_6269_; 
v_unused_6268_ = lean_ctor_get(v_b_6185_, 1);
lean_dec(v_unused_6268_);
v_unused_6269_ = lean_ctor_get(v_b_6185_, 0);
lean_dec(v_unused_6269_);
v___x_6257_ = v_b_6185_;
v_isShared_6258_ = v_isSharedCheck_6267_;
goto v_resetjp_6256_;
}
else
{
lean_dec(v_b_6185_);
v___x_6257_ = lean_box(0);
v_isShared_6258_ = v_isSharedCheck_6267_;
goto v_resetjp_6256_;
}
v_resetjp_6256_:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6265_; 
v___x_6259_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_6260_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6260_, 0, v_url_6230_);
lean_ctor_set(v___x_6260_, 1, v___y_6232_);
lean_ctor_set(v___x_6260_, 2, v___x_6259_);
lean_ctor_set_uint64(v___x_6260_, sizeof(void*)*3, v_hash_6228_);
lean_inc_ref(v_infos_6234_);
v___x_6261_ = lean_array_push(v_infos_6234_, v___x_6260_);
v___x_6262_ = lean_array_get_size(v_infos_6234_);
lean_dec_ref(v_infos_6234_);
v___x_6263_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6235_, v_hash_6228_, v___x_6262_);
if (v_isShared_6258_ == 0)
{
lean_ctor_set(v___x_6257_, 1, v___x_6263_);
lean_ctor_set(v___x_6257_, 0, v___x_6261_);
v___x_6265_ = v___x_6257_;
goto v_reusejp_6264_;
}
else
{
lean_object* v_reuseFailAlloc_6266_; 
v_reuseFailAlloc_6266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6266_, 0, v___x_6261_);
lean_ctor_set(v_reuseFailAlloc_6266_, 1, v___x_6263_);
v___x_6265_ = v_reuseFailAlloc_6266_;
goto v_reusejp_6264_;
}
v_reusejp_6264_:
{
v_a_6189_ = v___x_6265_;
goto v___jp_6188_;
}
}
}
}
else
{
lean_object* v_infos_6270_; lean_object* v_indices_6271_; lean_object* v___x_6272_; 
v_infos_6270_ = lean_ctor_get(v_b_6185_, 0);
v_indices_6271_ = lean_ctor_get(v_b_6185_, 1);
v___x_6272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_indices_6271_, v_hash_6228_);
if (lean_obj_tag(v___x_6272_) == 1)
{
lean_object* v_val_6273_; lean_object* v___x_6274_; uint8_t v___x_6275_; 
lean_dec_ref(v_url_6230_);
v_val_6273_ = lean_ctor_get(v___x_6272_, 0);
lean_inc(v_val_6273_);
lean_dec_ref_known(v___x_6272_, 1);
v___x_6274_ = lean_array_get_size(v_infos_6270_);
v___x_6275_ = lean_nat_dec_lt(v_val_6273_, v___x_6274_);
if (v___x_6275_ == 0)
{
lean_dec(v_val_6273_);
lean_dec_ref(v___y_6232_);
lean_inc_ref(v_infos_6270_);
v___y_6194_ = v_infos_6270_;
goto v___jp_6193_;
}
else
{
lean_object* v_v_6276_; lean_object* v_url_6277_; uint64_t v_hash_6278_; lean_object* v_path_6279_; lean_object* v_extraPaths_6280_; lean_object* v___x_6282_; uint8_t v_isShared_6283_; uint8_t v_isSharedCheck_6291_; 
v_v_6276_ = lean_array_fget(v_infos_6270_, v_val_6273_);
v_url_6277_ = lean_ctor_get(v_v_6276_, 0);
v_hash_6278_ = lean_ctor_get_uint64(v_v_6276_, sizeof(void*)*3);
v_path_6279_ = lean_ctor_get(v_v_6276_, 1);
v_extraPaths_6280_ = lean_ctor_get(v_v_6276_, 2);
v_isSharedCheck_6291_ = !lean_is_exclusive(v_v_6276_);
if (v_isSharedCheck_6291_ == 0)
{
v___x_6282_ = v_v_6276_;
v_isShared_6283_ = v_isSharedCheck_6291_;
goto v_resetjp_6281_;
}
else
{
lean_inc(v_extraPaths_6280_);
lean_inc(v_path_6279_);
lean_inc(v_url_6277_);
lean_dec(v_v_6276_);
v___x_6282_ = lean_box(0);
v_isShared_6283_ = v_isSharedCheck_6291_;
goto v_resetjp_6281_;
}
v_resetjp_6281_:
{
lean_object* v___x_6284_; lean_object* v_xs_x27_6285_; lean_object* v___x_6286_; lean_object* v___x_6288_; 
v___x_6284_ = lean_box(0);
lean_inc_ref(v_infos_6270_);
v_xs_x27_6285_ = lean_array_fset(v_infos_6270_, v_val_6273_, v___x_6284_);
v___x_6286_ = lean_array_push(v_extraPaths_6280_, v_path_6279_);
if (v_isShared_6283_ == 0)
{
lean_ctor_set(v___x_6282_, 2, v___x_6286_);
lean_ctor_set(v___x_6282_, 1, v___y_6232_);
v___x_6288_ = v___x_6282_;
goto v_reusejp_6287_;
}
else
{
lean_object* v_reuseFailAlloc_6290_; 
v_reuseFailAlloc_6290_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_url_6277_);
lean_ctor_set(v_reuseFailAlloc_6290_, 1, v___y_6232_);
lean_ctor_set(v_reuseFailAlloc_6290_, 2, v___x_6286_);
lean_ctor_set_uint64(v_reuseFailAlloc_6290_, sizeof(void*)*3, v_hash_6278_);
v___x_6288_ = v_reuseFailAlloc_6290_;
goto v_reusejp_6287_;
}
v_reusejp_6287_:
{
lean_object* v___x_6289_; 
v___x_6289_ = lean_array_fset(v_xs_x27_6285_, v_val_6273_, v___x_6288_);
lean_dec(v_val_6273_);
v___y_6194_ = v___x_6289_;
goto v___jp_6193_;
}
}
}
}
else
{
lean_object* v___x_6293_; uint8_t v_isShared_6294_; uint8_t v_isSharedCheck_6303_; 
lean_inc_ref(v_indices_6271_);
lean_inc_ref(v_infos_6270_);
lean_dec(v___x_6272_);
v_isSharedCheck_6303_ = !lean_is_exclusive(v_b_6185_);
if (v_isSharedCheck_6303_ == 0)
{
lean_object* v_unused_6304_; lean_object* v_unused_6305_; 
v_unused_6304_ = lean_ctor_get(v_b_6185_, 1);
lean_dec(v_unused_6304_);
v_unused_6305_ = lean_ctor_get(v_b_6185_, 0);
lean_dec(v_unused_6305_);
v___x_6293_ = v_b_6185_;
v_isShared_6294_ = v_isSharedCheck_6303_;
goto v_resetjp_6292_;
}
else
{
lean_dec(v_b_6185_);
v___x_6293_ = lean_box(0);
v_isShared_6294_ = v_isSharedCheck_6303_;
goto v_resetjp_6292_;
}
v_resetjp_6292_:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6301_; 
v___x_6295_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_6296_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6296_, 0, v_url_6230_);
lean_ctor_set(v___x_6296_, 1, v___y_6232_);
lean_ctor_set(v___x_6296_, 2, v___x_6295_);
lean_ctor_set_uint64(v___x_6296_, sizeof(void*)*3, v_hash_6228_);
lean_inc_ref(v_infos_6270_);
v___x_6297_ = lean_array_push(v_infos_6270_, v___x_6296_);
v___x_6298_ = lean_array_get_size(v_infos_6270_);
lean_dec_ref(v_infos_6270_);
v___x_6299_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6271_, v_hash_6228_, v___x_6298_);
if (v_isShared_6294_ == 0)
{
lean_ctor_set(v___x_6293_, 1, v___x_6299_);
lean_ctor_set(v___x_6293_, 0, v___x_6297_);
v___x_6301_ = v___x_6293_;
goto v_reusejp_6300_;
}
else
{
lean_object* v_reuseFailAlloc_6302_; 
v_reuseFailAlloc_6302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6302_, 0, v___x_6297_);
lean_ctor_set(v_reuseFailAlloc_6302_, 1, v___x_6299_);
v___x_6301_ = v_reuseFailAlloc_6302_;
goto v_reusejp_6300_;
}
v_reusejp_6300_:
{
v_a_6189_ = v___x_6301_;
goto v___jp_6188_;
}
}
}
}
}
v___jp_6308_:
{
lean_object* v_path_6310_; 
v_path_6310_ = l_System_FilePath_join(v___x_6307_, v___y_6309_);
if (v_force_6181_ == 0)
{
uint8_t v___x_6311_; lean_object* v___x_6312_; uint8_t v___x_6313_; 
v___x_6311_ = l_System_FilePath_pathExists(v_path_6310_);
v___x_6312_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6313_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_6313_ == 0)
{
v___y_6232_ = v_path_6310_;
v_a_6233_ = v___x_6311_;
goto v___jp_6231_;
}
else
{
lean_object* v___x_6314_; uint8_t v___x_6315_; 
v___x_6314_ = lean_box(0);
v___x_6315_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_6315_ == 0)
{
if (v___x_6313_ == 0)
{
v___y_6232_ = v_path_6310_;
v_a_6233_ = v___x_6311_;
goto v___jp_6231_;
}
else
{
size_t v___x_6316_; size_t v___x_6317_; lean_object* v___x_6318_; 
v___x_6316_ = ((size_t)0ULL);
v___x_6317_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6312_, v___x_6316_, v___x_6317_, v___x_6314_, v___y_6186_);
if (lean_obj_tag(v___x_6318_) == 0)
{
lean_dec_ref_known(v___x_6318_, 1);
v___y_6232_ = v_path_6310_;
v_a_6233_ = v___x_6311_;
goto v___jp_6231_;
}
else
{
lean_object* v_a_6319_; lean_object* v___x_6321_; uint8_t v_isShared_6322_; uint8_t v_isSharedCheck_6326_; 
lean_dec_ref(v_path_6310_);
lean_dec_ref(v_url_6230_);
lean_dec_ref(v_b_6185_);
lean_dec_ref(v_cache_6180_);
lean_dec_ref(v_scope_6179_);
lean_dec_ref(v_service_6178_);
v_a_6319_ = lean_ctor_get(v___x_6318_, 0);
v_isSharedCheck_6326_ = !lean_is_exclusive(v___x_6318_);
if (v_isSharedCheck_6326_ == 0)
{
v___x_6321_ = v___x_6318_;
v_isShared_6322_ = v_isSharedCheck_6326_;
goto v_resetjp_6320_;
}
else
{
lean_inc(v_a_6319_);
lean_dec(v___x_6318_);
v___x_6321_ = lean_box(0);
v_isShared_6322_ = v_isSharedCheck_6326_;
goto v_resetjp_6320_;
}
v_resetjp_6320_:
{
lean_object* v___x_6324_; 
if (v_isShared_6322_ == 0)
{
v___x_6324_ = v___x_6321_;
goto v_reusejp_6323_;
}
else
{
lean_object* v_reuseFailAlloc_6325_; 
v_reuseFailAlloc_6325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6325_, 0, v_a_6319_);
v___x_6324_ = v_reuseFailAlloc_6325_;
goto v_reusejp_6323_;
}
v_reusejp_6323_:
{
return v___x_6324_;
}
}
}
}
}
else
{
size_t v___x_6327_; size_t v___x_6328_; lean_object* v___x_6329_; 
v___x_6327_ = ((size_t)0ULL);
v___x_6328_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6312_, v___x_6327_, v___x_6328_, v___x_6314_, v___y_6186_);
if (lean_obj_tag(v___x_6329_) == 0)
{
lean_dec_ref_known(v___x_6329_, 1);
v___y_6232_ = v_path_6310_;
v_a_6233_ = v___x_6311_;
goto v___jp_6231_;
}
else
{
lean_object* v_a_6330_; lean_object* v___x_6332_; uint8_t v_isShared_6333_; uint8_t v_isSharedCheck_6337_; 
lean_dec_ref(v_path_6310_);
lean_dec_ref(v_url_6230_);
lean_dec_ref(v_b_6185_);
lean_dec_ref(v_cache_6180_);
lean_dec_ref(v_scope_6179_);
lean_dec_ref(v_service_6178_);
v_a_6330_ = lean_ctor_get(v___x_6329_, 0);
v_isSharedCheck_6337_ = !lean_is_exclusive(v___x_6329_);
if (v_isSharedCheck_6337_ == 0)
{
v___x_6332_ = v___x_6329_;
v_isShared_6333_ = v_isSharedCheck_6337_;
goto v_resetjp_6331_;
}
else
{
lean_inc(v_a_6330_);
lean_dec(v___x_6329_);
v___x_6332_ = lean_box(0);
v_isShared_6333_ = v_isSharedCheck_6337_;
goto v_resetjp_6331_;
}
v_resetjp_6331_:
{
lean_object* v___x_6335_; 
if (v_isShared_6333_ == 0)
{
v___x_6335_ = v___x_6332_;
goto v_reusejp_6334_;
}
else
{
lean_object* v_reuseFailAlloc_6336_; 
v_reuseFailAlloc_6336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_a_6330_);
v___x_6335_ = v_reuseFailAlloc_6336_;
goto v_reusejp_6334_;
}
v_reusejp_6334_:
{
return v___x_6335_;
}
}
}
}
}
}
else
{
lean_object* v___x_6338_; 
v___x_6338_ = l_Lake_removeFileIfExists(v_path_6310_);
if (lean_obj_tag(v___x_6338_) == 0)
{
lean_object* v_infos_6339_; lean_object* v_indices_6340_; lean_object* v___x_6341_; 
lean_dec_ref_known(v___x_6338_, 1);
v_infos_6339_ = lean_ctor_get(v_b_6185_, 0);
v_indices_6340_ = lean_ctor_get(v_b_6185_, 1);
v___x_6341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_indices_6340_, v_hash_6228_);
if (lean_obj_tag(v___x_6341_) == 1)
{
lean_object* v_val_6342_; lean_object* v___x_6343_; uint8_t v___x_6344_; 
lean_dec_ref(v_url_6230_);
v_val_6342_ = lean_ctor_get(v___x_6341_, 0);
lean_inc(v_val_6342_);
lean_dec_ref_known(v___x_6341_, 1);
v___x_6343_ = lean_array_get_size(v_infos_6339_);
v___x_6344_ = lean_nat_dec_lt(v_val_6342_, v___x_6343_);
if (v___x_6344_ == 0)
{
lean_dec(v_val_6342_);
lean_dec_ref(v_path_6310_);
lean_inc_ref(v_infos_6339_);
v___y_6216_ = v_infos_6339_;
goto v___jp_6215_;
}
else
{
lean_object* v_v_6345_; lean_object* v_url_6346_; uint64_t v_hash_6347_; lean_object* v_path_6348_; lean_object* v_extraPaths_6349_; lean_object* v___x_6351_; uint8_t v_isShared_6352_; uint8_t v_isSharedCheck_6360_; 
v_v_6345_ = lean_array_fget(v_infos_6339_, v_val_6342_);
v_url_6346_ = lean_ctor_get(v_v_6345_, 0);
v_hash_6347_ = lean_ctor_get_uint64(v_v_6345_, sizeof(void*)*3);
v_path_6348_ = lean_ctor_get(v_v_6345_, 1);
v_extraPaths_6349_ = lean_ctor_get(v_v_6345_, 2);
v_isSharedCheck_6360_ = !lean_is_exclusive(v_v_6345_);
if (v_isSharedCheck_6360_ == 0)
{
v___x_6351_ = v_v_6345_;
v_isShared_6352_ = v_isSharedCheck_6360_;
goto v_resetjp_6350_;
}
else
{
lean_inc(v_extraPaths_6349_);
lean_inc(v_path_6348_);
lean_inc(v_url_6346_);
lean_dec(v_v_6345_);
v___x_6351_ = lean_box(0);
v_isShared_6352_ = v_isSharedCheck_6360_;
goto v_resetjp_6350_;
}
v_resetjp_6350_:
{
lean_object* v___x_6353_; lean_object* v_xs_x27_6354_; lean_object* v___x_6355_; lean_object* v___x_6357_; 
v___x_6353_ = lean_box(0);
lean_inc_ref(v_infos_6339_);
v_xs_x27_6354_ = lean_array_fset(v_infos_6339_, v_val_6342_, v___x_6353_);
v___x_6355_ = lean_array_push(v_extraPaths_6349_, v_path_6310_);
if (v_isShared_6352_ == 0)
{
lean_ctor_set(v___x_6351_, 2, v___x_6355_);
v___x_6357_ = v___x_6351_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_url_6346_);
lean_ctor_set(v_reuseFailAlloc_6359_, 1, v_path_6348_);
lean_ctor_set(v_reuseFailAlloc_6359_, 2, v___x_6355_);
lean_ctor_set_uint64(v_reuseFailAlloc_6359_, sizeof(void*)*3, v_hash_6347_);
v___x_6357_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
lean_object* v___x_6358_; 
v___x_6358_ = lean_array_fset(v_xs_x27_6354_, v_val_6342_, v___x_6357_);
lean_dec(v_val_6342_);
v___y_6216_ = v___x_6358_;
goto v___jp_6215_;
}
}
}
}
else
{
lean_object* v___x_6362_; uint8_t v_isShared_6363_; uint8_t v_isSharedCheck_6372_; 
lean_inc_ref(v_indices_6340_);
lean_inc_ref(v_infos_6339_);
lean_dec(v___x_6341_);
v_isSharedCheck_6372_ = !lean_is_exclusive(v_b_6185_);
if (v_isSharedCheck_6372_ == 0)
{
lean_object* v_unused_6373_; lean_object* v_unused_6374_; 
v_unused_6373_ = lean_ctor_get(v_b_6185_, 1);
lean_dec(v_unused_6373_);
v_unused_6374_ = lean_ctor_get(v_b_6185_, 0);
lean_dec(v_unused_6374_);
v___x_6362_ = v_b_6185_;
v_isShared_6363_ = v_isSharedCheck_6372_;
goto v_resetjp_6361_;
}
else
{
lean_dec(v_b_6185_);
v___x_6362_ = lean_box(0);
v_isShared_6363_ = v_isSharedCheck_6372_;
goto v_resetjp_6361_;
}
v_resetjp_6361_:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6370_; 
v___x_6364_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_6365_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6365_, 0, v_url_6230_);
lean_ctor_set(v___x_6365_, 1, v_path_6310_);
lean_ctor_set(v___x_6365_, 2, v___x_6364_);
lean_ctor_set_uint64(v___x_6365_, sizeof(void*)*3, v_hash_6228_);
lean_inc_ref(v_infos_6339_);
v___x_6366_ = lean_array_push(v_infos_6339_, v___x_6365_);
v___x_6367_ = lean_array_get_size(v_infos_6339_);
lean_dec_ref(v_infos_6339_);
v___x_6368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6340_, v_hash_6228_, v___x_6367_);
if (v_isShared_6363_ == 0)
{
lean_ctor_set(v___x_6362_, 1, v___x_6368_);
lean_ctor_set(v___x_6362_, 0, v___x_6366_);
v___x_6370_ = v___x_6362_;
goto v_reusejp_6369_;
}
else
{
lean_object* v_reuseFailAlloc_6371_; 
v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6371_, 0, v___x_6366_);
lean_ctor_set(v_reuseFailAlloc_6371_, 1, v___x_6368_);
v___x_6370_ = v_reuseFailAlloc_6371_;
goto v_reusejp_6369_;
}
v_reusejp_6369_:
{
v_a_6189_ = v___x_6370_;
goto v___jp_6188_;
}
}
}
}
else
{
lean_object* v_a_6375_; lean_object* v___x_6377_; uint8_t v_isShared_6378_; uint8_t v_isSharedCheck_6387_; 
lean_dec_ref(v_path_6310_);
lean_dec_ref(v_url_6230_);
lean_dec_ref(v_b_6185_);
lean_dec_ref(v_cache_6180_);
lean_dec_ref(v_scope_6179_);
lean_dec_ref(v_service_6178_);
v_a_6375_ = lean_ctor_get(v___x_6338_, 0);
v_isSharedCheck_6387_ = !lean_is_exclusive(v___x_6338_);
if (v_isSharedCheck_6387_ == 0)
{
v___x_6377_ = v___x_6338_;
v_isShared_6378_ = v_isSharedCheck_6387_;
goto v_resetjp_6376_;
}
else
{
lean_inc(v_a_6375_);
lean_dec(v___x_6338_);
v___x_6377_ = lean_box(0);
v_isShared_6378_ = v_isSharedCheck_6387_;
goto v_resetjp_6376_;
}
v_resetjp_6376_:
{
lean_object* v___x_6379_; uint8_t v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; lean_object* v___x_6385_; 
v___x_6379_ = lean_io_error_to_string(v_a_6375_);
v___x_6380_ = 3;
v___x_6381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6381_, 0, v___x_6379_);
lean_ctor_set_uint8(v___x_6381_, sizeof(void*)*1, v___x_6380_);
lean_inc_ref(v___y_6186_);
v___x_6382_ = lean_apply_2(v___y_6186_, v___x_6381_, lean_box(0));
v___x_6383_ = lean_box(0);
if (v_isShared_6378_ == 0)
{
lean_ctor_set(v___x_6377_, 0, v___x_6383_);
v___x_6385_ = v___x_6377_;
goto v_reusejp_6384_;
}
else
{
lean_object* v_reuseFailAlloc_6386_; 
v_reuseFailAlloc_6386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6386_, 0, v___x_6383_);
v___x_6385_ = v_reuseFailAlloc_6386_;
goto v_reusejp_6384_;
}
v_reusejp_6384_:
{
return v___x_6385_;
}
}
}
}
}
}
else
{
lean_object* v___x_6396_; 
lean_dec_ref(v_cache_6180_);
lean_dec_ref(v_scope_6179_);
lean_dec_ref(v_service_6178_);
v___x_6396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6396_, 0, v_b_6185_);
return v___x_6396_;
}
v___jp_6188_:
{
size_t v___x_6190_; size_t v___x_6191_; 
v___x_6190_ = ((size_t)1ULL);
v___x_6191_ = lean_usize_add(v_i_6183_, v___x_6190_);
v_i_6183_ = v___x_6191_;
v_b_6185_ = v_a_6189_;
goto _start;
}
v___jp_6193_:
{
lean_object* v_indices_6195_; lean_object* v___x_6197_; uint8_t v_isShared_6198_; uint8_t v_isSharedCheck_6202_; 
v_indices_6195_ = lean_ctor_get(v_b_6185_, 1);
v_isSharedCheck_6202_ = !lean_is_exclusive(v_b_6185_);
if (v_isSharedCheck_6202_ == 0)
{
lean_object* v_unused_6203_; 
v_unused_6203_ = lean_ctor_get(v_b_6185_, 0);
lean_dec(v_unused_6203_);
v___x_6197_ = v_b_6185_;
v_isShared_6198_ = v_isSharedCheck_6202_;
goto v_resetjp_6196_;
}
else
{
lean_inc(v_indices_6195_);
lean_dec(v_b_6185_);
v___x_6197_ = lean_box(0);
v_isShared_6198_ = v_isSharedCheck_6202_;
goto v_resetjp_6196_;
}
v_resetjp_6196_:
{
lean_object* v___x_6200_; 
if (v_isShared_6198_ == 0)
{
lean_ctor_set(v___x_6197_, 0, v___y_6194_);
v___x_6200_ = v___x_6197_;
goto v_reusejp_6199_;
}
else
{
lean_object* v_reuseFailAlloc_6201_; 
v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___y_6194_);
lean_ctor_set(v_reuseFailAlloc_6201_, 1, v_indices_6195_);
v___x_6200_ = v_reuseFailAlloc_6201_;
goto v_reusejp_6199_;
}
v_reusejp_6199_:
{
v_a_6189_ = v___x_6200_;
goto v___jp_6188_;
}
}
}
v___jp_6204_:
{
lean_object* v_indices_6206_; lean_object* v___x_6208_; uint8_t v_isShared_6209_; uint8_t v_isSharedCheck_6213_; 
v_indices_6206_ = lean_ctor_get(v_b_6185_, 1);
v_isSharedCheck_6213_ = !lean_is_exclusive(v_b_6185_);
if (v_isSharedCheck_6213_ == 0)
{
lean_object* v_unused_6214_; 
v_unused_6214_ = lean_ctor_get(v_b_6185_, 0);
lean_dec(v_unused_6214_);
v___x_6208_ = v_b_6185_;
v_isShared_6209_ = v_isSharedCheck_6213_;
goto v_resetjp_6207_;
}
else
{
lean_inc(v_indices_6206_);
lean_dec(v_b_6185_);
v___x_6208_ = lean_box(0);
v_isShared_6209_ = v_isSharedCheck_6213_;
goto v_resetjp_6207_;
}
v_resetjp_6207_:
{
lean_object* v___x_6211_; 
if (v_isShared_6209_ == 0)
{
lean_ctor_set(v___x_6208_, 0, v___y_6205_);
v___x_6211_ = v___x_6208_;
goto v_reusejp_6210_;
}
else
{
lean_object* v_reuseFailAlloc_6212_; 
v_reuseFailAlloc_6212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6212_, 0, v___y_6205_);
lean_ctor_set(v_reuseFailAlloc_6212_, 1, v_indices_6206_);
v___x_6211_ = v_reuseFailAlloc_6212_;
goto v_reusejp_6210_;
}
v_reusejp_6210_:
{
v_a_6189_ = v___x_6211_;
goto v___jp_6188_;
}
}
}
v___jp_6215_:
{
lean_object* v_indices_6217_; lean_object* v___x_6219_; uint8_t v_isShared_6220_; uint8_t v_isSharedCheck_6224_; 
v_indices_6217_ = lean_ctor_get(v_b_6185_, 1);
v_isSharedCheck_6224_ = !lean_is_exclusive(v_b_6185_);
if (v_isSharedCheck_6224_ == 0)
{
lean_object* v_unused_6225_; 
v_unused_6225_ = lean_ctor_get(v_b_6185_, 0);
lean_dec(v_unused_6225_);
v___x_6219_ = v_b_6185_;
v_isShared_6220_ = v_isSharedCheck_6224_;
goto v_resetjp_6218_;
}
else
{
lean_inc(v_indices_6217_);
lean_dec(v_b_6185_);
v___x_6219_ = lean_box(0);
v_isShared_6220_ = v_isSharedCheck_6224_;
goto v_resetjp_6218_;
}
v_resetjp_6218_:
{
lean_object* v___x_6222_; 
if (v_isShared_6220_ == 0)
{
lean_ctor_set(v___x_6219_, 0, v___y_6216_);
v___x_6222_ = v___x_6219_;
goto v_reusejp_6221_;
}
else
{
lean_object* v_reuseFailAlloc_6223_; 
v_reuseFailAlloc_6223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6223_, 0, v___y_6216_);
lean_ctor_set(v_reuseFailAlloc_6223_, 1, v_indices_6217_);
v___x_6222_ = v_reuseFailAlloc_6223_;
goto v_reusejp_6221_;
}
v_reusejp_6221_:
{
v_a_6189_ = v___x_6222_;
goto v___jp_6188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3___boxed(lean_object* v_service_6397_, lean_object* v_scope_6398_, lean_object* v_cache_6399_, lean_object* v_force_6400_, lean_object* v_as_6401_, lean_object* v_i_6402_, lean_object* v_stop_6403_, lean_object* v_b_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_){
_start:
{
uint8_t v_force_boxed_6407_; size_t v_i_boxed_6408_; size_t v_stop_boxed_6409_; lean_object* v_res_6410_; 
v_force_boxed_6407_ = lean_unbox(v_force_6400_);
v_i_boxed_6408_ = lean_unbox_usize(v_i_6402_);
lean_dec(v_i_6402_);
v_stop_boxed_6409_ = lean_unbox_usize(v_stop_6403_);
lean_dec(v_stop_6403_);
v_res_6410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6397_, v_scope_6398_, v_cache_6399_, v_force_boxed_6407_, v_as_6401_, v_i_boxed_6408_, v_stop_boxed_6409_, v_b_6404_, v___y_6405_);
lean_dec_ref(v___y_6405_);
lean_dec_ref(v_as_6401_);
return v_res_6410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object* v_as_6412_, size_t v_i_6413_, size_t v_stop_6414_, lean_object* v_b_6415_, lean_object* v___y_6416_){
_start:
{
lean_object* v_a_6419_; uint8_t v___x_6423_; 
v___x_6423_ = lean_usize_dec_eq(v_i_6413_, v_stop_6414_);
if (v___x_6423_ == 0)
{
lean_object* v___x_6424_; lean_object* v_a_6428_; lean_object* v_path_6444_; lean_object* v_extraPaths_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; uint8_t v___x_6448_; 
v___x_6424_ = lean_array_uget_borrowed(v_as_6412_, v_i_6413_);
v_path_6444_ = lean_ctor_get(v___x_6424_, 1);
v_extraPaths_6445_ = lean_ctor_get(v___x_6424_, 2);
v___x_6446_ = lean_array_get_size(v_extraPaths_6445_);
v___x_6447_ = lean_unsigned_to_nat(0u);
v___x_6448_ = lean_nat_dec_eq(v___x_6446_, v___x_6447_);
if (v___x_6448_ == 0)
{
lean_object* v___x_6449_; lean_object* v_val_6451_; lean_object* v___x_6477_; 
v___x_6449_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6477_ = l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(v_path_6444_, v_extraPaths_6445_);
if (lean_obj_tag(v___x_6477_) == 0)
{
lean_object* v_a_6478_; lean_object* v___x_6480_; uint8_t v_isShared_6481_; uint8_t v_isSharedCheck_6485_; 
v_a_6478_ = lean_ctor_get(v___x_6477_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___x_6477_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6480_ = v___x_6477_;
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
else
{
lean_inc(v_a_6478_);
lean_dec(v___x_6477_);
v___x_6480_ = lean_box(0);
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
v_resetjp_6479_:
{
lean_object* v___x_6483_; 
if (v_isShared_6481_ == 0)
{
lean_ctor_set_tag(v___x_6480_, 1);
v___x_6483_ = v___x_6480_;
goto v_reusejp_6482_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v_a_6478_);
v___x_6483_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6482_;
}
v_reusejp_6482_:
{
v_val_6451_ = v___x_6483_;
goto v___jp_6450_;
}
}
}
else
{
lean_object* v_a_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6493_; 
v_a_6486_ = lean_ctor_get(v___x_6477_, 0);
v_isSharedCheck_6493_ = !lean_is_exclusive(v___x_6477_);
if (v_isSharedCheck_6493_ == 0)
{
v___x_6488_ = v___x_6477_;
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_a_6486_);
lean_dec(v___x_6477_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
lean_object* v___x_6491_; 
if (v_isShared_6489_ == 0)
{
lean_ctor_set_tag(v___x_6488_, 0);
v___x_6491_ = v___x_6488_;
goto v_reusejp_6490_;
}
else
{
lean_object* v_reuseFailAlloc_6492_; 
v_reuseFailAlloc_6492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6492_, 0, v_a_6486_);
v___x_6491_ = v_reuseFailAlloc_6492_;
goto v_reusejp_6490_;
}
v_reusejp_6490_:
{
v_val_6451_ = v___x_6491_;
goto v___jp_6450_;
}
}
}
v___jp_6450_:
{
uint8_t v___x_6452_; 
v___x_6452_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_6452_ == 0)
{
v_a_6428_ = v_val_6451_;
goto v___jp_6427_;
}
else
{
lean_object* v___x_6453_; uint8_t v___x_6454_; 
v___x_6453_ = lean_box(0);
v___x_6454_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_6454_ == 0)
{
if (v___x_6452_ == 0)
{
v_a_6428_ = v_val_6451_;
goto v___jp_6427_;
}
else
{
size_t v___x_6455_; size_t v___x_6456_; lean_object* v___x_6457_; 
v___x_6455_ = ((size_t)0ULL);
v___x_6456_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6449_, v___x_6455_, v___x_6456_, v___x_6453_, v___y_6416_);
if (lean_obj_tag(v___x_6457_) == 0)
{
lean_dec_ref_known(v___x_6457_, 1);
v_a_6428_ = v_val_6451_;
goto v___jp_6427_;
}
else
{
lean_object* v_a_6458_; lean_object* v___x_6460_; uint8_t v_isShared_6461_; uint8_t v_isSharedCheck_6465_; 
lean_dec_ref(v_val_6451_);
lean_dec_ref(v_b_6415_);
v_a_6458_ = lean_ctor_get(v___x_6457_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6457_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6460_ = v___x_6457_;
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
else
{
lean_inc(v_a_6458_);
lean_dec(v___x_6457_);
v___x_6460_ = lean_box(0);
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
v_resetjp_6459_:
{
lean_object* v___x_6463_; 
if (v_isShared_6461_ == 0)
{
v___x_6463_ = v___x_6460_;
goto v_reusejp_6462_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_a_6458_);
v___x_6463_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6462_;
}
v_reusejp_6462_:
{
return v___x_6463_;
}
}
}
}
}
else
{
size_t v___x_6466_; size_t v___x_6467_; lean_object* v___x_6468_; 
v___x_6466_ = ((size_t)0ULL);
v___x_6467_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6449_, v___x_6466_, v___x_6467_, v___x_6453_, v___y_6416_);
if (lean_obj_tag(v___x_6468_) == 0)
{
lean_dec_ref_known(v___x_6468_, 1);
v_a_6428_ = v_val_6451_;
goto v___jp_6427_;
}
else
{
lean_object* v_a_6469_; lean_object* v___x_6471_; uint8_t v_isShared_6472_; uint8_t v_isSharedCheck_6476_; 
lean_dec_ref(v_val_6451_);
lean_dec_ref(v_b_6415_);
v_a_6469_ = lean_ctor_get(v___x_6468_, 0);
v_isSharedCheck_6476_ = !lean_is_exclusive(v___x_6468_);
if (v_isSharedCheck_6476_ == 0)
{
v___x_6471_ = v___x_6468_;
v_isShared_6472_ = v_isSharedCheck_6476_;
goto v_resetjp_6470_;
}
else
{
lean_inc(v_a_6469_);
lean_dec(v___x_6468_);
v___x_6471_ = lean_box(0);
v_isShared_6472_ = v_isSharedCheck_6476_;
goto v_resetjp_6470_;
}
v_resetjp_6470_:
{
lean_object* v___x_6474_; 
if (v_isShared_6472_ == 0)
{
v___x_6474_ = v___x_6471_;
goto v_reusejp_6473_;
}
else
{
lean_object* v_reuseFailAlloc_6475_; 
v_reuseFailAlloc_6475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_a_6469_);
v___x_6474_ = v_reuseFailAlloc_6475_;
goto v_reusejp_6473_;
}
v_reusejp_6473_:
{
return v___x_6474_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_6494_; lean_object* v___x_6497_; uint8_t v___x_6498_; 
v___x_6494_ = l_System_FilePath_pathExists(v_path_6444_);
v___x_6497_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6498_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_6498_ == 0)
{
goto v___jp_6495_;
}
else
{
lean_object* v___x_6499_; uint8_t v___x_6500_; 
v___x_6499_ = lean_box(0);
v___x_6500_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_6500_ == 0)
{
if (v___x_6498_ == 0)
{
goto v___jp_6495_;
}
else
{
size_t v___x_6501_; size_t v___x_6502_; lean_object* v___x_6503_; 
v___x_6501_ = ((size_t)0ULL);
v___x_6502_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6497_, v___x_6501_, v___x_6502_, v___x_6499_, v___y_6416_);
if (lean_obj_tag(v___x_6503_) == 0)
{
lean_dec_ref_known(v___x_6503_, 1);
goto v___jp_6495_;
}
else
{
lean_object* v_a_6504_; lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6511_; 
lean_dec_ref(v_b_6415_);
v_a_6504_ = lean_ctor_get(v___x_6503_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___x_6503_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6506_ = v___x_6503_;
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
else
{
lean_inc(v_a_6504_);
lean_dec(v___x_6503_);
v___x_6506_ = lean_box(0);
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
v_resetjp_6505_:
{
lean_object* v___x_6509_; 
if (v_isShared_6507_ == 0)
{
v___x_6509_ = v___x_6506_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6504_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
return v___x_6509_;
}
}
}
}
}
else
{
size_t v___x_6512_; size_t v___x_6513_; lean_object* v___x_6514_; 
v___x_6512_ = ((size_t)0ULL);
v___x_6513_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6497_, v___x_6512_, v___x_6513_, v___x_6499_, v___y_6416_);
if (lean_obj_tag(v___x_6514_) == 0)
{
lean_dec_ref_known(v___x_6514_, 1);
goto v___jp_6495_;
}
else
{
lean_object* v_a_6515_; lean_object* v___x_6517_; uint8_t v_isShared_6518_; uint8_t v_isSharedCheck_6522_; 
lean_dec_ref(v_b_6415_);
v_a_6515_ = lean_ctor_get(v___x_6514_, 0);
v_isSharedCheck_6522_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6522_ == 0)
{
v___x_6517_ = v___x_6514_;
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
else
{
lean_inc(v_a_6515_);
lean_dec(v___x_6514_);
v___x_6517_ = lean_box(0);
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
v_resetjp_6516_:
{
lean_object* v___x_6520_; 
if (v_isShared_6518_ == 0)
{
v___x_6520_ = v___x_6517_;
goto v_reusejp_6519_;
}
else
{
lean_object* v_reuseFailAlloc_6521_; 
v_reuseFailAlloc_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_a_6515_);
v___x_6520_ = v_reuseFailAlloc_6521_;
goto v_reusejp_6519_;
}
v_reusejp_6519_:
{
return v___x_6520_;
}
}
}
}
}
v___jp_6495_:
{
uint8_t v___x_6496_; 
v___x_6496_ = lean_bool_not(v___x_6494_);
if (v___x_6496_ == 0)
{
v_a_6419_ = v_b_6415_;
goto v___jp_6418_;
}
else
{
goto v___jp_6425_;
}
}
}
v___jp_6425_:
{
lean_object* v___x_6426_; 
lean_inc(v___x_6424_);
v___x_6426_ = lean_array_push(v_b_6415_, v___x_6424_);
v_a_6419_ = v___x_6426_;
goto v___jp_6418_;
}
v___jp_6427_:
{
if (lean_obj_tag(v_a_6428_) == 0)
{
lean_object* v_a_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6443_; 
v_a_6429_ = lean_ctor_get(v_a_6428_, 0);
v_isSharedCheck_6443_ = !lean_is_exclusive(v_a_6428_);
if (v_isSharedCheck_6443_ == 0)
{
v___x_6431_ = v_a_6428_;
v_isShared_6432_ = v_isSharedCheck_6443_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_a_6429_);
lean_dec(v_a_6428_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6443_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
if (lean_obj_tag(v_a_6429_) == 11)
{
lean_dec_ref_known(v_a_6429_, 2);
lean_del_object(v___x_6431_);
goto v___jp_6425_;
}
else
{
lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; uint8_t v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6441_; 
lean_dec_ref(v_b_6415_);
v___x_6433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___closed__0));
v___x_6434_ = lean_io_error_to_string(v_a_6429_);
v___x_6435_ = lean_string_append(v___x_6433_, v___x_6434_);
lean_dec_ref(v___x_6434_);
v___x_6436_ = 3;
v___x_6437_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6437_, 0, v___x_6435_);
lean_ctor_set_uint8(v___x_6437_, sizeof(void*)*1, v___x_6436_);
lean_inc_ref(v___y_6416_);
v___x_6438_ = lean_apply_2(v___y_6416_, v___x_6437_, lean_box(0));
v___x_6439_ = lean_box(0);
if (v_isShared_6432_ == 0)
{
lean_ctor_set_tag(v___x_6431_, 1);
lean_ctor_set(v___x_6431_, 0, v___x_6439_);
v___x_6441_ = v___x_6431_;
goto v_reusejp_6440_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v___x_6439_);
v___x_6441_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6440_;
}
v_reusejp_6440_:
{
return v___x_6441_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_6428_, 1);
v_a_6419_ = v_b_6415_;
goto v___jp_6418_;
}
}
}
else
{
lean_object* v___x_6523_; 
v___x_6523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6523_, 0, v_b_6415_);
return v___x_6523_;
}
v___jp_6418_:
{
size_t v___x_6420_; size_t v___x_6421_; 
v___x_6420_ = ((size_t)1ULL);
v___x_6421_ = lean_usize_add(v_i_6413_, v___x_6420_);
v_i_6413_ = v___x_6421_;
v_b_6415_ = v_a_6419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_as_6524_, lean_object* v_i_6525_, lean_object* v_stop_6526_, lean_object* v_b_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_){
_start:
{
size_t v_i_boxed_6530_; size_t v_stop_boxed_6531_; lean_object* v_res_6532_; 
v_i_boxed_6530_ = lean_unbox_usize(v_i_6525_);
lean_dec(v_i_6525_);
v_stop_boxed_6531_ = lean_unbox_usize(v_stop_6526_);
lean_dec(v_stop_6526_);
v_res_6532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_as_6524_, v_i_boxed_6530_, v_stop_boxed_6531_, v_b_6527_, v___y_6528_);
lean_dec_ref(v___y_6528_);
lean_dec_ref(v_as_6524_);
return v_res_6532_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_6537_, lean_object* v_cache_6538_, lean_object* v_service_6539_, lean_object* v_scope_6540_, uint8_t v_force_6541_, lean_object* v_a_6542_){
_start:
{
lean_object* v_a_6545_; lean_object* v_a_6567_; lean_object* v___y_6586_; lean_object* v___x_6596_; lean_object* v___x_6597_; uint8_t v___x_6598_; 
v___x_6596_ = lean_array_get_size(v_descrs_6537_);
v___x_6597_ = lean_unsigned_to_nat(0u);
v___x_6598_ = lean_nat_dec_eq(v___x_6596_, v___x_6597_);
if (v___x_6598_ == 0)
{
lean_object* v___x_6599_; lean_object* v_infos_6601_; lean_object* v___y_6612_; uint8_t v___x_6623_; 
v___x_6599_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_6623_ = lean_nat_dec_lt(v___x_6597_, v___x_6596_);
if (v___x_6623_ == 0)
{
v_infos_6601_ = v___x_6599_;
goto v___jp_6600_;
}
else
{
lean_object* v___x_6624_; uint8_t v___x_6625_; 
v___x_6624_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
v___x_6625_ = lean_nat_dec_le(v___x_6596_, v___x_6596_);
if (v___x_6625_ == 0)
{
if (v___x_6623_ == 0)
{
v_infos_6601_ = v___x_6599_;
goto v___jp_6600_;
}
else
{
size_t v___x_6626_; size_t v___x_6627_; lean_object* v___x_6628_; 
v___x_6626_ = ((size_t)0ULL);
v___x_6627_ = lean_usize_of_nat(v___x_6596_);
lean_inc_ref(v_cache_6538_);
lean_inc_ref(v_scope_6540_);
lean_inc_ref(v_service_6539_);
v___x_6628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6539_, v_scope_6540_, v_cache_6538_, v_force_6541_, v_descrs_6537_, v___x_6626_, v___x_6627_, v___x_6624_, v_a_6542_);
v___y_6612_ = v___x_6628_;
goto v___jp_6611_;
}
}
else
{
size_t v___x_6629_; size_t v___x_6630_; lean_object* v___x_6631_; 
v___x_6629_ = ((size_t)0ULL);
v___x_6630_ = lean_usize_of_nat(v___x_6596_);
lean_inc_ref(v_cache_6538_);
lean_inc_ref(v_scope_6540_);
lean_inc_ref(v_service_6539_);
v___x_6631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6539_, v_scope_6540_, v_cache_6538_, v_force_6541_, v_descrs_6537_, v___x_6629_, v___x_6630_, v___x_6624_, v_a_6542_);
v___y_6612_ = v___x_6631_;
goto v___jp_6611_;
}
}
v___jp_6600_:
{
lean_object* v___x_6602_; uint8_t v___x_6603_; 
v___x_6602_ = lean_array_get_size(v_infos_6601_);
v___x_6603_ = lean_nat_dec_lt(v___x_6597_, v___x_6602_);
if (v___x_6603_ == 0)
{
lean_dec_ref(v_infos_6601_);
v_a_6567_ = v___x_6599_;
goto v___jp_6566_;
}
else
{
uint8_t v___x_6604_; 
v___x_6604_ = lean_nat_dec_le(v___x_6602_, v___x_6602_);
if (v___x_6604_ == 0)
{
if (v___x_6603_ == 0)
{
lean_dec_ref(v_infos_6601_);
v_a_6567_ = v___x_6599_;
goto v___jp_6566_;
}
else
{
size_t v___x_6605_; size_t v___x_6606_; lean_object* v___x_6607_; 
v___x_6605_ = ((size_t)0ULL);
v___x_6606_ = lean_usize_of_nat(v___x_6602_);
v___x_6607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6601_, v___x_6605_, v___x_6606_, v___x_6599_, v_a_6542_);
lean_dec_ref(v_infos_6601_);
v___y_6586_ = v___x_6607_;
goto v___jp_6585_;
}
}
else
{
size_t v___x_6608_; size_t v___x_6609_; lean_object* v___x_6610_; 
v___x_6608_ = ((size_t)0ULL);
v___x_6609_ = lean_usize_of_nat(v___x_6602_);
v___x_6610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6601_, v___x_6608_, v___x_6609_, v___x_6599_, v_a_6542_);
lean_dec_ref(v_infos_6601_);
v___y_6586_ = v___x_6610_;
goto v___jp_6585_;
}
}
}
v___jp_6611_:
{
if (lean_obj_tag(v___y_6612_) == 0)
{
lean_object* v_a_6613_; lean_object* v_infos_6614_; 
v_a_6613_ = lean_ctor_get(v___y_6612_, 0);
lean_inc(v_a_6613_);
lean_dec_ref_known(v___y_6612_, 1);
v_infos_6614_ = lean_ctor_get(v_a_6613_, 0);
lean_inc_ref(v_infos_6614_);
lean_dec(v_a_6613_);
v_infos_6601_ = v_infos_6614_;
goto v___jp_6600_;
}
else
{
lean_object* v_a_6615_; lean_object* v___x_6617_; uint8_t v_isShared_6618_; uint8_t v_isSharedCheck_6622_; 
lean_dec_ref(v_scope_6540_);
lean_dec_ref(v_service_6539_);
lean_dec_ref(v_cache_6538_);
v_a_6615_ = lean_ctor_get(v___y_6612_, 0);
v_isSharedCheck_6622_ = !lean_is_exclusive(v___y_6612_);
if (v_isSharedCheck_6622_ == 0)
{
v___x_6617_ = v___y_6612_;
v_isShared_6618_ = v_isSharedCheck_6622_;
goto v_resetjp_6616_;
}
else
{
lean_inc(v_a_6615_);
lean_dec(v___y_6612_);
v___x_6617_ = lean_box(0);
v_isShared_6618_ = v_isSharedCheck_6622_;
goto v_resetjp_6616_;
}
v_resetjp_6616_:
{
lean_object* v___x_6620_; 
if (v_isShared_6618_ == 0)
{
v___x_6620_ = v___x_6617_;
goto v_reusejp_6619_;
}
else
{
lean_object* v_reuseFailAlloc_6621_; 
v_reuseFailAlloc_6621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6621_, 0, v_a_6615_);
v___x_6620_ = v_reuseFailAlloc_6621_;
goto v_reusejp_6619_;
}
v_reusejp_6619_:
{
return v___x_6620_;
}
}
}
}
}
else
{
lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; 
lean_dec_ref(v_scope_6540_);
lean_dec_ref(v_service_6539_);
lean_dec_ref(v_cache_6538_);
v___x_6632_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__1));
lean_inc_ref(v_a_6542_);
v___x_6633_ = lean_apply_2(v_a_6542_, v___x_6632_, lean_box(0));
v___x_6634_ = lean_box(0);
v___x_6635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6635_, 0, v___x_6634_);
return v___x_6635_;
}
v___jp_6544_:
{
lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; 
v___x_6546_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6547_ = l_System_FilePath_join(v_cache_6538_, v___x_6546_);
v___x_6548_ = l_IO_FS_createDirAll(v___x_6547_);
if (lean_obj_tag(v___x_6548_) == 0)
{
uint8_t v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
lean_dec_ref_known(v___x_6548_, 1);
v___x_6549_ = 0;
v___x_6550_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6551_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6551_, 0, v_scope_6540_);
lean_ctor_set(v___x_6551_, 1, v_a_6545_);
lean_ctor_set(v___x_6551_, 2, v___x_6550_);
lean_ctor_set_uint8(v___x_6551_, sizeof(void*)*3, v___x_6549_);
v___x_6552_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6542_, v___x_6551_);
return v___x_6552_;
}
else
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6565_; 
lean_dec_ref(v_a_6545_);
lean_dec_ref(v_scope_6540_);
v_a_6553_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6565_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6565_ == 0)
{
v___x_6555_ = v___x_6548_;
v_isShared_6556_ = v_isSharedCheck_6565_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6548_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6565_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6557_; uint8_t v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6563_; 
v___x_6557_ = lean_io_error_to_string(v_a_6553_);
v___x_6558_ = 3;
v___x_6559_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6559_, 0, v___x_6557_);
lean_ctor_set_uint8(v___x_6559_, sizeof(void*)*1, v___x_6558_);
lean_inc_ref(v_a_6542_);
v___x_6560_ = lean_apply_2(v_a_6542_, v___x_6559_, lean_box(0));
v___x_6561_ = lean_box(0);
if (v_isShared_6556_ == 0)
{
lean_ctor_set(v___x_6555_, 0, v___x_6561_);
v___x_6563_ = v___x_6555_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6564_; 
v_reuseFailAlloc_6564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6564_, 0, v___x_6561_);
v___x_6563_ = v_reuseFailAlloc_6564_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
return v___x_6563_;
}
}
}
}
v___jp_6566_:
{
lean_object* v___x_6568_; lean_object* v___x_6569_; uint8_t v___x_6570_; 
v___x_6568_ = lean_array_get_size(v_a_6567_);
v___x_6569_ = lean_unsigned_to_nat(0u);
v___x_6570_ = lean_nat_dec_eq(v___x_6568_, v___x_6569_);
if (v___x_6570_ == 0)
{
uint8_t v_isReservoir_6571_; 
v_isReservoir_6571_ = lean_ctor_get_uint8(v_service_6539_, sizeof(void*)*5);
if (v_isReservoir_6571_ == 0)
{
lean_dec_ref(v_service_6539_);
v_a_6545_ = v_a_6567_;
goto v___jp_6544_;
}
else
{
lean_object* v___x_6572_; lean_object* v___x_6573_; 
lean_inc_ref(v_scope_6540_);
v___x_6572_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6539_, v_scope_6540_);
v___x_6573_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6542_, v___x_6572_, v_a_6567_);
if (lean_obj_tag(v___x_6573_) == 0)
{
lean_object* v_a_6574_; 
v_a_6574_ = lean_ctor_get(v___x_6573_, 0);
lean_inc(v_a_6574_);
lean_dec_ref_known(v___x_6573_, 1);
v_a_6545_ = v_a_6574_;
goto v___jp_6544_;
}
else
{
lean_object* v_a_6575_; lean_object* v___x_6577_; uint8_t v_isShared_6578_; uint8_t v_isSharedCheck_6582_; 
lean_dec_ref(v_scope_6540_);
lean_dec_ref(v_cache_6538_);
v_a_6575_ = lean_ctor_get(v___x_6573_, 0);
v_isSharedCheck_6582_ = !lean_is_exclusive(v___x_6573_);
if (v_isSharedCheck_6582_ == 0)
{
v___x_6577_ = v___x_6573_;
v_isShared_6578_ = v_isSharedCheck_6582_;
goto v_resetjp_6576_;
}
else
{
lean_inc(v_a_6575_);
lean_dec(v___x_6573_);
v___x_6577_ = lean_box(0);
v_isShared_6578_ = v_isSharedCheck_6582_;
goto v_resetjp_6576_;
}
v_resetjp_6576_:
{
lean_object* v___x_6580_; 
if (v_isShared_6578_ == 0)
{
v___x_6580_ = v___x_6577_;
goto v_reusejp_6579_;
}
else
{
lean_object* v_reuseFailAlloc_6581_; 
v_reuseFailAlloc_6581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6581_, 0, v_a_6575_);
v___x_6580_ = v_reuseFailAlloc_6581_;
goto v_reusejp_6579_;
}
v_reusejp_6579_:
{
return v___x_6580_;
}
}
}
}
}
else
{
lean_object* v___x_6583_; lean_object* v___x_6584_; 
lean_dec_ref(v_a_6567_);
lean_dec_ref(v_scope_6540_);
lean_dec_ref(v_service_6539_);
lean_dec_ref(v_cache_6538_);
v___x_6583_ = lean_box(0);
v___x_6584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6584_, 0, v___x_6583_);
return v___x_6584_;
}
}
v___jp_6585_:
{
if (lean_obj_tag(v___y_6586_) == 0)
{
lean_object* v_a_6587_; 
v_a_6587_ = lean_ctor_get(v___y_6586_, 0);
lean_inc(v_a_6587_);
lean_dec_ref_known(v___y_6586_, 1);
v_a_6567_ = v_a_6587_;
goto v___jp_6566_;
}
else
{
lean_object* v_a_6588_; lean_object* v___x_6590_; uint8_t v_isShared_6591_; uint8_t v_isSharedCheck_6595_; 
lean_dec_ref(v_scope_6540_);
lean_dec_ref(v_service_6539_);
lean_dec_ref(v_cache_6538_);
v_a_6588_ = lean_ctor_get(v___y_6586_, 0);
v_isSharedCheck_6595_ = !lean_is_exclusive(v___y_6586_);
if (v_isSharedCheck_6595_ == 0)
{
v___x_6590_ = v___y_6586_;
v_isShared_6591_ = v_isSharedCheck_6595_;
goto v_resetjp_6589_;
}
else
{
lean_inc(v_a_6588_);
lean_dec(v___y_6586_);
v___x_6590_ = lean_box(0);
v_isShared_6591_ = v_isSharedCheck_6595_;
goto v_resetjp_6589_;
}
v_resetjp_6589_:
{
lean_object* v___x_6593_; 
if (v_isShared_6591_ == 0)
{
v___x_6593_ = v___x_6590_;
goto v_reusejp_6592_;
}
else
{
lean_object* v_reuseFailAlloc_6594_; 
v_reuseFailAlloc_6594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6594_, 0, v_a_6588_);
v___x_6593_ = v_reuseFailAlloc_6594_;
goto v_reusejp_6592_;
}
v_reusejp_6592_:
{
return v___x_6593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_6636_, lean_object* v_cache_6637_, lean_object* v_service_6638_, lean_object* v_scope_6639_, lean_object* v_force_6640_, lean_object* v_a_6641_, lean_object* v_a_6642_){
_start:
{
uint8_t v_force_boxed_6643_; lean_object* v_res_6644_; 
v_force_boxed_6643_ = lean_unbox(v_force_6640_);
v_res_6644_ = l_Lake_CacheService_downloadArtifacts(v_descrs_6636_, v_cache_6637_, v_service_6638_, v_scope_6639_, v_force_boxed_6643_, v_a_6641_);
lean_dec_ref(v_a_6641_);
lean_dec_ref(v_descrs_6636_);
return v_res_6644_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_6645_, lean_object* v_descrs_6646_, lean_object* v_cache_6647_, lean_object* v_service_6648_, lean_object* v_scope_6649_, uint8_t v_force_6650_){
_start:
{
lean_object* v_a_6653_; lean_object* v_a_6675_; lean_object* v___y_6694_; lean_object* v___x_6704_; lean_object* v___x_6705_; uint8_t v___x_6706_; 
v___x_6704_ = lean_array_get_size(v_descrs_6646_);
v___x_6705_ = lean_unsigned_to_nat(0u);
v___x_6706_ = lean_nat_dec_eq(v___x_6704_, v___x_6705_);
if (v___x_6706_ == 0)
{
lean_object* v___x_6707_; lean_object* v_infos_6709_; lean_object* v___y_6720_; uint8_t v___x_6731_; 
v___x_6707_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_6731_ = lean_nat_dec_lt(v___x_6705_, v___x_6704_);
if (v___x_6731_ == 0)
{
v_infos_6709_ = v___x_6707_;
goto v___jp_6708_;
}
else
{
lean_object* v___x_6732_; uint8_t v___x_6733_; 
v___x_6732_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
v___x_6733_ = lean_nat_dec_le(v___x_6704_, v___x_6704_);
if (v___x_6733_ == 0)
{
if (v___x_6731_ == 0)
{
v_infos_6709_ = v___x_6707_;
goto v___jp_6708_;
}
else
{
size_t v___x_6734_; size_t v___x_6735_; lean_object* v___x_6736_; 
v___x_6734_ = ((size_t)0ULL);
v___x_6735_ = lean_usize_of_nat(v___x_6704_);
lean_inc_ref(v_cache_6647_);
lean_inc_ref(v_scope_6649_);
lean_inc_ref(v_service_6648_);
v___x_6736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6648_, v_scope_6649_, v_cache_6647_, v_force_6650_, v_descrs_6646_, v___x_6734_, v___x_6735_, v___x_6732_, v_a_6645_);
v___y_6720_ = v___x_6736_;
goto v___jp_6719_;
}
}
else
{
size_t v___x_6737_; size_t v___x_6738_; lean_object* v___x_6739_; 
v___x_6737_ = ((size_t)0ULL);
v___x_6738_ = lean_usize_of_nat(v___x_6704_);
lean_inc_ref(v_cache_6647_);
lean_inc_ref(v_scope_6649_);
lean_inc_ref(v_service_6648_);
v___x_6739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6648_, v_scope_6649_, v_cache_6647_, v_force_6650_, v_descrs_6646_, v___x_6737_, v___x_6738_, v___x_6732_, v_a_6645_);
v___y_6720_ = v___x_6739_;
goto v___jp_6719_;
}
}
v___jp_6708_:
{
lean_object* v___x_6710_; uint8_t v___x_6711_; 
v___x_6710_ = lean_array_get_size(v_infos_6709_);
v___x_6711_ = lean_nat_dec_lt(v___x_6705_, v___x_6710_);
if (v___x_6711_ == 0)
{
lean_dec_ref(v_infos_6709_);
v_a_6675_ = v___x_6707_;
goto v___jp_6674_;
}
else
{
uint8_t v___x_6712_; 
v___x_6712_ = lean_nat_dec_le(v___x_6710_, v___x_6710_);
if (v___x_6712_ == 0)
{
if (v___x_6711_ == 0)
{
lean_dec_ref(v_infos_6709_);
v_a_6675_ = v___x_6707_;
goto v___jp_6674_;
}
else
{
size_t v___x_6713_; size_t v___x_6714_; lean_object* v___x_6715_; 
v___x_6713_ = ((size_t)0ULL);
v___x_6714_ = lean_usize_of_nat(v___x_6710_);
v___x_6715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6709_, v___x_6713_, v___x_6714_, v___x_6707_, v_a_6645_);
lean_dec_ref(v_infos_6709_);
v___y_6694_ = v___x_6715_;
goto v___jp_6693_;
}
}
else
{
size_t v___x_6716_; size_t v___x_6717_; lean_object* v___x_6718_; 
v___x_6716_ = ((size_t)0ULL);
v___x_6717_ = lean_usize_of_nat(v___x_6710_);
v___x_6718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6709_, v___x_6716_, v___x_6717_, v___x_6707_, v_a_6645_);
lean_dec_ref(v_infos_6709_);
v___y_6694_ = v___x_6718_;
goto v___jp_6693_;
}
}
}
v___jp_6719_:
{
if (lean_obj_tag(v___y_6720_) == 0)
{
lean_object* v_a_6721_; lean_object* v_infos_6722_; 
v_a_6721_ = lean_ctor_get(v___y_6720_, 0);
lean_inc(v_a_6721_);
lean_dec_ref_known(v___y_6720_, 1);
v_infos_6722_ = lean_ctor_get(v_a_6721_, 0);
lean_inc_ref(v_infos_6722_);
lean_dec(v_a_6721_);
v_infos_6709_ = v_infos_6722_;
goto v___jp_6708_;
}
else
{
lean_object* v_a_6723_; lean_object* v___x_6725_; uint8_t v_isShared_6726_; uint8_t v_isSharedCheck_6730_; 
lean_dec_ref(v_scope_6649_);
lean_dec_ref(v_service_6648_);
lean_dec_ref(v_cache_6647_);
v_a_6723_ = lean_ctor_get(v___y_6720_, 0);
v_isSharedCheck_6730_ = !lean_is_exclusive(v___y_6720_);
if (v_isSharedCheck_6730_ == 0)
{
v___x_6725_ = v___y_6720_;
v_isShared_6726_ = v_isSharedCheck_6730_;
goto v_resetjp_6724_;
}
else
{
lean_inc(v_a_6723_);
lean_dec(v___y_6720_);
v___x_6725_ = lean_box(0);
v_isShared_6726_ = v_isSharedCheck_6730_;
goto v_resetjp_6724_;
}
v_resetjp_6724_:
{
lean_object* v___x_6728_; 
if (v_isShared_6726_ == 0)
{
v___x_6728_ = v___x_6725_;
goto v_reusejp_6727_;
}
else
{
lean_object* v_reuseFailAlloc_6729_; 
v_reuseFailAlloc_6729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6729_, 0, v_a_6723_);
v___x_6728_ = v_reuseFailAlloc_6729_;
goto v_reusejp_6727_;
}
v_reusejp_6727_:
{
return v___x_6728_;
}
}
}
}
}
else
{
lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v___x_6743_; 
lean_dec_ref(v_scope_6649_);
lean_dec_ref(v_service_6648_);
lean_dec_ref(v_cache_6647_);
v___x_6740_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__1));
lean_inc_ref(v_a_6645_);
v___x_6741_ = lean_apply_2(v_a_6645_, v___x_6740_, lean_box(0));
v___x_6742_ = lean_box(0);
v___x_6743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6743_, 0, v___x_6742_);
return v___x_6743_;
}
v___jp_6652_:
{
lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; 
v___x_6654_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6655_ = l_System_FilePath_join(v_cache_6647_, v___x_6654_);
v___x_6656_ = l_IO_FS_createDirAll(v___x_6655_);
if (lean_obj_tag(v___x_6656_) == 0)
{
uint8_t v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; 
lean_dec_ref_known(v___x_6656_, 1);
v___x_6657_ = 0;
v___x_6658_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6659_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6659_, 0, v_scope_6649_);
lean_ctor_set(v___x_6659_, 1, v_a_6653_);
lean_ctor_set(v___x_6659_, 2, v___x_6658_);
lean_ctor_set_uint8(v___x_6659_, sizeof(void*)*3, v___x_6657_);
v___x_6660_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6645_, v___x_6659_);
return v___x_6660_;
}
else
{
lean_object* v_a_6661_; lean_object* v___x_6663_; uint8_t v_isShared_6664_; uint8_t v_isSharedCheck_6673_; 
lean_dec_ref(v_a_6653_);
lean_dec_ref(v_scope_6649_);
v_a_6661_ = lean_ctor_get(v___x_6656_, 0);
v_isSharedCheck_6673_ = !lean_is_exclusive(v___x_6656_);
if (v_isSharedCheck_6673_ == 0)
{
v___x_6663_ = v___x_6656_;
v_isShared_6664_ = v_isSharedCheck_6673_;
goto v_resetjp_6662_;
}
else
{
lean_inc(v_a_6661_);
lean_dec(v___x_6656_);
v___x_6663_ = lean_box(0);
v_isShared_6664_ = v_isSharedCheck_6673_;
goto v_resetjp_6662_;
}
v_resetjp_6662_:
{
lean_object* v___x_6665_; uint8_t v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6671_; 
v___x_6665_ = lean_io_error_to_string(v_a_6661_);
v___x_6666_ = 3;
v___x_6667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6667_, 0, v___x_6665_);
lean_ctor_set_uint8(v___x_6667_, sizeof(void*)*1, v___x_6666_);
lean_inc_ref(v_a_6645_);
v___x_6668_ = lean_apply_2(v_a_6645_, v___x_6667_, lean_box(0));
v___x_6669_ = lean_box(0);
if (v_isShared_6664_ == 0)
{
lean_ctor_set(v___x_6663_, 0, v___x_6669_);
v___x_6671_ = v___x_6663_;
goto v_reusejp_6670_;
}
else
{
lean_object* v_reuseFailAlloc_6672_; 
v_reuseFailAlloc_6672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6672_, 0, v___x_6669_);
v___x_6671_ = v_reuseFailAlloc_6672_;
goto v_reusejp_6670_;
}
v_reusejp_6670_:
{
return v___x_6671_;
}
}
}
}
v___jp_6674_:
{
lean_object* v___x_6676_; lean_object* v___x_6677_; uint8_t v___x_6678_; 
v___x_6676_ = lean_array_get_size(v_a_6675_);
v___x_6677_ = lean_unsigned_to_nat(0u);
v___x_6678_ = lean_nat_dec_eq(v___x_6676_, v___x_6677_);
if (v___x_6678_ == 0)
{
uint8_t v_isReservoir_6679_; 
v_isReservoir_6679_ = lean_ctor_get_uint8(v_service_6648_, sizeof(void*)*5);
if (v_isReservoir_6679_ == 0)
{
lean_dec_ref(v_service_6648_);
v_a_6653_ = v_a_6675_;
goto v___jp_6652_;
}
else
{
lean_object* v___x_6680_; lean_object* v___x_6681_; 
lean_inc_ref(v_scope_6649_);
v___x_6680_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6648_, v_scope_6649_);
v___x_6681_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6645_, v___x_6680_, v_a_6675_);
if (lean_obj_tag(v___x_6681_) == 0)
{
lean_object* v_a_6682_; 
v_a_6682_ = lean_ctor_get(v___x_6681_, 0);
lean_inc(v_a_6682_);
lean_dec_ref_known(v___x_6681_, 1);
v_a_6653_ = v_a_6682_;
goto v___jp_6652_;
}
else
{
lean_object* v_a_6683_; lean_object* v___x_6685_; uint8_t v_isShared_6686_; uint8_t v_isSharedCheck_6690_; 
lean_dec_ref(v_scope_6649_);
lean_dec_ref(v_cache_6647_);
v_a_6683_ = lean_ctor_get(v___x_6681_, 0);
v_isSharedCheck_6690_ = !lean_is_exclusive(v___x_6681_);
if (v_isSharedCheck_6690_ == 0)
{
v___x_6685_ = v___x_6681_;
v_isShared_6686_ = v_isSharedCheck_6690_;
goto v_resetjp_6684_;
}
else
{
lean_inc(v_a_6683_);
lean_dec(v___x_6681_);
v___x_6685_ = lean_box(0);
v_isShared_6686_ = v_isSharedCheck_6690_;
goto v_resetjp_6684_;
}
v_resetjp_6684_:
{
lean_object* v___x_6688_; 
if (v_isShared_6686_ == 0)
{
v___x_6688_ = v___x_6685_;
goto v_reusejp_6687_;
}
else
{
lean_object* v_reuseFailAlloc_6689_; 
v_reuseFailAlloc_6689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6689_, 0, v_a_6683_);
v___x_6688_ = v_reuseFailAlloc_6689_;
goto v_reusejp_6687_;
}
v_reusejp_6687_:
{
return v___x_6688_;
}
}
}
}
}
else
{
lean_object* v___x_6691_; lean_object* v___x_6692_; 
lean_dec_ref(v_a_6675_);
lean_dec_ref(v_scope_6649_);
lean_dec_ref(v_service_6648_);
lean_dec_ref(v_cache_6647_);
v___x_6691_ = lean_box(0);
v___x_6692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6692_, 0, v___x_6691_);
return v___x_6692_;
}
}
v___jp_6693_:
{
if (lean_obj_tag(v___y_6694_) == 0)
{
lean_object* v_a_6695_; 
v_a_6695_ = lean_ctor_get(v___y_6694_, 0);
lean_inc(v_a_6695_);
lean_dec_ref_known(v___y_6694_, 1);
v_a_6675_ = v_a_6695_;
goto v___jp_6674_;
}
else
{
lean_object* v_a_6696_; lean_object* v___x_6698_; uint8_t v_isShared_6699_; uint8_t v_isSharedCheck_6703_; 
lean_dec_ref(v_scope_6649_);
lean_dec_ref(v_service_6648_);
lean_dec_ref(v_cache_6647_);
v_a_6696_ = lean_ctor_get(v___y_6694_, 0);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___y_6694_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6698_ = v___y_6694_;
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
else
{
lean_inc(v_a_6696_);
lean_dec(v___y_6694_);
v___x_6698_ = lean_box(0);
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
v_resetjp_6697_:
{
lean_object* v___x_6701_; 
if (v_isShared_6699_ == 0)
{
v___x_6701_ = v___x_6698_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_a_6696_);
v___x_6701_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
return v___x_6701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_6744_, lean_object* v_descrs_6745_, lean_object* v_cache_6746_, lean_object* v_service_6747_, lean_object* v_scope_6748_, lean_object* v_force_6749_, lean_object* v_a_6750_){
_start:
{
uint8_t v_force_boxed_6751_; lean_object* v_res_6752_; 
v_force_boxed_6751_ = lean_unbox(v_force_6749_);
v_res_6752_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6744_, v_descrs_6745_, v_cache_6746_, v_service_6747_, v_scope_6748_, v_force_boxed_6751_);
lean_dec_ref(v_descrs_6745_);
lean_dec_ref(v_a_6744_);
return v_res_6752_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_6753_, lean_object* v_cache_6754_, lean_object* v_service_6755_, lean_object* v_localScope_6756_, lean_object* v_remoteScope_6757_, uint8_t v_force_6758_, lean_object* v_a_6759_){
_start:
{
lean_object* v_name_x3f_6764_; lean_object* v___x_6765_; uint8_t v___x_6766_; lean_object* v___x_6767_; 
v_name_x3f_6764_ = lean_ctor_get(v_service_6755_, 0);
lean_inc_ref(v_remoteScope_6757_);
v___x_6765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6765_, 0, v_remoteScope_6757_);
v___x_6766_ = 1;
lean_inc(v_name_x3f_6764_);
lean_inc_ref(v_cache_6754_);
v___x_6767_ = l_Lake_Cache_writeMap(v_cache_6754_, v_localScope_6756_, v_map_6753_, v_name_x3f_6764_, v___x_6765_, v___x_6766_);
if (lean_obj_tag(v___x_6767_) == 0)
{
lean_object* v___x_6769_; uint8_t v_isShared_6770_; uint8_t v_isSharedCheck_6805_; 
v_isSharedCheck_6805_ = !lean_is_exclusive(v___x_6767_);
if (v_isSharedCheck_6805_ == 0)
{
lean_object* v_unused_6806_; 
v_unused_6806_ = lean_ctor_get(v___x_6767_, 0);
lean_dec(v_unused_6806_);
v___x_6769_ = v___x_6767_;
v_isShared_6770_ = v_isSharedCheck_6805_;
goto v_resetjp_6768_;
}
else
{
lean_dec(v___x_6767_);
v___x_6769_ = lean_box(0);
v_isShared_6770_ = v_isSharedCheck_6805_;
goto v_resetjp_6768_;
}
v_resetjp_6768_:
{
lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; 
v___x_6771_ = lean_unsigned_to_nat(0u);
v___x_6772_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6773_ = l_Lake_CacheMap_collectOutputDescrs(v_map_6753_, v___x_6772_);
if (lean_obj_tag(v___x_6773_) == 0)
{
lean_object* v_a_6774_; lean_object* v_a_6775_; lean_object* v___x_6776_; uint8_t v___x_6777_; 
lean_del_object(v___x_6769_);
v_a_6774_ = lean_ctor_get(v___x_6773_, 0);
lean_inc(v_a_6774_);
v_a_6775_ = lean_ctor_get(v___x_6773_, 1);
lean_inc(v_a_6775_);
lean_dec_ref_known(v___x_6773_, 2);
v___x_6776_ = lean_array_get_size(v_a_6775_);
v___x_6777_ = lean_nat_dec_lt(v___x_6771_, v___x_6776_);
if (v___x_6777_ == 0)
{
lean_object* v___x_6778_; 
lean_dec(v_a_6775_);
v___x_6778_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6759_, v_a_6774_, v_cache_6754_, v_service_6755_, v_remoteScope_6757_, v_force_6758_);
lean_dec(v_a_6774_);
return v___x_6778_;
}
else
{
lean_object* v___x_6779_; uint8_t v___x_6780_; 
v___x_6779_ = lean_box(0);
v___x_6780_ = lean_nat_dec_le(v___x_6776_, v___x_6776_);
if (v___x_6780_ == 0)
{
if (v___x_6777_ == 0)
{
lean_object* v___x_6781_; 
lean_dec(v_a_6775_);
v___x_6781_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6759_, v_a_6774_, v_cache_6754_, v_service_6755_, v_remoteScope_6757_, v_force_6758_);
lean_dec(v_a_6774_);
return v___x_6781_;
}
else
{
size_t v___x_6782_; size_t v___x_6783_; lean_object* v___x_6784_; 
v___x_6782_ = ((size_t)0ULL);
v___x_6783_ = lean_usize_of_nat(v___x_6776_);
v___x_6784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6775_, v___x_6782_, v___x_6783_, v___x_6779_, v_a_6759_);
lean_dec(v_a_6775_);
if (lean_obj_tag(v___x_6784_) == 0)
{
lean_object* v___x_6785_; 
lean_dec_ref_known(v___x_6784_, 1);
v___x_6785_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6759_, v_a_6774_, v_cache_6754_, v_service_6755_, v_remoteScope_6757_, v_force_6758_);
lean_dec(v_a_6774_);
return v___x_6785_;
}
else
{
lean_dec(v_a_6774_);
lean_dec_ref(v_remoteScope_6757_);
lean_dec_ref(v_service_6755_);
lean_dec_ref(v_cache_6754_);
return v___x_6784_;
}
}
}
else
{
size_t v___x_6786_; size_t v___x_6787_; lean_object* v___x_6788_; 
v___x_6786_ = ((size_t)0ULL);
v___x_6787_ = lean_usize_of_nat(v___x_6776_);
v___x_6788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6775_, v___x_6786_, v___x_6787_, v___x_6779_, v_a_6759_);
lean_dec(v_a_6775_);
if (lean_obj_tag(v___x_6788_) == 0)
{
lean_object* v___x_6789_; 
lean_dec_ref_known(v___x_6788_, 1);
v___x_6789_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6759_, v_a_6774_, v_cache_6754_, v_service_6755_, v_remoteScope_6757_, v_force_6758_);
lean_dec(v_a_6774_);
return v___x_6789_;
}
else
{
lean_dec(v_a_6774_);
lean_dec_ref(v_remoteScope_6757_);
lean_dec_ref(v_service_6755_);
lean_dec_ref(v_cache_6754_);
return v___x_6788_;
}
}
}
}
else
{
lean_object* v_a_6790_; lean_object* v___x_6791_; uint8_t v___x_6792_; 
lean_dec_ref(v_remoteScope_6757_);
lean_dec_ref(v_service_6755_);
lean_dec_ref(v_cache_6754_);
v_a_6790_ = lean_ctor_get(v___x_6773_, 1);
lean_inc(v_a_6790_);
lean_dec_ref_known(v___x_6773_, 2);
v___x_6791_ = lean_array_get_size(v_a_6790_);
v___x_6792_ = lean_nat_dec_lt(v___x_6771_, v___x_6791_);
if (v___x_6792_ == 0)
{
lean_object* v___x_6793_; lean_object* v___x_6795_; 
lean_dec(v_a_6790_);
v___x_6793_ = lean_box(0);
if (v_isShared_6770_ == 0)
{
lean_ctor_set_tag(v___x_6769_, 1);
lean_ctor_set(v___x_6769_, 0, v___x_6793_);
v___x_6795_ = v___x_6769_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6796_; 
v_reuseFailAlloc_6796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6796_, 0, v___x_6793_);
v___x_6795_ = v_reuseFailAlloc_6796_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
return v___x_6795_;
}
}
else
{
lean_object* v___x_6797_; uint8_t v___x_6798_; 
lean_del_object(v___x_6769_);
v___x_6797_ = lean_box(0);
v___x_6798_ = lean_nat_dec_le(v___x_6791_, v___x_6791_);
if (v___x_6798_ == 0)
{
if (v___x_6792_ == 0)
{
lean_dec(v_a_6790_);
goto v___jp_6761_;
}
else
{
size_t v___x_6799_; size_t v___x_6800_; lean_object* v___x_6801_; 
v___x_6799_ = ((size_t)0ULL);
v___x_6800_ = lean_usize_of_nat(v___x_6791_);
v___x_6801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6790_, v___x_6799_, v___x_6800_, v___x_6797_, v_a_6759_);
lean_dec(v_a_6790_);
if (lean_obj_tag(v___x_6801_) == 0)
{
lean_dec_ref_known(v___x_6801_, 1);
goto v___jp_6761_;
}
else
{
return v___x_6801_;
}
}
}
else
{
size_t v___x_6802_; size_t v___x_6803_; lean_object* v___x_6804_; 
v___x_6802_ = ((size_t)0ULL);
v___x_6803_ = lean_usize_of_nat(v___x_6791_);
v___x_6804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6790_, v___x_6802_, v___x_6803_, v___x_6797_, v_a_6759_);
lean_dec(v_a_6790_);
if (lean_obj_tag(v___x_6804_) == 0)
{
lean_dec_ref_known(v___x_6804_, 1);
goto v___jp_6761_;
}
else
{
return v___x_6804_;
}
}
}
}
}
}
else
{
lean_object* v_a_6807_; lean_object* v___x_6809_; uint8_t v_isShared_6810_; uint8_t v_isSharedCheck_6819_; 
lean_dec_ref(v_remoteScope_6757_);
lean_dec_ref(v_service_6755_);
lean_dec_ref(v_cache_6754_);
lean_dec_ref(v_map_6753_);
v_a_6807_ = lean_ctor_get(v___x_6767_, 0);
v_isSharedCheck_6819_ = !lean_is_exclusive(v___x_6767_);
if (v_isSharedCheck_6819_ == 0)
{
v___x_6809_ = v___x_6767_;
v_isShared_6810_ = v_isSharedCheck_6819_;
goto v_resetjp_6808_;
}
else
{
lean_inc(v_a_6807_);
lean_dec(v___x_6767_);
v___x_6809_ = lean_box(0);
v_isShared_6810_ = v_isSharedCheck_6819_;
goto v_resetjp_6808_;
}
v_resetjp_6808_:
{
lean_object* v___x_6811_; uint8_t v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6817_; 
v___x_6811_ = lean_io_error_to_string(v_a_6807_);
v___x_6812_ = 3;
v___x_6813_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6813_, 0, v___x_6811_);
lean_ctor_set_uint8(v___x_6813_, sizeof(void*)*1, v___x_6812_);
lean_inc_ref(v_a_6759_);
v___x_6814_ = lean_apply_2(v_a_6759_, v___x_6813_, lean_box(0));
v___x_6815_ = lean_box(0);
if (v_isShared_6810_ == 0)
{
lean_ctor_set(v___x_6809_, 0, v___x_6815_);
v___x_6817_ = v___x_6809_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v___x_6815_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
v___jp_6761_:
{
lean_object* v___x_6762_; lean_object* v___x_6763_; 
v___x_6762_ = lean_box(0);
v___x_6763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6763_, 0, v___x_6762_);
return v___x_6763_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_6820_, lean_object* v_cache_6821_, lean_object* v_service_6822_, lean_object* v_localScope_6823_, lean_object* v_remoteScope_6824_, lean_object* v_force_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_){
_start:
{
uint8_t v_force_boxed_6828_; lean_object* v_res_6829_; 
v_force_boxed_6828_ = lean_unbox(v_force_6825_);
v_res_6829_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_6820_, v_cache_6821_, v_service_6822_, v_localScope_6823_, v_remoteScope_6824_, v_force_boxed_6828_, v_a_6826_);
lean_dec_ref(v_a_6826_);
return v_res_6829_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* v_m_6830_, uint64_t v_a_6831_){
_start:
{
lean_object* v_buckets_6832_; lean_object* v___x_6833_; uint64_t v___x_6834_; uint64_t v___x_6835_; uint64_t v_fold_6836_; uint64_t v___x_6837_; uint64_t v___x_6838_; uint64_t v___x_6839_; size_t v___x_6840_; size_t v___x_6841_; size_t v___x_6842_; size_t v___x_6843_; size_t v___x_6844_; lean_object* v___x_6845_; uint8_t v___x_6846_; 
v_buckets_6832_ = lean_ctor_get(v_m_6830_, 1);
v___x_6833_ = lean_array_get_size(v_buckets_6832_);
v___x_6834_ = 32ULL;
v___x_6835_ = lean_uint64_shift_right(v_a_6831_, v___x_6834_);
v_fold_6836_ = lean_uint64_xor(v_a_6831_, v___x_6835_);
v___x_6837_ = 16ULL;
v___x_6838_ = lean_uint64_shift_right(v_fold_6836_, v___x_6837_);
v___x_6839_ = lean_uint64_xor(v_fold_6836_, v___x_6838_);
v___x_6840_ = lean_uint64_to_usize(v___x_6839_);
v___x_6841_ = lean_usize_of_nat(v___x_6833_);
v___x_6842_ = ((size_t)1ULL);
v___x_6843_ = lean_usize_sub(v___x_6841_, v___x_6842_);
v___x_6844_ = lean_usize_land(v___x_6840_, v___x_6843_);
v___x_6845_ = lean_array_uget_borrowed(v_buckets_6832_, v___x_6844_);
v___x_6846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_6831_, v___x_6845_);
return v___x_6846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* v_m_6847_, lean_object* v_a_6848_){
_start:
{
uint64_t v_a_boxed_6849_; uint8_t v_res_6850_; lean_object* v_r_6851_; 
v_a_boxed_6849_ = lean_unbox_uint64(v_a_6848_);
lean_dec_ref(v_a_6848_);
v_res_6850_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_m_6847_, v_a_boxed_6849_);
lean_dec_ref(v_m_6847_);
v_r_6851_ = lean_box(v_res_6850_);
return v_r_6851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(lean_object* v_descrs_6852_, lean_object* v_service_6853_, lean_object* v_scope_6854_, lean_object* v_paths_6855_, lean_object* v_n_6856_, lean_object* v_i_6857_, lean_object* v_a_6858_){
_start:
{
lean_object* v_zero_6860_; uint8_t v_isZero_6861_; 
v_zero_6860_ = lean_unsigned_to_nat(0u);
v_isZero_6861_ = lean_nat_dec_eq(v_i_6857_, v_zero_6860_);
if (v_isZero_6861_ == 1)
{
lean_object* v___x_6862_; 
lean_dec(v_i_6857_);
lean_dec_ref(v_scope_6854_);
lean_dec_ref(v_service_6853_);
v___x_6862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6862_, 0, v_a_6858_);
return v___x_6862_;
}
else
{
lean_object* v_one_6863_; lean_object* v_n_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; lean_object* v___x_6867_; uint64_t v_hash_6868_; lean_object* v_infos_6869_; lean_object* v_indices_6870_; lean_object* v_url_6871_; uint8_t v___x_6872_; 
v_one_6863_ = lean_unsigned_to_nat(1u);
v_n_6864_ = lean_nat_sub(v_i_6857_, v_one_6863_);
lean_dec(v_i_6857_);
v___x_6865_ = lean_nat_sub(v_n_6856_, v_n_6864_);
v___x_6866_ = lean_nat_sub(v___x_6865_, v_one_6863_);
lean_dec(v___x_6865_);
v___x_6867_ = lean_array_fget_borrowed(v_descrs_6852_, v___x_6866_);
v_hash_6868_ = lean_ctor_get_uint64(v___x_6867_, sizeof(void*)*1);
v_infos_6869_ = lean_ctor_get(v_a_6858_, 0);
v_indices_6870_ = lean_ctor_get(v_a_6858_, 1);
lean_inc_ref(v_scope_6854_);
lean_inc_ref(v_service_6853_);
v_url_6871_ = l_Lake_CacheService_artifactUrl(v_hash_6868_, v_service_6853_, v_scope_6854_);
v___x_6872_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_indices_6870_, v_hash_6868_);
if (v___x_6872_ == 0)
{
lean_object* v___x_6874_; uint8_t v_isShared_6875_; uint8_t v_isSharedCheck_6886_; 
lean_inc_ref(v_indices_6870_);
lean_inc_ref(v_infos_6869_);
v_isSharedCheck_6886_ = !lean_is_exclusive(v_a_6858_);
if (v_isSharedCheck_6886_ == 0)
{
lean_object* v_unused_6887_; lean_object* v_unused_6888_; 
v_unused_6887_ = lean_ctor_get(v_a_6858_, 1);
lean_dec(v_unused_6887_);
v_unused_6888_ = lean_ctor_get(v_a_6858_, 0);
lean_dec(v_unused_6888_);
v___x_6874_ = v_a_6858_;
v_isShared_6875_ = v_isSharedCheck_6886_;
goto v_resetjp_6873_;
}
else
{
lean_dec(v_a_6858_);
v___x_6874_ = lean_box(0);
v_isShared_6875_ = v_isSharedCheck_6886_;
goto v_resetjp_6873_;
}
v_resetjp_6873_:
{
lean_object* v___x_6876_; lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v___x_6879_; lean_object* v___x_6880_; lean_object* v___x_6881_; lean_object* v___x_6883_; 
v___x_6876_ = lean_array_fget_borrowed(v_paths_6855_, v___x_6866_);
lean_dec(v___x_6866_);
v___x_6877_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc(v___x_6876_);
v___x_6878_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6878_, 0, v_url_6871_);
lean_ctor_set(v___x_6878_, 1, v___x_6876_);
lean_ctor_set(v___x_6878_, 2, v___x_6877_);
lean_ctor_set_uint64(v___x_6878_, sizeof(void*)*3, v_hash_6868_);
lean_inc_ref(v_infos_6869_);
v___x_6879_ = lean_array_push(v_infos_6869_, v___x_6878_);
v___x_6880_ = lean_array_get_size(v_infos_6869_);
lean_dec_ref(v_infos_6869_);
v___x_6881_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6870_, v_hash_6868_, v___x_6880_);
if (v_isShared_6875_ == 0)
{
lean_ctor_set(v___x_6874_, 1, v___x_6881_);
lean_ctor_set(v___x_6874_, 0, v___x_6879_);
v___x_6883_ = v___x_6874_;
goto v_reusejp_6882_;
}
else
{
lean_object* v_reuseFailAlloc_6885_; 
v_reuseFailAlloc_6885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6885_, 0, v___x_6879_);
lean_ctor_set(v_reuseFailAlloc_6885_, 1, v___x_6881_);
v___x_6883_ = v_reuseFailAlloc_6885_;
goto v_reusejp_6882_;
}
v_reusejp_6882_:
{
v_i_6857_ = v_n_6864_;
v_a_6858_ = v___x_6883_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_url_6871_);
lean_dec(v___x_6866_);
v_i_6857_ = v_n_6864_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg___boxed(lean_object* v_descrs_6890_, lean_object* v_service_6891_, lean_object* v_scope_6892_, lean_object* v_paths_6893_, lean_object* v_n_6894_, lean_object* v_i_6895_, lean_object* v_a_6896_, lean_object* v___y_6897_){
_start:
{
lean_object* v_res_6898_; 
v_res_6898_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_6890_, v_service_6891_, v_scope_6892_, v_paths_6893_, v_n_6894_, v_i_6895_, v_a_6896_);
lean_dec(v_n_6894_);
lean_dec_ref(v_paths_6893_);
lean_dec_ref(v_descrs_6890_);
return v_res_6898_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_6903_, lean_object* v_descrs_6904_, lean_object* v_paths_6905_, lean_object* v_service_6906_, lean_object* v_scope_6907_, lean_object* v_a_6908_){
_start:
{
lean_object* v___x_6910_; uint8_t v___x_6911_; 
v___x_6910_ = lean_unsigned_to_nat(0u);
v___x_6911_ = lean_nat_dec_eq(v_n_6903_, v___x_6910_);
if (v___x_6911_ == 0)
{
lean_object* v___x_6912_; lean_object* v___x_6913_; lean_object* v_a_6914_; lean_object* v_infos_6915_; lean_object* v_key_6916_; uint8_t v___x_6917_; lean_object* v___x_6918_; lean_object* v___x_6919_; 
v___x_6912_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
lean_inc(v_n_6903_);
lean_inc_ref(v_scope_6907_);
lean_inc_ref(v_service_6906_);
v___x_6913_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_6904_, v_service_6906_, v_scope_6907_, v_paths_6905_, v_n_6903_, v_n_6903_, v___x_6912_);
lean_dec(v_n_6903_);
v_a_6914_ = lean_ctor_get(v___x_6913_, 0);
lean_inc(v_a_6914_);
lean_dec_ref(v___x_6913_);
v_infos_6915_ = lean_ctor_get(v_a_6914_, 0);
lean_inc_ref(v_infos_6915_);
lean_dec(v_a_6914_);
v_key_6916_ = lean_ctor_get(v_service_6906_, 1);
lean_inc_ref(v_key_6916_);
lean_dec_ref(v_service_6906_);
v___x_6917_ = 1;
v___x_6918_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6918_, 0, v_scope_6907_);
lean_ctor_set(v___x_6918_, 1, v_infos_6915_);
lean_ctor_set(v___x_6918_, 2, v_key_6916_);
lean_ctor_set_uint8(v___x_6918_, sizeof(void*)*3, v___x_6917_);
v___x_6919_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6908_, v___x_6918_);
return v___x_6919_;
}
else
{
lean_object* v___x_6920_; lean_object* v___x_6921_; lean_object* v___x_6922_; lean_object* v___x_6923_; 
lean_dec_ref(v_scope_6907_);
lean_dec_ref(v_service_6906_);
lean_dec(v_n_6903_);
v___x_6920_ = ((lean_object*)(l_Lake_CacheService_uploadArtifacts___closed__1));
lean_inc_ref(v_a_6908_);
v___x_6921_ = lean_apply_2(v_a_6908_, v___x_6920_, lean_box(0));
v___x_6922_ = lean_box(0);
v___x_6923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6923_, 0, v___x_6922_);
return v___x_6923_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_6924_, lean_object* v_descrs_6925_, lean_object* v_paths_6926_, lean_object* v_service_6927_, lean_object* v_scope_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_){
_start:
{
lean_object* v_res_6931_; 
v_res_6931_ = l_Lake_CacheService_uploadArtifacts(v_n_6924_, v_descrs_6925_, v_paths_6926_, v_service_6927_, v_scope_6928_, v_a_6929_);
lean_dec_ref(v_a_6929_);
lean_dec_ref(v_paths_6926_);
lean_dec_ref(v_descrs_6925_);
return v_res_6931_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object* v_00_u03b2_6932_, lean_object* v_m_6933_, uint64_t v_a_6934_){
_start:
{
uint8_t v___x_6935_; 
v___x_6935_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_m_6933_, v_a_6934_);
return v___x_6935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* v_00_u03b2_6936_, lean_object* v_m_6937_, lean_object* v_a_6938_){
_start:
{
uint64_t v_a_boxed_6939_; uint8_t v_res_6940_; lean_object* v_r_6941_; 
v_a_boxed_6939_ = lean_unbox_uint64(v_a_6938_);
lean_dec_ref(v_a_6938_);
v_res_6940_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(v_00_u03b2_6936_, v_m_6937_, v_a_boxed_6939_);
lean_dec_ref(v_m_6937_);
v_r_6941_ = lean_box(v_res_6940_);
return v_r_6941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(lean_object* v_descrs_6942_, lean_object* v_service_6943_, lean_object* v_scope_6944_, lean_object* v_paths_6945_, lean_object* v_n_6946_, lean_object* v_i_6947_, lean_object* v_a_6948_, lean_object* v_a_6949_, lean_object* v___y_6950_){
_start:
{
lean_object* v___x_6952_; 
v___x_6952_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_6942_, v_service_6943_, v_scope_6944_, v_paths_6945_, v_n_6946_, v_i_6947_, v_a_6949_);
return v___x_6952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___boxed(lean_object* v_descrs_6953_, lean_object* v_service_6954_, lean_object* v_scope_6955_, lean_object* v_paths_6956_, lean_object* v_n_6957_, lean_object* v_i_6958_, lean_object* v_a_6959_, lean_object* v_a_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_){
_start:
{
lean_object* v_res_6963_; 
v_res_6963_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(v_descrs_6953_, v_service_6954_, v_scope_6955_, v_paths_6956_, v_n_6957_, v_i_6958_, v_a_6959_, v_a_6960_, v___y_6961_);
lean_dec_ref(v___y_6961_);
lean_dec(v_n_6957_);
lean_dec_ref(v_paths_6956_);
lean_dec_ref(v_descrs_6953_);
return v_res_6963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_6968_, lean_object* v_service_6969_, lean_object* v_scope_6970_, lean_object* v_platform_6971_, lean_object* v_toolchain_6972_){
_start:
{
lean_object* v_url_6974_; lean_object* v_url_6981_; 
if (lean_obj_tag(v_scope_6970_) == 0)
{
lean_object* v_s_6990_; lean_object* v_revisionEndpoint_6991_; lean_object* v___x_6992_; lean_object* v___x_6993_; lean_object* v___x_6994_; lean_object* v___x_6995_; lean_object* v___x_6996_; lean_object* v___x_6997_; 
lean_dec_ref(v_platform_6971_);
v_s_6990_ = lean_ctor_get(v_scope_6970_, 0);
lean_inc_ref(v_s_6990_);
lean_dec_ref_known(v_scope_6970_, 1);
v_revisionEndpoint_6991_ = lean_ctor_get(v_service_6969_, 3);
lean_inc_ref(v_revisionEndpoint_6991_);
lean_dec_ref(v_service_6969_);
v___x_6992_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_6991_, v_s_6990_);
v___x_6993_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_6994_ = lean_string_append(v___x_6993_, v_rev_6968_);
v___x_6995_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_6996_ = lean_string_append(v___x_6994_, v___x_6995_);
v___x_6997_ = lean_string_append(v___x_6992_, v___x_6996_);
lean_dec_ref(v___x_6996_);
return v___x_6997_;
}
else
{
lean_object* v_s_6998_; lean_object* v_revisionEndpoint_6999_; lean_object* v_url_7000_; lean_object* v___x_7001_; lean_object* v___x_7002_; uint8_t v___x_7003_; 
v_s_6998_ = lean_ctor_get(v_scope_6970_, 0);
lean_inc_ref(v_s_6998_);
lean_dec_ref_known(v_scope_6970_, 1);
v_revisionEndpoint_6999_ = lean_ctor_get(v_service_6969_, 3);
lean_inc_ref(v_revisionEndpoint_6999_);
lean_dec_ref(v_service_6969_);
v_url_7000_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_6999_, v_s_6998_);
v___x_7001_ = lean_string_utf8_byte_size(v_platform_6971_);
v___x_7002_ = lean_unsigned_to_nat(0u);
v___x_7003_ = lean_nat_dec_eq(v___x_7001_, v___x_7002_);
if (v___x_7003_ == 0)
{
lean_object* v___x_7004_; lean_object* v___x_7005_; lean_object* v_url_7006_; 
v___x_7004_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_7005_ = lean_string_append(v_url_7000_, v___x_7004_);
v_url_7006_ = l_Lake_uriEncode(v_platform_6971_, v___x_7005_);
v_url_6981_ = v_url_7006_;
goto v___jp_6980_;
}
else
{
lean_dec_ref(v_platform_6971_);
v_url_6981_ = v_url_7000_;
goto v___jp_6980_;
}
}
v___jp_6973_:
{
lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; lean_object* v___x_6979_; 
v___x_6975_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_6976_ = lean_string_append(v_url_6974_, v___x_6975_);
v___x_6977_ = lean_string_append(v___x_6976_, v_rev_6968_);
v___x_6978_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_6979_ = lean_string_append(v___x_6977_, v___x_6978_);
return v___x_6979_;
}
v___jp_6980_:
{
lean_object* v___x_6982_; lean_object* v___x_6983_; uint8_t v___x_6984_; 
v___x_6982_ = lean_string_utf8_byte_size(v_toolchain_6972_);
v___x_6983_ = lean_unsigned_to_nat(0u);
v___x_6984_ = lean_nat_dec_eq(v___x_6982_, v___x_6983_);
if (v___x_6984_ == 0)
{
lean_object* v___x_6985_; lean_object* v___x_6986_; lean_object* v___x_6987_; lean_object* v___x_6988_; lean_object* v_url_6989_; 
v___x_6985_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6986_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_6972_, v___x_6985_, v___x_6983_);
v___x_6987_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_6988_ = lean_string_append(v_url_6981_, v___x_6987_);
v_url_6989_ = l_Lake_uriEncode(v___x_6986_, v___x_6988_);
v_url_6974_ = v_url_6989_;
goto v___jp_6973_;
}
else
{
v_url_6974_ = v_url_6981_;
goto v___jp_6973_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_7007_, lean_object* v_service_7008_, lean_object* v_scope_7009_, lean_object* v_platform_7010_, lean_object* v_toolchain_7011_){
_start:
{
lean_object* v_res_7012_; 
v_res_7012_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7007_, v_service_7008_, v_scope_7009_, v_platform_7010_, v_toolchain_7011_);
lean_dec_ref(v_toolchain_7011_);
lean_dec_ref(v_rev_7007_);
return v_res_7012_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_7016_, lean_object* v_service_7017_, lean_object* v_scope_7018_, lean_object* v_platform_7019_, lean_object* v_toolchain_7020_){
_start:
{
lean_object* v_url_7022_; lean_object* v___y_7030_; uint8_t v_isReservoir_7040_; 
v_isReservoir_7040_ = lean_ctor_get_uint8(v_service_7017_, sizeof(void*)*5);
if (v_isReservoir_7040_ == 0)
{
lean_object* v___x_7041_; 
v___x_7041_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7016_, v_service_7017_, v_scope_7018_, v_platform_7019_, v_toolchain_7020_);
lean_dec_ref(v_toolchain_7020_);
return v___x_7041_;
}
else
{
if (lean_obj_tag(v_scope_7018_) == 0)
{
lean_object* v_apiEndpoint_7042_; lean_object* v_s_7043_; lean_object* v___x_7044_; lean_object* v___x_7045_; lean_object* v___x_7046_; 
v_apiEndpoint_7042_ = lean_ctor_get(v_service_7017_, 4);
lean_inc_ref(v_apiEndpoint_7042_);
lean_dec_ref(v_service_7017_);
v_s_7043_ = lean_ctor_get(v_scope_7018_, 0);
lean_inc_ref(v_s_7043_);
lean_dec_ref_known(v_scope_7018_, 1);
v___x_7044_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_7045_ = lean_string_append(v_apiEndpoint_7042_, v___x_7044_);
v___x_7046_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_7045_, v_s_7043_);
v___y_7030_ = v___x_7046_;
goto v___jp_7029_;
}
else
{
lean_object* v_apiEndpoint_7047_; lean_object* v_s_7048_; lean_object* v___x_7049_; lean_object* v___x_7050_; lean_object* v___x_7051_; 
v_apiEndpoint_7047_ = lean_ctor_get(v_service_7017_, 4);
lean_inc_ref(v_apiEndpoint_7047_);
lean_dec_ref(v_service_7017_);
v_s_7048_ = lean_ctor_get(v_scope_7018_, 0);
lean_inc_ref(v_s_7048_);
lean_dec_ref_known(v_scope_7018_, 1);
v___x_7049_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_7050_ = lean_string_append(v_apiEndpoint_7047_, v___x_7049_);
v___x_7051_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_7050_, v_s_7048_);
v___y_7030_ = v___x_7051_;
goto v___jp_7029_;
}
}
v___jp_7021_:
{
lean_object* v___x_7023_; lean_object* v___x_7024_; uint8_t v___x_7025_; 
v___x_7023_ = lean_string_utf8_byte_size(v_toolchain_7020_);
v___x_7024_ = lean_unsigned_to_nat(0u);
v___x_7025_ = lean_nat_dec_eq(v___x_7023_, v___x_7024_);
if (v___x_7025_ == 0)
{
lean_object* v___x_7026_; lean_object* v___x_7027_; lean_object* v_url_7028_; 
v___x_7026_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_7027_ = lean_string_append(v_url_7022_, v___x_7026_);
v_url_7028_ = l_Lake_uriEncode(v_toolchain_7020_, v___x_7027_);
return v_url_7028_;
}
else
{
lean_dec_ref(v_toolchain_7020_);
return v_url_7022_;
}
}
v___jp_7029_:
{
lean_object* v___x_7031_; lean_object* v___x_7032_; lean_object* v_url_7033_; lean_object* v___x_7034_; lean_object* v___x_7035_; uint8_t v___x_7036_; 
v___x_7031_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_7032_ = lean_string_append(v___y_7030_, v___x_7031_);
v_url_7033_ = lean_string_append(v___x_7032_, v_rev_7016_);
v___x_7034_ = lean_string_utf8_byte_size(v_platform_7019_);
v___x_7035_ = lean_unsigned_to_nat(0u);
v___x_7036_ = lean_nat_dec_eq(v___x_7034_, v___x_7035_);
if (v___x_7036_ == 0)
{
lean_object* v___x_7037_; lean_object* v___x_7038_; lean_object* v_url_7039_; 
v___x_7037_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_7038_ = lean_string_append(v_url_7033_, v___x_7037_);
v_url_7039_ = l_Lake_uriEncode(v_platform_7019_, v___x_7038_);
v_url_7022_ = v_url_7039_;
goto v___jp_7021_;
}
else
{
lean_dec_ref(v_platform_7019_);
v_url_7022_ = v_url_7033_;
goto v___jp_7021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_7052_, lean_object* v_service_7053_, lean_object* v_scope_7054_, lean_object* v_platform_7055_, lean_object* v_toolchain_7056_){
_start:
{
lean_object* v_res_7057_; 
v_res_7057_ = l_Lake_CacheService_revisionUrl(v_rev_7052_, v_service_7053_, v_scope_7054_, v_platform_7055_, v_toolchain_7056_);
lean_dec_ref(v_rev_7052_);
return v_res_7057_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_7062_, lean_object* v_cache_7063_, lean_object* v_service_7064_, lean_object* v_localScope_7065_, lean_object* v_remoteScope_7066_, lean_object* v_platform_7067_, lean_object* v_toolchain_7068_, uint8_t v_force_7069_, lean_object* v_a_7070_){
_start:
{
lean_object* v_a_7076_; lean_object* v_a_7083_; lean_object* v___y_7087_; lean_object* v___y_7088_; lean_object* v_a_7096_; lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; lean_object* v___x_7103_; lean_object* v___x_7104_; lean_object* v_path_7105_; lean_object* v_a_7107_; lean_object* v___y_7209_; lean_object* v___y_7210_; uint8_t v___x_7259_; lean_object* v___x_7324_; uint8_t v___x_7325_; 
v___x_7100_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_7101_ = l_System_FilePath_join(v_cache_7063_, v___x_7100_);
lean_inc_ref(v_localScope_7065_);
v___x_7102_ = l_System_FilePath_join(v___x_7101_, v_localScope_7065_);
v___x_7103_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_7062_);
v___x_7104_ = lean_string_append(v_rev_7062_, v___x_7103_);
v_path_7105_ = l_System_FilePath_join(v___x_7102_, v___x_7104_);
v___x_7259_ = l_System_FilePath_pathExists(v_path_7105_);
v___x_7324_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7325_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_7325_ == 0)
{
goto v___jp_7260_;
}
else
{
lean_object* v___x_7326_; uint8_t v___x_7327_; 
v___x_7326_ = lean_box(0);
v___x_7327_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_7327_ == 0)
{
if (v___x_7325_ == 0)
{
goto v___jp_7260_;
}
else
{
size_t v___x_7328_; size_t v___x_7329_; lean_object* v___x_7330_; 
v___x_7328_ = ((size_t)0ULL);
v___x_7329_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_7330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_7324_, v___x_7328_, v___x_7329_, v___x_7326_, v_a_7070_);
if (lean_obj_tag(v___x_7330_) == 0)
{
lean_dec_ref_known(v___x_7330_, 1);
goto v___jp_7260_;
}
else
{
lean_object* v_a_7331_; lean_object* v___x_7333_; uint8_t v_isShared_7334_; uint8_t v_isSharedCheck_7338_; 
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_toolchain_7068_);
lean_dec_ref(v_platform_7067_);
lean_dec_ref(v_remoteScope_7066_);
lean_dec_ref(v_localScope_7065_);
lean_dec_ref(v_service_7064_);
lean_dec_ref(v_rev_7062_);
v_a_7331_ = lean_ctor_get(v___x_7330_, 0);
v_isSharedCheck_7338_ = !lean_is_exclusive(v___x_7330_);
if (v_isSharedCheck_7338_ == 0)
{
v___x_7333_ = v___x_7330_;
v_isShared_7334_ = v_isSharedCheck_7338_;
goto v_resetjp_7332_;
}
else
{
lean_inc(v_a_7331_);
lean_dec(v___x_7330_);
v___x_7333_ = lean_box(0);
v_isShared_7334_ = v_isSharedCheck_7338_;
goto v_resetjp_7332_;
}
v_resetjp_7332_:
{
lean_object* v___x_7336_; 
if (v_isShared_7334_ == 0)
{
v___x_7336_ = v___x_7333_;
goto v_reusejp_7335_;
}
else
{
lean_object* v_reuseFailAlloc_7337_; 
v_reuseFailAlloc_7337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7337_, 0, v_a_7331_);
v___x_7336_ = v_reuseFailAlloc_7337_;
goto v_reusejp_7335_;
}
v_reusejp_7335_:
{
return v___x_7336_;
}
}
}
}
}
else
{
size_t v___x_7339_; size_t v___x_7340_; lean_object* v___x_7341_; 
v___x_7339_ = ((size_t)0ULL);
v___x_7340_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_7341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_7324_, v___x_7339_, v___x_7340_, v___x_7326_, v_a_7070_);
if (lean_obj_tag(v___x_7341_) == 0)
{
lean_dec_ref_known(v___x_7341_, 1);
goto v___jp_7260_;
}
else
{
lean_object* v_a_7342_; lean_object* v___x_7344_; uint8_t v_isShared_7345_; uint8_t v_isSharedCheck_7349_; 
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_toolchain_7068_);
lean_dec_ref(v_platform_7067_);
lean_dec_ref(v_remoteScope_7066_);
lean_dec_ref(v_localScope_7065_);
lean_dec_ref(v_service_7064_);
lean_dec_ref(v_rev_7062_);
v_a_7342_ = lean_ctor_get(v___x_7341_, 0);
v_isSharedCheck_7349_ = !lean_is_exclusive(v___x_7341_);
if (v_isSharedCheck_7349_ == 0)
{
v___x_7344_ = v___x_7341_;
v_isShared_7345_ = v_isSharedCheck_7349_;
goto v_resetjp_7343_;
}
else
{
lean_inc(v_a_7342_);
lean_dec(v___x_7341_);
v___x_7344_ = lean_box(0);
v_isShared_7345_ = v_isSharedCheck_7349_;
goto v_resetjp_7343_;
}
v_resetjp_7343_:
{
lean_object* v___x_7347_; 
if (v_isShared_7345_ == 0)
{
v___x_7347_ = v___x_7344_;
goto v_reusejp_7346_;
}
else
{
lean_object* v_reuseFailAlloc_7348_; 
v_reuseFailAlloc_7348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7348_, 0, v_a_7342_);
v___x_7347_ = v_reuseFailAlloc_7348_;
goto v_reusejp_7346_;
}
v_reusejp_7346_:
{
return v___x_7347_;
}
}
}
}
}
v___jp_7072_:
{
lean_object* v___x_7073_; lean_object* v___x_7074_; 
v___x_7073_ = lean_box(0);
v___x_7074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7074_, 0, v___x_7073_);
return v___x_7074_;
}
v___jp_7075_:
{
lean_object* v___x_7077_; lean_object* v___x_7078_; 
v___x_7077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7077_, 0, v_a_7076_);
v___x_7078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7078_, 0, v___x_7077_);
return v___x_7078_;
}
v___jp_7079_:
{
lean_object* v___x_7080_; lean_object* v___x_7081_; 
v___x_7080_ = lean_box(0);
v___x_7081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7081_, 0, v___x_7080_);
return v___x_7081_;
}
v___jp_7082_:
{
lean_object* v___x_7084_; lean_object* v___x_7085_; 
v___x_7084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7084_, 0, v_a_7083_);
v___x_7085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7085_, 0, v___x_7084_);
return v___x_7085_;
}
v___jp_7086_:
{
lean_object* v___x_7089_; lean_object* v___x_7090_; uint8_t v___x_7091_; lean_object* v___x_7092_; lean_object* v___x_7093_; lean_object* v___x_7094_; 
v___x_7089_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_7090_ = lean_string_append(v___y_7088_, v___x_7089_);
v___x_7091_ = 3;
v___x_7092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7092_, 0, v___x_7090_);
lean_ctor_set_uint8(v___x_7092_, sizeof(void*)*1, v___x_7091_);
lean_inc_ref(v_a_7070_);
v___x_7093_ = lean_apply_2(v_a_7070_, v___x_7092_, lean_box(0));
v___x_7094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7094_, 0, v___y_7087_);
return v___x_7094_;
}
v___jp_7095_:
{
lean_object* v_s_7097_; 
v_s_7097_ = lean_ctor_get(v_remoteScope_7066_, 0);
lean_inc_ref(v_s_7097_);
lean_dec_ref(v_remoteScope_7066_);
v___y_7087_ = v_a_7096_;
v___y_7088_ = v_s_7097_;
goto v___jp_7086_;
}
v___jp_7098_:
{
lean_object* v___x_7099_; 
v___x_7099_ = lean_box(0);
v_a_7096_ = v___x_7099_;
goto v___jp_7095_;
}
v___jp_7106_:
{
if (lean_obj_tag(v_a_7107_) == 1)
{
lean_object* v_val_7108_; lean_object* v___x_7109_; 
v_val_7108_ = lean_ctor_get(v_a_7107_, 0);
lean_inc(v_val_7108_);
lean_dec_ref_known(v_a_7107_, 1);
lean_inc_ref(v_path_7105_);
v___x_7109_ = l_Lake_createParentDirs(v_path_7105_);
if (lean_obj_tag(v___x_7109_) == 0)
{
lean_object* v___x_7110_; 
lean_dec_ref_known(v___x_7109_, 1);
v___x_7110_ = l_IO_FS_writeFile(v_path_7105_, v_val_7108_);
lean_dec(v_val_7108_);
if (lean_obj_tag(v___x_7110_) == 0)
{
lean_object* v___x_7112_; uint8_t v_isShared_7113_; uint8_t v_isSharedCheck_7178_; 
v_isSharedCheck_7178_ = !lean_is_exclusive(v___x_7110_);
if (v_isSharedCheck_7178_ == 0)
{
lean_object* v_unused_7179_; 
v_unused_7179_ = lean_ctor_get(v___x_7110_, 0);
lean_dec(v_unused_7179_);
v___x_7112_ = v___x_7110_;
v_isShared_7113_ = v_isSharedCheck_7178_;
goto v_resetjp_7111_;
}
else
{
lean_dec(v___x_7110_);
v___x_7112_ = lean_box(0);
v_isShared_7113_ = v_isSharedCheck_7178_;
goto v_resetjp_7111_;
}
v_resetjp_7111_:
{
lean_object* v___x_7114_; lean_object* v___x_7115_; uint8_t v___x_7116_; lean_object* v___x_7117_; lean_object* v___x_7118_; 
v___x_7114_ = lean_string_utf8_byte_size(v_platform_7067_);
lean_dec_ref(v_platform_7067_);
v___x_7115_ = lean_unsigned_to_nat(0u);
v___x_7116_ = lean_nat_dec_eq(v___x_7114_, v___x_7115_);
v___x_7117_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7118_ = l_Lake_CacheMap_load(v_path_7105_, v___x_7116_, v___x_7117_);
if (lean_obj_tag(v___x_7118_) == 0)
{
lean_object* v_a_7119_; lean_object* v_a_7120_; lean_object* v___x_7121_; uint8_t v___x_7122_; 
lean_del_object(v___x_7112_);
v_a_7119_ = lean_ctor_get(v___x_7118_, 0);
lean_inc(v_a_7119_);
v_a_7120_ = lean_ctor_get(v___x_7118_, 1);
lean_inc(v_a_7120_);
lean_dec_ref_known(v___x_7118_, 2);
v___x_7121_ = lean_array_get_size(v_a_7120_);
v___x_7122_ = lean_nat_dec_lt(v___x_7115_, v___x_7121_);
if (v___x_7122_ == 0)
{
lean_dec(v_a_7120_);
v_a_7083_ = v_a_7119_;
goto v___jp_7082_;
}
else
{
lean_object* v___x_7123_; uint8_t v___x_7124_; 
v___x_7123_ = lean_box(0);
v___x_7124_ = lean_nat_dec_le(v___x_7121_, v___x_7121_);
if (v___x_7124_ == 0)
{
if (v___x_7122_ == 0)
{
lean_dec(v_a_7120_);
v_a_7083_ = v_a_7119_;
goto v___jp_7082_;
}
else
{
size_t v___x_7125_; size_t v___x_7126_; lean_object* v___x_7127_; 
v___x_7125_ = ((size_t)0ULL);
v___x_7126_ = lean_usize_of_nat(v___x_7121_);
v___x_7127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7120_, v___x_7125_, v___x_7126_, v___x_7123_, v_a_7070_);
lean_dec(v_a_7120_);
if (lean_obj_tag(v___x_7127_) == 0)
{
lean_dec_ref_known(v___x_7127_, 1);
v_a_7083_ = v_a_7119_;
goto v___jp_7082_;
}
else
{
lean_object* v_a_7128_; lean_object* v___x_7130_; uint8_t v_isShared_7131_; uint8_t v_isSharedCheck_7135_; 
lean_dec(v_a_7119_);
v_a_7128_ = lean_ctor_get(v___x_7127_, 0);
v_isSharedCheck_7135_ = !lean_is_exclusive(v___x_7127_);
if (v_isSharedCheck_7135_ == 0)
{
v___x_7130_ = v___x_7127_;
v_isShared_7131_ = v_isSharedCheck_7135_;
goto v_resetjp_7129_;
}
else
{
lean_inc(v_a_7128_);
lean_dec(v___x_7127_);
v___x_7130_ = lean_box(0);
v_isShared_7131_ = v_isSharedCheck_7135_;
goto v_resetjp_7129_;
}
v_resetjp_7129_:
{
lean_object* v___x_7133_; 
if (v_isShared_7131_ == 0)
{
v___x_7133_ = v___x_7130_;
goto v_reusejp_7132_;
}
else
{
lean_object* v_reuseFailAlloc_7134_; 
v_reuseFailAlloc_7134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7134_, 0, v_a_7128_);
v___x_7133_ = v_reuseFailAlloc_7134_;
goto v_reusejp_7132_;
}
v_reusejp_7132_:
{
return v___x_7133_;
}
}
}
}
}
else
{
size_t v___x_7136_; size_t v___x_7137_; lean_object* v___x_7138_; 
v___x_7136_ = ((size_t)0ULL);
v___x_7137_ = lean_usize_of_nat(v___x_7121_);
v___x_7138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7120_, v___x_7136_, v___x_7137_, v___x_7123_, v_a_7070_);
lean_dec(v_a_7120_);
if (lean_obj_tag(v___x_7138_) == 0)
{
lean_dec_ref_known(v___x_7138_, 1);
v_a_7083_ = v_a_7119_;
goto v___jp_7082_;
}
else
{
lean_object* v_a_7139_; lean_object* v___x_7141_; uint8_t v_isShared_7142_; uint8_t v_isSharedCheck_7146_; 
lean_dec(v_a_7119_);
v_a_7139_ = lean_ctor_get(v___x_7138_, 0);
v_isSharedCheck_7146_ = !lean_is_exclusive(v___x_7138_);
if (v_isSharedCheck_7146_ == 0)
{
v___x_7141_ = v___x_7138_;
v_isShared_7142_ = v_isSharedCheck_7146_;
goto v_resetjp_7140_;
}
else
{
lean_inc(v_a_7139_);
lean_dec(v___x_7138_);
v___x_7141_ = lean_box(0);
v_isShared_7142_ = v_isSharedCheck_7146_;
goto v_resetjp_7140_;
}
v_resetjp_7140_:
{
lean_object* v___x_7144_; 
if (v_isShared_7142_ == 0)
{
v___x_7144_ = v___x_7141_;
goto v_reusejp_7143_;
}
else
{
lean_object* v_reuseFailAlloc_7145_; 
v_reuseFailAlloc_7145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7145_, 0, v_a_7139_);
v___x_7144_ = v_reuseFailAlloc_7145_;
goto v_reusejp_7143_;
}
v_reusejp_7143_:
{
return v___x_7144_;
}
}
}
}
}
}
else
{
lean_object* v_a_7147_; lean_object* v___x_7148_; uint8_t v___x_7149_; 
v_a_7147_ = lean_ctor_get(v___x_7118_, 1);
lean_inc(v_a_7147_);
lean_dec_ref_known(v___x_7118_, 2);
v___x_7148_ = lean_array_get_size(v_a_7147_);
v___x_7149_ = lean_nat_dec_lt(v___x_7115_, v___x_7148_);
if (v___x_7149_ == 0)
{
lean_object* v___x_7150_; lean_object* v___x_7152_; 
lean_dec(v_a_7147_);
v___x_7150_ = lean_box(0);
if (v_isShared_7113_ == 0)
{
lean_ctor_set_tag(v___x_7112_, 1);
lean_ctor_set(v___x_7112_, 0, v___x_7150_);
v___x_7152_ = v___x_7112_;
goto v_reusejp_7151_;
}
else
{
lean_object* v_reuseFailAlloc_7153_; 
v_reuseFailAlloc_7153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7153_, 0, v___x_7150_);
v___x_7152_ = v_reuseFailAlloc_7153_;
goto v_reusejp_7151_;
}
v_reusejp_7151_:
{
return v___x_7152_;
}
}
else
{
lean_object* v___x_7154_; uint8_t v___x_7155_; 
lean_del_object(v___x_7112_);
v___x_7154_ = lean_box(0);
v___x_7155_ = lean_nat_dec_le(v___x_7148_, v___x_7148_);
if (v___x_7155_ == 0)
{
if (v___x_7149_ == 0)
{
lean_dec(v_a_7147_);
goto v___jp_7079_;
}
else
{
size_t v___x_7156_; size_t v___x_7157_; lean_object* v___x_7158_; 
v___x_7156_ = ((size_t)0ULL);
v___x_7157_ = lean_usize_of_nat(v___x_7148_);
v___x_7158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7147_, v___x_7156_, v___x_7157_, v___x_7154_, v_a_7070_);
lean_dec(v_a_7147_);
if (lean_obj_tag(v___x_7158_) == 0)
{
lean_dec_ref_known(v___x_7158_, 1);
goto v___jp_7079_;
}
else
{
lean_object* v_a_7159_; lean_object* v___x_7161_; uint8_t v_isShared_7162_; uint8_t v_isSharedCheck_7166_; 
v_a_7159_ = lean_ctor_get(v___x_7158_, 0);
v_isSharedCheck_7166_ = !lean_is_exclusive(v___x_7158_);
if (v_isSharedCheck_7166_ == 0)
{
v___x_7161_ = v___x_7158_;
v_isShared_7162_ = v_isSharedCheck_7166_;
goto v_resetjp_7160_;
}
else
{
lean_inc(v_a_7159_);
lean_dec(v___x_7158_);
v___x_7161_ = lean_box(0);
v_isShared_7162_ = v_isSharedCheck_7166_;
goto v_resetjp_7160_;
}
v_resetjp_7160_:
{
lean_object* v___x_7164_; 
if (v_isShared_7162_ == 0)
{
v___x_7164_ = v___x_7161_;
goto v_reusejp_7163_;
}
else
{
lean_object* v_reuseFailAlloc_7165_; 
v_reuseFailAlloc_7165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7165_, 0, v_a_7159_);
v___x_7164_ = v_reuseFailAlloc_7165_;
goto v_reusejp_7163_;
}
v_reusejp_7163_:
{
return v___x_7164_;
}
}
}
}
}
else
{
size_t v___x_7167_; size_t v___x_7168_; lean_object* v___x_7169_; 
v___x_7167_ = ((size_t)0ULL);
v___x_7168_ = lean_usize_of_nat(v___x_7148_);
v___x_7169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7147_, v___x_7167_, v___x_7168_, v___x_7154_, v_a_7070_);
lean_dec(v_a_7147_);
if (lean_obj_tag(v___x_7169_) == 0)
{
lean_dec_ref_known(v___x_7169_, 1);
goto v___jp_7079_;
}
else
{
lean_object* v_a_7170_; lean_object* v___x_7172_; uint8_t v_isShared_7173_; uint8_t v_isSharedCheck_7177_; 
v_a_7170_ = lean_ctor_get(v___x_7169_, 0);
v_isSharedCheck_7177_ = !lean_is_exclusive(v___x_7169_);
if (v_isSharedCheck_7177_ == 0)
{
v___x_7172_ = v___x_7169_;
v_isShared_7173_ = v_isSharedCheck_7177_;
goto v_resetjp_7171_;
}
else
{
lean_inc(v_a_7170_);
lean_dec(v___x_7169_);
v___x_7172_ = lean_box(0);
v_isShared_7173_ = v_isSharedCheck_7177_;
goto v_resetjp_7171_;
}
v_resetjp_7171_:
{
lean_object* v___x_7175_; 
if (v_isShared_7173_ == 0)
{
v___x_7175_ = v___x_7172_;
goto v_reusejp_7174_;
}
else
{
lean_object* v_reuseFailAlloc_7176_; 
v_reuseFailAlloc_7176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7176_, 0, v_a_7170_);
v___x_7175_ = v_reuseFailAlloc_7176_;
goto v_reusejp_7174_;
}
v_reusejp_7174_:
{
return v___x_7175_;
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
lean_object* v_a_7180_; lean_object* v___x_7182_; uint8_t v_isShared_7183_; uint8_t v_isSharedCheck_7192_; 
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_platform_7067_);
v_a_7180_ = lean_ctor_get(v___x_7110_, 0);
v_isSharedCheck_7192_ = !lean_is_exclusive(v___x_7110_);
if (v_isSharedCheck_7192_ == 0)
{
v___x_7182_ = v___x_7110_;
v_isShared_7183_ = v_isSharedCheck_7192_;
goto v_resetjp_7181_;
}
else
{
lean_inc(v_a_7180_);
lean_dec(v___x_7110_);
v___x_7182_ = lean_box(0);
v_isShared_7183_ = v_isSharedCheck_7192_;
goto v_resetjp_7181_;
}
v_resetjp_7181_:
{
lean_object* v___x_7184_; uint8_t v___x_7185_; lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7190_; 
v___x_7184_ = lean_io_error_to_string(v_a_7180_);
v___x_7185_ = 3;
v___x_7186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7186_, 0, v___x_7184_);
lean_ctor_set_uint8(v___x_7186_, sizeof(void*)*1, v___x_7185_);
lean_inc_ref(v_a_7070_);
v___x_7187_ = lean_apply_2(v_a_7070_, v___x_7186_, lean_box(0));
v___x_7188_ = lean_box(0);
if (v_isShared_7183_ == 0)
{
lean_ctor_set(v___x_7182_, 0, v___x_7188_);
v___x_7190_ = v___x_7182_;
goto v_reusejp_7189_;
}
else
{
lean_object* v_reuseFailAlloc_7191_; 
v_reuseFailAlloc_7191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7191_, 0, v___x_7188_);
v___x_7190_ = v_reuseFailAlloc_7191_;
goto v_reusejp_7189_;
}
v_reusejp_7189_:
{
return v___x_7190_;
}
}
}
}
else
{
lean_object* v_a_7193_; lean_object* v___x_7195_; uint8_t v_isShared_7196_; uint8_t v_isSharedCheck_7205_; 
lean_dec(v_val_7108_);
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_platform_7067_);
v_a_7193_ = lean_ctor_get(v___x_7109_, 0);
v_isSharedCheck_7205_ = !lean_is_exclusive(v___x_7109_);
if (v_isSharedCheck_7205_ == 0)
{
v___x_7195_ = v___x_7109_;
v_isShared_7196_ = v_isSharedCheck_7205_;
goto v_resetjp_7194_;
}
else
{
lean_inc(v_a_7193_);
lean_dec(v___x_7109_);
v___x_7195_ = lean_box(0);
v_isShared_7196_ = v_isSharedCheck_7205_;
goto v_resetjp_7194_;
}
v_resetjp_7194_:
{
lean_object* v___x_7197_; uint8_t v___x_7198_; lean_object* v___x_7199_; lean_object* v___x_7200_; lean_object* v___x_7201_; lean_object* v___x_7203_; 
v___x_7197_ = lean_io_error_to_string(v_a_7193_);
v___x_7198_ = 3;
v___x_7199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7199_, 0, v___x_7197_);
lean_ctor_set_uint8(v___x_7199_, sizeof(void*)*1, v___x_7198_);
lean_inc_ref(v_a_7070_);
v___x_7200_ = lean_apply_2(v_a_7070_, v___x_7199_, lean_box(0));
v___x_7201_ = lean_box(0);
if (v_isShared_7196_ == 0)
{
lean_ctor_set(v___x_7195_, 0, v___x_7201_);
v___x_7203_ = v___x_7195_;
goto v_reusejp_7202_;
}
else
{
lean_object* v_reuseFailAlloc_7204_; 
v_reuseFailAlloc_7204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7204_, 0, v___x_7201_);
v___x_7203_ = v_reuseFailAlloc_7204_;
goto v_reusejp_7202_;
}
v_reusejp_7202_:
{
return v___x_7203_;
}
}
}
}
else
{
lean_object* v___x_7206_; lean_object* v___x_7207_; 
lean_dec(v_a_7107_);
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_platform_7067_);
v___x_7206_ = lean_box(0);
v___x_7207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7207_, 0, v___x_7206_);
return v___x_7207_;
}
}
v___jp_7208_:
{
lean_object* v___x_7211_; lean_object* v___x_7212_; lean_object* v___x_7213_; 
v___x_7211_ = lean_unsigned_to_nat(0u);
v___x_7212_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7213_ = l_Lake_getUrl_x3f(v___y_7209_, v___y_7210_, v___x_7212_);
if (lean_obj_tag(v___x_7213_) == 0)
{
lean_object* v_a_7214_; lean_object* v_a_7215_; lean_object* v___x_7216_; uint8_t v___x_7217_; 
v_a_7214_ = lean_ctor_get(v___x_7213_, 0);
lean_inc(v_a_7214_);
v_a_7215_ = lean_ctor_get(v___x_7213_, 1);
lean_inc(v_a_7215_);
lean_dec_ref_known(v___x_7213_, 2);
v___x_7216_ = lean_array_get_size(v_a_7215_);
v___x_7217_ = lean_nat_dec_lt(v___x_7211_, v___x_7216_);
if (v___x_7217_ == 0)
{
lean_dec(v_a_7215_);
lean_dec_ref(v_remoteScope_7066_);
v_a_7107_ = v_a_7214_;
goto v___jp_7106_;
}
else
{
lean_object* v___x_7218_; uint8_t v___x_7219_; 
v___x_7218_ = lean_box(0);
v___x_7219_ = lean_nat_dec_le(v___x_7216_, v___x_7216_);
if (v___x_7219_ == 0)
{
if (v___x_7217_ == 0)
{
lean_dec(v_a_7215_);
lean_dec_ref(v_remoteScope_7066_);
v_a_7107_ = v_a_7214_;
goto v___jp_7106_;
}
else
{
size_t v___x_7220_; size_t v___x_7221_; lean_object* v___x_7222_; 
v___x_7220_ = ((size_t)0ULL);
v___x_7221_ = lean_usize_of_nat(v___x_7216_);
v___x_7222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7215_, v___x_7220_, v___x_7221_, v___x_7218_, v_a_7070_);
lean_dec(v_a_7215_);
if (lean_obj_tag(v___x_7222_) == 0)
{
lean_dec_ref_known(v___x_7222_, 1);
lean_dec_ref(v_remoteScope_7066_);
v_a_7107_ = v_a_7214_;
goto v___jp_7106_;
}
else
{
lean_object* v_a_7223_; 
lean_dec(v_a_7214_);
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_platform_7067_);
v_a_7223_ = lean_ctor_get(v___x_7222_, 0);
lean_inc(v_a_7223_);
lean_dec_ref_known(v___x_7222_, 1);
v_a_7096_ = v_a_7223_;
goto v___jp_7095_;
}
}
}
else
{
size_t v___x_7224_; size_t v___x_7225_; lean_object* v___x_7226_; 
v___x_7224_ = ((size_t)0ULL);
v___x_7225_ = lean_usize_of_nat(v___x_7216_);
v___x_7226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7215_, v___x_7224_, v___x_7225_, v___x_7218_, v_a_7070_);
lean_dec(v_a_7215_);
if (lean_obj_tag(v___x_7226_) == 0)
{
lean_dec_ref_known(v___x_7226_, 1);
lean_dec_ref(v_remoteScope_7066_);
v_a_7107_ = v_a_7214_;
goto v___jp_7106_;
}
else
{
lean_object* v_a_7227_; 
lean_dec(v_a_7214_);
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_platform_7067_);
v_a_7227_ = lean_ctor_get(v___x_7226_, 0);
lean_inc(v_a_7227_);
lean_dec_ref_known(v___x_7226_, 1);
v_a_7096_ = v_a_7227_;
goto v___jp_7095_;
}
}
}
}
else
{
lean_object* v_a_7228_; lean_object* v___x_7229_; uint8_t v___x_7230_; 
lean_dec_ref(v_path_7105_);
lean_dec_ref(v_platform_7067_);
v_a_7228_ = lean_ctor_get(v___x_7213_, 1);
lean_inc(v_a_7228_);
lean_dec_ref_known(v___x_7213_, 2);
v___x_7229_ = lean_array_get_size(v_a_7228_);
v___x_7230_ = lean_nat_dec_lt(v___x_7211_, v___x_7229_);
if (v___x_7230_ == 0)
{
lean_object* v___x_7231_; 
lean_dec(v_a_7228_);
v___x_7231_ = lean_box(0);
v_a_7096_ = v___x_7231_;
goto v___jp_7095_;
}
else
{
lean_object* v___x_7232_; uint8_t v___x_7233_; 
v___x_7232_ = lean_box(0);
v___x_7233_ = lean_nat_dec_le(v___x_7229_, v___x_7229_);
if (v___x_7233_ == 0)
{
if (v___x_7230_ == 0)
{
lean_dec(v_a_7228_);
goto v___jp_7098_;
}
else
{
size_t v___x_7234_; size_t v___x_7235_; lean_object* v___x_7236_; 
v___x_7234_ = ((size_t)0ULL);
v___x_7235_ = lean_usize_of_nat(v___x_7229_);
v___x_7236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7228_, v___x_7234_, v___x_7235_, v___x_7232_, v_a_7070_);
lean_dec(v_a_7228_);
if (lean_obj_tag(v___x_7236_) == 0)
{
lean_dec_ref_known(v___x_7236_, 1);
goto v___jp_7098_;
}
else
{
lean_object* v_a_7237_; 
v_a_7237_ = lean_ctor_get(v___x_7236_, 0);
lean_inc(v_a_7237_);
lean_dec_ref_known(v___x_7236_, 1);
v_a_7096_ = v_a_7237_;
goto v___jp_7095_;
}
}
}
else
{
size_t v___x_7238_; size_t v___x_7239_; lean_object* v___x_7240_; 
v___x_7238_ = ((size_t)0ULL);
v___x_7239_ = lean_usize_of_nat(v___x_7229_);
v___x_7240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7228_, v___x_7238_, v___x_7239_, v___x_7232_, v_a_7070_);
lean_dec(v_a_7228_);
if (lean_obj_tag(v___x_7240_) == 0)
{
lean_dec_ref_known(v___x_7240_, 1);
goto v___jp_7098_;
}
else
{
lean_object* v_a_7241_; 
v_a_7241_ = lean_ctor_get(v___x_7240_, 0);
lean_inc(v_a_7241_);
lean_dec_ref_known(v___x_7240_, 1);
v_a_7096_ = v_a_7241_;
goto v___jp_7095_;
}
}
}
}
}
v___jp_7242_:
{
lean_object* v___x_7243_; lean_object* v___x_7244_; lean_object* v___x_7245_; lean_object* v___x_7246_; lean_object* v___x_7247_; lean_object* v___x_7248_; lean_object* v___x_7249_; lean_object* v___x_7250_; lean_object* v___x_7251_; lean_object* v___x_7252_; uint8_t v___x_7253_; lean_object* v___x_7254_; lean_object* v___x_7255_; uint8_t v_isReservoir_7256_; 
lean_inc_ref(v_platform_7067_);
lean_inc_ref(v_remoteScope_7066_);
lean_inc_ref(v_service_7064_);
v___x_7243_ = l_Lake_CacheService_revisionUrl(v_rev_7062_, v_service_7064_, v_remoteScope_7066_, v_platform_7067_, v_toolchain_7068_);
v___x_7244_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_7245_ = lean_string_append(v_localScope_7065_, v___x_7244_);
v___x_7246_ = lean_string_append(v___x_7245_, v_rev_7062_);
lean_dec_ref(v_rev_7062_);
v___x_7247_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_7248_ = lean_string_append(v___x_7246_, v___x_7247_);
v___x_7249_ = lean_string_append(v___x_7248_, v_path_7105_);
v___x_7250_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_7251_ = lean_string_append(v___x_7249_, v___x_7250_);
v___x_7252_ = lean_string_append(v___x_7251_, v___x_7243_);
v___x_7253_ = 1;
v___x_7254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7254_, 0, v___x_7252_);
lean_ctor_set_uint8(v___x_7254_, sizeof(void*)*1, v___x_7253_);
lean_inc_ref(v_a_7070_);
v___x_7255_ = lean_apply_2(v_a_7070_, v___x_7254_, lean_box(0));
v_isReservoir_7256_ = lean_ctor_get_uint8(v_service_7064_, sizeof(void*)*5);
lean_dec_ref(v_service_7064_);
if (v_isReservoir_7256_ == 0)
{
lean_object* v___x_7257_; 
v___x_7257_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_7209_ = v___x_7243_;
v___y_7210_ = v___x_7257_;
goto v___jp_7208_;
}
else
{
lean_object* v___x_7258_; 
v___x_7258_ = l_Lake_Reservoir_lakeHeaders;
v___y_7209_ = v___x_7243_;
v___y_7210_ = v___x_7258_;
goto v___jp_7208_;
}
}
v___jp_7260_:
{
if (v___x_7259_ == 0)
{
goto v___jp_7242_;
}
else
{
uint8_t v___x_7261_; 
v___x_7261_ = lean_bool_not(v_force_7069_);
if (v___x_7261_ == 0)
{
goto v___jp_7242_;
}
else
{
lean_object* v___x_7262_; lean_object* v___x_7263_; uint8_t v___x_7264_; lean_object* v___x_7265_; lean_object* v___x_7266_; 
lean_dec_ref(v_toolchain_7068_);
lean_dec_ref(v_remoteScope_7066_);
lean_dec_ref(v_localScope_7065_);
lean_dec_ref(v_service_7064_);
lean_dec_ref(v_rev_7062_);
v___x_7262_ = lean_string_utf8_byte_size(v_platform_7067_);
lean_dec_ref(v_platform_7067_);
v___x_7263_ = lean_unsigned_to_nat(0u);
v___x_7264_ = lean_nat_dec_eq(v___x_7262_, v___x_7263_);
v___x_7265_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7266_ = l_Lake_CacheMap_load(v_path_7105_, v___x_7264_, v___x_7265_);
if (lean_obj_tag(v___x_7266_) == 0)
{
lean_object* v_a_7267_; lean_object* v_a_7268_; lean_object* v___x_7269_; uint8_t v___x_7270_; 
v_a_7267_ = lean_ctor_get(v___x_7266_, 0);
lean_inc(v_a_7267_);
v_a_7268_ = lean_ctor_get(v___x_7266_, 1);
lean_inc(v_a_7268_);
lean_dec_ref_known(v___x_7266_, 2);
v___x_7269_ = lean_array_get_size(v_a_7268_);
v___x_7270_ = lean_nat_dec_lt(v___x_7263_, v___x_7269_);
if (v___x_7270_ == 0)
{
lean_dec(v_a_7268_);
v_a_7076_ = v_a_7267_;
goto v___jp_7075_;
}
else
{
lean_object* v___x_7271_; uint8_t v___x_7272_; 
v___x_7271_ = lean_box(0);
v___x_7272_ = lean_nat_dec_le(v___x_7269_, v___x_7269_);
if (v___x_7272_ == 0)
{
if (v___x_7270_ == 0)
{
lean_dec(v_a_7268_);
v_a_7076_ = v_a_7267_;
goto v___jp_7075_;
}
else
{
size_t v___x_7273_; size_t v___x_7274_; lean_object* v___x_7275_; 
v___x_7273_ = ((size_t)0ULL);
v___x_7274_ = lean_usize_of_nat(v___x_7269_);
v___x_7275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7268_, v___x_7273_, v___x_7274_, v___x_7271_, v_a_7070_);
lean_dec(v_a_7268_);
if (lean_obj_tag(v___x_7275_) == 0)
{
lean_dec_ref_known(v___x_7275_, 1);
v_a_7076_ = v_a_7267_;
goto v___jp_7075_;
}
else
{
lean_object* v_a_7276_; lean_object* v___x_7278_; uint8_t v_isShared_7279_; uint8_t v_isSharedCheck_7283_; 
lean_dec(v_a_7267_);
v_a_7276_ = lean_ctor_get(v___x_7275_, 0);
v_isSharedCheck_7283_ = !lean_is_exclusive(v___x_7275_);
if (v_isSharedCheck_7283_ == 0)
{
v___x_7278_ = v___x_7275_;
v_isShared_7279_ = v_isSharedCheck_7283_;
goto v_resetjp_7277_;
}
else
{
lean_inc(v_a_7276_);
lean_dec(v___x_7275_);
v___x_7278_ = lean_box(0);
v_isShared_7279_ = v_isSharedCheck_7283_;
goto v_resetjp_7277_;
}
v_resetjp_7277_:
{
lean_object* v___x_7281_; 
if (v_isShared_7279_ == 0)
{
v___x_7281_ = v___x_7278_;
goto v_reusejp_7280_;
}
else
{
lean_object* v_reuseFailAlloc_7282_; 
v_reuseFailAlloc_7282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7282_, 0, v_a_7276_);
v___x_7281_ = v_reuseFailAlloc_7282_;
goto v_reusejp_7280_;
}
v_reusejp_7280_:
{
return v___x_7281_;
}
}
}
}
}
else
{
size_t v___x_7284_; size_t v___x_7285_; lean_object* v___x_7286_; 
v___x_7284_ = ((size_t)0ULL);
v___x_7285_ = lean_usize_of_nat(v___x_7269_);
v___x_7286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7268_, v___x_7284_, v___x_7285_, v___x_7271_, v_a_7070_);
lean_dec(v_a_7268_);
if (lean_obj_tag(v___x_7286_) == 0)
{
lean_dec_ref_known(v___x_7286_, 1);
v_a_7076_ = v_a_7267_;
goto v___jp_7075_;
}
else
{
lean_object* v_a_7287_; lean_object* v___x_7289_; uint8_t v_isShared_7290_; uint8_t v_isSharedCheck_7294_; 
lean_dec(v_a_7267_);
v_a_7287_ = lean_ctor_get(v___x_7286_, 0);
v_isSharedCheck_7294_ = !lean_is_exclusive(v___x_7286_);
if (v_isSharedCheck_7294_ == 0)
{
v___x_7289_ = v___x_7286_;
v_isShared_7290_ = v_isSharedCheck_7294_;
goto v_resetjp_7288_;
}
else
{
lean_inc(v_a_7287_);
lean_dec(v___x_7286_);
v___x_7289_ = lean_box(0);
v_isShared_7290_ = v_isSharedCheck_7294_;
goto v_resetjp_7288_;
}
v_resetjp_7288_:
{
lean_object* v___x_7292_; 
if (v_isShared_7290_ == 0)
{
v___x_7292_ = v___x_7289_;
goto v_reusejp_7291_;
}
else
{
lean_object* v_reuseFailAlloc_7293_; 
v_reuseFailAlloc_7293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7293_, 0, v_a_7287_);
v___x_7292_ = v_reuseFailAlloc_7293_;
goto v_reusejp_7291_;
}
v_reusejp_7291_:
{
return v___x_7292_;
}
}
}
}
}
}
else
{
lean_object* v_a_7295_; lean_object* v___x_7296_; uint8_t v___x_7297_; 
v_a_7295_ = lean_ctor_get(v___x_7266_, 1);
lean_inc(v_a_7295_);
lean_dec_ref_known(v___x_7266_, 2);
v___x_7296_ = lean_array_get_size(v_a_7295_);
v___x_7297_ = lean_nat_dec_lt(v___x_7263_, v___x_7296_);
if (v___x_7297_ == 0)
{
lean_object* v___x_7298_; lean_object* v___x_7299_; 
lean_dec(v_a_7295_);
v___x_7298_ = lean_box(0);
v___x_7299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7299_, 0, v___x_7298_);
return v___x_7299_;
}
else
{
lean_object* v___x_7300_; uint8_t v___x_7301_; 
v___x_7300_ = lean_box(0);
v___x_7301_ = lean_nat_dec_le(v___x_7296_, v___x_7296_);
if (v___x_7301_ == 0)
{
if (v___x_7297_ == 0)
{
lean_dec(v_a_7295_);
goto v___jp_7072_;
}
else
{
size_t v___x_7302_; size_t v___x_7303_; lean_object* v___x_7304_; 
v___x_7302_ = ((size_t)0ULL);
v___x_7303_ = lean_usize_of_nat(v___x_7296_);
v___x_7304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7295_, v___x_7302_, v___x_7303_, v___x_7300_, v_a_7070_);
lean_dec(v_a_7295_);
if (lean_obj_tag(v___x_7304_) == 0)
{
lean_dec_ref_known(v___x_7304_, 1);
goto v___jp_7072_;
}
else
{
lean_object* v_a_7305_; lean_object* v___x_7307_; uint8_t v_isShared_7308_; uint8_t v_isSharedCheck_7312_; 
v_a_7305_ = lean_ctor_get(v___x_7304_, 0);
v_isSharedCheck_7312_ = !lean_is_exclusive(v___x_7304_);
if (v_isSharedCheck_7312_ == 0)
{
v___x_7307_ = v___x_7304_;
v_isShared_7308_ = v_isSharedCheck_7312_;
goto v_resetjp_7306_;
}
else
{
lean_inc(v_a_7305_);
lean_dec(v___x_7304_);
v___x_7307_ = lean_box(0);
v_isShared_7308_ = v_isSharedCheck_7312_;
goto v_resetjp_7306_;
}
v_resetjp_7306_:
{
lean_object* v___x_7310_; 
if (v_isShared_7308_ == 0)
{
v___x_7310_ = v___x_7307_;
goto v_reusejp_7309_;
}
else
{
lean_object* v_reuseFailAlloc_7311_; 
v_reuseFailAlloc_7311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7311_, 0, v_a_7305_);
v___x_7310_ = v_reuseFailAlloc_7311_;
goto v_reusejp_7309_;
}
v_reusejp_7309_:
{
return v___x_7310_;
}
}
}
}
}
else
{
size_t v___x_7313_; size_t v___x_7314_; lean_object* v___x_7315_; 
v___x_7313_ = ((size_t)0ULL);
v___x_7314_ = lean_usize_of_nat(v___x_7296_);
v___x_7315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7295_, v___x_7313_, v___x_7314_, v___x_7300_, v_a_7070_);
lean_dec(v_a_7295_);
if (lean_obj_tag(v___x_7315_) == 0)
{
lean_dec_ref_known(v___x_7315_, 1);
goto v___jp_7072_;
}
else
{
lean_object* v_a_7316_; lean_object* v___x_7318_; uint8_t v_isShared_7319_; uint8_t v_isSharedCheck_7323_; 
v_a_7316_ = lean_ctor_get(v___x_7315_, 0);
v_isSharedCheck_7323_ = !lean_is_exclusive(v___x_7315_);
if (v_isSharedCheck_7323_ == 0)
{
v___x_7318_ = v___x_7315_;
v_isShared_7319_ = v_isSharedCheck_7323_;
goto v_resetjp_7317_;
}
else
{
lean_inc(v_a_7316_);
lean_dec(v___x_7315_);
v___x_7318_ = lean_box(0);
v_isShared_7319_ = v_isSharedCheck_7323_;
goto v_resetjp_7317_;
}
v_resetjp_7317_:
{
lean_object* v___x_7321_; 
if (v_isShared_7319_ == 0)
{
v___x_7321_ = v___x_7318_;
goto v_reusejp_7320_;
}
else
{
lean_object* v_reuseFailAlloc_7322_; 
v_reuseFailAlloc_7322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7322_, 0, v_a_7316_);
v___x_7321_ = v_reuseFailAlloc_7322_;
goto v_reusejp_7320_;
}
v_reusejp_7320_:
{
return v___x_7321_;
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
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_7350_, lean_object* v_cache_7351_, lean_object* v_service_7352_, lean_object* v_localScope_7353_, lean_object* v_remoteScope_7354_, lean_object* v_platform_7355_, lean_object* v_toolchain_7356_, lean_object* v_force_7357_, lean_object* v_a_7358_, lean_object* v_a_7359_){
_start:
{
uint8_t v_force_boxed_7360_; lean_object* v_res_7361_; 
v_force_boxed_7360_ = lean_unbox(v_force_7357_);
v_res_7361_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_7350_, v_cache_7351_, v_service_7352_, v_localScope_7353_, v_remoteScope_7354_, v_platform_7355_, v_toolchain_7356_, v_force_boxed_7360_, v_a_7358_);
lean_dec_ref(v_a_7358_);
return v_res_7361_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_7363_, lean_object* v_outputs_7364_, lean_object* v_service_7365_, lean_object* v_scope_7366_, lean_object* v_platform_7367_, lean_object* v_toolchain_7368_, lean_object* v_a_7369_){
_start:
{
lean_object* v_url_7371_; lean_object* v___y_7373_; lean_object* v_s_7389_; 
lean_inc_ref(v_scope_7366_);
lean_inc_ref(v_service_7365_);
v_url_7371_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7363_, v_service_7365_, v_scope_7366_, v_platform_7367_, v_toolchain_7368_);
v_s_7389_ = lean_ctor_get(v_scope_7366_, 0);
lean_inc_ref(v_s_7389_);
lean_dec_ref(v_scope_7366_);
v___y_7373_ = v_s_7389_;
goto v___jp_7372_;
v___jp_7372_:
{
lean_object* v___x_7374_; lean_object* v___x_7375_; lean_object* v___x_7376_; lean_object* v___x_7377_; lean_object* v___x_7378_; lean_object* v___x_7379_; lean_object* v___x_7380_; lean_object* v___x_7381_; lean_object* v___x_7382_; uint8_t v___x_7383_; lean_object* v___x_7384_; lean_object* v___x_7385_; lean_object* v_key_7386_; lean_object* v___x_7387_; lean_object* v___x_7388_; 
v___x_7374_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_7375_ = lean_string_append(v___y_7373_, v___x_7374_);
v___x_7376_ = lean_string_append(v___x_7375_, v_rev_7363_);
v___x_7377_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_7378_ = lean_string_append(v___x_7376_, v___x_7377_);
v___x_7379_ = lean_string_append(v___x_7378_, v_outputs_7364_);
v___x_7380_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_7381_ = lean_string_append(v___x_7379_, v___x_7380_);
v___x_7382_ = lean_string_append(v___x_7381_, v_url_7371_);
v___x_7383_ = 1;
v___x_7384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7384_, 0, v___x_7382_);
lean_ctor_set_uint8(v___x_7384_, sizeof(void*)*1, v___x_7383_);
lean_inc_ref(v_a_7369_);
v___x_7385_ = lean_apply_2(v_a_7369_, v___x_7384_, lean_box(0));
v_key_7386_ = lean_ctor_get(v_service_7365_, 1);
lean_inc_ref(v_key_7386_);
lean_dec_ref(v_service_7365_);
v___x_7387_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_7388_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_7369_, v_outputs_7364_, v___x_7387_, v_url_7371_, v_key_7386_);
return v___x_7388_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_7390_, lean_object* v_outputs_7391_, lean_object* v_service_7392_, lean_object* v_scope_7393_, lean_object* v_platform_7394_, lean_object* v_toolchain_7395_, lean_object* v_a_7396_, lean_object* v_a_7397_){
_start:
{
lean_object* v_res_7398_; 
v_res_7398_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_7390_, v_outputs_7391_, v_service_7392_, v_scope_7393_, v_platform_7394_, v_toolchain_7395_, v_a_7396_);
lean_dec_ref(v_a_7396_);
lean_dec_ref(v_toolchain_7395_);
lean_dec_ref(v_rev_7390_);
return v_res_7398_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
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
res = runtime_initialize_Lake_Util_Git(builtin);
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
l_Lake_CachePlatform_system = _init_l_Lake_CachePlatform_system();
lean_mark_persistent(l_Lake_CachePlatform_system);
l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty = _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty);
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
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
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
res = initialize_Lake_Util_Git(builtin);
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
