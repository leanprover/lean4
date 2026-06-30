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
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object*, lean_object*, uint8_t, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object*);
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
lean_dec_ref_known(v_x_221_, 1);
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
lean_dec_ref_known(v___x_242_, 1);
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
uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_698_; lean_object* v_searcher_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
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
if (v___y_673_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = lean_unsigned_to_nat(2u);
v___x_677_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_675_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_string_utf8_next_fast(v_contents_665_, v___y_674_);
lean_dec(v___y_674_);
v___x_680_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_667_, v_inputName_664_, v_platformIndependent_666_, v___x_676_, v___x_678_, v_contents_665_, v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___y_674_);
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
lean_dec_ref_known(v___y_688_, 1);
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
goto v___jp_672_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___y_687_);
lean_dec(v___y_686_);
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
v___y_673_ = v___x_709_;
v___y_674_ = v___y_698_;
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
v___y_673_ = v___x_709_;
v___y_674_ = v___y_698_;
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
lean_dec_ref_known(v___x_717_, 1);
v___y_673_ = v___x_709_;
v___y_674_ = v___y_698_;
v___y_675_ = v___x_699_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___x_709_;
v___y_686_ = v___y_698_;
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
lean_dec_ref_known(v___x_720_, 1);
v___y_673_ = v___x_709_;
v___y_674_ = v___y_698_;
v___y_675_ = v___x_699_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___x_709_;
v___y_686_ = v___y_698_;
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
v___y_685_ = v___x_709_;
v___y_686_ = v___y_698_;
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
lean_dec_ref_known(v___x_733_, 1);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___x_709_;
v___y_686_ = v___y_698_;
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2393_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
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
v___x_2442_ = l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2441_);
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
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2620_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v___x_2577_, 0);
lean_dec(v_unused_2621_);
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2620_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2620_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lake_computeBinFileHash(v_path_2573_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; uint64_t v___x_2584_; uint8_t v___x_2585_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = lean_unbox_uint64(v_a_2583_);
v___x_2585_ = lean_uint64_dec_eq(v___x_2584_, v_hash_2571_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; uint64_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2586_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_2573_);
v___x_2587_ = lean_string_append(v_path_2573_, v___x_2586_);
v___x_2588_ = lean_unbox_uint64(v_a_2583_);
lean_dec(v_a_2583_);
v___x_2589_ = l_Lake_lowerHexUInt64(v___x_2588_);
v___x_2590_ = lean_string_append(v___x_2587_, v___x_2589_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = 3;
v___x_2592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set_uint8(v___x_2592_, sizeof(void*)*1, v___x_2591_);
lean_inc(v_a_2578_);
v___x_2593_ = lean_array_push(v_a_2578_, v___x_2592_);
v___x_2594_ = lean_io_remove_file(v_path_2573_);
lean_dec_ref(v_path_2573_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_dec_ref_known(v___x_2594_, 1);
v___x_2595_ = lean_array_get_size(v_a_2578_);
lean_dec(v_a_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2593_);
lean_ctor_set(v___x_2580_, 0, v___x_2595_);
v___x_2597_ = v___x_2580_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2593_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec(v_a_2578_);
v_a_2599_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2600_ = lean_io_error_to_string(v_a_2599_);
v___x_2601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*1, v___x_2591_);
v___x_2602_ = lean_array_get_size(v___x_2593_);
v___x_2603_ = lean_array_push(v___x_2593_, v___x_2601_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2603_);
lean_ctor_set(v___x_2580_, 0, v___x_2602_);
v___x_2605_ = v___x_2580_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec(v_a_2583_);
lean_dec_ref(v_path_2573_);
v___x_2607_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2607_);
v___x_2609_ = v___x_2580_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_a_2578_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec_ref(v_path_2573_);
v_a_2611_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2612_ = lean_io_error_to_string(v_a_2611_);
v___x_2613_ = 3;
v___x_2614_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*1, v___x_2613_);
v___x_2615_ = lean_array_get_size(v_a_2578_);
v___x_2616_ = lean_array_push(v_a_2578_, v___x_2614_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2616_);
lean_ctor_set(v___x_2580_, 0, v___x_2615_);
v___x_2618_ = v___x_2580_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
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
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2622_, lean_object* v_url_2623_, lean_object* v_path_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
uint64_t v_hash_boxed_2627_; lean_object* v_res_2628_; 
v_hash_boxed_2627_ = lean_unbox_uint64(v_hash_2622_);
lean_dec_ref(v_hash_2622_);
v_res_2628_ = l_Lake_downloadArtifactCore(v_hash_boxed_2627_, v_url_2623_, v_path_2624_, v_a_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2631_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v___x_2632_; 
v___x_2632_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Json_getNat_x3f(v_x_2631_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2650_; 
v_a_2642_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2644_ = v___x_2633_;
v_isShared_2645_ = v_isSharedCheck_2650_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2633_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2650_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2642_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2646_);
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2673_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2674_ = lean_unsigned_to_nat(14u);
v___x_2675_ = lean_mk_empty_array_with_capacity(v___x_2674_);
v___x_2676_ = lean_array_push(v___x_2675_, v___x_2673_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2678_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2679_ = lean_array_push(v___x_2678_, v___x_2677_);
return v___x_2679_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2681_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2682_ = lean_array_push(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2684_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2685_ = lean_array_push(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2687_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2688_ = lean_array_push(v___x_2687_, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2690_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2691_ = lean_array_push(v___x_2690_, v___x_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2695_, lean_object* v_contentType_2696_, lean_object* v_url_2697_, lean_object* v_key_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___y_2702_; lean_object* v_a_2703_; lean_object* v_stderr_2716_; lean_object* v___y_2725_; lean_object* v___y_2728_; lean_object* v_a_2729_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_stderr_2768_; lean_object* v_a_2769_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2783_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2784_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2785_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2786_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2787_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2788_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2789_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2790_ = lean_string_append(v___x_2789_, v_contentType_2696_);
v___x_2791_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2792_ = lean_array_push(v___x_2791_, v_key_2698_);
v___x_2793_ = lean_array_push(v___x_2792_, v___x_2785_);
v___x_2794_ = lean_array_push(v___x_2793_, v___x_2786_);
v___x_2795_ = lean_array_push(v___x_2794_, v___x_2787_);
v___x_2796_ = lean_array_push(v___x_2795_, v_file_2695_);
v___x_2797_ = lean_array_push(v___x_2796_, v_url_2697_);
v___x_2798_ = lean_array_push(v___x_2797_, v___x_2788_);
v___x_2799_ = lean_array_push(v___x_2798_, v___x_2790_);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2803_ = 1;
v___x_2804_ = 0;
v___x_2805_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2805_, 0, v___x_2783_);
lean_ctor_set(v___x_2805_, 1, v___x_2784_);
lean_ctor_set(v___x_2805_, 2, v___x_2799_);
lean_ctor_set(v___x_2805_, 3, v___x_2800_);
lean_ctor_set(v___x_2805_, 4, v___x_2802_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*5, v___x_2803_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*5 + 1, v___x_2804_);
v___x_2806_ = l_Lake_captureProc_x27(v___x_2805_, v___x_2802_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_a_2808_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
v_a_2808_ = lean_ctor_get(v___x_2806_, 1);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2806_, 2);
v___x_2822_ = lean_array_get_size(v_a_2808_);
v___x_2823_ = lean_nat_dec_lt(v___x_2801_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec(v_a_2808_);
goto v___jp_2809_;
}
else
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_nat_dec_le(v___x_2822_, v___x_2822_);
if (v___x_2825_ == 0)
{
if (v___x_2823_ == 0)
{
lean_dec(v_a_2808_);
goto v___jp_2809_;
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = lean_usize_of_nat(v___x_2822_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2808_, v___x_2826_, v___x_2827_, v___x_2824_, v_a_2699_);
lean_dec(v_a_2808_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_dec_ref_known(v___x_2828_, 1);
goto v___jp_2809_;
}
else
{
lean_dec(v_a_2807_);
return v___x_2828_;
}
}
}
else
{
size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = lean_usize_of_nat(v___x_2822_);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2808_, v___x_2829_, v___x_2830_, v___x_2824_, v_a_2699_);
lean_dec(v_a_2808_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
goto v___jp_2809_;
}
else
{
lean_dec(v_a_2807_);
return v___x_2831_;
}
}
}
v___jp_2809_:
{
lean_object* v_stderr_2810_; lean_object* v___x_2811_; 
v_stderr_2810_ = lean_ctor_get(v_a_2807_, 1);
lean_inc_ref(v_stderr_2810_);
v___x_2811_ = l_Lean_Json_parse(v_stderr_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; 
lean_inc_ref(v_stderr_2810_);
lean_dec(v_a_2807_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_stderr_2768_ = v_stderr_2810_;
v_a_2769_ = v_a_2812_;
goto v___jp_2767_;
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2814_; 
v_a_2813_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2814_ = l_Lean_Json_getObj_x3f(v_a_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; 
lean_inc_ref(v_stderr_2810_);
lean_dec(v_a_2807_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v_stderr_2768_ = v_stderr_2810_;
v_a_2769_ = v_a_2815_;
goto v___jp_2767_;
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_a_2816_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2817_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2818_ = l_Lake_JsonObject_getJson_x3f(v_a_2816_, v___x_2817_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_inc_ref(v_stderr_2810_);
lean_dec(v_a_2816_);
lean_dec(v_a_2807_);
v_stderr_2716_ = v_stderr_2810_;
goto v___jp_2715_;
}
else
{
lean_object* v_val_2819_; lean_object* v___x_2820_; 
v_val_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2819_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_dec_ref_known(v___x_2820_, 1);
v___y_2756_ = v_a_2816_;
v___y_2757_ = v_a_2807_;
goto v___jp_2755_;
}
else
{
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_dec_ref_known(v___x_2820_, 1);
v___y_2756_ = v_a_2816_;
v___y_2757_ = v_a_2807_;
goto v___jp_2755_;
}
else
{
lean_object* v_a_2821_; 
lean_dec(v_a_2816_);
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___y_2728_ = v_a_2807_;
v_a_2729_ = v_a_2821_;
goto v___jp_2727_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v_a_2832_ = lean_ctor_get(v___x_2806_, 1);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2806_, 2);
v___x_2833_ = lean_array_get_size(v_a_2832_);
v___x_2834_ = lean_nat_dec_lt(v___x_2801_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec(v_a_2832_);
v___x_2835_ = lean_box(0);
v___x_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_nat_dec_le(v___x_2833_, v___x_2833_);
if (v___x_2838_ == 0)
{
if (v___x_2834_ == 0)
{
lean_dec(v_a_2832_);
goto v___jp_2780_;
}
else
{
size_t v___x_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = ((size_t)0ULL);
v___x_2840_ = lean_usize_of_nat(v___x_2833_);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2832_, v___x_2839_, v___x_2840_, v___x_2837_, v_a_2699_);
lean_dec(v_a_2832_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_dec_ref_known(v___x_2841_, 1);
goto v___jp_2780_;
}
else
{
return v___x_2841_;
}
}
}
else
{
size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = ((size_t)0ULL);
v___x_2843_ = lean_usize_of_nat(v___x_2833_);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2832_, v___x_2842_, v___x_2843_, v___x_2837_, v_a_2699_);
lean_dec(v_a_2832_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_dec_ref_known(v___x_2844_, 1);
goto v___jp_2780_;
}
else
{
return v___x_2844_;
}
}
}
}
v___jp_2701_:
{
lean_object* v_stderr_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_stderr_2704_ = lean_ctor_get(v___y_2702_, 1);
lean_inc_ref(v_stderr_2704_);
lean_dec_ref(v___y_2702_);
v___x_2705_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2706_ = lean_string_append(v___x_2705_, v_a_2703_);
lean_dec_ref(v_a_2703_);
v___x_2707_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2708_ = lean_string_append(v___x_2706_, v___x_2707_);
v___x_2709_ = lean_string_append(v___x_2708_, v_stderr_2704_);
lean_dec_ref(v_stderr_2704_);
v___x_2710_ = 3;
v___x_2711_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set_uint8(v___x_2711_, sizeof(void*)*1, v___x_2710_);
lean_inc_ref(v_a_2699_);
v___x_2712_ = lean_apply_2(v_a_2699_, v___x_2711_, lean_box(0));
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
return v___x_2714_;
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2717_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2718_ = lean_string_append(v___x_2717_, v_stderr_2716_);
lean_dec_ref(v_stderr_2716_);
v___x_2719_ = 3;
v___x_2720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*1, v___x_2719_);
lean_inc_ref(v_a_2699_);
v___x_2721_ = lean_apply_2(v_a_2699_, v___x_2720_, lean_box(0));
v___x_2722_ = lean_box(0);
v___x_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
v___jp_2724_:
{
lean_object* v_stderr_2726_; 
v_stderr_2726_ = lean_ctor_get(v___y_2725_, 1);
lean_inc_ref(v_stderr_2726_);
lean_dec_ref(v___y_2725_);
v_stderr_2716_ = v_stderr_2726_;
goto v___jp_2715_;
}
v___jp_2727_:
{
if (lean_obj_tag(v_a_2729_) == 0)
{
v___y_2725_ = v___y_2728_;
goto v___jp_2724_;
}
else
{
lean_object* v_val_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2754_; 
v_val_2730_ = lean_ctor_get(v_a_2729_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_a_2729_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2732_ = v_a_2729_;
v_isShared_2733_ = v_isSharedCheck_2754_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_val_2730_);
lean_dec(v_a_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2754_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = lean_unsigned_to_nat(200u);
v___x_2735_ = lean_nat_dec_eq(v_val_2730_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v_stdout_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v_stdout_2736_ = lean_ctor_get(v___y_2728_, 0);
lean_inc_ref(v_stdout_2736_);
lean_dec_ref(v___y_2728_);
v___x_2737_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2738_ = l_Nat_reprFast(v_val_2730_);
v___x_2739_ = lean_string_append(v___x_2737_, v___x_2738_);
lean_dec_ref(v___x_2738_);
v___x_2740_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2741_ = lean_string_append(v___x_2739_, v___x_2740_);
v___x_2742_ = lean_string_append(v___x_2741_, v_stdout_2736_);
lean_dec_ref(v_stdout_2736_);
v___x_2743_ = 3;
v___x_2744_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*1, v___x_2743_);
lean_inc_ref(v_a_2699_);
v___x_2745_ = lean_apply_2(v_a_2699_, v___x_2744_, lean_box(0));
v___x_2746_ = lean_box(0);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2746_);
v___x_2748_ = v___x_2732_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_dec(v_val_2730_);
lean_dec_ref(v___y_2728_);
v___x_2750_ = lean_box(0);
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2750_);
v___x_2752_ = v___x_2732_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
v___jp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2759_ = l_Lake_JsonObject_getJson_x3f(v___y_2756_, v___x_2758_);
lean_dec(v___y_2756_);
if (lean_obj_tag(v___x_2759_) == 0)
{
v___y_2725_ = v___y_2757_;
goto v___jp_2724_;
}
else
{
lean_object* v_val_2760_; lean_object* v___x_2761_; 
v_val_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_val_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2760_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2764_ = lean_string_append(v___x_2763_, v_a_2762_);
lean_dec(v_a_2762_);
v___y_2702_ = v___y_2757_;
v_a_2703_ = v___x_2764_;
goto v___jp_2701_;
}
else
{
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2765_; 
v_a_2765_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2761_, 1);
v___y_2702_ = v___y_2757_;
v_a_2703_ = v_a_2765_;
goto v___jp_2701_;
}
else
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2761_, 1);
v___y_2728_ = v___y_2757_;
v_a_2729_ = v_a_2766_;
goto v___jp_2727_;
}
}
}
}
v___jp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2770_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2771_ = lean_string_append(v___x_2770_, v_a_2769_);
lean_dec_ref(v_a_2769_);
v___x_2772_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2773_ = lean_string_append(v___x_2771_, v___x_2772_);
v___x_2774_ = lean_string_append(v___x_2773_, v_stderr_2768_);
lean_dec_ref(v_stderr_2768_);
v___x_2775_ = 3;
v___x_2776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*1, v___x_2775_);
lean_inc_ref(v_a_2699_);
v___x_2777_ = lean_apply_2(v_a_2699_, v___x_2776_, lean_box(0));
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
v___jp_2780_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2845_, lean_object* v_contentType_2846_, lean_object* v_url_2847_, lean_object* v_key_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2845_, v_contentType_2846_, v_url_2847_, v_key_2848_, v_a_2849_);
lean_dec_ref(v_a_2849_);
lean_dec_ref(v_contentType_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2852_){
_start:
{
lean_object* v_name_x3f_2853_; 
v_name_x3f_2853_ = lean_ctor_get(v_service_2852_, 0);
lean_inc(v_name_x3f_2853_);
return v_name_x3f_2853_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lake_CacheService_name_x3f(v_service_2854_);
lean_dec_ref(v_service_2854_);
return v_res_2855_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2856_){
_start:
{
uint8_t v_isReservoir_2857_; 
v_isReservoir_2857_ = lean_ctor_get_uint8(v_service_2856_, sizeof(void*)*5);
return v_isReservoir_2857_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2858_){
_start:
{
uint8_t v_res_2859_; lean_object* v_r_2860_; 
v_res_2859_ = l_Lake_CacheService_isReservoir(v_service_2858_);
lean_dec_ref(v_service_2858_);
v_r_2860_ = lean_box(v_res_2859_);
return v_r_2860_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2861_, lean_object* v_name_x3f_2862_){
_start:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2864_ = 1;
v___x_2865_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2865_, 0, v_name_x3f_2862_);
lean_ctor_set(v___x_2865_, 1, v___x_2863_);
lean_ctor_set(v___x_2865_, 2, v___x_2863_);
lean_ctor_set(v___x_2865_, 3, v___x_2863_);
lean_ctor_set(v___x_2865_, 4, v_apiEndpoint_2861_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*5, v___x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2866_, lean_object* v_artifactEndpoint_2867_, lean_object* v_revisionEndpoint_2868_){
_start:
{
lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = lean_box(0);
v___x_2870_ = 0;
v___x_2871_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2872_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v_key_2866_);
lean_ctor_set(v___x_2872_, 2, v_artifactEndpoint_2867_);
lean_ctor_set(v___x_2872_, 3, v_revisionEndpoint_2868_);
lean_ctor_set(v___x_2872_, 4, v___x_2871_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*5, v___x_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2873_, lean_object* v_revisionEndpoint_2874_, lean_object* v_name_x3f_2875_){
_start:
{
lean_object* v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2877_ = 0;
v___x_2878_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2878_, 0, v_name_x3f_2875_);
lean_ctor_set(v___x_2878_, 1, v___x_2876_);
lean_ctor_set(v___x_2878_, 2, v_artifactEndpoint_2873_);
lean_ctor_set(v___x_2878_, 3, v_revisionEndpoint_2874_);
lean_ctor_set(v___x_2878_, 4, v___x_2876_);
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*5, v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2879_, lean_object* v_name_x3f_2880_){
_start:
{
lean_object* v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2882_ = 0;
v___x_2883_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2883_, 0, v_name_x3f_2880_);
lean_ctor_set(v___x_2883_, 1, v___x_2881_);
lean_ctor_set(v___x_2883_, 2, v_artifactEndpoint_2879_);
lean_ctor_set(v___x_2883_, 3, v___x_2881_);
lean_ctor_set(v___x_2883_, 4, v___x_2881_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*5, v___x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2884_, lean_object* v_key_2885_){
_start:
{
lean_object* v_name_x3f_2886_; lean_object* v_artifactEndpoint_2887_; lean_object* v_revisionEndpoint_2888_; uint8_t v_isReservoir_2889_; lean_object* v_apiEndpoint_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
v_name_x3f_2886_ = lean_ctor_get(v_service_2884_, 0);
v_artifactEndpoint_2887_ = lean_ctor_get(v_service_2884_, 2);
v_revisionEndpoint_2888_ = lean_ctor_get(v_service_2884_, 3);
v_isReservoir_2889_ = lean_ctor_get_uint8(v_service_2884_, sizeof(void*)*5);
v_apiEndpoint_2890_ = lean_ctor_get(v_service_2884_, 4);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_service_2884_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v_service_2884_, 1);
lean_dec(v_unused_2898_);
v___x_2892_ = v_service_2884_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_apiEndpoint_2890_);
lean_inc(v_revisionEndpoint_2888_);
lean_inc(v_artifactEndpoint_2887_);
lean_inc(v_name_x3f_2886_);
lean_dec(v_service_2884_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v_key_2885_);
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_name_x3f_2886_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_key_2885_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_artifactEndpoint_2887_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_revisionEndpoint_2888_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_apiEndpoint_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*5, v_isReservoir_2889_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2905_);
lean_dec_ref(v_s_2905_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2907_, lean_object* v___x_2908_, lean_object* v___x_2909_, lean_object* v_a_2910_, lean_object* v_b_2911_){
_start:
{
if (lean_obj_tag(v_a_2910_) == 0)
{
lean_object* v_currPos_2912_; lean_object* v_searcher_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2947_; 
v_currPos_2912_ = lean_ctor_get(v_a_2910_, 0);
v_searcher_2913_ = lean_ctor_get(v_a_2910_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2910_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2915_ = v_a_2910_;
v_isShared_2916_ = v_isSharedCheck_2947_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_searcher_2913_);
lean_inc(v_currPos_2912_);
lean_dec(v_a_2910_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2947_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v_startInclusive_2917_; lean_object* v_endExclusive_2918_; uint32_t v___x_2919_; lean_object* v_it_2921_; lean_object* v_startInclusive_2922_; lean_object* v_endExclusive_2923_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_startInclusive_2917_ = lean_ctor_get(v___x_2908_, 1);
v_endExclusive_2918_ = lean_ctor_get(v___x_2908_, 2);
v___x_2919_ = 47;
v___x_2928_ = lean_nat_sub(v_endExclusive_2918_, v_startInclusive_2917_);
v___x_2929_ = lean_nat_dec_eq(v_searcher_2913_, v___x_2928_);
lean_dec(v___x_2928_);
if (v___x_2929_ == 0)
{
uint32_t v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = lean_string_utf8_get_fast(v_scope_2907_, v_searcher_2913_);
v___x_2931_ = lean_uint32_dec_eq(v___x_2930_, v___x_2919_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = lean_string_utf8_next_fast(v_scope_2907_, v_searcher_2913_);
lean_dec(v_searcher_2913_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2932_);
v___x_2934_ = v___x_2915_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_currPos_2912_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
v_a_2910_ = v___x_2934_;
goto _start;
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_slice_2940_; lean_object* v_nextIt_2942_; 
v___x_2937_ = lean_string_utf8_next_fast(v_scope_2907_, v_searcher_2913_);
v___x_2938_ = lean_nat_sub(v___x_2937_, v_searcher_2913_);
v___x_2939_ = lean_nat_add(v_searcher_2913_, v___x_2938_);
lean_dec(v___x_2938_);
v_slice_2940_ = l_String_Slice_subslice_x21(v___x_2908_, v_currPos_2912_, v_searcher_2913_);
lean_inc(v___x_2939_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2939_);
lean_ctor_set(v___x_2915_, 0, v___x_2939_);
v_nextIt_2942_ = v___x_2915_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v___x_2939_);
v_nextIt_2942_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v_startInclusive_2943_; lean_object* v_endExclusive_2944_; 
v_startInclusive_2943_ = lean_ctor_get(v_slice_2940_, 0);
lean_inc(v_startInclusive_2943_);
v_endExclusive_2944_ = lean_ctor_get(v_slice_2940_, 1);
lean_inc(v_endExclusive_2944_);
lean_dec_ref(v_slice_2940_);
v_it_2921_ = v_nextIt_2942_;
v_startInclusive_2922_ = v_startInclusive_2943_;
v_endExclusive_2923_ = v_endExclusive_2944_;
goto v___jp_2920_;
}
}
}
else
{
lean_object* v___x_2946_; 
lean_del_object(v___x_2915_);
lean_dec(v_searcher_2913_);
v___x_2946_ = lean_box(1);
lean_inc(v___x_2909_);
v_it_2921_ = v___x_2946_;
v_startInclusive_2922_ = v_currPos_2912_;
v_endExclusive_2923_ = v___x_2909_;
goto v___jp_2920_;
}
v___jp_2920_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_string_utf8_extract(v_scope_2907_, v_startInclusive_2922_, v_endExclusive_2923_);
lean_dec(v_endExclusive_2923_);
lean_dec(v_startInclusive_2922_);
v___x_2925_ = lean_string_push(v_b_2911_, v___x_2919_);
v___x_2926_ = l_Lake_uriEncode(v___x_2924_, v___x_2925_);
v_a_2910_ = v_it_2921_;
v_b_2911_ = v___x_2926_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2909_);
return v_b_2911_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_2948_, lean_object* v___x_2949_, lean_object* v___x_2950_, lean_object* v_a_2951_, lean_object* v_b_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2948_, v___x_2949_, v___x_2950_, v_a_2951_, v_b_2952_);
lean_dec_ref(v___x_2949_);
lean_dec_ref(v_scope_2948_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_2954_, lean_object* v_scope_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = lean_string_utf8_byte_size(v_scope_2955_);
lean_inc_ref(v_scope_2955_);
v___x_2958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2958_, 0, v_scope_2955_);
lean_ctor_set(v___x_2958_, 1, v___x_2956_);
lean_ctor_set(v___x_2958_, 2, v___x_2957_);
v___x_2959_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_2958_);
v___x_2960_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2955_, v___x_2958_, v___x_2957_, v___x_2959_, v_endpoint_2954_);
lean_dec_ref_known(v___x_2958_, 3);
lean_dec_ref(v_scope_2955_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_2961_, lean_object* v___x_2962_, lean_object* v___x_2963_, lean_object* v_inst_2964_, lean_object* v_R_2965_, lean_object* v_a_2966_, lean_object* v_b_2967_, lean_object* v_c_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2961_, v___x_2962_, v___x_2963_, v_a_2966_, v_b_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_2970_, lean_object* v___x_2971_, lean_object* v___x_2972_, lean_object* v_inst_2973_, lean_object* v_R_2974_, lean_object* v_a_2975_, lean_object* v_b_2976_, lean_object* v_c_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_2970_, v___x_2971_, v___x_2972_, v_inst_2973_, v_R_2974_, v_a_2975_, v_b_2976_, v_c_2977_);
lean_dec_ref(v___x_2971_);
lean_dec_ref(v_scope_2970_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_2979_, lean_object* v_scope_2980_){
_start:
{
lean_object* v_artifactEndpoint_2981_; lean_object* v___x_2982_; 
v_artifactEndpoint_2981_ = lean_ctor_get(v_service_2979_, 2);
lean_inc_ref(v_artifactEndpoint_2981_);
lean_dec_ref(v_service_2979_);
v___x_2982_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_2981_, v_scope_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_2985_, lean_object* v_service_2986_, lean_object* v_scope_2987_){
_start:
{
lean_object* v___y_2989_; lean_object* v_s_2996_; lean_object* v___x_2997_; 
v_s_2996_ = lean_ctor_get(v_scope_2987_, 0);
lean_inc_ref(v_s_2996_);
lean_dec_ref(v_scope_2987_);
v___x_2997_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_2986_, v_s_2996_);
v___y_2989_ = v___x_2997_;
goto v___jp_2988_;
v___jp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2990_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_2991_ = lean_string_append(v___y_2989_, v___x_2990_);
v___x_2992_ = l_Lake_lowerHexUInt64(v_contentHash_2985_);
v___x_2993_ = lean_string_append(v___x_2991_, v___x_2992_);
lean_dec_ref(v___x_2992_);
v___x_2994_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2995_ = lean_string_append(v___x_2993_, v___x_2994_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_2998_, lean_object* v_service_2999_, lean_object* v_scope_3000_){
_start:
{
uint64_t v_contentHash_boxed_3001_; lean_object* v_res_3002_; 
v_contentHash_boxed_3001_ = lean_unbox_uint64(v_contentHash_2998_);
lean_dec_ref(v_contentHash_2998_);
v_res_3002_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_3001_, v_service_2999_, v_scope_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_3006_, lean_object* v_service_3007_, lean_object* v_scope_3008_){
_start:
{
lean_object* v___y_3010_; uint8_t v_isReservoir_3017_; 
v_isReservoir_3017_ = lean_ctor_get_uint8(v_service_3007_, sizeof(void*)*5);
if (v_isReservoir_3017_ == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3006_, v_service_3007_, v_scope_3008_);
return v___x_3018_;
}
else
{
if (lean_obj_tag(v_scope_3008_) == 0)
{
lean_object* v_apiEndpoint_3019_; lean_object* v_s_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_apiEndpoint_3019_ = lean_ctor_get(v_service_3007_, 4);
lean_inc_ref(v_apiEndpoint_3019_);
lean_dec_ref(v_service_3007_);
v_s_3020_ = lean_ctor_get(v_scope_3008_, 0);
lean_inc_ref(v_s_3020_);
lean_dec_ref_known(v_scope_3008_, 1);
v___x_3021_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_3022_ = lean_string_append(v_apiEndpoint_3019_, v___x_3021_);
v___x_3023_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3022_, v_s_3020_);
v___y_3010_ = v___x_3023_;
goto v___jp_3009_;
}
else
{
lean_object* v_apiEndpoint_3024_; lean_object* v_s_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_apiEndpoint_3024_ = lean_ctor_get(v_service_3007_, 4);
lean_inc_ref(v_apiEndpoint_3024_);
lean_dec_ref(v_service_3007_);
v_s_3025_ = lean_ctor_get(v_scope_3008_, 0);
lean_inc_ref(v_s_3025_);
lean_dec_ref_known(v_scope_3008_, 1);
v___x_3026_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3027_ = lean_string_append(v_apiEndpoint_3024_, v___x_3026_);
v___x_3028_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3027_, v_s_3025_);
v___y_3010_ = v___x_3028_;
goto v___jp_3009_;
}
}
v___jp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3011_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_3012_ = lean_string_append(v___y_3010_, v___x_3011_);
v___x_3013_ = l_Lake_lowerHexUInt64(v_contentHash_3006_);
v___x_3014_ = lean_string_append(v___x_3012_, v___x_3013_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_3016_ = lean_string_append(v___x_3014_, v___x_3015_);
return v___x_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_3029_, lean_object* v_service_3030_, lean_object* v_scope_3031_){
_start:
{
uint64_t v_contentHash_boxed_3032_; lean_object* v_res_3033_; 
v_contentHash_boxed_3032_ = lean_unbox_uint64(v_contentHash_3029_);
lean_dec_ref(v_contentHash_3029_);
v_res_3033_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_3032_, v_service_3030_, v_scope_3031_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3038_ = lean_array_get_size(v___x_3037_);
return v___x_3038_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3039_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_nat_dec_lt(v___x_3040_, v___x_3039_);
return v___x_3041_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3043_ = lean_nat_dec_le(v___x_3042_, v___x_3042_);
return v___x_3043_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_3044_; size_t v___x_3045_; 
v___x_3044_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3045_ = lean_usize_of_nat(v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_3046_, lean_object* v_cache_3047_, lean_object* v_service_3048_, lean_object* v_scope_3049_, uint8_t v_force_3050_, lean_object* v_a_3051_){
_start:
{
uint64_t v_hash_3056_; lean_object* v_ext_3057_; lean_object* v_url_3058_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3122_; lean_object* v___y_3125_; uint8_t v_a_3126_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___y_3132_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_hash_3056_ = lean_ctor_get_uint64(v_descr_3046_, sizeof(void*)*1);
v_ext_3057_ = lean_ctor_get(v_descr_3046_, 0);
lean_inc_ref(v_scope_3049_);
v_url_3058_ = l_Lake_CacheService_artifactUrl(v_hash_3056_, v_service_3048_, v_scope_3049_);
v___x_3129_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3130_ = l_System_FilePath_join(v_cache_3047_, v___x_3129_);
v___x_3145_ = lean_string_utf8_byte_size(v_ext_3057_);
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_nat_dec_eq(v___x_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3148_ = l_Lake_lowerHexUInt64(v_hash_3056_);
v___x_3149_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3150_ = lean_string_append(v___x_3148_, v___x_3149_);
v___x_3151_ = lean_string_append(v___x_3150_, v_ext_3057_);
v___y_3132_ = v___x_3151_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lake_lowerHexUInt64(v_hash_3056_);
v___y_3132_ = v___x_3152_;
goto v___jp_3131_;
}
v___jp_3053_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
v___jp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3062_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3063_ = lean_string_append(v___y_3061_, v___x_3062_);
v___x_3064_ = l_Lake_lowerHexUInt64(v_hash_3056_);
v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
lean_dec_ref(v___x_3064_);
v___x_3066_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
v___x_3068_ = lean_string_append(v___x_3067_, v___y_3060_);
v___x_3069_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3070_ = lean_string_append(v___x_3068_, v___x_3069_);
v___x_3071_ = lean_string_append(v___x_3070_, v_url_3058_);
v___x_3072_ = 1;
v___x_3073_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*1, v___x_3072_);
lean_inc_ref(v_a_3051_);
v___x_3074_ = lean_apply_2(v_a_3051_, v___x_3073_, lean_box(0));
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3077_ = l_Lake_downloadArtifactCore(v_hash_3056_, v_url_3058_, v___y_3060_, v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v_a_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
v_a_3079_ = lean_ctor_get(v___x_3077_, 1);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3077_, 2);
v___x_3080_ = lean_array_get_size(v_a_3079_);
v___x_3081_ = lean_nat_dec_lt(v___x_3075_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec(v_a_3079_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_a_3078_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_nat_dec_le(v___x_3080_, v___x_3080_);
if (v___x_3084_ == 0)
{
if (v___x_3081_ == 0)
{
lean_object* v___x_3085_; 
lean_dec(v_a_3079_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_a_3078_);
return v___x_3085_;
}
else
{
size_t v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = lean_usize_of_nat(v___x_3080_);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3079_, v___x_3086_, v___x_3087_, v___x_3083_, v_a_3051_);
lean_dec(v_a_3079_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; 
v_unused_3096_ = lean_ctor_get(v___x_3088_, 0);
lean_dec(v_unused_3096_);
v___x_3090_ = v___x_3088_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_dec(v___x_3088_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v_a_3078_);
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3078_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_dec(v_a_3078_);
return v___x_3088_;
}
}
}
else
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = lean_usize_of_nat(v___x_3080_);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3079_, v___x_3097_, v___x_3098_, v___x_3083_, v_a_3051_);
lean_dec(v_a_3079_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v___x_3099_, 0);
lean_dec(v_unused_3107_);
v___x_3101_ = v___x_3099_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v___x_3099_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v_a_3078_);
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3078_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_dec(v_a_3078_);
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3077_, 1);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3077_, 2);
v___x_3109_ = lean_array_get_size(v_a_3108_);
v___x_3110_ = lean_nat_dec_lt(v___x_3075_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v_a_3108_);
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = lean_box(0);
v___x_3114_ = lean_nat_dec_le(v___x_3109_, v___x_3109_);
if (v___x_3114_ == 0)
{
if (v___x_3110_ == 0)
{
lean_dec(v_a_3108_);
goto v___jp_3053_;
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = lean_usize_of_nat(v___x_3109_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3108_, v___x_3115_, v___x_3116_, v___x_3113_, v_a_3051_);
lean_dec(v_a_3108_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_dec_ref_known(v___x_3117_, 1);
goto v___jp_3053_;
}
else
{
return v___x_3117_;
}
}
}
else
{
size_t v___x_3118_; size_t v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = ((size_t)0ULL);
v___x_3119_ = lean_usize_of_nat(v___x_3109_);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3108_, v___x_3118_, v___x_3119_, v___x_3113_, v_a_3051_);
lean_dec(v_a_3108_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_dec_ref_known(v___x_3120_, 1);
goto v___jp_3053_;
}
else
{
return v___x_3120_;
}
}
}
}
}
v___jp_3121_:
{
lean_object* v_s_3123_; 
v_s_3123_ = lean_ctor_get(v_scope_3049_, 0);
lean_inc_ref(v_s_3123_);
lean_dec_ref(v_scope_3049_);
v___y_3060_ = v___y_3122_;
v___y_3061_ = v_s_3123_;
goto v___jp_3059_;
}
v___jp_3124_:
{
if (v_a_3126_ == 0)
{
v___y_3122_ = v___y_3125_;
goto v___jp_3121_;
}
else
{
if (v_force_3050_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v___y_3125_);
lean_dec_ref(v_url_3058_);
lean_dec_ref(v_scope_3049_);
v___x_3127_ = lean_box(0);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
else
{
v___y_3122_ = v___y_3125_;
goto v___jp_3121_;
}
}
}
v___jp_3131_:
{
lean_object* v_path_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_path_3133_ = l_System_FilePath_join(v___x_3130_, v___y_3132_);
v___x_3134_ = l_System_FilePath_pathExists(v_path_3133_);
v___x_3135_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3136_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3136_ == 0)
{
v___y_3125_ = v_path_3133_;
v_a_3126_ = v___x_3134_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = lean_box(0);
v___x_3138_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3138_ == 0)
{
if (v___x_3136_ == 0)
{
v___y_3125_ = v_path_3133_;
v_a_3126_ = v___x_3134_;
goto v___jp_3124_;
}
else
{
size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = ((size_t)0ULL);
v___x_3140_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3135_, v___x_3139_, v___x_3140_, v___x_3137_, v_a_3051_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_dec_ref_known(v___x_3141_, 1);
v___y_3125_ = v_path_3133_;
v_a_3126_ = v___x_3134_;
goto v___jp_3124_;
}
else
{
lean_dec_ref(v_path_3133_);
lean_dec_ref(v_url_3058_);
lean_dec_ref(v_scope_3049_);
return v___x_3141_;
}
}
}
else
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3135_, v___x_3142_, v___x_3143_, v___x_3137_, v_a_3051_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_dec_ref_known(v___x_3144_, 1);
v___y_3125_ = v_path_3133_;
v_a_3126_ = v___x_3134_;
goto v___jp_3124_;
}
else
{
lean_dec_ref(v_path_3133_);
lean_dec_ref(v_url_3058_);
lean_dec_ref(v_scope_3049_);
return v___x_3144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3153_, lean_object* v_cache_3154_, lean_object* v_service_3155_, lean_object* v_scope_3156_, lean_object* v_force_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
uint8_t v_force_boxed_3160_; lean_object* v_res_3161_; 
v_force_boxed_3160_ = lean_unbox(v_force_3157_);
v_res_3161_ = l_Lake_CacheService_downloadArtifact(v_descr_3153_, v_cache_3154_, v_service_3155_, v_scope_3156_, v_force_boxed_3160_, v_a_3158_);
lean_dec_ref(v_a_3158_);
lean_dec_ref(v_descr_3153_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3162_, lean_object* v_file_3163_, lean_object* v_contentType_3164_, lean_object* v_url_3165_, lean_object* v_key_3166_){
_start:
{
lean_object* v___y_3169_; lean_object* v_a_3170_; lean_object* v_stderr_3183_; lean_object* v___y_3192_; lean_object* v___y_3195_; lean_object* v_a_3196_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v_stderr_3235_; lean_object* v_a_3236_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3250_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3251_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3252_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3253_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3254_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3255_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3256_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3257_ = lean_string_append(v___x_3256_, v_contentType_3164_);
v___x_3258_ = lean_unsigned_to_nat(14u);
v___x_3259_ = lean_mk_empty_array_with_capacity(v___x_3258_);
lean_dec_ref(v___x_3259_);
v___x_3260_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3261_ = lean_array_push(v___x_3260_, v_key_3166_);
v___x_3262_ = lean_array_push(v___x_3261_, v___x_3252_);
v___x_3263_ = lean_array_push(v___x_3262_, v___x_3253_);
v___x_3264_ = lean_array_push(v___x_3263_, v___x_3254_);
v___x_3265_ = lean_array_push(v___x_3264_, v_file_3163_);
v___x_3266_ = lean_array_push(v___x_3265_, v_url_3165_);
v___x_3267_ = lean_array_push(v___x_3266_, v___x_3255_);
v___x_3268_ = lean_array_push(v___x_3267_, v___x_3257_);
v___x_3269_ = lean_box(0);
v___x_3270_ = lean_unsigned_to_nat(0u);
v___x_3271_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3272_ = 1;
v___x_3273_ = 0;
v___x_3274_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3274_, 0, v___x_3250_);
lean_ctor_set(v___x_3274_, 1, v___x_3251_);
lean_ctor_set(v___x_3274_, 2, v___x_3268_);
lean_ctor_set(v___x_3274_, 3, v___x_3269_);
lean_ctor_set(v___x_3274_, 4, v___x_3271_);
lean_ctor_set_uint8(v___x_3274_, sizeof(void*)*5, v___x_3272_);
lean_ctor_set_uint8(v___x_3274_, sizeof(void*)*5 + 1, v___x_3273_);
v___x_3275_ = l_Lake_captureProc_x27(v___x_3274_, v___x_3271_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v_a_3277_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
v_a_3277_ = lean_ctor_get(v___x_3275_, 1);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3275_, 2);
v___x_3291_ = lean_array_get_size(v_a_3277_);
v___x_3292_ = lean_nat_dec_lt(v___x_3270_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_dec(v_a_3277_);
goto v___jp_3278_;
}
else
{
lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_nat_dec_le(v___x_3291_, v___x_3291_);
if (v___x_3294_ == 0)
{
if (v___x_3292_ == 0)
{
lean_dec(v_a_3277_);
goto v___jp_3278_;
}
else
{
size_t v___x_3295_; size_t v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = lean_usize_of_nat(v___x_3291_);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3277_, v___x_3295_, v___x_3296_, v___x_3293_, v_a_3162_);
lean_dec(v_a_3277_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref_known(v___x_3297_, 1);
goto v___jp_3278_;
}
else
{
lean_dec(v_a_3276_);
return v___x_3297_;
}
}
}
else
{
size_t v___x_3298_; size_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = ((size_t)0ULL);
v___x_3299_ = lean_usize_of_nat(v___x_3291_);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3277_, v___x_3298_, v___x_3299_, v___x_3293_, v_a_3162_);
lean_dec(v_a_3277_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_dec_ref_known(v___x_3300_, 1);
goto v___jp_3278_;
}
else
{
lean_dec(v_a_3276_);
return v___x_3300_;
}
}
}
v___jp_3278_:
{
lean_object* v_stderr_3279_; lean_object* v___x_3280_; 
v_stderr_3279_ = lean_ctor_get(v_a_3276_, 1);
lean_inc_ref(v_stderr_3279_);
v___x_3280_ = l_Lean_Json_parse(v_stderr_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; 
lean_inc_ref(v_stderr_3279_);
lean_dec(v_a_3276_);
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
v_stderr_3235_ = v_stderr_3279_;
v_a_3236_ = v_a_3281_;
goto v___jp_3234_;
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3283_; 
v_a_3282_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3280_, 1);
v___x_3283_ = l_Lean_Json_getObj_x3f(v_a_3282_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; 
lean_inc_ref(v_stderr_3279_);
lean_dec(v_a_3276_);
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3283_, 1);
v_stderr_3235_ = v_stderr_3279_;
v_a_3236_ = v_a_3284_;
goto v___jp_3234_;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3285_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3283_, 1);
v___x_3286_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3287_ = l_Lake_JsonObject_getJson_x3f(v_a_3285_, v___x_3286_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_inc_ref(v_stderr_3279_);
lean_dec(v_a_3285_);
lean_dec(v_a_3276_);
v_stderr_3183_ = v_stderr_3279_;
goto v___jp_3182_;
}
else
{
lean_object* v_val_3288_; lean_object* v___x_3289_; 
v_val_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_val_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3289_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3288_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_dec_ref_known(v___x_3289_, 1);
v___y_3223_ = v_a_3285_;
v___y_3224_ = v_a_3276_;
goto v___jp_3222_;
}
else
{
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_dec_ref_known(v___x_3289_, 1);
v___y_3223_ = v_a_3285_;
v___y_3224_ = v_a_3276_;
goto v___jp_3222_;
}
else
{
lean_object* v_a_3290_; 
lean_dec(v_a_3285_);
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___y_3195_ = v_a_3276_;
v_a_3196_ = v_a_3290_;
goto v___jp_3194_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v_a_3301_ = lean_ctor_get(v___x_3275_, 1);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3275_, 2);
v___x_3302_ = lean_array_get_size(v_a_3301_);
v___x_3303_ = lean_nat_dec_lt(v___x_3270_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v_a_3301_);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
else
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_nat_dec_le(v___x_3302_, v___x_3302_);
if (v___x_3307_ == 0)
{
if (v___x_3303_ == 0)
{
lean_dec(v_a_3301_);
goto v___jp_3247_;
}
else
{
size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3302_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3301_, v___x_3308_, v___x_3309_, v___x_3306_, v_a_3162_);
lean_dec(v_a_3301_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_dec_ref_known(v___x_3310_, 1);
goto v___jp_3247_;
}
else
{
return v___x_3310_;
}
}
}
else
{
size_t v___x_3311_; size_t v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = ((size_t)0ULL);
v___x_3312_ = lean_usize_of_nat(v___x_3302_);
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3301_, v___x_3311_, v___x_3312_, v___x_3306_, v_a_3162_);
lean_dec(v_a_3301_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_dec_ref_known(v___x_3313_, 1);
goto v___jp_3247_;
}
else
{
return v___x_3313_;
}
}
}
}
v___jp_3168_:
{
lean_object* v_stderr_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_stderr_3171_ = lean_ctor_get(v___y_3169_, 1);
lean_inc_ref(v_stderr_3171_);
lean_dec_ref(v___y_3169_);
v___x_3172_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3173_ = lean_string_append(v___x_3172_, v_a_3170_);
lean_dec_ref(v_a_3170_);
v___x_3174_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3175_ = lean_string_append(v___x_3173_, v___x_3174_);
v___x_3176_ = lean_string_append(v___x_3175_, v_stderr_3171_);
lean_dec_ref(v_stderr_3171_);
v___x_3177_ = 3;
v___x_3178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*1, v___x_3177_);
lean_inc_ref(v_a_3162_);
v___x_3179_ = lean_apply_2(v_a_3162_, v___x_3178_, lean_box(0));
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
v___jp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3184_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3185_ = lean_string_append(v___x_3184_, v_stderr_3183_);
lean_dec_ref(v_stderr_3183_);
v___x_3186_ = 3;
v___x_3187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*1, v___x_3186_);
lean_inc_ref(v_a_3162_);
v___x_3188_ = lean_apply_2(v_a_3162_, v___x_3187_, lean_box(0));
v___x_3189_ = lean_box(0);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
v___jp_3191_:
{
lean_object* v_stderr_3193_; 
v_stderr_3193_ = lean_ctor_get(v___y_3192_, 1);
lean_inc_ref(v_stderr_3193_);
lean_dec_ref(v___y_3192_);
v_stderr_3183_ = v_stderr_3193_;
goto v___jp_3182_;
}
v___jp_3194_:
{
if (lean_obj_tag(v_a_3196_) == 0)
{
v___y_3192_ = v___y_3195_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3221_; 
v_val_3197_ = lean_ctor_get(v_a_3196_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_a_3196_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3199_ = v_a_3196_;
v_isShared_3200_ = v_isSharedCheck_3221_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_val_3197_);
lean_dec(v_a_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3221_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = lean_unsigned_to_nat(200u);
v___x_3202_ = lean_nat_dec_eq(v_val_3197_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v_stdout_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v_stdout_3203_ = lean_ctor_get(v___y_3195_, 0);
lean_inc_ref(v_stdout_3203_);
lean_dec_ref(v___y_3195_);
v___x_3204_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3205_ = l_Nat_reprFast(v_val_3197_);
v___x_3206_ = lean_string_append(v___x_3204_, v___x_3205_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3208_ = lean_string_append(v___x_3206_, v___x_3207_);
v___x_3209_ = lean_string_append(v___x_3208_, v_stdout_3203_);
lean_dec_ref(v_stdout_3203_);
v___x_3210_ = 3;
v___x_3211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*1, v___x_3210_);
lean_inc_ref(v_a_3162_);
v___x_3212_ = lean_apply_2(v_a_3162_, v___x_3211_, lean_box(0));
v___x_3213_ = lean_box(0);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3213_);
v___x_3215_ = v___x_3199_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
lean_dec(v_val_3197_);
lean_dec_ref(v___y_3195_);
v___x_3217_ = lean_box(0);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3217_);
v___x_3219_ = v___x_3199_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
v___jp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3226_ = l_Lake_JsonObject_getJson_x3f(v___y_3223_, v___x_3225_);
lean_dec(v___y_3223_);
if (lean_obj_tag(v___x_3226_) == 0)
{
v___y_3192_ = v___y_3224_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3227_; lean_object* v___x_3228_; 
v_val_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3227_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3231_ = lean_string_append(v___x_3230_, v_a_3229_);
lean_dec(v_a_3229_);
v___y_3169_ = v___y_3224_;
v_a_3170_ = v___x_3231_;
goto v___jp_3168_;
}
else
{
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3232_; 
v_a_3232_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3228_, 1);
v___y_3169_ = v___y_3224_;
v_a_3170_ = v_a_3232_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3233_; 
v_a_3233_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3228_, 1);
v___y_3195_ = v___y_3224_;
v_a_3196_ = v_a_3233_;
goto v___jp_3194_;
}
}
}
}
v___jp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3237_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3238_ = lean_string_append(v___x_3237_, v_a_3236_);
lean_dec_ref(v_a_3236_);
v___x_3239_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3240_ = lean_string_append(v___x_3238_, v___x_3239_);
v___x_3241_ = lean_string_append(v___x_3240_, v_stderr_3235_);
lean_dec_ref(v_stderr_3235_);
v___x_3242_ = 3;
v___x_3243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*1, v___x_3242_);
lean_inc_ref(v_a_3162_);
v___x_3244_ = lean_apply_2(v_a_3162_, v___x_3243_, lean_box(0));
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
return v___x_3246_;
}
v___jp_3247_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_box(0);
v___x_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3314_, lean_object* v_file_3315_, lean_object* v_contentType_3316_, lean_object* v_url_3317_, lean_object* v_key_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3314_, v_file_3315_, v_contentType_3316_, v_url_3317_, v_key_3318_);
lean_dec_ref(v_contentType_3316_);
lean_dec_ref(v_a_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3322_, lean_object* v_art_3323_, lean_object* v_service_3324_, lean_object* v_scope_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_url_3328_; lean_object* v___y_3330_; lean_object* v_s_3347_; 
lean_inc_ref(v_scope_3325_);
lean_inc_ref(v_service_3324_);
v_url_3328_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3322_, v_service_3324_, v_scope_3325_);
v_s_3347_ = lean_ctor_get(v_scope_3325_, 0);
lean_inc_ref(v_s_3347_);
lean_dec_ref(v_scope_3325_);
v___y_3330_ = v_s_3347_;
goto v___jp_3329_;
v___jp_3329_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v_key_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3331_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3332_ = lean_string_append(v___y_3330_, v___x_3331_);
v___x_3333_ = l_Lake_lowerHexUInt64(v_contentHash_3322_);
v___x_3334_ = lean_string_append(v___x_3332_, v___x_3333_);
lean_dec_ref(v___x_3333_);
v___x_3335_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3336_ = lean_string_append(v___x_3334_, v___x_3335_);
v___x_3337_ = lean_string_append(v___x_3336_, v_art_3323_);
v___x_3338_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_string_append(v___x_3339_, v_url_3328_);
v___x_3341_ = 1;
v___x_3342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*1, v___x_3341_);
lean_inc_ref(v_a_3326_);
v___x_3343_ = lean_apply_2(v_a_3326_, v___x_3342_, lean_box(0));
v_key_3344_ = lean_ctor_get(v_service_3324_, 1);
lean_inc_ref(v_key_3344_);
lean_dec_ref(v_service_3324_);
v___x_3345_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3346_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3326_, v_art_3323_, v___x_3345_, v_url_3328_, v_key_3344_);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3348_, lean_object* v_art_3349_, lean_object* v_service_3350_, lean_object* v_scope_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
uint64_t v_contentHash_boxed_3354_; lean_object* v_res_3355_; 
v_contentHash_boxed_3354_ = lean_unbox_uint64(v_contentHash_3348_);
lean_dec_ref(v_contentHash_3348_);
v_res_3355_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3354_, v_art_3349_, v_service_3350_, v_scope_3351_, v_a_3352_);
lean_dec_ref(v_a_3352_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(uint8_t v_x_3356_){
_start:
{
if (v_x_3356_ == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
return v___x_3357_;
}
else
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_unsigned_to_nat(1u);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___boxed(lean_object* v_x_3359_){
_start:
{
uint8_t v_x_boxed_3360_; lean_object* v_res_3361_; 
v_x_boxed_3360_ = lean_unbox(v_x_3359_);
v_res_3361_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_boxed_3360_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(uint8_t v_x_3362_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx___boxed(lean_object* v_x_3364_){
_start:
{
uint8_t v_x_4__boxed_3365_; lean_object* v_res_3366_; 
v_x_4__boxed_3365_ = lean_unbox(v_x_3364_);
v_res_3366_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(v_x_4__boxed_3365_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object* v_k_3367_){
_start:
{
lean_inc(v_k_3367_);
return v_k_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object* v_k_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(v_k_3368_);
lean_dec(v_k_3368_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object* v_motive_3370_, lean_object* v_ctorIdx_3371_, uint8_t v_t_3372_, lean_object* v_h_3373_, lean_object* v_k_3374_){
_start:
{
lean_inc(v_k_3374_);
return v_k_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object* v_motive_3375_, lean_object* v_ctorIdx_3376_, lean_object* v_t_3377_, lean_object* v_h_3378_, lean_object* v_k_3379_){
_start:
{
uint8_t v_t_boxed_3380_; lean_object* v_res_3381_; 
v_t_boxed_3380_ = lean_unbox(v_t_3377_);
v_res_3381_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(v_motive_3375_, v_ctorIdx_3376_, v_t_boxed_3380_, v_h_3378_, v_k_3379_);
lean_dec(v_k_3379_);
lean_dec(v_ctorIdx_3376_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object* v_get_3382_){
_start:
{
lean_inc(v_get_3382_);
return v_get_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object* v_get_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(v_get_3383_);
lean_dec(v_get_3383_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object* v_motive_3385_, uint8_t v_t_3386_, lean_object* v_h_3387_, lean_object* v_get_3388_){
_start:
{
lean_inc(v_get_3388_);
return v_get_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object* v_motive_3389_, lean_object* v_t_3390_, lean_object* v_h_3391_, lean_object* v_get_3392_){
_start:
{
uint8_t v_t_boxed_3393_; lean_object* v_res_3394_; 
v_t_boxed_3393_ = lean_unbox(v_t_3390_);
v_res_3394_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(v_motive_3389_, v_t_boxed_3393_, v_h_3391_, v_get_3392_);
lean_dec(v_get_3392_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object* v_put_3395_){
_start:
{
lean_inc(v_put_3395_);
return v_put_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object* v_put_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(v_put_3396_);
lean_dec(v_put_3396_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object* v_motive_3398_, uint8_t v_t_3399_, lean_object* v_h_3400_, lean_object* v_put_3401_){
_start:
{
lean_inc(v_put_3401_);
return v_put_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object* v_motive_3402_, lean_object* v_t_3403_, lean_object* v_h_3404_, lean_object* v_put_3405_){
_start:
{
uint8_t v_t_boxed_3406_; lean_object* v_res_3407_; 
v_t_boxed_3406_ = lean_unbox(v_t_3403_);
v_res_3407_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(v_motive_3402_, v_t_boxed_3406_, v_h_3404_, v_put_3405_);
lean_dec(v_put_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object* v_n_3408_){
_start:
{
lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3409_ = lean_unsigned_to_nat(0u);
v___x_3410_ = lean_nat_dec_le(v_n_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
uint8_t v___x_3411_; 
v___x_3411_ = 1;
return v___x_3411_;
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = 0;
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object* v_n_3413_){
_start:
{
uint8_t v_res_3414_; lean_object* v_r_3415_; 
v_res_3414_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(v_n_3413_);
lean_dec(v_n_3413_);
v_r_3415_ = lean_box(v_res_3414_);
return v_r_3415_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t v_x_3416_, uint8_t v_y_3417_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3418_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3416_);
v___x_3419_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_y_3417_);
v___x_3420_ = lean_nat_dec_eq(v___x_3418_, v___x_3419_);
lean_dec(v___x_3419_);
lean_dec(v___x_3418_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object* v_x_3421_, lean_object* v_y_3422_){
_start:
{
uint8_t v_x_13__boxed_3423_; uint8_t v_y_14__boxed_3424_; uint8_t v_res_3425_; lean_object* v_r_3426_; 
v_x_13__boxed_3423_ = lean_unbox(v_x_3421_);
v_y_14__boxed_3424_ = lean_unbox(v_y_3422_);
v_res_3425_ = l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(v_x_13__boxed_3423_, v_y_14__boxed_3424_);
v_r_3426_ = lean_box(v_res_3425_);
return v_r_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(lean_object* v_self_3427_, lean_object* v_path_3428_, uint8_t v_extra_3429_){
_start:
{
if (v_extra_3429_ == 0)
{
lean_object* v_url_3430_; uint64_t v_hash_3431_; lean_object* v_path_3432_; lean_object* v_extraPaths_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3441_; 
v_url_3430_ = lean_ctor_get(v_self_3427_, 0);
v_hash_3431_ = lean_ctor_get_uint64(v_self_3427_, sizeof(void*)*3);
v_path_3432_ = lean_ctor_get(v_self_3427_, 1);
v_extraPaths_3433_ = lean_ctor_get(v_self_3427_, 2);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_self_3427_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3435_ = v_self_3427_;
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_extraPaths_3433_);
lean_inc(v_path_3432_);
lean_inc(v_url_3430_);
lean_dec(v_self_3427_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = lean_array_push(v_extraPaths_3433_, v_path_3432_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 2, v___x_3437_);
lean_ctor_set(v___x_3435_, 1, v_path_3428_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_url_3430_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_path_3428_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v___x_3437_);
lean_ctor_set_uint64(v_reuseFailAlloc_3440_, sizeof(void*)*3, v_hash_3431_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
else
{
lean_object* v_url_3442_; uint64_t v_hash_3443_; lean_object* v_path_3444_; lean_object* v_extraPaths_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3453_; 
v_url_3442_ = lean_ctor_get(v_self_3427_, 0);
v_hash_3443_ = lean_ctor_get_uint64(v_self_3427_, sizeof(void*)*3);
v_path_3444_ = lean_ctor_get(v_self_3427_, 1);
v_extraPaths_3445_ = lean_ctor_get(v_self_3427_, 2);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_self_3427_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3447_ = v_self_3427_;
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_extraPaths_3445_);
lean_inc(v_path_3444_);
lean_inc(v_url_3442_);
lean_dec(v_self_3427_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_array_push(v_extraPaths_3445_, v_path_3428_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 2, v___x_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_url_3442_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_path_3444_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v___x_3449_);
lean_ctor_set_uint64(v_reuseFailAlloc_3452_, sizeof(void*)*3, v_hash_3443_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath___boxed(lean_object* v_self_3454_, lean_object* v_path_3455_, lean_object* v_extra_3456_){
_start:
{
uint8_t v_extra_boxed_3457_; lean_object* v_res_3458_; 
v_extra_boxed_3457_ = lean_unbox(v_extra_3456_);
v_res_3458_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(v_self_3454_, v_path_3455_, v_extra_boxed_3457_);
return v_res_3458_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_3462_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v___x_3461_);
return v___x_3463_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty(void){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
return v___x_3464_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___f_3467_; 
v___x_3466_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_3467_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3467_, 0, v___x_3466_);
return v___f_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(lean_object* v_self_3468_, lean_object* v_url_3469_, uint64_t v_hash_3470_, lean_object* v_path_3471_){
_start:
{
lean_object* v_infos_3472_; lean_object* v_indices_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3488_; 
v_infos_3472_ = lean_ctor_get(v_self_3468_, 0);
v_indices_3473_ = lean_ctor_get(v_self_3468_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_self_3468_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3475_ = v_self_3468_;
v_isShared_3476_ = v_isSharedCheck_3488_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_indices_3473_);
lean_inc(v_infos_3472_);
lean_dec(v_self_3468_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3488_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___f_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___f_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___f_3477_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___x_3478_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3479_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3479_, 0, v_url_3469_);
lean_ctor_set(v___x_3479_, 1, v_path_3471_);
lean_ctor_set(v___x_3479_, 2, v___x_3478_);
lean_ctor_set_uint64(v___x_3479_, sizeof(void*)*3, v_hash_3470_);
lean_inc_ref(v_infos_3472_);
v___x_3480_ = lean_array_push(v_infos_3472_, v___x_3479_);
v___f_3481_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3482_ = lean_array_get_size(v_infos_3472_);
lean_dec_ref(v_infos_3472_);
v___x_3483_ = lean_box_uint64(v_hash_3470_);
v___x_3484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3481_, v___f_3477_, v_indices_3473_, v___x_3483_, v___x_3482_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v___x_3484_);
lean_ctor_set(v___x_3475_, 0, v___x_3480_);
v___x_3486_ = v___x_3475_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___boxed(lean_object* v_self_3489_, lean_object* v_url_3490_, lean_object* v_hash_3491_, lean_object* v_path_3492_){
_start:
{
uint64_t v_hash_boxed_3493_; lean_object* v_res_3494_; 
v_hash_boxed_3493_ = lean_unbox_uint64(v_hash_3491_);
lean_dec_ref(v_hash_3491_);
v_res_3494_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(v_self_3489_, v_url_3490_, v_hash_boxed_3493_, v_path_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(lean_object* v_self_3495_, lean_object* v_url_3496_, uint64_t v_hash_3497_, lean_object* v_path_3498_){
_start:
{
lean_object* v_infos_3499_; lean_object* v_indices_3500_; lean_object* v___f_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_infos_3499_ = lean_ctor_get(v_self_3495_, 0);
v_indices_3500_ = lean_ctor_get(v_self_3495_, 1);
v___f_3501_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___f_3502_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3503_ = lean_box_uint64(v_hash_3497_);
v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_3502_, v___f_3501_, v_indices_3500_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3517_; 
lean_inc_ref(v_indices_3500_);
lean_inc_ref(v_infos_3499_);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_self_3495_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; lean_object* v_unused_3519_; 
v_unused_3518_ = lean_ctor_get(v_self_3495_, 1);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_self_3495_, 0);
lean_dec(v_unused_3519_);
v___x_3506_ = v_self_3495_;
v_isShared_3507_ = v_isSharedCheck_3517_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v_self_3495_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3517_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3508_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3509_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3509_, 0, v_url_3496_);
lean_ctor_set(v___x_3509_, 1, v_path_3498_);
lean_ctor_set(v___x_3509_, 2, v___x_3508_);
lean_ctor_set_uint64(v___x_3509_, sizeof(void*)*3, v_hash_3497_);
lean_inc_ref(v_infos_3499_);
v___x_3510_ = lean_array_push(v_infos_3499_, v___x_3509_);
v___x_3511_ = lean_array_get_size(v_infos_3499_);
lean_dec_ref(v_infos_3499_);
v___x_3512_ = lean_box_uint64(v_hash_3497_);
v___x_3513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3502_, v___f_3501_, v_indices_3500_, v___x_3512_, v___x_3511_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v___x_3513_);
lean_ctor_set(v___x_3506_, 0, v___x_3510_);
v___x_3515_ = v___x_3506_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_dec_ref(v_path_3498_);
lean_dec_ref(v_url_3496_);
return v_self_3495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew___boxed(lean_object* v_self_3520_, lean_object* v_url_3521_, lean_object* v_hash_3522_, lean_object* v_path_3523_){
_start:
{
uint64_t v_hash_boxed_3524_; lean_object* v_res_3525_; 
v_hash_boxed_3524_ = lean_unbox_uint64(v_hash_3522_);
lean_dec_ref(v_hash_3522_);
v_res_3525_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(v_self_3520_, v_url_3521_, v_hash_boxed_3524_, v_path_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(lean_object* v_self_3526_, lean_object* v_url_3527_, uint64_t v_hash_3528_, lean_object* v_path_3529_, uint8_t v_extra_3530_){
_start:
{
lean_object* v_infos_3531_; lean_object* v_indices_3532_; lean_object* v___f_3533_; lean_object* v___f_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_infos_3531_ = lean_ctor_get(v_self_3526_, 0);
v_indices_3532_ = lean_ctor_get(v_self_3526_, 1);
v___f_3533_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___f_3534_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3535_ = lean_box_uint64(v_hash_3528_);
v___x_3536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3534_, v___f_3533_, v_indices_3532_, v___x_3535_);
if (lean_obj_tag(v___x_3536_) == 1)
{
lean_object* v_val_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
lean_dec_ref(v_url_3527_);
v_val_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = lean_array_get_size(v_infos_3531_);
v___x_3539_ = lean_nat_dec_lt(v_val_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_dec(v_val_3537_);
lean_dec_ref(v_path_3529_);
return v_self_3526_;
}
else
{
lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3576_; 
lean_inc_ref(v_indices_3532_);
lean_inc_ref(v_infos_3531_);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_self_3526_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; 
v_unused_3577_ = lean_ctor_get(v_self_3526_, 1);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_self_3526_, 0);
lean_dec(v_unused_3578_);
v___x_3541_ = v_self_3526_;
v_isShared_3542_ = v_isSharedCheck_3576_;
goto v_resetjp_3540_;
}
else
{
lean_dec(v_self_3526_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3576_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v_v_3543_; lean_object* v___x_3544_; lean_object* v_xs_x27_3545_; lean_object* v___y_3547_; 
v_v_3543_ = lean_array_fget(v_infos_3531_, v_val_3537_);
v___x_3544_ = lean_box(0);
v_xs_x27_3545_ = lean_array_fset(v_infos_3531_, v_val_3537_, v___x_3544_);
if (v_extra_3530_ == 0)
{
lean_object* v_url_3552_; uint64_t v_hash_3553_; lean_object* v_path_3554_; lean_object* v_extraPaths_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3563_; 
v_url_3552_ = lean_ctor_get(v_v_3543_, 0);
v_hash_3553_ = lean_ctor_get_uint64(v_v_3543_, sizeof(void*)*3);
v_path_3554_ = lean_ctor_get(v_v_3543_, 1);
v_extraPaths_3555_ = lean_ctor_get(v_v_3543_, 2);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_v_3543_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3557_ = v_v_3543_;
v_isShared_3558_ = v_isSharedCheck_3563_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_extraPaths_3555_);
lean_inc(v_path_3554_);
lean_inc(v_url_3552_);
lean_dec(v_v_3543_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3563_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = lean_array_push(v_extraPaths_3555_, v_path_3554_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 2, v___x_3559_);
lean_ctor_set(v___x_3557_, 1, v_path_3529_);
v___x_3561_ = v___x_3557_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_url_3552_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_path_3529_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v___x_3559_);
lean_ctor_set_uint64(v_reuseFailAlloc_3562_, sizeof(void*)*3, v_hash_3553_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
v___y_3547_ = v___x_3561_;
goto v___jp_3546_;
}
}
}
else
{
lean_object* v_url_3564_; uint64_t v_hash_3565_; lean_object* v_path_3566_; lean_object* v_extraPaths_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3575_; 
v_url_3564_ = lean_ctor_get(v_v_3543_, 0);
v_hash_3565_ = lean_ctor_get_uint64(v_v_3543_, sizeof(void*)*3);
v_path_3566_ = lean_ctor_get(v_v_3543_, 1);
v_extraPaths_3567_ = lean_ctor_get(v_v_3543_, 2);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_v_3543_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3569_ = v_v_3543_;
v_isShared_3570_ = v_isSharedCheck_3575_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_extraPaths_3567_);
lean_inc(v_path_3566_);
lean_inc(v_url_3564_);
lean_dec(v_v_3543_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3575_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3571_ = lean_array_push(v_extraPaths_3567_, v_path_3529_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 2, v___x_3571_);
v___x_3573_ = v___x_3569_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_url_3564_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_path_3566_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v___x_3571_);
lean_ctor_set_uint64(v_reuseFailAlloc_3574_, sizeof(void*)*3, v_hash_3565_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
v___y_3547_ = v___x_3573_;
goto v___jp_3546_;
}
}
}
v___jp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = lean_array_fset(v_xs_x27_3545_, v_val_3537_, v___y_3547_);
lean_dec(v_val_3537_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3548_);
v___x_3550_ = v___x_3541_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_indices_3532_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
else
{
lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3591_; 
lean_inc_ref(v_indices_3532_);
lean_inc_ref(v_infos_3531_);
lean_dec(v___x_3536_);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_self_3526_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; lean_object* v_unused_3593_; 
v_unused_3592_ = lean_ctor_get(v_self_3526_, 1);
lean_dec(v_unused_3592_);
v_unused_3593_ = lean_ctor_get(v_self_3526_, 0);
lean_dec(v_unused_3593_);
v___x_3580_ = v_self_3526_;
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
else
{
lean_dec(v_self_3526_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3582_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3583_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3583_, 0, v_url_3527_);
lean_ctor_set(v___x_3583_, 1, v_path_3529_);
lean_ctor_set(v___x_3583_, 2, v___x_3582_);
lean_ctor_set_uint64(v___x_3583_, sizeof(void*)*3, v_hash_3528_);
lean_inc_ref(v_infos_3531_);
v___x_3584_ = lean_array_push(v_infos_3531_, v___x_3583_);
v___x_3585_ = lean_array_get_size(v_infos_3531_);
lean_dec_ref(v_infos_3531_);
v___x_3586_ = lean_box_uint64(v_hash_3528_);
v___x_3587_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3534_, v___f_3533_, v_indices_3532_, v___x_3586_, v___x_3585_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v___x_3587_);
lean_ctor_set(v___x_3580_, 0, v___x_3584_);
v___x_3589_ = v___x_3580_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add___boxed(lean_object* v_self_3594_, lean_object* v_url_3595_, lean_object* v_hash_3596_, lean_object* v_path_3597_, lean_object* v_extra_3598_){
_start:
{
uint64_t v_hash_boxed_3599_; uint8_t v_extra_boxed_3600_; lean_object* v_res_3601_; 
v_hash_boxed_3599_ = lean_unbox_uint64(v_hash_3596_);
lean_dec_ref(v_hash_3596_);
v_extra_boxed_3600_ = lean_unbox(v_extra_3598_);
v_res_3601_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(v_self_3594_, v_url_3595_, v_hash_boxed_3599_, v_path_3597_, v_extra_boxed_3600_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(lean_object* v_a_3602_, lean_object* v_as_3603_, size_t v_sz_3604_, size_t v_i_3605_, lean_object* v_b_3606_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_usize_dec_lt(v_i_3605_, v_sz_3604_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_b_3606_);
return v___x_3609_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3611_; 
v_a_3610_ = lean_array_uget_borrowed(v_as_3603_, v_i_3605_);
v___x_3611_ = l_IO_FS_writeBinFile(v_a_3610_, v_a_3602_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v___x_3612_; size_t v___x_3613_; size_t v___x_3614_; 
lean_dec_ref_known(v___x_3611_, 1);
v___x_3612_ = lean_box(0);
v___x_3613_ = ((size_t)1ULL);
v___x_3614_ = lean_usize_add(v_i_3605_, v___x_3613_);
v_i_3605_ = v___x_3614_;
v_b_3606_ = v___x_3612_;
goto _start;
}
else
{
return v___x_3611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0___boxed(lean_object* v_a_3616_, lean_object* v_as_3617_, lean_object* v_sz_3618_, lean_object* v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_){
_start:
{
size_t v_sz_boxed_3622_; size_t v_i_boxed_3623_; lean_object* v_res_3624_; 
v_sz_boxed_3622_ = lean_unbox_usize(v_sz_3618_);
lean_dec(v_sz_3618_);
v_i_boxed_3623_ = lean_unbox_usize(v_i_3619_);
lean_dec(v_i_3619_);
v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(v_a_3616_, v_as_3617_, v_sz_boxed_3622_, v_i_boxed_3623_, v_b_3620_);
lean_dec_ref(v_as_3617_);
lean_dec_ref(v_a_3616_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(lean_object* v_path_3625_, lean_object* v_extraPaths_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_IO_FS_readBinFile(v_path_3625_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3630_; size_t v_sz_3631_; size_t v___x_3632_; lean_object* v___x_3633_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v___x_3630_ = lean_box(0);
v_sz_3631_ = lean_array_size(v_extraPaths_3626_);
v___x_3632_ = ((size_t)0ULL);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths_spec__0(v_a_3629_, v_extraPaths_3626_, v_sz_3631_, v___x_3632_, v___x_3630_);
lean_dec(v_a_3629_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v___x_3633_, 0);
lean_dec(v_unused_3641_);
v___x_3635_ = v___x_3633_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_dec(v___x_3633_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3630_);
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3630_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
else
{
return v___x_3633_;
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v_a_3642_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3628_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3628_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths___boxed(lean_object* v_path_3650_, lean_object* v_extraPaths_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(v_path_3650_, v_extraPaths_3651_);
lean_dec_ref(v_extraPaths_3651_);
lean_dec_ref(v_path_3650_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object* v_cfg_3655_, lean_object* v_out_3656_){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0));
v___x_3658_ = l_Lake_JsonObject_getJson_x3f(v_out_3656_, v___x_3657_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_box(0);
return v___x_3659_;
}
else
{
lean_object* v_val_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3676_; 
v_val_3660_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3662_ = v___x_3658_;
v_isShared_3663_ = v_isSharedCheck_3676_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_val_3660_);
lean_dec(v___x_3658_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3676_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_Json_getNat_x3f(v_val_3660_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v___x_3665_; 
lean_dec_ref_known(v___x_3664_, 1);
lean_del_object(v___x_3662_);
v___x_3665_ = lean_box(0);
return v___x_3665_;
}
else
{
if (lean_obj_tag(v___x_3664_) == 1)
{
lean_object* v_a_3666_; lean_object* v_infos_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v_a_3666_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3664_, 1);
v_infos_3667_ = lean_ctor_get(v_cfg_3655_, 1);
v___x_3668_ = lean_array_get_size(v_infos_3667_);
v___x_3669_ = lean_nat_dec_lt(v_a_3666_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
lean_dec(v_a_3666_);
lean_del_object(v___x_3662_);
v___x_3670_ = lean_box(0);
return v___x_3670_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3671_ = lean_array_fget_borrowed(v_infos_3667_, v_a_3666_);
lean_dec(v_a_3666_);
lean_inc(v___x_3671_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3671_);
v___x_3673_ = v___x_3662_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_object* v___x_3675_; 
lean_dec_ref_known(v___x_3664_, 1);
lean_del_object(v___x_3662_);
v___x_3675_ = lean_box(0);
return v___x_3675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object* v_cfg_3677_, lean_object* v_out_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3677_, v_out_3678_);
lean_dec(v_out_3678_);
lean_dec_ref(v_cfg_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object* v_s_3680_, lean_object* v_pos_3681_){
_start:
{
lean_object* v_str_3682_; lean_object* v_startInclusive_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v_str_3682_ = lean_ctor_get(v_s_3680_, 0);
v_startInclusive_3683_ = lean_ctor_get(v_s_3680_, 1);
v___x_3684_ = lean_nat_add(v_startInclusive_3683_, v_pos_3681_);
v___x_3685_ = lean_nat_sub(v___x_3684_, v_startInclusive_3683_);
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_nat_dec_eq(v___x_3685_, v___x_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___y_3696_; lean_object* v___x_3697_; uint32_t v___x_3698_; uint8_t v___y_3700_; uint32_t v___x_3705_; uint8_t v___x_3706_; 
lean_inc(v_startInclusive_3683_);
lean_inc_ref(v_str_3682_);
v___x_3688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3688_, 0, v_str_3682_);
lean_ctor_set(v___x_3688_, 1, v_startInclusive_3683_);
lean_ctor_set(v___x_3688_, 2, v___x_3684_);
v___x_3689_ = lean_unsigned_to_nat(1u);
v___x_3690_ = lean_nat_sub(v___x_3685_, v___x_3689_);
lean_dec(v___x_3685_);
v___x_3691_ = l_String_Slice_posLE(v___x_3688_, v___x_3690_);
lean_dec_ref_known(v___x_3688_, 3);
v___x_3697_ = lean_nat_add(v_startInclusive_3683_, v___x_3691_);
v___x_3698_ = lean_string_utf8_get_fast(v_str_3682_, v___x_3697_);
lean_dec(v___x_3697_);
v___x_3705_ = 32;
v___x_3706_ = lean_uint32_dec_eq(v___x_3698_, v___x_3705_);
if (v___x_3706_ == 0)
{
uint32_t v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = 9;
v___x_3708_ = lean_uint32_dec_eq(v___x_3698_, v___x_3707_);
v___y_3700_ = v___x_3708_;
goto v___jp_3699_;
}
else
{
v___y_3700_ = v___x_3706_;
goto v___jp_3699_;
}
v___jp_3692_:
{
uint8_t v___x_3693_; 
v___x_3693_ = lean_nat_dec_lt(v___x_3691_, v_pos_3681_);
if (v___x_3693_ == 0)
{
lean_dec(v___x_3691_);
return v_pos_3681_;
}
else
{
lean_dec(v_pos_3681_);
v_pos_3681_ = v___x_3691_;
goto _start;
}
}
v___jp_3695_:
{
if (v___y_3696_ == 0)
{
lean_dec(v___x_3691_);
return v_pos_3681_;
}
else
{
goto v___jp_3692_;
}
}
v___jp_3699_:
{
if (v___y_3700_ == 0)
{
uint32_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = 13;
v___x_3702_ = lean_uint32_dec_eq(v___x_3698_, v___x_3701_);
if (v___x_3702_ == 0)
{
uint32_t v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = 10;
v___x_3704_ = lean_uint32_dec_eq(v___x_3698_, v___x_3703_);
v___y_3696_ = v___x_3704_;
goto v___jp_3695_;
}
else
{
v___y_3696_ = v___x_3702_;
goto v___jp_3695_;
}
}
else
{
goto v___jp_3692_;
}
}
}
else
{
lean_dec(v___x_3685_);
lean_dec(v___x_3684_);
return v_pos_3681_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object* v_s_3709_, lean_object* v_pos_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v_s_3709_, v_pos_3710_);
lean_dec_ref(v_s_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object* v_cfg_3724_, lean_object* v_hOut_3725_, lean_object* v_info_3726_, lean_object* v_code_x3f_3727_, lean_object* v_out_3728_, lean_object* v_line_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_msg_3733_; lean_object* v___y_3734_; lean_object* v___y_3751_; lean_object* v_msg_3752_; lean_object* v___y_3753_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v_a_3772_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v_val_3783_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v_kind_3826_; lean_object* v_scope_3827_; lean_object* v_msg_3829_; lean_object* v___y_3830_; lean_object* v_msg_3871_; lean_object* v___y_3872_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3900_; 
v_kind_3826_ = lean_ctor_get_uint8(v_cfg_3724_, sizeof(void*)*3);
v_scope_3827_ = lean_ctor_get(v_cfg_3724_, 0);
lean_inc_ref(v_scope_3827_);
lean_dec_ref(v_cfg_3724_);
if (v_kind_3826_ == 0)
{
lean_object* v___x_3902_; 
v___x_3902_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___y_3900_ = v___x_3902_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___y_3900_ = v___x_3903_;
goto v___jp_3899_;
}
v___jp_3732_:
{
uint8_t v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3735_ = 3;
v___x_3736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3736_, 0, v_msg_3733_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*1, v___x_3735_);
lean_inc_ref_n(v___y_3734_, 2);
v___x_3737_ = lean_apply_2(v___y_3734_, v___x_3736_, lean_box(0));
v___x_3738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0));
v___x_3739_ = lean_unsigned_to_nat(0u);
v___x_3740_ = lean_string_utf8_byte_size(v_line_3729_);
lean_inc_ref(v_line_3729_);
v___x_3741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3741_, 0, v_line_3729_);
lean_ctor_set(v___x_3741_, 1, v___x_3739_);
lean_ctor_set(v___x_3741_, 2, v___x_3740_);
v___x_3742_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_3741_, v___x_3740_);
lean_dec_ref_known(v___x_3741_, 3);
v___x_3743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3743_, 0, v_line_3729_);
lean_ctor_set(v___x_3743_, 1, v___x_3739_);
lean_ctor_set(v___x_3743_, 2, v___x_3742_);
v___x_3744_ = l_String_Slice_toString(v___x_3743_);
lean_dec_ref_known(v___x_3743_, 3);
v___x_3745_ = lean_string_append(v___x_3738_, v___x_3744_);
lean_dec_ref(v___x_3744_);
v___x_3746_ = 0;
v___x_3747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*1, v___x_3746_);
v___x_3748_ = lean_apply_2(v___y_3734_, v___x_3747_, lean_box(0));
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
v___jp_3750_:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lake_removeFileIfExists(v___y_3751_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_dec_ref_known(v___x_3754_, 1);
v_msg_3733_ = v_msg_3752_;
v___y_3734_ = v___y_3753_;
goto v___jp_3732_;
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3767_; 
lean_dec_ref(v_msg_3752_);
lean_dec_ref(v_line_3729_);
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3767_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3767_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3759_; uint8_t v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3759_ = lean_io_error_to_string(v_a_3755_);
v___x_3760_ = 3;
v___x_3761_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set_uint8(v___x_3761_, sizeof(void*)*1, v___x_3760_);
lean_inc_ref(v___y_3753_);
v___x_3762_ = lean_apply_2(v___y_3753_, v___x_3761_, lean_box(0));
v___x_3763_ = lean_box(0);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3763_);
v___x_3765_ = v___x_3757_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
v___jp_3768_:
{
if (lean_obj_tag(v_a_3772_) == 1)
{
lean_object* v_a_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_a_3773_ = lean_ctor_get(v_a_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v_a_3772_, 1);
v___x_3774_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3775_ = lean_string_append(v___y_3771_, v___x_3774_);
v___x_3776_ = lean_string_append(v___x_3775_, v_a_3773_);
lean_dec(v_a_3773_);
v___y_3751_ = v___y_3769_;
v_msg_3752_ = v___x_3776_;
v___y_3753_ = v___y_3770_;
goto v___jp_3750_;
}
else
{
lean_dec_ref(v_a_3772_);
v___y_3751_ = v___y_3769_;
v_msg_3752_ = v___y_3771_;
v___y_3753_ = v___y_3770_;
goto v___jp_3750_;
}
}
v___jp_3777_:
{
lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = lean_array_get_size(v___y_3782_);
v___x_3785_ = lean_nat_dec_lt(v___y_3780_, v___x_3784_);
if (v___x_3785_ == 0)
{
v___y_3769_ = v___y_3778_;
v___y_3770_ = v___y_3779_;
v___y_3771_ = v___y_3781_;
v_a_3772_ = v_val_3783_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3786_; uint8_t v___x_3787_; 
v___x_3786_ = lean_box(0);
v___x_3787_ = lean_nat_dec_le(v___x_3784_, v___x_3784_);
if (v___x_3787_ == 0)
{
if (v___x_3785_ == 0)
{
v___y_3769_ = v___y_3778_;
v___y_3770_ = v___y_3779_;
v___y_3771_ = v___y_3781_;
v_a_3772_ = v_val_3783_;
goto v___jp_3768_;
}
else
{
size_t v___x_3788_; size_t v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = ((size_t)0ULL);
v___x_3789_ = lean_usize_of_nat(v___x_3784_);
v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3782_, v___x_3788_, v___x_3789_, v___x_3786_, v___y_3779_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_dec_ref_known(v___x_3790_, 1);
v___y_3769_ = v___y_3778_;
v___y_3770_ = v___y_3779_;
v___y_3771_ = v___y_3781_;
v_a_3772_ = v_val_3783_;
goto v___jp_3768_;
}
else
{
lean_dec_ref(v_val_3783_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v_line_3729_);
return v___x_3790_;
}
}
}
else
{
size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = ((size_t)0ULL);
v___x_3792_ = lean_usize_of_nat(v___x_3784_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3782_, v___x_3791_, v___x_3792_, v___x_3786_, v___y_3779_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_dec_ref_known(v___x_3793_, 1);
v___y_3769_ = v___y_3778_;
v___y_3770_ = v___y_3779_;
v___y_3771_ = v___y_3781_;
v_a_3772_ = v_val_3783_;
goto v___jp_3768_;
}
else
{
lean_dec_ref(v_val_3783_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v_line_3729_);
return v___x_3793_;
}
}
}
}
v___jp_3794_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3799_ = l_Lake_JsonObject_getJson_x3f(v_out_3728_, v___x_3798_);
if (lean_obj_tag(v___x_3799_) == 0)
{
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
else
{
lean_object* v_val_3800_; lean_object* v___x_3801_; 
v_val_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_val_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___x_3801_ = l_Lean_Json_getNat_x3f(v_val_3800_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_dec_ref_known(v___x_3801_, 1);
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
else
{
if (lean_obj_tag(v___x_3801_) == 1)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_nat_dec_lt(v___x_3803_, v_a_3802_);
lean_dec(v_a_3802_);
if (v___x_3804_ == 0)
{
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3));
v___x_3806_ = l_Lake_JsonObject_getJson_x3f(v_out_3728_, v___x_3805_);
if (lean_obj_tag(v___x_3806_) == 0)
{
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
else
{
lean_object* v_val_3807_; lean_object* v___x_3808_; 
v_val_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_val_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___x_3808_ = l_Lean_Json_getStr_x3f(v_val_3807_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_dec_ref_known(v___x_3808_, 1);
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
else
{
if (lean_obj_tag(v___x_3808_) == 1)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3825_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3825_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3825_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3813_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3814_ = lean_string_dec_eq(v_a_3809_, v___x_3813_);
lean_dec(v_a_3809_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3816_ = l_IO_FS_readFile(v___y_3795_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v_a_3817_);
v___x_3819_ = v___x_3811_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
v___y_3778_ = v___y_3795_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___x_3803_;
v___y_3781_ = v___y_3797_;
v___y_3782_ = v___x_3815_;
v_val_3783_ = v___x_3819_;
goto v___jp_3777_;
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; 
v_a_3821_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3816_, 1);
if (v_isShared_3812_ == 0)
{
lean_ctor_set_tag(v___x_3811_, 0);
lean_ctor_set(v___x_3811_, 0, v_a_3821_);
v___x_3823_ = v___x_3811_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
v___y_3778_ = v___y_3795_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___x_3803_;
v___y_3781_ = v___y_3797_;
v___y_3782_ = v___x_3815_;
v_val_3783_ = v___x_3823_;
goto v___jp_3777_;
}
}
}
else
{
lean_del_object(v___x_3811_);
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
}
}
else
{
lean_dec_ref_known(v___x_3808_, 1);
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3801_, 1);
v___y_3751_ = v___y_3795_;
v_msg_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
goto v___jp_3750_;
}
}
}
}
v___jp_3828_:
{
lean_object* v_url_3831_; lean_object* v_path_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v_msg_3838_; 
v_url_3831_ = lean_ctor_get(v_info_3726_, 0);
v_path_3832_ = lean_ctor_get(v_info_3726_, 1);
v___x_3833_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3834_ = lean_string_append(v_msg_3829_, v___x_3833_);
v___x_3835_ = lean_string_append(v___x_3834_, v_path_3832_);
v___x_3836_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3837_ = lean_string_append(v___x_3835_, v___x_3836_);
v_msg_3838_ = lean_string_append(v___x_3837_, v_url_3831_);
if (v_kind_3826_ == 0)
{
if (lean_obj_tag(v_code_x3f_3727_) == 1)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_a_3839_ = lean_ctor_get(v_code_x3f_3727_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v_code_x3f_3727_, 1);
v___x_3840_ = lean_unsigned_to_nat(404u);
v___x_3841_ = lean_nat_dec_eq(v_a_3839_, v___x_3840_);
lean_dec(v_a_3839_);
if (v___x_3841_ == 0)
{
v___y_3795_ = v_path_3832_;
v___y_3796_ = v___y_3830_;
v___y_3797_ = v_msg_3838_;
goto v___jp_3794_;
}
else
{
v___y_3751_ = v_path_3832_;
v_msg_3752_ = v_msg_3838_;
v___y_3753_ = v___y_3830_;
goto v___jp_3750_;
}
}
else
{
lean_dec_ref(v_code_x3f_3727_);
v___y_3795_ = v_path_3832_;
v___y_3796_ = v___y_3830_;
v___y_3797_ = v_msg_3838_;
goto v___jp_3794_;
}
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec_ref(v_code_x3f_3727_);
v___x_3842_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3843_ = l_Lake_JsonObject_getJson_x3f(v_out_3728_, v___x_3842_);
if (lean_obj_tag(v___x_3843_) == 0)
{
v_msg_3733_ = v_msg_3838_;
v___y_3734_ = v___y_3830_;
goto v___jp_3732_;
}
else
{
lean_object* v_val_3844_; lean_object* v___x_3845_; 
v_val_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_val_3844_);
lean_dec_ref_known(v___x_3843_, 1);
v___x_3845_ = l_Lean_Json_getNat_x3f(v_val_3844_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_dec_ref_known(v___x_3845_, 1);
v_msg_3733_ = v_msg_3838_;
v___y_3734_ = v___y_3830_;
goto v___jp_3732_;
}
else
{
if (lean_obj_tag(v___x_3845_) == 1)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = lean_unsigned_to_nat(0u);
v___x_3848_ = lean_nat_dec_lt(v___x_3847_, v_a_3846_);
if (v___x_3848_ == 0)
{
lean_dec(v_a_3846_);
v_msg_3733_ = v_msg_3838_;
v___y_3734_ = v___y_3830_;
goto v___jp_3732_;
}
else
{
size_t v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = lean_usize_of_nat(v_a_3846_);
lean_dec(v_a_3846_);
v___x_3850_ = lean_io_prim_handle_read(v_hOut_3725_, v___x_3849_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; uint8_t v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = lean_string_validate_utf8(v_a_3851_);
if (v___x_3852_ == 0)
{
lean_dec(v_a_3851_);
v_msg_3733_ = v_msg_3838_;
v___y_3734_ = v___y_3830_;
goto v___jp_3732_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3853_ = lean_string_from_utf8_unchecked(v_a_3851_);
v___x_3854_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3855_ = lean_string_append(v_msg_3838_, v___x_3854_);
v___x_3856_ = lean_string_append(v___x_3855_, v___x_3853_);
lean_dec_ref(v___x_3853_);
v_msg_3733_ = v___x_3856_;
v___y_3734_ = v___y_3830_;
goto v___jp_3732_;
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_msg_3838_);
lean_dec_ref(v_line_3729_);
v_a_3857_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3859_ = v___x_3850_;
v_isShared_3860_ = v_isSharedCheck_3869_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3850_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3869_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3861_ = lean_io_error_to_string(v_a_3857_);
v___x_3862_ = 3;
v___x_3863_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*1, v___x_3862_);
lean_inc_ref(v___y_3830_);
v___x_3864_ = lean_apply_2(v___y_3830_, v___x_3863_, lean_box(0));
v___x_3865_ = lean_box(0);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3865_);
v___x_3867_ = v___x_3859_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3845_, 1);
v_msg_3733_ = v_msg_3838_;
v___y_3734_ = v___y_3830_;
goto v___jp_3732_;
}
}
}
}
}
v___jp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_3874_ = l_Lake_JsonObject_getJson_x3f(v_out_3728_, v___x_3873_);
if (lean_obj_tag(v___x_3874_) == 0)
{
v_msg_3829_ = v_msg_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3828_;
}
else
{
lean_object* v_val_3875_; lean_object* v___x_3876_; 
v_val_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_val_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = l_Lean_Json_getStr_x3f(v_val_3875_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_dec_ref_known(v___x_3876_, 1);
v_msg_3829_ = v_msg_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3828_;
}
else
{
if (lean_obj_tag(v___x_3876_) == 1)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v_msg_3880_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5));
v___x_3879_ = lean_string_append(v_msg_3871_, v___x_3878_);
v_msg_3880_ = lean_string_append(v___x_3879_, v_a_3877_);
lean_dec(v_a_3877_);
v_msg_3829_ = v_msg_3880_;
v___y_3830_ = v___y_3872_;
goto v___jp_3828_;
}
else
{
lean_dec_ref_known(v___x_3876_, 1);
v_msg_3829_ = v_msg_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3828_;
}
}
}
}
v___jp_3881_:
{
uint64_t v_hash_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v_msg_3891_; 
v_hash_3884_ = lean_ctor_get_uint64(v_info_3726_, sizeof(void*)*3);
v___x_3885_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_3886_ = lean_string_append(v___y_3883_, v___x_3885_);
v___x_3887_ = lean_string_append(v___x_3886_, v___y_3882_);
v___x_3888_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7));
v___x_3889_ = lean_string_append(v___x_3887_, v___x_3888_);
v___x_3890_ = l_Lake_lowerHexUInt64(v_hash_3884_);
v_msg_3891_ = lean_string_append(v___x_3889_, v___x_3890_);
lean_dec_ref(v___x_3890_);
if (lean_obj_tag(v_code_x3f_3727_) == 1)
{
lean_object* v_a_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_msg_3898_; 
v_a_3892_ = lean_ctor_get(v_code_x3f_3727_, 0);
v___x_3893_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8));
v___x_3894_ = lean_string_append(v_msg_3891_, v___x_3893_);
lean_inc(v_a_3892_);
v___x_3895_ = l_Nat_reprFast(v_a_3892_);
v___x_3896_ = lean_string_append(v___x_3894_, v___x_3895_);
lean_dec_ref(v___x_3895_);
v___x_3897_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v_msg_3898_ = lean_string_append(v___x_3896_, v___x_3897_);
v_msg_3871_ = v_msg_3898_;
v___y_3872_ = v_a_3730_;
goto v___jp_3870_;
}
else
{
v_msg_3871_ = v_msg_3891_;
v___y_3872_ = v_a_3730_;
goto v___jp_3870_;
}
}
v___jp_3899_:
{
lean_object* v_s_3901_; 
v_s_3901_ = lean_ctor_get(v_scope_3827_, 0);
lean_inc_ref(v_s_3901_);
lean_dec_ref(v_scope_3827_);
v___y_3882_ = v___y_3900_;
v___y_3883_ = v_s_3901_;
goto v___jp_3881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object* v_cfg_3904_, lean_object* v_hOut_3905_, lean_object* v_info_3906_, lean_object* v_code_x3f_3907_, lean_object* v_out_3908_, lean_object* v_line_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3904_, v_hOut_3905_, v_info_3906_, v_code_x3f_3907_, v_out_3908_, v_line_3909_, v_a_3910_);
lean_dec_ref(v_a_3910_);
lean_dec(v_out_3908_);
lean_dec_ref(v_info_3906_);
lean_dec(v_hOut_3905_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object* v_cfg_3913_, lean_object* v_hOut_3914_, lean_object* v_val_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, uint8_t v___x_3918_, lean_object* v_code_x3f_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3913_, v_hOut_3914_, v_val_3915_, v_code_x3f_3919_, v_a_3916_, v_a_3917_, v___y_3921_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3940_; 
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; 
v_unused_3941_ = lean_ctor_get(v___x_3923_, 0);
lean_dec(v_unused_3941_);
v___x_3925_ = v___x_3923_;
v_isShared_3926_ = v_isSharedCheck_3940_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v___x_3923_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3940_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v_numSuccesses_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3939_; 
v_numSuccesses_3927_ = lean_ctor_get(v___y_3920_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___y_3920_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3929_ = v___y_3920_;
v_isShared_3930_ = v_isSharedCheck_3939_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_numSuccesses_3927_);
lean_dec(v___y_3920_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3939_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3931_ = lean_box(0);
if (v_isShared_3930_ == 0)
{
v___x_3933_ = v___x_3929_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_numSuccesses_3927_);
v___x_3933_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3936_; 
lean_ctor_set_uint8(v___x_3933_, sizeof(void*)*1, v___x_3918_);
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3931_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3934_);
v___x_3936_ = v___x_3925_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec_ref(v___y_3920_);
v_a_3942_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3923_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3923_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object* v_cfg_3950_, lean_object* v_hOut_3951_, lean_object* v_val_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v___x_3955_, lean_object* v_code_x3f_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
uint8_t v___x_34032__boxed_3960_; lean_object* v_res_3961_; 
v___x_34032__boxed_3960_ = lean_unbox(v___x_3955_);
v_res_3961_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_3950_, v_hOut_3951_, v_val_3952_, v_a_3953_, v_a_3954_, v___x_34032__boxed_3960_, v_code_x3f_3956_, v___y_3957_, v___y_3958_);
lean_dec_ref(v___y_3958_);
lean_dec(v_a_3953_);
lean_dec_ref(v_val_3952_);
lean_dec(v_hOut_3951_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object* v_cfg_3964_, lean_object* v_path_3965_, uint8_t v___x_3966_, uint64_t v_hash_3967_, lean_object* v_url_3968_, uint8_t v___x_3969_, lean_object* v_extraPaths_3970_, lean_object* v___x_3971_, lean_object* v_00___3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___y_3977_; uint64_t v___y_3993_; lean_object* v___y_4033_; lean_object* v___y_4083_; uint8_t v_kind_4111_; 
v_kind_4111_ = lean_ctor_get_uint8(v_cfg_3964_, sizeof(void*)*3);
if (v_kind_4111_ == 0)
{
lean_object* v_scope_4112_; lean_object* v_s_4113_; 
v_scope_4112_ = lean_ctor_get(v_cfg_3964_, 0);
lean_inc_ref(v_scope_4112_);
lean_dec_ref(v_cfg_3964_);
v_s_4113_ = lean_ctor_get(v_scope_4112_, 0);
lean_inc_ref(v_s_4113_);
lean_dec_ref(v_scope_4112_);
v___y_4033_ = v_s_4113_;
goto v___jp_4032_;
}
else
{
lean_object* v_scope_4114_; lean_object* v_s_4115_; 
v_scope_4114_ = lean_ctor_get(v_cfg_3964_, 0);
lean_inc_ref(v_scope_4114_);
lean_dec_ref(v_cfg_3964_);
v_s_4115_ = lean_ctor_get(v_scope_4114_, 0);
lean_inc_ref(v_s_4115_);
lean_dec_ref(v_scope_4114_);
v___y_4083_ = v_s_4115_;
goto v___jp_4082_;
}
v___jp_3976_:
{
uint8_t v_didError_3978_; lean_object* v_numSuccesses_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3991_; 
v_didError_3978_ = lean_ctor_get_uint8(v___y_3977_, sizeof(void*)*1);
v_numSuccesses_3979_ = lean_ctor_get(v___y_3977_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___y_3977_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3981_ = v___y_3977_;
v_isShared_3982_ = v_isSharedCheck_3991_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_numSuccesses_3979_);
lean_dec(v___y_3977_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3991_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3983_ = lean_box(0);
v___x_3984_ = lean_unsigned_to_nat(1u);
v___x_3985_ = lean_nat_add(v_numSuccesses_3979_, v___x_3984_);
lean_dec(v_numSuccesses_3979_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3985_);
v___x_3987_ = v___x_3981_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3990_, sizeof(void*)*1, v_didError_3978_);
v___x_3987_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3983_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
}
}
v___jp_3992_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3994_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_3965_);
v___x_3995_ = lean_string_append(v_path_3965_, v___x_3994_);
v___x_3996_ = l_Lake_lowerHexUInt64(v___y_3993_);
v___x_3997_ = lean_string_append(v___x_3995_, v___x_3996_);
lean_dec_ref(v___x_3996_);
v___x_3998_ = 3;
v___x_3999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set_uint8(v___x_3999_, sizeof(void*)*1, v___x_3998_);
lean_inc_ref(v___y_3974_);
v___x_4000_ = lean_apply_2(v___y_3974_, v___x_3999_, lean_box(0));
v___x_4001_ = lean_io_remove_file(v_path_3965_);
lean_dec_ref(v_path_3965_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4018_; 
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; 
v_unused_4019_ = lean_ctor_get(v___x_4001_, 0);
lean_dec(v_unused_4019_);
v___x_4003_ = v___x_4001_;
v_isShared_4004_ = v_isSharedCheck_4018_;
goto v_resetjp_4002_;
}
else
{
lean_dec(v___x_4001_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4018_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v_numSuccesses_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4017_; 
v_numSuccesses_4005_ = lean_ctor_get(v___y_3973_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___y_3973_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4007_ = v___y_3973_;
v_isShared_4008_ = v_isSharedCheck_4017_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_numSuccesses_4005_);
lean_dec(v___y_3973_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4017_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4009_ = lean_box(0);
if (v_isShared_4008_ == 0)
{
v___x_4011_ = v___x_4007_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_numSuccesses_4005_);
v___x_4011_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4012_; lean_object* v___x_4014_; 
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*1, v___x_3966_);
v___x_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4009_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 0, v___x_4012_);
v___x_4014_ = v___x_4003_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref(v___y_3973_);
v_a_4020_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4022_ = v___x_4001_;
v_isShared_4023_ = v_isSharedCheck_4031_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4001_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4031_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4024_ = lean_io_error_to_string(v_a_4020_);
v___x_4025_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*1, v___x_3998_);
lean_inc_ref(v___y_3974_);
v___x_4026_ = lean_apply_2(v___y_3974_, v___x_4025_, lean_box(0));
v___x_4027_ = lean_box(0);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4027_);
v___x_4029_ = v___x_4022_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
v___jp_4032_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4034_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0));
v___x_4035_ = lean_string_append(v___y_4033_, v___x_4034_);
v___x_4036_ = l_Lake_lowerHexUInt64(v_hash_3967_);
v___x_4037_ = lean_string_append(v___x_4035_, v___x_4036_);
lean_dec_ref(v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4039_ = lean_string_append(v___x_4037_, v___x_4038_);
v___x_4040_ = lean_string_append(v___x_4039_, v_path_3965_);
v___x_4041_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
v___x_4043_ = lean_string_append(v___x_4042_, v_url_3968_);
v___x_4044_ = 1;
v___x_4045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set_uint8(v___x_4045_, sizeof(void*)*1, v___x_4044_);
lean_inc_ref(v___y_3974_);
v___x_4046_ = lean_apply_2(v___y_3974_, v___x_4045_, lean_box(0));
v___x_4047_ = l_Lake_computeBinFileHash(v_path_3965_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; uint64_t v___x_4049_; uint8_t v___x_4050_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
v___x_4049_ = lean_unbox_uint64(v_a_4048_);
v___x_4050_ = lean_uint64_dec_eq(v___x_4049_, v_hash_3967_);
if (v___x_4050_ == 0)
{
uint64_t v___x_4051_; 
v___x_4051_ = lean_unbox_uint64(v_a_4048_);
lean_dec(v_a_4048_);
v___y_3993_ = v___x_4051_;
goto v___jp_3992_;
}
else
{
if (v___x_3969_ == 0)
{
lean_object* v___x_4052_; uint8_t v___x_4053_; 
lean_dec(v_a_4048_);
v___x_4052_ = lean_array_get_size(v_extraPaths_3970_);
v___x_4053_ = lean_nat_dec_eq(v___x_4052_, v___x_3971_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = l___private_Lake_Config_Cache_0__Lake_CacheService_createExtraPaths(v_path_3965_, v_extraPaths_3970_);
lean_dec_ref(v_path_3965_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_dec_ref_known(v___x_4054_, 1);
v___y_3977_ = v___y_3973_;
goto v___jp_3976_;
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v___y_3973_);
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4067_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4067_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
v___x_4059_ = lean_io_error_to_string(v_a_4055_);
v___x_4060_ = 3;
v___x_4061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4061_, 0, v___x_4059_);
lean_ctor_set_uint8(v___x_4061_, sizeof(void*)*1, v___x_4060_);
lean_inc_ref(v___y_3974_);
v___x_4062_ = lean_apply_2(v___y_3974_, v___x_4061_, lean_box(0));
v___x_4063_ = lean_box(0);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4063_);
v___x_4065_ = v___x_4057_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_dec_ref(v_path_3965_);
v___y_3977_ = v___y_3973_;
goto v___jp_3976_;
}
}
else
{
uint64_t v___x_4068_; 
v___x_4068_ = lean_unbox_uint64(v_a_4048_);
lean_dec(v_a_4048_);
v___y_3993_ = v___x_4068_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v___y_3973_);
lean_dec_ref(v_path_3965_);
v_a_4069_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4071_ = v___x_4047_;
v_isShared_4072_ = v_isSharedCheck_4081_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4047_);
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
lean_inc_ref(v___y_3974_);
v___x_4076_ = lean_apply_2(v___y_3974_, v___x_4075_, lean_box(0));
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
v___x_4086_ = l_Lake_lowerHexUInt64(v_hash_3967_);
v___x_4087_ = lean_string_append(v___x_4085_, v___x_4086_);
lean_dec_ref(v___x_4086_);
v___x_4088_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4089_ = lean_string_append(v___x_4087_, v___x_4088_);
v___x_4090_ = lean_string_append(v___x_4089_, v_path_3965_);
lean_dec_ref(v_path_3965_);
v___x_4091_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4092_ = lean_string_append(v___x_4090_, v___x_4091_);
v___x_4093_ = lean_string_append(v___x_4092_, v_url_3968_);
v___x_4094_ = 1;
v___x_4095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*1, v___x_4094_);
lean_inc_ref(v___y_3974_);
v___x_4096_ = lean_apply_2(v___y_3974_, v___x_4095_, lean_box(0));
v_didError_4097_ = lean_ctor_get_uint8(v___y_3973_, sizeof(void*)*1);
v_numSuccesses_4098_ = lean_ctor_get(v___y_3973_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___y_3973_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4100_ = v___y_3973_;
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_numSuccesses_4098_);
lean_dec(v___y_3973_);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object* v_cfg_4116_, lean_object* v_path_4117_, lean_object* v___x_4118_, lean_object* v_hash_4119_, lean_object* v_url_4120_, lean_object* v___x_4121_, lean_object* v_extraPaths_4122_, lean_object* v___x_4123_, lean_object* v_00___4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
uint8_t v___x_34112__boxed_4128_; uint64_t v_hash_34113__boxed_4129_; uint8_t v___x_34115__boxed_4130_; lean_object* v_res_4131_; 
v___x_34112__boxed_4128_ = lean_unbox(v___x_4118_);
v_hash_34113__boxed_4129_ = lean_unbox_uint64(v_hash_4119_);
lean_dec_ref(v_hash_4119_);
v___x_34115__boxed_4130_ = lean_unbox(v___x_4121_);
v_res_4131_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4116_, v_path_4117_, v___x_34112__boxed_4128_, v_hash_34113__boxed_4129_, v_url_4120_, v___x_34115__boxed_4130_, v_extraPaths_4122_, v___x_4123_, v_00___4124_, v___y_4125_, v___y_4126_);
lean_dec_ref(v___y_4126_);
lean_dec(v___x_4123_);
lean_dec_ref(v_extraPaths_4122_);
lean_dec_ref(v_url_4120_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object* v_a_4138_, lean_object* v_cfg_4139_, lean_object* v_h_4140_, lean_object* v_hOut_4141_, lean_object* v_s_4142_){
_start:
{
lean_object* v___y_4145_; lean_object* v___x_4157_; 
v___x_4157_ = lean_io_prim_handle_get_line(v_h_4140_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4257_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4257_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4257_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v_startInclusive_4170_; lean_object* v_endExclusive_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
v___x_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = lean_string_utf8_byte_size(v_a_4158_);
lean_inc(v_a_4158_);
v___x_4168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4168_, 0, v_a_4158_);
lean_ctor_set(v___x_4168_, 1, v___x_4166_);
lean_ctor_set(v___x_4168_, 2, v___x_4167_);
v___x_4169_ = l_String_Slice_trimAscii(v___x_4168_);
v_startInclusive_4170_ = lean_ctor_get(v___x_4169_, 1);
lean_inc(v_startInclusive_4170_);
v_endExclusive_4171_ = lean_ctor_get(v___x_4169_, 2);
lean_inc(v_endExclusive_4171_);
v___x_4172_ = lean_nat_sub(v_endExclusive_4171_, v_startInclusive_4170_);
lean_dec(v_startInclusive_4170_);
lean_dec(v_endExclusive_4171_);
v___x_4173_ = lean_nat_dec_eq(v___x_4172_, v___x_4166_);
lean_dec(v___x_4172_);
if (v___x_4173_ == 0)
{
uint8_t v___x_4174_; lean_object* v___y_4176_; lean_object* v_a_4194_; lean_object* v___x_4213_; 
lean_del_object(v___x_4160_);
v___x_4174_ = 1;
lean_inc(v_a_4158_);
v___x_4213_ = l_Lean_Json_parse(v_a_4158_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; 
lean_dec(v_a_4158_);
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v_a_4194_ = v_a_4214_;
goto v___jp_4193_;
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4216_; 
v_a_4215_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4216_ = l_Lean_Json_getObj_x3f(v_a_4215_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; 
lean_dec(v_a_4158_);
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v_a_4194_ = v_a_4217_;
goto v___jp_4193_;
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4216_, 1);
v___x_4219_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4139_, v_a_4218_);
if (lean_obj_tag(v___x_4219_) == 1)
{
lean_object* v_val_4220_; lean_object* v_url_4221_; uint64_t v_hash_4222_; lean_object* v_path_4223_; lean_object* v_extraPaths_4224_; lean_object* v___x_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_dec_ref(v___x_4169_);
v_val_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc_n(v_val_4220_, 2);
lean_dec_ref_known(v___x_4219_, 1);
v_url_4221_ = lean_ctor_get(v_val_4220_, 0);
v_hash_4222_ = lean_ctor_get_uint64(v_val_4220_, sizeof(void*)*3);
v_path_4223_ = lean_ctor_get(v_val_4220_, 1);
v_extraPaths_4224_ = lean_ctor_get(v_val_4220_, 2);
v___x_4225_ = lean_box(v___x_4174_);
lean_inc(v_a_4158_);
lean_inc(v_a_4218_);
lean_inc(v_hOut_4141_);
lean_inc_ref(v_cfg_4139_);
v___f_4226_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed), 10, 6);
lean_closure_set(v___f_4226_, 0, v_cfg_4139_);
lean_closure_set(v___f_4226_, 1, v_hOut_4141_);
lean_closure_set(v___f_4226_, 2, v_val_4220_);
lean_closure_set(v___f_4226_, 3, v_a_4218_);
lean_closure_set(v___f_4226_, 4, v_a_4158_);
lean_closure_set(v___f_4226_, 5, v___x_4225_);
v___x_4227_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4228_ = l_Lake_JsonObject_getJson_x3f(v_a_4218_, v___x_4227_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v___x_4229_; 
lean_dec(v_val_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4158_);
v___x_4229_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_4163_ = v___f_4226_;
v___y_4164_ = v___x_4229_;
goto v___jp_4162_;
}
else
{
lean_object* v_val_4230_; lean_object* v___x_4231_; 
v_val_4230_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_val_4230_);
lean_dec_ref_known(v___x_4228_, 1);
v___x_4231_ = l_Lean_Json_getNat_x3f(v_val_4230_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_val_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4158_);
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4241_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4241_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4236_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4237_ = lean_string_append(v___x_4236_, v_a_4232_);
lean_dec(v_a_4232_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v___x_4237_);
v___x_4239_ = v___x_4234_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
v___y_4163_ = v___f_4226_;
v___y_4164_ = v___x_4239_;
goto v___jp_4162_;
}
}
}
else
{
if (lean_obj_tag(v___x_4231_) == 1)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; 
lean_dec_ref(v___f_4226_);
v_a_4242_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4242_);
v___x_4243_ = lean_unsigned_to_nat(200u);
v___x_4244_ = lean_nat_dec_eq(v_a_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; uint8_t v___x_4246_; 
v___x_4245_ = lean_unsigned_to_nat(201u);
v___x_4246_ = lean_nat_dec_eq(v_a_4242_, v___x_4245_);
lean_dec(v_a_4242_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; 
lean_inc_ref(v_cfg_4139_);
v___x_4247_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4139_, v_hOut_4141_, v_val_4220_, v_a_4218_, v_a_4158_, v___x_4174_, v___x_4231_, v_s_4142_, v_a_4138_);
lean_dec(v_a_4218_);
lean_dec(v_val_4220_);
v___y_4145_ = v___x_4247_;
goto v___jp_4144_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_inc_ref(v_extraPaths_4224_);
lean_inc_ref(v_path_4223_);
lean_inc_ref(v_url_4221_);
lean_dec_ref_known(v___x_4231_, 1);
lean_dec(v_val_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4158_);
v___x_4248_ = lean_box(0);
lean_inc_ref(v_cfg_4139_);
v___x_4249_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4139_, v_path_4223_, v___x_4174_, v_hash_4222_, v_url_4221_, v___x_4173_, v_extraPaths_4224_, v___x_4166_, v___x_4248_, v_s_4142_, v_a_4138_);
lean_dec_ref(v_extraPaths_4224_);
lean_dec_ref(v_url_4221_);
v___y_4145_ = v___x_4249_;
goto v___jp_4144_;
}
}
else
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
lean_inc_ref(v_extraPaths_4224_);
lean_inc_ref(v_path_4223_);
lean_inc_ref(v_url_4221_);
lean_dec(v_a_4242_);
lean_dec_ref_known(v___x_4231_, 1);
lean_dec(v_val_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4158_);
v___x_4250_ = lean_box(0);
lean_inc_ref(v_cfg_4139_);
v___x_4251_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4139_, v_path_4223_, v___x_4174_, v_hash_4222_, v_url_4221_, v___x_4173_, v_extraPaths_4224_, v___x_4166_, v___x_4250_, v_s_4142_, v_a_4138_);
lean_dec_ref(v_extraPaths_4224_);
lean_dec_ref(v_url_4221_);
v___y_4145_ = v___x_4251_;
goto v___jp_4144_;
}
}
else
{
lean_dec(v_val_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4158_);
v___y_4163_ = v___f_4226_;
v___y_4164_ = v___x_4231_;
goto v___jp_4162_;
}
}
}
}
else
{
lean_object* v_scope_4252_; lean_object* v_s_4253_; 
lean_dec(v___x_4219_);
lean_dec(v_a_4218_);
lean_dec(v_a_4158_);
v_scope_4252_ = lean_ctor_get(v_cfg_4139_, 0);
v_s_4253_ = lean_ctor_get(v_scope_4252_, 0);
lean_inc_ref(v_s_4253_);
v___y_4176_ = v_s_4253_;
goto v___jp_4175_;
}
}
}
v___jp_4175_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v_numSuccesses_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4192_; 
v___x_4177_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4178_ = lean_string_append(v___y_4176_, v___x_4177_);
v___x_4179_ = l_String_Slice_toString(v___x_4169_);
lean_dec_ref(v___x_4169_);
v___x_4180_ = lean_string_append(v___x_4178_, v___x_4179_);
lean_dec_ref(v___x_4179_);
v___x_4181_ = 3;
v___x_4182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4182_, 0, v___x_4180_);
lean_ctor_set_uint8(v___x_4182_, sizeof(void*)*1, v___x_4181_);
lean_inc_ref(v_a_4138_);
v___x_4183_ = lean_apply_2(v_a_4138_, v___x_4182_, lean_box(0));
v_numSuccesses_4184_ = lean_ctor_get(v_s_4142_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v_s_4142_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4186_ = v_s_4142_;
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_numSuccesses_4184_);
lean_dec(v_s_4142_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_numSuccesses_4184_);
v___x_4189_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_ctor_set_uint8(v___x_4189_, sizeof(void*)*1, v___x_4174_);
v_s_4142_ = v___x_4189_;
goto _start;
}
}
}
v___jp_4193_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v_numSuccesses_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v___x_4195_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4196_ = lean_string_append(v___x_4195_, v_a_4194_);
lean_dec_ref(v_a_4194_);
v___x_4197_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4198_ = lean_string_append(v___x_4196_, v___x_4197_);
v___x_4199_ = l_String_Slice_toString(v___x_4169_);
lean_dec_ref(v___x_4169_);
v___x_4200_ = lean_string_append(v___x_4198_, v___x_4199_);
lean_dec_ref(v___x_4199_);
v___x_4201_ = 3;
v___x_4202_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4202_, 0, v___x_4200_);
lean_ctor_set_uint8(v___x_4202_, sizeof(void*)*1, v___x_4201_);
lean_inc_ref(v_a_4138_);
v___x_4203_ = lean_apply_2(v_a_4138_, v___x_4202_, lean_box(0));
v_numSuccesses_4204_ = lean_ctor_get(v_s_4142_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_s_4142_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v_s_4142_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_numSuccesses_4204_);
lean_dec(v_s_4142_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_numSuccesses_4204_);
v___x_4209_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*1, v___x_4174_);
v_s_4142_ = v___x_4209_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4255_; 
lean_dec_ref(v___x_4169_);
lean_dec(v_a_4158_);
lean_dec(v_hOut_4141_);
lean_dec_ref(v_cfg_4139_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v_s_4142_);
v___x_4255_ = v___x_4160_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_s_4142_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
v___jp_4162_:
{
lean_object* v___x_4165_; 
lean_inc_ref(v_a_4138_);
v___x_4165_ = lean_apply_4(v___y_4163_, v___y_4164_, v_s_4142_, v_a_4138_, lean_box(0));
v___y_4145_ = v___x_4165_;
goto v___jp_4144_;
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4270_; 
lean_dec_ref(v_s_4142_);
lean_dec(v_hOut_4141_);
lean_dec_ref(v_cfg_4139_);
v_a_4258_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4260_ = v___x_4157_;
v_isShared_4261_ = v_isSharedCheck_4270_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4157_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4270_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4262_ = lean_io_error_to_string(v_a_4258_);
v___x_4263_ = 3;
v___x_4264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set_uint8(v___x_4264_, sizeof(void*)*1, v___x_4263_);
lean_inc_ref(v_a_4138_);
v___x_4265_ = lean_apply_2(v_a_4138_, v___x_4264_, lean_box(0));
v___x_4266_ = lean_box(0);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4266_);
v___x_4268_ = v___x_4260_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
v___jp_4144_:
{
if (lean_obj_tag(v___y_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v_snd_4147_; 
v_a_4146_ = lean_ctor_get(v___y_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___y_4145_, 1);
v_snd_4147_ = lean_ctor_get(v_a_4146_, 1);
lean_inc(v_snd_4147_);
lean_dec(v_a_4146_);
v_s_4142_ = v_snd_4147_;
goto _start;
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec(v_hOut_4141_);
lean_dec_ref(v_cfg_4139_);
v_a_4149_ = lean_ctor_get(v___y_4145_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___y_4145_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___y_4145_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___y_4145_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object* v_a_4271_, lean_object* v_cfg_4272_, lean_object* v_h_4273_, lean_object* v_hOut_4274_, lean_object* v_s_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4271_, v_cfg_4272_, v_h_4273_, v_hOut_4274_, v_s_4275_);
lean_dec(v_h_4273_);
lean_dec_ref(v_a_4271_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object* v_cfg_4278_, lean_object* v_h_4279_, lean_object* v_hOut_4280_, lean_object* v_s_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v___y_4285_; lean_object* v___x_4297_; 
v___x_4297_ = lean_io_prim_handle_get_line(v_h_4279_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4394_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4394_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4394_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v_startInclusive_4306_; lean_object* v_endExclusive_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4302_ = lean_unsigned_to_nat(0u);
v___x_4303_ = lean_string_utf8_byte_size(v_a_4298_);
lean_inc(v_a_4298_);
v___x_4304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4304_, 0, v_a_4298_);
lean_ctor_set(v___x_4304_, 1, v___x_4302_);
lean_ctor_set(v___x_4304_, 2, v___x_4303_);
v___x_4305_ = l_String_Slice_trimAscii(v___x_4304_);
v_startInclusive_4306_ = lean_ctor_get(v___x_4305_, 1);
lean_inc(v_startInclusive_4306_);
v_endExclusive_4307_ = lean_ctor_get(v___x_4305_, 2);
lean_inc(v_endExclusive_4307_);
v___x_4308_ = lean_nat_sub(v_endExclusive_4307_, v_startInclusive_4306_);
lean_dec(v_startInclusive_4306_);
lean_dec(v_endExclusive_4307_);
v___x_4309_ = lean_nat_dec_eq(v___x_4308_, v___x_4302_);
lean_dec(v___x_4308_);
if (v___x_4309_ == 0)
{
uint8_t v___x_4310_; lean_object* v___y_4312_; lean_object* v_a_4330_; lean_object* v___x_4349_; 
lean_del_object(v___x_4300_);
v___x_4310_ = 1;
lean_inc(v_a_4298_);
v___x_4349_ = l_Lean_Json_parse(v_a_4298_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; 
lean_dec(v_a_4298_);
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v_a_4330_ = v_a_4350_;
goto v___jp_4329_;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4352_; 
v_a_4351_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4352_ = l_Lean_Json_getObj_x3f(v_a_4351_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; 
lean_dec(v_a_4298_);
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v_a_4330_ = v_a_4353_;
goto v___jp_4329_;
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4355_; 
v_a_4354_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4355_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4278_, v_a_4354_);
if (lean_obj_tag(v___x_4355_) == 1)
{
lean_object* v_val_4356_; lean_object* v_url_4357_; uint64_t v_hash_4358_; lean_object* v_path_4359_; lean_object* v_extraPaths_4360_; lean_object* v___y_4362_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_dec_ref(v___x_4305_);
v_val_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_val_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v_url_4357_ = lean_ctor_get(v_val_4356_, 0);
v_hash_4358_ = lean_ctor_get_uint64(v_val_4356_, sizeof(void*)*3);
v_path_4359_ = lean_ctor_get(v_val_4356_, 1);
v_extraPaths_4360_ = lean_ctor_get(v_val_4356_, 2);
v___x_4364_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4365_ = l_Lake_JsonObject_getJson_x3f(v_a_4354_, v___x_4364_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v___x_4366_; 
v___x_4366_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_4362_ = v___x_4366_;
goto v___jp_4361_;
}
else
{
lean_object* v_val_4367_; lean_object* v___x_4368_; 
v_val_4367_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_val_4367_);
lean_dec_ref_known(v___x_4365_, 1);
v___x_4368_ = l_Lean_Json_getNat_x3f(v_val_4367_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4378_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4378_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4378_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4376_; 
v___x_4373_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4374_ = lean_string_append(v___x_4373_, v_a_4369_);
lean_dec(v_a_4369_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4374_);
v___x_4376_ = v___x_4371_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
v___y_4362_ = v___x_4376_;
goto v___jp_4361_;
}
}
}
else
{
if (lean_obj_tag(v___x_4368_) == 1)
{
lean_object* v_a_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v_a_4379_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4379_);
v___x_4380_ = lean_unsigned_to_nat(200u);
v___x_4381_ = lean_nat_dec_eq(v_a_4379_, v___x_4380_);
if (v___x_4381_ == 0)
{
lean_object* v___x_4382_; uint8_t v___x_4383_; 
v___x_4382_ = lean_unsigned_to_nat(201u);
v___x_4383_ = lean_nat_dec_eq(v_a_4379_, v___x_4382_);
lean_dec(v_a_4379_);
if (v___x_4383_ == 0)
{
lean_object* v___x_4384_; 
lean_inc_ref(v_cfg_4278_);
v___x_4384_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4278_, v_hOut_4280_, v_val_4356_, v_a_4354_, v_a_4298_, v___x_4310_, v___x_4368_, v_s_4281_, v_a_4282_);
lean_dec(v_a_4354_);
lean_dec(v_val_4356_);
v___y_4285_ = v___x_4384_;
goto v___jp_4284_;
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_inc_ref(v_extraPaths_4360_);
lean_inc_ref(v_path_4359_);
lean_inc_ref(v_url_4357_);
lean_dec_ref_known(v___x_4368_, 1);
lean_dec(v_val_4356_);
lean_dec(v_a_4354_);
lean_dec(v_a_4298_);
v___x_4385_ = lean_box(0);
lean_inc_ref(v_cfg_4278_);
v___x_4386_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4278_, v_path_4359_, v___x_4310_, v_hash_4358_, v_url_4357_, v___x_4309_, v_extraPaths_4360_, v___x_4302_, v___x_4385_, v_s_4281_, v_a_4282_);
lean_dec_ref(v_extraPaths_4360_);
lean_dec_ref(v_url_4357_);
v___y_4285_ = v___x_4386_;
goto v___jp_4284_;
}
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
lean_inc_ref(v_extraPaths_4360_);
lean_inc_ref(v_path_4359_);
lean_inc_ref(v_url_4357_);
lean_dec(v_a_4379_);
lean_dec_ref_known(v___x_4368_, 1);
lean_dec(v_val_4356_);
lean_dec(v_a_4354_);
lean_dec(v_a_4298_);
v___x_4387_ = lean_box(0);
lean_inc_ref(v_cfg_4278_);
v___x_4388_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4278_, v_path_4359_, v___x_4310_, v_hash_4358_, v_url_4357_, v___x_4309_, v_extraPaths_4360_, v___x_4302_, v___x_4387_, v_s_4281_, v_a_4282_);
lean_dec_ref(v_extraPaths_4360_);
lean_dec_ref(v_url_4357_);
v___y_4285_ = v___x_4388_;
goto v___jp_4284_;
}
}
else
{
v___y_4362_ = v___x_4368_;
goto v___jp_4361_;
}
}
}
v___jp_4361_:
{
lean_object* v___x_4363_; 
lean_inc_ref(v_cfg_4278_);
v___x_4363_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4278_, v_hOut_4280_, v_val_4356_, v_a_4354_, v_a_4298_, v___x_4310_, v___y_4362_, v_s_4281_, v_a_4282_);
lean_dec(v_a_4354_);
lean_dec(v_val_4356_);
v___y_4285_ = v___x_4363_;
goto v___jp_4284_;
}
}
else
{
lean_object* v_scope_4389_; lean_object* v_s_4390_; 
lean_dec(v___x_4355_);
lean_dec(v_a_4354_);
lean_dec(v_a_4298_);
v_scope_4389_ = lean_ctor_get(v_cfg_4278_, 0);
v_s_4390_ = lean_ctor_get(v_scope_4389_, 0);
lean_inc_ref(v_s_4390_);
v___y_4312_ = v_s_4390_;
goto v___jp_4311_;
}
}
}
v___jp_4311_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v_numSuccesses_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4328_; 
v___x_4313_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4314_ = lean_string_append(v___y_4312_, v___x_4313_);
v___x_4315_ = l_String_Slice_toString(v___x_4305_);
lean_dec_ref(v___x_4305_);
v___x_4316_ = lean_string_append(v___x_4314_, v___x_4315_);
lean_dec_ref(v___x_4315_);
v___x_4317_ = 3;
v___x_4318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set_uint8(v___x_4318_, sizeof(void*)*1, v___x_4317_);
lean_inc_ref(v_a_4282_);
v___x_4319_ = lean_apply_2(v_a_4282_, v___x_4318_, lean_box(0));
v_numSuccesses_4320_ = lean_ctor_get(v_s_4281_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v_s_4281_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4322_ = v_s_4281_;
v_isShared_4323_ = v_isSharedCheck_4328_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_numSuccesses_4320_);
lean_dec(v_s_4281_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4328_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_numSuccesses_4320_);
v___x_4325_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4326_; 
lean_ctor_set_uint8(v___x_4325_, sizeof(void*)*1, v___x_4310_);
v___x_4326_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4282_, v_cfg_4278_, v_h_4279_, v_hOut_4280_, v___x_4325_);
return v___x_4326_;
}
}
}
v___jp_4329_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v_numSuccesses_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4348_; 
v___x_4331_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4332_ = lean_string_append(v___x_4331_, v_a_4330_);
lean_dec_ref(v_a_4330_);
v___x_4333_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4334_ = lean_string_append(v___x_4332_, v___x_4333_);
v___x_4335_ = l_String_Slice_toString(v___x_4305_);
lean_dec_ref(v___x_4305_);
v___x_4336_ = lean_string_append(v___x_4334_, v___x_4335_);
lean_dec_ref(v___x_4335_);
v___x_4337_ = 3;
v___x_4338_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set_uint8(v___x_4338_, sizeof(void*)*1, v___x_4337_);
lean_inc_ref(v_a_4282_);
v___x_4339_ = lean_apply_2(v_a_4282_, v___x_4338_, lean_box(0));
v_numSuccesses_4340_ = lean_ctor_get(v_s_4281_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_s_4281_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4342_ = v_s_4281_;
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_numSuccesses_4340_);
lean_dec(v_s_4281_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_numSuccesses_4340_);
v___x_4345_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; 
lean_ctor_set_uint8(v___x_4345_, sizeof(void*)*1, v___x_4310_);
v___x_4346_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4282_, v_cfg_4278_, v_h_4279_, v_hOut_4280_, v___x_4345_);
return v___x_4346_;
}
}
}
}
else
{
lean_object* v___x_4392_; 
lean_dec_ref(v___x_4305_);
lean_dec(v_a_4298_);
lean_dec(v_hOut_4280_);
lean_dec_ref(v_cfg_4278_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v_s_4281_);
v___x_4392_ = v___x_4300_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_s_4281_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4407_; 
lean_dec_ref(v_s_4281_);
lean_dec(v_hOut_4280_);
lean_dec_ref(v_cfg_4278_);
v_a_4395_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4397_ = v___x_4297_;
v_isShared_4398_ = v_isSharedCheck_4407_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4297_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4407_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4399_ = lean_io_error_to_string(v_a_4395_);
v___x_4400_ = 3;
v___x_4401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set_uint8(v___x_4401_, sizeof(void*)*1, v___x_4400_);
lean_inc_ref(v_a_4282_);
v___x_4402_ = lean_apply_2(v_a_4282_, v___x_4401_, lean_box(0));
v___x_4403_ = lean_box(0);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4403_);
v___x_4405_ = v___x_4397_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
v___jp_4284_:
{
if (lean_obj_tag(v___y_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v_snd_4287_; lean_object* v___x_4288_; 
v_a_4286_ = lean_ctor_get(v___y_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___y_4285_, 1);
v_snd_4287_ = lean_ctor_get(v_a_4286_, 1);
lean_inc(v_snd_4287_);
lean_dec(v_a_4286_);
v___x_4288_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4282_, v_cfg_4278_, v_h_4279_, v_hOut_4280_, v_snd_4287_);
return v___x_4288_;
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_hOut_4280_);
lean_dec_ref(v_cfg_4278_);
v_a_4289_ = lean_ctor_get(v___y_4285_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___y_4285_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___y_4285_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___y_4285_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object* v_cfg_4408_, lean_object* v_h_4409_, lean_object* v_hOut_4410_, lean_object* v_s_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4408_, v_h_4409_, v_hOut_4410_, v_s_4411_, v_a_4412_);
lean_dec_ref(v_a_4412_);
lean_dec(v_h_4409_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object* v_snd_4415_, lean_object* v___y_4416_, lean_object* v_a_x3f_4417_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_io_remove_file(v_snd_4415_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4440_; 
v_a_4428_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4430_ = v___x_4419_;
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4419_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; uint8_t v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4432_ = lean_io_error_to_string(v_a_4428_);
v___x_4433_ = 3;
v___x_4434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*1, v___x_4433_);
lean_inc_ref(v___y_4416_);
v___x_4435_ = lean_apply_2(v___y_4416_, v___x_4434_, lean_box(0));
v___x_4436_ = lean_box(0);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4436_);
v___x_4438_ = v___x_4430_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object* v_snd_4441_, lean_object* v___y_4442_, lean_object* v_a_x3f_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4441_, v___y_4442_, v_a_x3f_4443_);
lean_dec(v_a_x3f_4443_);
lean_dec_ref(v___y_4442_);
lean_dec_ref(v_snd_4441_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object* v_f_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v_fst_4451_; lean_object* v_snd_4452_; lean_object* v_r_4453_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v_fst_4451_ = lean_ctor_get(v_a_4450_, 0);
lean_inc(v_fst_4451_);
v_snd_4452_ = lean_ctor_get(v_a_4450_, 1);
lean_inc_n(v_snd_4452_, 2);
lean_dec(v_a_4450_);
lean_inc_ref(v___y_4447_);
v_r_4453_ = lean_apply_4(v_f_4446_, v_fst_4451_, v_snd_4452_, v___y_4447_, lean_box(0));
if (lean_obj_tag(v_r_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4478_; 
v_a_4454_ = lean_ctor_get(v_r_4453_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_r_4453_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4456_ = v_r_4453_;
v_isShared_4457_ = v_isSharedCheck_4478_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v_r_4453_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4478_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
lean_inc(v_a_4454_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set_tag(v___x_4456_, 1);
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4452_, v___y_4447_, v___x_4459_);
lean_dec_ref(v___x_4459_);
lean_dec(v_snd_4452_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4467_ == 0)
{
lean_object* v_unused_4468_; 
v_unused_4468_ = lean_ctor_get(v___x_4460_, 0);
lean_dec(v_unused_4468_);
v___x_4462_ = v___x_4460_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_dec(v___x_4460_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v_a_4454_);
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4454_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_a_4454_);
v_a_4469_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4460_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4460_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_a_4479_ = lean_ctor_get(v_r_4453_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v_r_4453_, 1);
v___x_4480_ = lean_box(0);
v___x_4481_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4452_, v___y_4447_, v___x_4480_);
lean_dec(v_snd_4452_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v___x_4481_, 0);
lean_dec(v_unused_4489_);
v___x_4483_ = v___x_4481_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v___x_4481_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
lean_ctor_set_tag(v___x_4483_, 1);
lean_ctor_set(v___x_4483_, 0, v_a_4479_);
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4479_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec(v_a_4479_);
v_a_4490_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4481_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4481_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4510_; 
lean_dec_ref(v_f_4446_);
v_a_4498_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4500_ = v___x_4449_;
v_isShared_4501_ = v_isSharedCheck_4510_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4449_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4510_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; uint8_t v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4502_ = lean_io_error_to_string(v_a_4498_);
v___x_4503_ = 3;
v___x_4504_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*1, v___x_4503_);
lean_inc_ref(v___y_4447_);
v___x_4505_ = lean_apply_2(v___y_4447_, v___x_4504_, lean_box(0));
v___x_4506_ = lean_box(0);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v___x_4506_);
v___x_4508_ = v___x_4500_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object* v_f_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4511_, v___y_4512_);
lean_dec_ref(v___y_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object* v_00_u03b1_4515_, lean_object* v_f_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; 
v___x_4519_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4516_, v___y_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object* v_00_u03b1_4520_, lean_object* v_f_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(v_00_u03b1_4520_, v_f_4521_, v___y_4522_);
lean_dec_ref(v___y_4522_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object* v_h_4527_, lean_object* v_as_4528_, size_t v_i_4529_, size_t v_stop_4530_, lean_object* v_b_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v___x_4534_; 
v___x_4534_ = lean_usize_dec_eq(v_i_4529_, v_stop_4530_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; lean_object* v_url_4536_; lean_object* v_path_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4535_ = lean_array_uget_borrowed(v_as_4528_, v_i_4529_);
v_url_4536_ = lean_ctor_get(v___x_4535_, 0);
v_path_4537_ = lean_ctor_get(v___x_4535_, 1);
v___x_4538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4536_);
v___x_4539_ = l_String_quote(v_url_4536_);
v___x_4540_ = lean_string_append(v___x_4538_, v___x_4539_);
lean_dec_ref(v___x_4539_);
v___x_4541_ = l_IO_FS_Handle_putStrLn(v_h_4527_, v___x_4540_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
lean_dec_ref_known(v___x_4541_, 1);
v___x_4542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1));
lean_inc_ref(v_path_4537_);
v___x_4543_ = l_String_quote(v_path_4537_);
v___x_4544_ = lean_string_append(v___x_4542_, v___x_4543_);
lean_dec_ref(v___x_4543_);
v___x_4545_ = l_IO_FS_Handle_putStrLn(v_h_4527_, v___x_4544_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; size_t v___x_4547_; size_t v___x_4548_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v___x_4547_ = ((size_t)1ULL);
v___x_4548_ = lean_usize_add(v_i_4529_, v___x_4547_);
v_i_4529_ = v___x_4548_;
v_b_4531_ = v_a_4546_;
goto _start;
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4562_; 
v_a_4550_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4552_ = v___x_4545_;
v_isShared_4553_ = v_isSharedCheck_4562_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4545_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4562_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4560_; 
v___x_4554_ = lean_io_error_to_string(v_a_4550_);
v___x_4555_ = 3;
v___x_4556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*1, v___x_4555_);
lean_inc_ref(v___y_4532_);
v___x_4557_ = lean_apply_2(v___y_4532_, v___x_4556_, lean_box(0));
v___x_4558_ = lean_box(0);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4558_);
v___x_4560_ = v___x_4552_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4558_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4575_; 
v_a_4563_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4565_ = v___x_4541_;
v_isShared_4566_ = v_isSharedCheck_4575_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4541_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4575_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4573_; 
v___x_4567_ = lean_io_error_to_string(v_a_4563_);
v___x_4568_ = 3;
v___x_4569_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4569_, 0, v___x_4567_);
lean_ctor_set_uint8(v___x_4569_, sizeof(void*)*1, v___x_4568_);
lean_inc_ref(v___y_4532_);
v___x_4570_ = lean_apply_2(v___y_4532_, v___x_4569_, lean_box(0));
v___x_4571_ = lean_box(0);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 0, v___x_4571_);
v___x_4573_ = v___x_4565_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4571_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
lean_object* v___x_4576_; 
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v_b_4531_);
return v___x_4576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object* v_h_4577_, lean_object* v_as_4578_, lean_object* v_i_4579_, lean_object* v_stop_4580_, lean_object* v_b_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
size_t v_i_boxed_4584_; size_t v_stop_boxed_4585_; lean_object* v_res_4586_; 
v_i_boxed_4584_ = lean_unbox_usize(v_i_4579_);
lean_dec(v_i_4579_);
v_stop_boxed_4585_ = lean_unbox_usize(v_stop_4580_);
lean_dec(v_stop_4580_);
v_res_4586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4577_, v_as_4578_, v_i_boxed_4584_, v_stop_boxed_4585_, v_b_4581_, v___y_4582_);
lean_dec_ref(v___y_4582_);
lean_dec_ref(v_as_4578_);
lean_dec(v_h_4577_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object* v_h_4588_, lean_object* v_as_4589_, size_t v_i_4590_, size_t v_stop_4591_, lean_object* v_b_4592_, lean_object* v___y_4593_){
_start:
{
uint8_t v___x_4595_; 
v___x_4595_ = lean_usize_dec_eq(v_i_4590_, v_stop_4591_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v_url_4597_; lean_object* v_path_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4596_ = lean_array_uget_borrowed(v_as_4589_, v_i_4590_);
v_url_4597_ = lean_ctor_get(v___x_4596_, 0);
v_path_4598_ = lean_ctor_get(v___x_4596_, 1);
v___x_4599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0));
lean_inc_ref(v_path_4598_);
v___x_4600_ = l_String_quote(v_path_4598_);
v___x_4601_ = lean_string_append(v___x_4599_, v___x_4600_);
lean_dec_ref(v___x_4600_);
v___x_4602_ = l_IO_FS_Handle_putStrLn(v_h_4588_, v___x_4601_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
lean_dec_ref_known(v___x_4602_, 1);
v___x_4603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4597_);
v___x_4604_ = l_String_quote(v_url_4597_);
v___x_4605_ = lean_string_append(v___x_4603_, v___x_4604_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = l_IO_FS_Handle_putStrLn(v_h_4588_, v___x_4605_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; size_t v___x_4608_; size_t v___x_4609_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref_known(v___x_4606_, 1);
v___x_4608_ = ((size_t)1ULL);
v___x_4609_ = lean_usize_add(v_i_4590_, v___x_4608_);
v_i_4590_ = v___x_4609_;
v_b_4592_ = v_a_4607_;
goto _start;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4623_; 
v_a_4611_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4613_ = v___x_4606_;
v_isShared_4614_ = v_isSharedCheck_4623_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4606_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4623_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; uint8_t v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4615_ = lean_io_error_to_string(v_a_4611_);
v___x_4616_ = 3;
v___x_4617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4617_, 0, v___x_4615_);
lean_ctor_set_uint8(v___x_4617_, sizeof(void*)*1, v___x_4616_);
lean_inc_ref(v___y_4593_);
v___x_4618_ = lean_apply_2(v___y_4593_, v___x_4617_, lean_box(0));
v___x_4619_ = lean_box(0);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4619_);
v___x_4621_ = v___x_4613_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4636_; 
v_a_4624_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4626_ = v___x_4602_;
v_isShared_4627_ = v_isSharedCheck_4636_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4602_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4636_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; uint8_t v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4628_ = lean_io_error_to_string(v_a_4624_);
v___x_4629_ = 3;
v___x_4630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set_uint8(v___x_4630_, sizeof(void*)*1, v___x_4629_);
lean_inc_ref(v___y_4593_);
v___x_4631_ = lean_apply_2(v___y_4593_, v___x_4630_, lean_box(0));
v___x_4632_ = lean_box(0);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4632_);
v___x_4634_ = v___x_4626_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_b_4592_);
return v___x_4637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object* v_h_4638_, lean_object* v_as_4639_, lean_object* v_i_4640_, lean_object* v_stop_4641_, lean_object* v_b_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
size_t v_i_boxed_4645_; size_t v_stop_boxed_4646_; lean_object* v_res_4647_; 
v_i_boxed_4645_ = lean_unbox_usize(v_i_4640_);
lean_dec(v_i_4640_);
v_stop_boxed_4646_ = lean_unbox_usize(v_stop_4641_);
lean_dec(v_stop_4641_);
v_res_4647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4638_, v_as_4639_, v_i_boxed_4645_, v_stop_boxed_4646_, v_b_4642_, v___y_4643_);
lean_dec_ref(v___y_4643_);
lean_dec_ref(v_as_4639_);
lean_dec(v_h_4638_);
return v_res_4647_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4663_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4664_ = lean_unsigned_to_nat(11u);
v___x_4665_ = lean_mk_empty_array_with_capacity(v___x_4664_);
v___x_4666_ = lean_array_push(v___x_4665_, v___x_4663_);
return v___x_4666_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12(void){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4668_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11);
v___x_4669_ = lean_array_push(v___x_4668_, v___x_4667_);
return v___x_4669_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4670_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6));
v___x_4671_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12);
v___x_4672_ = lean_array_push(v___x_4671_, v___x_4670_);
return v___x_4672_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4673_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4674_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13);
v___x_4675_ = lean_array_push(v___x_4674_, v___x_4673_);
return v___x_4675_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4676_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4677_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14);
v___x_4678_ = lean_array_push(v___x_4677_, v___x_4676_);
return v___x_4678_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16(void){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4680_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15);
v___x_4681_ = lean_array_push(v___x_4680_, v___x_4679_);
return v___x_4681_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4682_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4683_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16);
v___x_4684_ = lean_array_push(v___x_4683_, v___x_4682_);
return v___x_4684_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4686_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17);
v___x_4687_ = lean_array_push(v___x_4686_, v___x_4685_);
return v___x_4687_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19(void){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4688_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4689_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18);
v___x_4690_ = lean_array_push(v___x_4689_, v___x_4688_);
return v___x_4690_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4692_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19);
v___x_4693_ = lean_array_push(v___x_4692_, v___x_4691_);
return v___x_4693_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4695_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4696_ = lean_unsigned_to_nat(17u);
v___x_4697_ = lean_mk_empty_array_with_capacity(v___x_4696_);
v___x_4698_ = lean_array_push(v___x_4697_, v___x_4695_);
return v___x_4698_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23(void){
_start:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4699_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4700_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22);
v___x_4701_ = lean_array_push(v___x_4700_, v___x_4699_);
return v___x_4701_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24(void){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_4703_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23);
v___x_4704_ = lean_array_push(v___x_4703_, v___x_4702_);
return v___x_4704_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25(void){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4705_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4706_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24);
v___x_4707_ = lean_array_push(v___x_4706_, v___x_4705_);
return v___x_4707_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26(void){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_4709_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25);
v___x_4710_ = lean_array_push(v___x_4709_, v___x_4708_);
return v___x_4710_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4711_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21));
v___x_4712_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26);
v___x_4713_ = lean_array_push(v___x_4712_, v___x_4711_);
return v___x_4713_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28(void){
_start:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4714_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4715_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27);
v___x_4716_ = lean_array_push(v___x_4715_, v___x_4714_);
return v___x_4716_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29(void){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4717_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4718_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28);
v___x_4719_ = lean_array_push(v___x_4718_, v___x_4717_);
return v___x_4719_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30(void){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4720_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_4721_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29);
v___x_4722_ = lean_array_push(v___x_4721_, v___x_4720_);
return v___x_4722_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31(void){
_start:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4723_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_4724_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30);
v___x_4725_ = lean_array_push(v___x_4724_, v___x_4723_);
return v___x_4725_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_4727_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31);
v___x_4728_ = lean_array_push(v___x_4727_, v___x_4726_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object* v_cfg_4729_, lean_object* v_h_4730_, lean_object* v_path_4731_, lean_object* v___y_4732_){
_start:
{
uint8_t v___y_4735_; uint32_t v___y_4741_; uint8_t v___y_4742_; lean_object* v___y_4743_; lean_object* v___y_4744_; uint8_t v_kind_4753_; lean_object* v_scope_4754_; lean_object* v_infos_4755_; lean_object* v_key_4756_; uint32_t v___y_4758_; uint8_t v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4765_; uint32_t v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; uint8_t v___y_4769_; lean_object* v___y_4770_; lean_object* v___y_4771_; lean_object* v___y_4783_; uint32_t v___y_4784_; uint8_t v___y_4785_; lean_object* v___y_4786_; lean_object* v___y_4787_; uint32_t v___y_4792_; lean_object* v___y_4793_; uint8_t v___y_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; lean_object* v___y_4807_; uint32_t v___y_4808_; uint8_t v___y_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v_a_4814_; lean_object* v___y_4908_; lean_object* v___y_4936_; 
v_kind_4753_ = lean_ctor_get_uint8(v_cfg_4729_, sizeof(void*)*3);
v_scope_4754_ = lean_ctor_get(v_cfg_4729_, 0);
lean_inc_ref(v_scope_4754_);
v_infos_4755_ = lean_ctor_get(v_cfg_4729_, 1);
lean_inc_ref(v_infos_4755_);
v_key_4756_ = lean_ctor_get(v_cfg_4729_, 2);
if (v_kind_4753_ == 0)
{
lean_object* v___x_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; 
v___x_4937_ = lean_unsigned_to_nat(0u);
v___x_4938_ = lean_array_get_size(v_infos_4755_);
v___x_4939_ = lean_nat_dec_lt(v___x_4937_, v___x_4938_);
if (v___x_4939_ == 0)
{
goto v___jp_4890_;
}
else
{
lean_object* v___x_4940_; uint8_t v___x_4941_; 
v___x_4940_ = lean_box(0);
v___x_4941_ = lean_nat_dec_le(v___x_4938_, v___x_4938_);
if (v___x_4941_ == 0)
{
if (v___x_4939_ == 0)
{
goto v___jp_4890_;
}
else
{
size_t v___x_4942_; size_t v___x_4943_; lean_object* v___x_4944_; 
v___x_4942_ = ((size_t)0ULL);
v___x_4943_ = lean_usize_of_nat(v___x_4938_);
v___x_4944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4730_, v_infos_4755_, v___x_4942_, v___x_4943_, v___x_4940_, v___y_4732_);
v___y_4908_ = v___x_4944_;
goto v___jp_4907_;
}
}
else
{
size_t v___x_4945_; size_t v___x_4946_; lean_object* v___x_4947_; 
v___x_4945_ = ((size_t)0ULL);
v___x_4946_ = lean_usize_of_nat(v___x_4938_);
v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4730_, v_infos_4755_, v___x_4945_, v___x_4946_, v___x_4940_, v___y_4732_);
v___y_4908_ = v___x_4947_;
goto v___jp_4907_;
}
}
}
else
{
lean_object* v___x_4948_; lean_object* v___x_4949_; uint8_t v___x_4950_; 
v___x_4948_ = lean_unsigned_to_nat(0u);
v___x_4949_ = lean_array_get_size(v_infos_4755_);
v___x_4950_ = lean_nat_dec_lt(v___x_4948_, v___x_4949_);
if (v___x_4950_ == 0)
{
goto v___jp_4909_;
}
else
{
lean_object* v___x_4951_; uint8_t v___x_4952_; 
v___x_4951_ = lean_box(0);
v___x_4952_ = lean_nat_dec_le(v___x_4949_, v___x_4949_);
if (v___x_4952_ == 0)
{
if (v___x_4950_ == 0)
{
goto v___jp_4909_;
}
else
{
size_t v___x_4953_; size_t v___x_4954_; lean_object* v___x_4955_; 
v___x_4953_ = ((size_t)0ULL);
v___x_4954_ = lean_usize_of_nat(v___x_4949_);
v___x_4955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4730_, v_infos_4755_, v___x_4953_, v___x_4954_, v___x_4951_, v___y_4732_);
v___y_4936_ = v___x_4955_;
goto v___jp_4935_;
}
}
else
{
size_t v___x_4956_; size_t v___x_4957_; lean_object* v___x_4958_; 
v___x_4956_ = ((size_t)0ULL);
v___x_4957_ = lean_usize_of_nat(v___x_4949_);
v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4730_, v_infos_4755_, v___x_4956_, v___x_4957_, v___x_4951_, v___y_4732_);
v___y_4936_ = v___x_4958_;
goto v___jp_4935_;
}
}
}
v___jp_4734_:
{
if (v___y_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
return v___x_4737_;
}
else
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4738_ = lean_box(0);
v___x_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4738_);
return v___x_4739_;
}
}
v___jp_4740_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4745_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_4746_ = lean_string_append(v___y_4744_, v___x_4745_);
v___x_4747_ = lean_uint32_to_nat(v___y_4741_);
v___x_4748_ = l_Nat_reprFast(v___x_4747_);
v___x_4749_ = lean_string_append(v___x_4746_, v___x_4748_);
lean_dec_ref(v___x_4748_);
v___x_4750_ = 3;
v___x_4751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set_uint8(v___x_4751_, sizeof(void*)*1, v___x_4750_);
lean_inc_ref(v___y_4743_);
v___x_4752_ = lean_apply_2(v___y_4743_, v___x_4751_, lean_box(0));
v___y_4735_ = v___y_4742_;
goto v___jp_4734_;
}
v___jp_4757_:
{
uint32_t v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = 0;
v___x_4762_ = lean_uint32_dec_eq(v___y_4758_, v___x_4761_);
if (v___x_4762_ == 0)
{
lean_object* v_s_4763_; 
v_s_4763_ = lean_ctor_get(v_scope_4754_, 0);
lean_inc_ref(v_s_4763_);
lean_dec_ref(v_scope_4754_);
v___y_4741_ = v___y_4758_;
v___y_4742_ = v___y_4759_;
v___y_4743_ = v___y_4760_;
v___y_4744_ = v_s_4763_;
goto v___jp_4740_;
}
else
{
lean_dec_ref(v_scope_4754_);
v___y_4735_ = v___y_4759_;
goto v___jp_4734_;
}
}
v___jp_4764_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4772_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_4773_ = lean_string_append(v___y_4771_, v___x_4772_);
lean_inc(v___y_4765_);
lean_inc(v___y_4768_);
lean_inc_ref(v___y_4770_);
v___x_4774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4774_, 0, v___y_4770_);
lean_ctor_set(v___x_4774_, 1, v___y_4768_);
lean_ctor_set(v___x_4774_, 2, v___y_4765_);
v___x_4775_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_4774_, v___y_4765_);
lean_dec_ref_known(v___x_4774_, 3);
v___x_4776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4776_, 0, v___y_4770_);
lean_ctor_set(v___x_4776_, 1, v___y_4768_);
lean_ctor_set(v___x_4776_, 2, v___x_4775_);
v___x_4777_ = l_String_Slice_toString(v___x_4776_);
lean_dec_ref_known(v___x_4776_, 3);
v___x_4778_ = lean_string_append(v___x_4773_, v___x_4777_);
lean_dec_ref(v___x_4777_);
v___x_4779_ = 2;
v___x_4780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4780_, 0, v___x_4778_);
lean_ctor_set_uint8(v___x_4780_, sizeof(void*)*1, v___x_4779_);
lean_inc_ref(v___y_4767_);
v___x_4781_ = lean_apply_2(v___y_4767_, v___x_4780_, lean_box(0));
v___y_4758_ = v___y_4766_;
v___y_4759_ = v___y_4769_;
v___y_4760_ = v___y_4767_;
goto v___jp_4757_;
}
v___jp_4782_:
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = lean_string_utf8_byte_size(v___y_4786_);
v___x_4789_ = lean_nat_dec_eq(v___x_4788_, v___y_4783_);
if (v___x_4789_ == 0)
{
lean_object* v_s_4790_; 
v_s_4790_ = lean_ctor_get(v_scope_4754_, 0);
lean_inc_ref(v_s_4790_);
v___y_4765_ = v___x_4788_;
v___y_4766_ = v___y_4784_;
v___y_4767_ = v___y_4787_;
v___y_4768_ = v___y_4783_;
v___y_4769_ = v___y_4785_;
v___y_4770_ = v___y_4786_;
v___y_4771_ = v_s_4790_;
goto v___jp_4764_;
}
else
{
lean_dec_ref(v___y_4786_);
lean_dec(v___y_4783_);
v___y_4758_ = v___y_4784_;
v___y_4759_ = v___y_4785_;
v___y_4760_ = v___y_4787_;
goto v___jp_4757_;
}
}
v___jp_4791_:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4798_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_4799_ = lean_string_append(v___y_4797_, v___x_4798_);
v___x_4800_ = lean_string_append(v___x_4799_, v___y_4796_);
v___x_4801_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_4802_ = lean_string_append(v___x_4800_, v___x_4801_);
v___x_4803_ = 3;
v___x_4804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4804_, 0, v___x_4802_);
lean_ctor_set_uint8(v___x_4804_, sizeof(void*)*1, v___x_4803_);
lean_inc_ref(v___y_4732_);
v___x_4805_ = lean_apply_2(v___y_4732_, v___x_4804_, lean_box(0));
v___y_4783_ = v___y_4793_;
v___y_4784_ = v___y_4792_;
v___y_4785_ = v___y_4794_;
v___y_4786_ = v___y_4795_;
v___y_4787_ = v___y_4732_;
goto v___jp_4782_;
}
v___jp_4806_:
{
lean_object* v_s_4812_; 
v_s_4812_ = lean_ctor_get(v_scope_4754_, 0);
lean_inc_ref(v_s_4812_);
v___y_4792_ = v___y_4808_;
v___y_4793_ = v___y_4807_;
v___y_4794_ = v___y_4809_;
v___y_4795_ = v___y_4810_;
v___y_4796_ = v___y_4811_;
v___y_4797_ = v_s_4812_;
goto v___jp_4791_;
}
v___jp_4813_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; uint8_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4815_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_4816_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_4817_ = lean_box(0);
v___x_4818_ = lean_unsigned_to_nat(0u);
v___x_4819_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_4820_ = 1;
v___x_4821_ = 0;
v___x_4822_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4822_, 0, v___x_4815_);
lean_ctor_set(v___x_4822_, 1, v___x_4816_);
lean_ctor_set(v___x_4822_, 2, v_a_4814_);
lean_ctor_set(v___x_4822_, 3, v___x_4817_);
lean_ctor_set(v___x_4822_, 4, v___x_4819_);
lean_ctor_set_uint8(v___x_4822_, sizeof(void*)*5, v___x_4820_);
lean_ctor_set_uint8(v___x_4822_, sizeof(void*)*5 + 1, v___x_4821_);
v___x_4823_ = lean_io_process_spawn(v___x_4822_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v_stdout_4825_; lean_object* v_stderr_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref_known(v___x_4823_, 1);
v_stdout_4825_ = lean_ctor_get(v_a_4824_, 1);
lean_inc_n(v_stdout_4825_, 2);
v_stderr_4826_ = lean_ctor_get(v_a_4824_, 2);
v___x_4827_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_4828_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4729_, v_stderr_4826_, v_stdout_4825_, v___x_4827_, v___y_4732_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
v___x_4830_ = lean_io_process_child_wait(v___x_4815_, v_a_4824_);
lean_dec(v_a_4824_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
v___x_4832_ = l_IO_FS_Handle_readToEnd(v_stdout_4825_);
lean_dec(v_stdout_4825_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; uint8_t v_didError_4834_; lean_object* v_numSuccesses_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_a_4833_);
lean_dec_ref_known(v___x_4832_, 1);
v_didError_4834_ = lean_ctor_get_uint8(v_a_4829_, sizeof(void*)*1);
v_numSuccesses_4835_ = lean_ctor_get(v_a_4829_, 0);
lean_inc(v_numSuccesses_4835_);
lean_dec(v_a_4829_);
v___x_4836_ = lean_array_get_size(v_infos_4755_);
lean_dec_ref(v_infos_4755_);
v___x_4837_ = lean_nat_dec_lt(v_numSuccesses_4835_, v___x_4836_);
lean_dec(v_numSuccesses_4835_);
if (v___x_4837_ == 0)
{
uint32_t v___x_4838_; 
v___x_4838_ = lean_unbox_uint32(v_a_4831_);
lean_dec(v_a_4831_);
v___y_4783_ = v___x_4818_;
v___y_4784_ = v___x_4838_;
v___y_4785_ = v_didError_4834_;
v___y_4786_ = v_a_4833_;
v___y_4787_ = v___y_4732_;
goto v___jp_4782_;
}
else
{
if (v_kind_4753_ == 0)
{
lean_object* v___x_4839_; uint32_t v___x_4840_; 
v___x_4839_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_4840_ = lean_unbox_uint32(v_a_4831_);
lean_dec(v_a_4831_);
v___y_4807_ = v___x_4818_;
v___y_4808_ = v___x_4840_;
v___y_4809_ = v_didError_4834_;
v___y_4810_ = v_a_4833_;
v___y_4811_ = v___x_4839_;
goto v___jp_4806_;
}
else
{
lean_object* v___x_4841_; uint32_t v___x_4842_; 
v___x_4841_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_4842_ = lean_unbox_uint32(v_a_4831_);
lean_dec(v_a_4831_);
v___y_4807_ = v___x_4818_;
v___y_4808_ = v___x_4842_;
v___y_4809_ = v_didError_4834_;
v___y_4810_ = v_a_4833_;
v___y_4811_ = v___x_4841_;
goto v___jp_4806_;
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4855_; 
lean_dec(v_a_4831_);
lean_dec(v_a_4829_);
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
v_a_4843_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4845_ = v___x_4832_;
v_isShared_4846_ = v_isSharedCheck_4855_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4832_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4855_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
v___x_4847_ = lean_io_error_to_string(v_a_4843_);
v___x_4848_ = 3;
v___x_4849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4849_, 0, v___x_4847_);
lean_ctor_set_uint8(v___x_4849_, sizeof(void*)*1, v___x_4848_);
lean_inc_ref(v___y_4732_);
v___x_4850_ = lean_apply_2(v___y_4732_, v___x_4849_, lean_box(0));
v___x_4851_ = lean_box(0);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4851_);
v___x_4853_ = v___x_4845_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4868_; 
lean_dec(v_a_4829_);
lean_dec(v_stdout_4825_);
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
v_a_4856_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4858_ = v___x_4830_;
v_isShared_4859_ = v_isSharedCheck_4868_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4830_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4868_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; uint8_t v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4860_ = lean_io_error_to_string(v_a_4856_);
v___x_4861_ = 3;
v___x_4862_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4862_, 0, v___x_4860_);
lean_ctor_set_uint8(v___x_4862_, sizeof(void*)*1, v___x_4861_);
lean_inc_ref(v___y_4732_);
v___x_4863_ = lean_apply_2(v___y_4732_, v___x_4862_, lean_box(0));
v___x_4864_ = lean_box(0);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4864_);
v___x_4866_ = v___x_4858_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v_stdout_4825_);
lean_dec(v_a_4824_);
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
v_a_4869_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4828_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4828_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4889_; 
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
lean_dec_ref(v_cfg_4729_);
v_a_4877_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4879_ = v___x_4823_;
v_isShared_4880_ = v_isSharedCheck_4889_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4823_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4889_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4881_; uint8_t v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4881_ = lean_io_error_to_string(v_a_4877_);
v___x_4882_ = 3;
v___x_4883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4883_, 0, v___x_4881_);
lean_ctor_set_uint8(v___x_4883_, sizeof(void*)*1, v___x_4882_);
lean_inc_ref(v___y_4732_);
v___x_4884_ = lean_apply_2(v___y_4732_, v___x_4883_, lean_box(0));
v___x_4885_ = lean_box(0);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v___x_4885_);
v___x_4887_ = v___x_4879_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
v___jp_4890_:
{
lean_object* v___x_4891_; 
v___x_4891_ = lean_io_prim_handle_flush(v_h_4730_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec_ref_known(v___x_4891_, 1);
v___x_4892_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_4893_ = lean_array_push(v___x_4892_, v_path_4731_);
v_a_4814_ = v___x_4893_;
goto v___jp_4813_;
}
else
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4906_; 
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
lean_dec_ref(v_path_4731_);
lean_dec_ref(v_cfg_4729_);
v_a_4894_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4896_ = v___x_4891_;
v_isShared_4897_ = v_isSharedCheck_4906_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4891_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4906_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4898_; uint8_t v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4898_ = lean_io_error_to_string(v_a_4894_);
v___x_4899_ = 3;
v___x_4900_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4900_, 0, v___x_4898_);
lean_ctor_set_uint8(v___x_4900_, sizeof(void*)*1, v___x_4899_);
lean_inc_ref(v___y_4732_);
v___x_4901_ = lean_apply_2(v___y_4732_, v___x_4900_, lean_box(0));
v___x_4902_ = lean_box(0);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4902_);
v___x_4904_ = v___x_4896_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
v___jp_4907_:
{
if (lean_obj_tag(v___y_4908_) == 0)
{
lean_dec_ref_known(v___y_4908_, 1);
goto v___jp_4890_;
}
else
{
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
lean_dec_ref(v_path_4731_);
lean_dec_ref(v_cfg_4729_);
return v___y_4908_;
}
}
v___jp_4909_:
{
lean_object* v___x_4910_; 
v___x_4910_ = lean_io_prim_handle_flush(v_h_4730_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
lean_dec_ref_known(v___x_4910_, 1);
v___x_4911_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4912_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4913_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4914_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4915_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_4756_);
v___x_4916_ = lean_array_push(v___x_4915_, v_key_4756_);
v___x_4917_ = lean_array_push(v___x_4916_, v___x_4911_);
v___x_4918_ = lean_array_push(v___x_4917_, v___x_4912_);
v___x_4919_ = lean_array_push(v___x_4918_, v___x_4913_);
v___x_4920_ = lean_array_push(v___x_4919_, v___x_4914_);
v___x_4921_ = lean_array_push(v___x_4920_, v_path_4731_);
v_a_4814_ = v___x_4921_;
goto v___jp_4813_;
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4934_; 
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
lean_dec_ref(v_path_4731_);
lean_dec_ref(v_cfg_4729_);
v_a_4922_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4924_ = v___x_4910_;
v_isShared_4925_ = v_isSharedCheck_4934_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4910_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4934_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4926_; uint8_t v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4932_; 
v___x_4926_ = lean_io_error_to_string(v_a_4922_);
v___x_4927_ = 3;
v___x_4928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4928_, 0, v___x_4926_);
lean_ctor_set_uint8(v___x_4928_, sizeof(void*)*1, v___x_4927_);
lean_inc_ref(v___y_4732_);
v___x_4929_ = lean_apply_2(v___y_4732_, v___x_4928_, lean_box(0));
v___x_4930_ = lean_box(0);
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 0, v___x_4930_);
v___x_4932_ = v___x_4924_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4930_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
v___jp_4935_:
{
if (lean_obj_tag(v___y_4936_) == 0)
{
lean_dec_ref_known(v___y_4936_, 1);
goto v___jp_4909_;
}
else
{
lean_dec_ref(v_infos_4755_);
lean_dec_ref(v_scope_4754_);
lean_dec_ref(v_path_4731_);
lean_dec_ref(v_cfg_4729_);
return v___y_4936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object* v_cfg_4959_, lean_object* v_h_4960_, lean_object* v_path_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(v_cfg_4959_, v_h_4960_, v_path_4961_, v___y_4962_);
lean_dec_ref(v___y_4962_);
lean_dec(v_h_4960_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object* v_cfg_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v___f_4968_; lean_object* v___x_4969_; 
v___f_4968_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4968_, 0, v_cfg_4965_);
v___x_4969_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_4968_, v_a_4966_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object* v_cfg_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(v_cfg_4970_, v_a_4971_);
lean_dec_ref(v_a_4971_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(lean_object* v_service_4975_, lean_object* v_scope_4976_){
_start:
{
lean_object* v___y_4978_; 
if (lean_obj_tag(v_scope_4976_) == 0)
{
lean_object* v_s_4981_; lean_object* v_apiEndpoint_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v_s_4981_ = lean_ctor_get(v_scope_4976_, 0);
lean_inc_ref(v_s_4981_);
lean_dec_ref_known(v_scope_4976_, 1);
v_apiEndpoint_4982_ = lean_ctor_get(v_service_4975_, 4);
lean_inc_ref(v_apiEndpoint_4982_);
lean_dec_ref(v_service_4975_);
v___x_4983_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_4984_ = lean_string_append(v_apiEndpoint_4982_, v___x_4983_);
v___x_4985_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4984_, v_s_4981_);
v___y_4978_ = v___x_4985_;
goto v___jp_4977_;
}
else
{
lean_object* v_s_4986_; lean_object* v_apiEndpoint_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_s_4986_ = lean_ctor_get(v_scope_4976_, 0);
lean_inc_ref(v_s_4986_);
lean_dec_ref_known(v_scope_4976_, 1);
v_apiEndpoint_4987_ = lean_ctor_get(v_service_4975_, 4);
lean_inc_ref(v_apiEndpoint_4987_);
lean_dec_ref(v_service_4975_);
v___x_4988_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_4989_ = lean_string_append(v_apiEndpoint_4987_, v___x_4988_);
v___x_4990_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4989_, v_s_4986_);
v___y_4978_ = v___x_4990_;
goto v___jp_4977_;
}
v___jp_4977_:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0));
v___x_4980_ = lean_string_append(v___y_4978_, v___x_4979_);
return v___x_4980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(size_t v_sz_4991_, size_t v_i_4992_, lean_object* v_bs_4993_){
_start:
{
uint8_t v___x_4994_; 
v___x_4994_ = lean_usize_dec_lt(v_i_4992_, v_sz_4991_);
if (v___x_4994_ == 0)
{
return v_bs_4993_;
}
else
{
lean_object* v_v_4995_; uint64_t v_hash_4996_; lean_object* v___x_4997_; lean_object* v_bs_x27_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; size_t v___x_5001_; size_t v___x_5002_; lean_object* v___x_5003_; 
v_v_4995_ = lean_array_uget_borrowed(v_bs_4993_, v_i_4992_);
v_hash_4996_ = lean_ctor_get_uint64(v_v_4995_, sizeof(void*)*3);
v___x_4997_ = lean_unsigned_to_nat(0u);
v_bs_x27_4998_ = lean_array_uset(v_bs_4993_, v_i_4992_, v___x_4997_);
v___x_4999_ = l_Lake_lowerHexUInt64(v_hash_4996_);
v___x_5000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
v___x_5001_ = ((size_t)1ULL);
v___x_5002_ = lean_usize_add(v_i_4992_, v___x_5001_);
v___x_5003_ = lean_array_uset(v_bs_x27_4998_, v_i_4992_, v___x_5000_);
v_i_4992_ = v___x_5002_;
v_bs_4993_ = v___x_5003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0___boxed(lean_object* v_sz_5005_, lean_object* v_i_5006_, lean_object* v_bs_5007_){
_start:
{
size_t v_sz_boxed_5008_; size_t v_i_boxed_5009_; lean_object* v_res_5010_; 
v_sz_boxed_5008_ = lean_unbox_usize(v_sz_5005_);
lean_dec(v_sz_5005_);
v_i_boxed_5009_ = lean_unbox_usize(v_i_5006_);
lean_dec(v_i_5006_);
v_res_5010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_boxed_5008_, v_i_boxed_5009_, v_bs_5007_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(lean_object* v_a_5011_, lean_object* v_n_5012_, lean_object* v_j_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_zero_5015_; uint8_t v_isZero_5016_; 
v_zero_5015_ = lean_unsigned_to_nat(0u);
v_isZero_5016_ = lean_nat_dec_eq(v_j_5013_, v_zero_5015_);
if (v_isZero_5016_ == 1)
{
lean_dec(v_j_5013_);
return v_a_5014_;
}
else
{
lean_object* v___x_5017_; lean_object* v___x_5018_; uint64_t v_hash_5019_; lean_object* v_path_5020_; lean_object* v_extraPaths_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5033_; 
v___x_5017_ = lean_nat_sub(v_n_5012_, v_j_5013_);
v___x_5018_ = lean_array_fget(v_a_5014_, v___x_5017_);
v_hash_5019_ = lean_ctor_get_uint64(v___x_5018_, sizeof(void*)*3);
v_path_5020_ = lean_ctor_get(v___x_5018_, 1);
v_extraPaths_5021_ = lean_ctor_get(v___x_5018_, 2);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5033_ == 0)
{
lean_object* v_unused_5034_; 
v_unused_5034_ = lean_ctor_get(v___x_5018_, 0);
lean_dec(v_unused_5034_);
v___x_5023_ = v___x_5018_;
v_isShared_5024_ = v_isSharedCheck_5033_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_extraPaths_5021_);
lean_inc(v_path_5020_);
lean_dec(v___x_5018_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5033_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v_one_5025_; lean_object* v_n_5026_; lean_object* v___x_5027_; lean_object* v___x_5029_; 
v_one_5025_ = lean_unsigned_to_nat(1u);
v_n_5026_ = lean_nat_sub(v_j_5013_, v_one_5025_);
lean_dec(v_j_5013_);
v___x_5027_ = lean_array_fget_borrowed(v_a_5011_, v___x_5017_);
lean_inc(v___x_5027_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 0, v___x_5027_);
v___x_5029_ = v___x_5023_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5027_);
lean_ctor_set(v_reuseFailAlloc_5032_, 1, v_path_5020_);
lean_ctor_set(v_reuseFailAlloc_5032_, 2, v_extraPaths_5021_);
lean_ctor_set_uint64(v_reuseFailAlloc_5032_, sizeof(void*)*3, v_hash_5019_);
v___x_5029_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
lean_object* v___x_5030_; 
v___x_5030_ = lean_array_fset(v_a_5014_, v___x_5017_, v___x_5029_);
lean_dec(v___x_5017_);
v_j_5013_ = v_n_5026_;
v_a_5014_ = v___x_5030_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg___boxed(lean_object* v_a_5035_, lean_object* v_n_5036_, lean_object* v_j_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5035_, v_n_5036_, v_j_5037_, v_a_5038_);
lean_dec(v_n_5036_);
lean_dec_ref(v_a_5035_);
return v_res_5039_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5040_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5041_ = lean_unsigned_to_nat(2u);
v___x_5042_ = lean_mk_empty_array_with_capacity(v___x_5041_);
v___x_5043_ = lean_array_push(v___x_5042_, v___x_5040_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(lean_object* v_as_5044_, size_t v_i_5045_, size_t v_stop_5046_, lean_object* v_b_5047_){
_start:
{
uint8_t v___x_5048_; 
v___x_5048_ = lean_usize_dec_eq(v_i_5045_, v_stop_5046_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; size_t v___x_5053_; size_t v___x_5054_; 
v___x_5049_ = lean_array_uget_borrowed(v_as_5044_, v_i_5045_);
v___x_5050_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0);
lean_inc(v___x_5049_);
v___x_5051_ = lean_array_push(v___x_5050_, v___x_5049_);
v___x_5052_ = l_Array_append___redArg(v_b_5047_, v___x_5051_);
lean_dec_ref(v___x_5051_);
v___x_5053_ = ((size_t)1ULL);
v___x_5054_ = lean_usize_add(v_i_5045_, v___x_5053_);
v_i_5045_ = v___x_5054_;
v_b_5047_ = v___x_5052_;
goto _start;
}
else
{
return v_b_5047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___boxed(lean_object* v_as_5056_, lean_object* v_i_5057_, lean_object* v_stop_5058_, lean_object* v_b_5059_){
_start:
{
size_t v_i_boxed_5060_; size_t v_stop_boxed_5061_; lean_object* v_res_5062_; 
v_i_boxed_5060_ = lean_unbox_usize(v_i_5057_);
lean_dec(v_i_5057_);
v_stop_boxed_5061_ = lean_unbox_usize(v_stop_5058_);
lean_dec(v_stop_5058_);
v_res_5062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v_as_5056_, v_i_boxed_5060_, v_stop_boxed_5061_, v_b_5059_);
lean_dec_ref(v_as_5056_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object* v_x_5065_){
_start:
{
if (lean_obj_tag(v_x_5065_) == 0)
{
lean_object* v___x_5066_; 
v___x_5066_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0));
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_x_5065_);
v___x_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
return v___x_5068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t v_sz_5069_, size_t v_i_5070_, lean_object* v_bs_5071_){
_start:
{
uint8_t v___x_5072_; 
v___x_5072_ = lean_usize_dec_lt(v_i_5070_, v_sz_5069_);
if (v___x_5072_ == 0)
{
lean_object* v___x_5073_; 
v___x_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5073_, 0, v_bs_5071_);
return v___x_5073_;
}
else
{
lean_object* v_v_5074_; lean_object* v___x_5075_; 
v_v_5074_ = lean_array_uget_borrowed(v_bs_5071_, v_i_5070_);
lean_inc(v_v_5074_);
v___x_5075_ = l_Lean_Json_getStr_x3f(v_v_5074_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec_ref(v_bs_5071_);
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5075_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5075_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v___x_5085_; lean_object* v_bs_x27_5086_; size_t v___x_5087_; size_t v___x_5088_; lean_object* v___x_5089_; 
v_a_5084_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5084_);
lean_dec_ref_known(v___x_5075_, 1);
v___x_5085_ = lean_unsigned_to_nat(0u);
v_bs_x27_5086_ = lean_array_uset(v_bs_5071_, v_i_5070_, v___x_5085_);
v___x_5087_ = ((size_t)1ULL);
v___x_5088_ = lean_usize_add(v_i_5070_, v___x_5087_);
v___x_5089_ = lean_array_uset(v_bs_x27_5086_, v_i_5070_, v_a_5084_);
v_i_5070_ = v___x_5088_;
v_bs_5071_ = v___x_5089_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_5091_, lean_object* v_i_5092_, lean_object* v_bs_5093_){
_start:
{
size_t v_sz_boxed_5094_; size_t v_i_boxed_5095_; lean_object* v_res_5096_; 
v_sz_boxed_5094_ = lean_unbox_usize(v_sz_5091_);
lean_dec(v_sz_5091_);
v_i_boxed_5095_ = lean_unbox_usize(v_i_5092_);
lean_dec(v_i_5092_);
v_res_5096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_boxed_5094_, v_i_boxed_5095_, v_bs_5093_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object* v_x_5097_){
_start:
{
if (lean_obj_tag(v_x_5097_) == 4)
{
lean_object* v_elems_5098_; size_t v_sz_5099_; size_t v___x_5100_; lean_object* v___x_5101_; 
v_elems_5098_ = lean_ctor_get(v_x_5097_, 0);
lean_inc_ref(v_elems_5098_);
lean_dec_ref_known(v_x_5097_, 1);
v_sz_5099_ = lean_array_size(v_elems_5098_);
v___x_5100_ = ((size_t)0ULL);
v___x_5101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_5099_, v___x_5100_, v_elems_5098_);
return v___x_5101_;
}
else
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5102_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_5103_ = lean_unsigned_to_nat(80u);
v___x_5104_ = l_Lean_Json_pretty(v_x_5097_, v___x_5103_);
v___x_5105_ = lean_string_append(v___x_5102_, v___x_5104_);
lean_dec_ref(v___x_5104_);
v___x_5106_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
v___x_5107_ = lean_string_append(v___x_5105_, v___x_5106_);
v___x_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
return v___x_5108_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object* v_x_5111_){
_start:
{
if (lean_obj_tag(v_x_5111_) == 0)
{
lean_object* v___x_5112_; 
v___x_5112_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0));
return v___x_5112_;
}
else
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_Json_getObj_x3f(v_x_5111_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5130_; 
v_a_5122_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5124_ = v___x_5113_;
v_isShared_5125_ = v_isSharedCheck_5130_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5113_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5130_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5126_; lean_object* v___x_5128_; 
v___x_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5126_, 0, v_a_5122_);
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 0, v___x_5126_);
v___x_5128_ = v___x_5124_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(lean_object* v_val_5143_){
_start:
{
lean_object* v_a_5145_; lean_object* v___x_5189_; 
lean_inc(v_val_5143_);
v___x_5189_ = l_Lean_Json_getObj_x3f(v_val_5143_);
if (lean_obj_tag(v___x_5189_) == 1)
{
lean_object* v_a_5190_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref_known(v___x_5189_, 1);
v___x_5197_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0));
v___x_5198_ = l_Lake_JsonObject_getJson_x3f(v_a_5190_, v___x_5197_);
if (lean_obj_tag(v___x_5198_) == 0)
{
goto v___jp_5191_;
}
else
{
lean_object* v_val_5199_; lean_object* v___x_5200_; 
v_val_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_val_5199_);
lean_dec_ref_known(v___x_5198_, 1);
v___x_5200_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(v_val_5199_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5210_; 
lean_dec(v_a_5190_);
lean_dec(v_val_5143_);
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5203_ = v___x_5200_;
v_isShared_5204_ = v_isSharedCheck_5210_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5200_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5210_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5208_; 
v___x_5205_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1));
v___x_5206_ = lean_string_append(v___x_5205_, v_a_5201_);
lean_dec(v_a_5201_);
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 0, v___x_5206_);
v___x_5208_ = v___x_5203_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5206_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
else
{
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_dec(v_a_5190_);
lean_dec(v_val_5143_);
v_a_5211_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5200_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5200_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
lean_ctor_set_tag(v___x_5213_, 0);
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
else
{
lean_object* v_a_5219_; 
v_a_5219_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5219_);
lean_dec_ref_known(v___x_5200_, 1);
if (lean_obj_tag(v_a_5219_) == 1)
{
lean_object* v_val_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec(v_a_5190_);
lean_dec(v_val_5143_);
v_val_5220_ = lean_ctor_get(v_a_5219_, 0);
lean_inc(v_val_5220_);
lean_dec_ref_known(v_a_5219_, 1);
v___x_5221_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2));
v___x_5222_ = l_Lake_JsonObject_getJson_x3f(v_val_5220_, v___x_5221_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_object* v___x_5223_; 
lean_dec(v_val_5220_);
v___x_5223_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4));
return v___x_5223_;
}
else
{
lean_object* v_val_5224_; lean_object* v___x_5225_; 
v_val_5224_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_val_5224_);
lean_dec_ref_known(v___x_5222_, 1);
v___x_5225_ = l_Lean_Json_getNat_x3f(v_val_5224_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5235_; 
lean_dec(v_val_5220_);
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5235_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5225_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5235_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5233_; 
v___x_5230_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5));
v___x_5231_ = lean_string_append(v___x_5230_, v_a_5226_);
lean_dec(v_a_5226_);
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v___x_5231_);
v___x_5233_ = v___x_5228_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
else
{
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec(v_val_5220_);
v_a_5236_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5225_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5225_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
lean_ctor_set_tag(v___x_5238_, 0);
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v_a_5244_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5244_);
lean_dec_ref_known(v___x_5225_, 1);
v___x_5245_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6));
v___x_5246_ = l_Lake_JsonObject_getJson_x3f(v_val_5220_, v___x_5245_);
lean_dec(v_val_5220_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v___x_5247_; 
lean_dec(v_a_5244_);
v___x_5247_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8));
return v___x_5247_;
}
else
{
lean_object* v_val_5248_; lean_object* v___x_5249_; 
v_val_5248_ = lean_ctor_get(v___x_5246_, 0);
lean_inc(v_val_5248_);
lean_dec_ref_known(v___x_5246_, 1);
v___x_5249_ = l_Lean_Json_getStr_x3f(v_val_5248_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5259_; 
lean_dec(v_a_5244_);
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5252_ = v___x_5249_;
v_isShared_5253_ = v_isSharedCheck_5259_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5249_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5259_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5257_; 
v___x_5254_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9));
v___x_5255_ = lean_string_append(v___x_5254_, v_a_5250_);
lean_dec(v_a_5250_);
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 0, v___x_5255_);
v___x_5257_ = v___x_5252_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5255_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
else
{
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_dec(v_a_5244_);
v_a_5260_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5249_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5249_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
lean_ctor_set_tag(v___x_5262_, 0);
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
else
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5276_; 
v_a_5268_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5270_ = v___x_5249_;
v_isShared_5271_ = v_isSharedCheck_5276_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v___x_5249_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5276_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5272_; lean_object* v___x_5274_; 
v___x_5272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5272_, 0, v_a_5244_);
lean_ctor_set(v___x_5272_, 1, v_a_5268_);
if (v_isShared_5271_ == 0)
{
lean_ctor_set(v___x_5270_, 0, v___x_5272_);
v___x_5274_ = v___x_5270_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5272_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
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
lean_dec(v_a_5219_);
goto v___jp_5191_;
}
}
}
}
v___jp_5191_:
{
lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5192_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_5193_ = l_Lake_JsonObject_getJson_x3f(v_a_5190_, v___x_5192_);
lean_dec(v_a_5190_);
if (lean_obj_tag(v___x_5193_) == 0)
{
v_a_5145_ = v___x_5193_;
goto v___jp_5144_;
}
else
{
lean_object* v_val_5194_; lean_object* v___x_5195_; lean_object* v_a_5196_; 
v_val_5194_ = lean_ctor_get(v___x_5193_, 0);
lean_inc(v_val_5194_);
lean_dec_ref_known(v___x_5193_, 1);
v___x_5195_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(v_val_5194_);
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref(v___x_5195_);
v_a_5145_ = v_a_5196_;
goto v___jp_5144_;
}
}
}
else
{
lean_object* v___x_5277_; 
lean_dec_ref(v___x_5189_);
v___x_5277_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5143_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5285_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5285_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5285_ == 0)
{
v___x_5280_ = v___x_5277_;
v_isShared_5281_ = v_isSharedCheck_5285_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_a_5278_);
lean_dec(v___x_5277_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5285_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5283_; 
if (v_isShared_5281_ == 0)
{
v___x_5283_ = v___x_5280_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_a_5278_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5294_; 
v_a_5286_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5288_ = v___x_5277_;
v_isShared_5289_ = v_isSharedCheck_5294_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5277_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5294_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5290_; lean_object* v___x_5292_; 
v___x_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5290_, 0, v_a_5286_);
if (v_isShared_5289_ == 0)
{
lean_ctor_set(v___x_5288_, 0, v___x_5290_);
v___x_5292_ = v___x_5288_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v___x_5290_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
v___jp_5144_:
{
if (lean_obj_tag(v_a_5145_) == 1)
{
lean_object* v_val_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5170_; 
lean_dec(v_val_5143_);
v_val_5146_ = lean_ctor_get(v_a_5145_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v_a_5145_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5148_ = v_a_5145_;
v_isShared_5149_ = v_isSharedCheck_5170_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_val_5146_);
lean_dec(v_a_5145_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5170_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5150_; 
v___x_5150_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5146_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_del_object(v___x_5148_);
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5150_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5150_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5169_; 
v_a_5159_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5161_ = v___x_5150_;
v_isShared_5162_ = v_isSharedCheck_5169_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5150_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5169_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5149_ == 0)
{
lean_ctor_set_tag(v___x_5148_, 0);
lean_ctor_set(v___x_5148_, 0, v_a_5159_);
v___x_5164_ = v___x_5148_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
lean_object* v___x_5166_; 
if (v_isShared_5162_ == 0)
{
lean_ctor_set(v___x_5161_, 0, v___x_5164_);
v___x_5166_ = v___x_5161_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
}
else
{
lean_object* v___x_5171_; 
lean_dec(v_a_5145_);
v___x_5171_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5143_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5171_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5171_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
else
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5188_; 
v_a_5180_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5182_ = v___x_5171_;
v_isShared_5183_ = v_isSharedCheck_5188_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_5171_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5188_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5184_; lean_object* v___x_5186_; 
v___x_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5184_, 0, v_a_5180_);
if (v_isShared_5183_ == 0)
{
lean_ctor_set(v___x_5182_, 0, v___x_5184_);
v___x_5186_ = v___x_5182_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5184_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
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
lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5313_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_5314_ = lean_unsigned_to_nat(12u);
v___x_5315_ = lean_mk_empty_array_with_capacity(v___x_5314_);
v___x_5316_ = lean_array_push(v___x_5315_, v___x_5313_);
return v___x_5316_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19(void){
_start:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; 
v___x_5317_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14));
v___x_5318_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18);
v___x_5319_ = lean_array_push(v___x_5318_, v___x_5317_);
return v___x_5319_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20(void){
_start:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5320_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_5321_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19);
v___x_5322_ = lean_array_push(v___x_5321_, v___x_5320_);
return v___x_5322_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21(void){
_start:
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5323_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15));
v___x_5324_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20);
v___x_5325_ = lean_array_push(v___x_5324_, v___x_5323_);
return v___x_5325_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5326_ = l_Lake_Reservoir_lakeHeaders;
v___x_5327_ = lean_array_get_size(v___x_5326_);
return v___x_5327_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23(void){
_start:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; uint8_t v___x_5330_; 
v___x_5328_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5329_ = lean_unsigned_to_nat(0u);
v___x_5330_ = lean_nat_dec_lt(v___x_5329_, v___x_5328_);
return v___x_5330_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24(void){
_start:
{
lean_object* v___x_5331_; uint8_t v___x_5332_; 
v___x_5331_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5332_ = lean_nat_dec_le(v___x_5331_, v___x_5331_);
return v___x_5332_;
}
}
static size_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25(void){
_start:
{
lean_object* v___x_5333_; size_t v___x_5334_; 
v___x_5333_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5334_ = lean_usize_of_nat(v___x_5333_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(lean_object* v_infos_5335_, lean_object* v_url_5336_, lean_object* v_h_5337_, lean_object* v_path_5338_, lean_object* v___y_5339_){
_start:
{
uint32_t v___y_5342_; lean_object* v___y_5343_; uint32_t v___y_5354_; lean_object* v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v_a_5358_; uint32_t v___y_5386_; lean_object* v___y_5387_; lean_object* v___y_5388_; uint8_t v___y_5389_; lean_object* v_msg_5390_; lean_object* v___y_5391_; uint32_t v___y_5405_; lean_object* v___y_5406_; lean_object* v___y_5407_; lean_object* v___y_5408_; uint8_t v___y_5409_; lean_object* v_msg_5410_; lean_object* v___y_5411_; uint32_t v___y_5422_; lean_object* v___y_5423_; lean_object* v___y_5424_; lean_object* v___y_5425_; uint8_t v___y_5426_; lean_object* v___y_5427_; lean_object* v_msg_5428_; lean_object* v___y_5429_; uint32_t v___y_5442_; lean_object* v___y_5443_; lean_object* v___y_5444_; lean_object* v___y_5445_; uint8_t v___y_5446_; size_t v_sz_5464_; size_t v___x_5465_; lean_object* v___x_5466_; lean_object* v_body_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v_sz_5464_ = lean_array_size(v_infos_5335_);
v___x_5465_ = ((size_t)0ULL);
lean_inc_ref(v_infos_5335_);
v___x_5466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_5464_, v___x_5465_, v_infos_5335_);
v_body_5467_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_5467_, 0, v___x_5466_);
v___x_5468_ = l_Lean_Json_compress(v_body_5467_);
v___x_5469_ = lean_io_prim_handle_put_str(v_h_5337_, v___x_5468_);
lean_dec_ref(v___x_5468_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v___x_5470_; 
lean_dec_ref_known(v___x_5469_, 1);
v___x_5470_ = lean_io_prim_handle_flush(v_h_5337_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v___y_5472_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; uint8_t v___x_5574_; 
lean_dec_ref_known(v___x_5470_, 1);
v___x_5555_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_5556_ = lean_string_append(v___x_5555_, v_path_5338_);
v___x_5557_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_5558_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_5559_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5560_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5561_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5562_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5563_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_5564_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_5565_ = lean_array_push(v___x_5564_, v___x_5556_);
v___x_5566_ = lean_array_push(v___x_5565_, v___x_5557_);
v___x_5567_ = lean_array_push(v___x_5566_, v___x_5558_);
v___x_5568_ = lean_array_push(v___x_5567_, v___x_5559_);
v___x_5569_ = lean_array_push(v___x_5568_, v___x_5560_);
v___x_5570_ = lean_array_push(v___x_5569_, v___x_5561_);
v___x_5571_ = lean_array_push(v___x_5570_, v___x_5562_);
v___x_5572_ = lean_array_push(v___x_5571_, v___x_5563_);
v___x_5573_ = l_Lake_Reservoir_lakeHeaders;
v___x_5574_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_5574_ == 0)
{
v___y_5472_ = v___x_5572_;
goto v___jp_5471_;
}
else
{
uint8_t v___x_5575_; 
v___x_5575_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
if (v___x_5575_ == 0)
{
if (v___x_5574_ == 0)
{
v___y_5472_ = v___x_5572_;
goto v___jp_5471_;
}
else
{
size_t v___x_5576_; lean_object* v___x_5577_; 
v___x_5576_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5573_, v___x_5465_, v___x_5576_, v___x_5572_);
v___y_5472_ = v___x_5577_;
goto v___jp_5471_;
}
}
else
{
size_t v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5573_, v___x_5465_, v___x_5578_, v___x_5572_);
v___y_5472_ = v___x_5579_;
goto v___jp_5471_;
}
}
v___jp_5471_:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; uint8_t v___x_5479_; uint8_t v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; uint8_t v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5473_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5474_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
lean_inc_ref(v_url_5336_);
v___x_5475_ = lean_array_push(v___y_5472_, v_url_5336_);
v___x_5476_ = lean_box(0);
v___x_5477_ = lean_unsigned_to_nat(0u);
v___x_5478_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5479_ = 1;
v___x_5480_ = 0;
v___x_5481_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5481_, 0, v___x_5473_);
lean_ctor_set(v___x_5481_, 1, v___x_5474_);
lean_ctor_set(v___x_5481_, 2, v___x_5475_);
lean_ctor_set(v___x_5481_, 3, v___x_5476_);
lean_ctor_set(v___x_5481_, 4, v___x_5478_);
lean_ctor_set_uint8(v___x_5481_, sizeof(void*)*5, v___x_5479_);
lean_ctor_set_uint8(v___x_5481_, sizeof(void*)*5 + 1, v___x_5480_);
lean_inc_ref(v___x_5481_);
v___x_5482_ = l_Lake_mkCmdLog(v___x_5481_);
v___x_5483_ = 0;
v___x_5484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5484_, 0, v___x_5482_);
lean_ctor_set_uint8(v___x_5484_, sizeof(void*)*1, v___x_5483_);
lean_inc_ref(v___y_5339_);
v___x_5485_ = lean_apply_2(v___y_5339_, v___x_5484_, lean_box(0));
v___x_5486_ = l_IO_Process_output(v___x_5481_, v___x_5476_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5541_; 
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5489_ = v___x_5486_;
v_isShared_5490_ = v_isSharedCheck_5541_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5486_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5541_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
uint32_t v_exitCode_5491_; lean_object* v_stdout_5492_; lean_object* v_stderr_5493_; lean_object* v___x_5494_; 
v_exitCode_5491_ = lean_ctor_get_uint32(v_a_5487_, sizeof(void*)*2);
v_stdout_5492_ = lean_ctor_get(v_a_5487_, 0);
lean_inc_ref_n(v_stdout_5492_, 2);
v_stderr_5493_ = lean_ctor_get(v_a_5487_, 1);
lean_inc_ref(v_stderr_5493_);
lean_dec(v_a_5487_);
v___x_5494_ = l_Lean_Json_parse(v_stdout_5492_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_dec_ref_known(v___x_5494_, 1);
lean_del_object(v___x_5489_);
lean_dec_ref(v_infos_5335_);
v___y_5442_ = v_exitCode_5491_;
v___y_5443_ = v___x_5477_;
v___y_5444_ = v_stdout_5492_;
v___y_5445_ = v_stderr_5493_;
v___y_5446_ = v___x_5483_;
goto v___jp_5441_;
}
else
{
lean_object* v_a_5495_; lean_object* v___x_5496_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref_known(v___x_5494_, 1);
v___x_5496_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_5495_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_dec_ref_known(v___x_5496_, 1);
lean_del_object(v___x_5489_);
lean_dec_ref(v_infos_5335_);
v___y_5442_ = v_exitCode_5491_;
v___y_5443_ = v___x_5477_;
v___y_5444_ = v_stdout_5492_;
v___y_5445_ = v_stderr_5493_;
v___y_5446_ = v___x_5483_;
goto v___jp_5441_;
}
else
{
lean_object* v_a_5497_; 
lean_dec_ref(v_stderr_5493_);
lean_dec_ref(v_stdout_5492_);
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
lean_inc(v_a_5497_);
lean_dec_ref_known(v___x_5496_, 1);
if (lean_obj_tag(v_a_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; uint8_t v___x_5501_; 
v_a_5498_ = lean_ctor_get(v_a_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref_known(v_a_5497_, 1);
v___x_5499_ = lean_array_get_size(v_infos_5335_);
v___x_5500_ = lean_array_get_size(v_a_5498_);
v___x_5501_ = lean_nat_dec_eq(v___x_5499_, v___x_5500_);
if (v___x_5501_ == 0)
{
lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; uint8_t v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5517_; 
lean_dec(v_a_5498_);
lean_dec_ref(v_infos_5335_);
v___x_5502_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5503_ = lean_string_append(v___x_5502_, v_url_5336_);
lean_dec_ref(v_url_5336_);
v___x_5504_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_5505_ = lean_string_append(v___x_5503_, v___x_5504_);
v___x_5506_ = l_Nat_reprFast(v___x_5499_);
v___x_5507_ = lean_string_append(v___x_5505_, v___x_5506_);
lean_dec_ref(v___x_5506_);
v___x_5508_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_5509_ = lean_string_append(v___x_5507_, v___x_5508_);
v___x_5510_ = l_Nat_reprFast(v___x_5500_);
v___x_5511_ = lean_string_append(v___x_5509_, v___x_5510_);
lean_dec_ref(v___x_5510_);
v___x_5512_ = 3;
v___x_5513_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5513_, 0, v___x_5511_);
lean_ctor_set_uint8(v___x_5513_, sizeof(void*)*1, v___x_5512_);
lean_inc_ref(v___y_5339_);
v___x_5514_ = lean_apply_2(v___y_5339_, v___x_5513_, lean_box(0));
v___x_5515_ = lean_box(0);
if (v_isShared_5490_ == 0)
{
lean_ctor_set_tag(v___x_5489_, 1);
lean_ctor_set(v___x_5489_, 0, v___x_5515_);
v___x_5517_ = v___x_5489_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5515_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
else
{
lean_object* v___x_5519_; lean_object* v___x_5521_; 
lean_dec_ref(v_url_5336_);
v___x_5519_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5498_, v___x_5499_, v___x_5499_, v_infos_5335_);
lean_dec(v_a_5498_);
if (v_isShared_5490_ == 0)
{
lean_ctor_set(v___x_5489_, 0, v___x_5519_);
v___x_5521_ = v___x_5489_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5519_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
else
{
lean_object* v_status_5523_; lean_object* v_message_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; uint8_t v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5539_; 
lean_dec_ref(v_infos_5335_);
v_status_5523_ = lean_ctor_get(v_a_5497_, 0);
lean_inc(v_status_5523_);
v_message_5524_ = lean_ctor_get(v_a_5497_, 1);
lean_inc_ref(v_message_5524_);
lean_dec_ref_known(v_a_5497_, 2);
v___x_5525_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5526_ = l_Nat_reprFast(v_status_5523_);
v___x_5527_ = lean_string_append(v___x_5525_, v___x_5526_);
lean_dec_ref(v___x_5526_);
v___x_5528_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_5529_ = lean_string_append(v___x_5527_, v___x_5528_);
v___x_5530_ = lean_string_append(v___x_5529_, v_url_5336_);
lean_dec_ref(v_url_5336_);
v___x_5531_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_5532_ = lean_string_append(v___x_5530_, v___x_5531_);
v___x_5533_ = lean_string_append(v___x_5532_, v_message_5524_);
lean_dec_ref(v_message_5524_);
v___x_5534_ = 3;
v___x_5535_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5535_, 0, v___x_5533_);
lean_ctor_set_uint8(v___x_5535_, sizeof(void*)*1, v___x_5534_);
lean_inc_ref(v___y_5339_);
v___x_5536_ = lean_apply_2(v___y_5339_, v___x_5535_, lean_box(0));
v___x_5537_ = lean_box(0);
if (v_isShared_5490_ == 0)
{
lean_ctor_set_tag(v___x_5489_, 1);
lean_ctor_set(v___x_5489_, 0, v___x_5537_);
v___x_5539_ = v___x_5489_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
}
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5554_; 
lean_dec_ref(v_url_5336_);
lean_dec_ref(v_infos_5335_);
v_a_5542_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5544_ = v___x_5486_;
v_isShared_5545_ = v_isSharedCheck_5554_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5486_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5554_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5546_; uint8_t v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5552_; 
v___x_5546_ = lean_io_error_to_string(v_a_5542_);
v___x_5547_ = 3;
v___x_5548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5548_, 0, v___x_5546_);
lean_ctor_set_uint8(v___x_5548_, sizeof(void*)*1, v___x_5547_);
lean_inc_ref(v___y_5339_);
v___x_5549_ = lean_apply_2(v___y_5339_, v___x_5548_, lean_box(0));
v___x_5550_ = lean_box(0);
if (v_isShared_5545_ == 0)
{
lean_ctor_set(v___x_5544_, 0, v___x_5550_);
v___x_5552_ = v___x_5544_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
}
else
{
lean_object* v_a_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5592_; 
lean_dec_ref(v_url_5336_);
lean_dec_ref(v_infos_5335_);
v_a_5580_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5582_ = v___x_5470_;
v_isShared_5583_ = v_isSharedCheck_5592_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_a_5580_);
lean_dec(v___x_5470_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5592_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5584_; uint8_t v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5584_ = lean_io_error_to_string(v_a_5580_);
v___x_5585_ = 3;
v___x_5586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5586_, 0, v___x_5584_);
lean_ctor_set_uint8(v___x_5586_, sizeof(void*)*1, v___x_5585_);
lean_inc_ref(v___y_5339_);
v___x_5587_ = lean_apply_2(v___y_5339_, v___x_5586_, lean_box(0));
v___x_5588_ = lean_box(0);
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 0, v___x_5588_);
v___x_5590_ = v___x_5582_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5588_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5605_; 
lean_dec_ref(v_url_5336_);
lean_dec_ref(v_infos_5335_);
v_a_5593_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5595_ = v___x_5469_;
v_isShared_5596_ = v_isSharedCheck_5605_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5469_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5605_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5597_; uint8_t v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5603_; 
v___x_5597_ = lean_io_error_to_string(v_a_5593_);
v___x_5598_ = 3;
v___x_5599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5599_, 0, v___x_5597_);
lean_ctor_set_uint8(v___x_5599_, sizeof(void*)*1, v___x_5598_);
lean_inc_ref(v___y_5339_);
v___x_5600_ = lean_apply_2(v___y_5339_, v___x_5599_, lean_box(0));
v___x_5601_ = lean_box(0);
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 0, v___x_5601_);
v___x_5603_ = v___x_5595_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5601_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
v___jp_5341_:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; uint8_t v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5344_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_5345_ = lean_uint32_to_nat(v___y_5342_);
v___x_5346_ = l_Nat_reprFast(v___x_5345_);
v___x_5347_ = lean_string_append(v___x_5344_, v___x_5346_);
lean_dec_ref(v___x_5346_);
v___x_5348_ = 3;
v___x_5349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5349_, 0, v___x_5347_);
lean_ctor_set_uint8(v___x_5349_, sizeof(void*)*1, v___x_5348_);
lean_inc_ref(v___y_5343_);
v___x_5350_ = lean_apply_2(v___y_5343_, v___x_5349_, lean_box(0));
v___x_5351_ = lean_box(0);
v___x_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5351_);
return v___x_5352_;
}
v___jp_5353_:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; uint8_t v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; uint8_t v___x_5375_; 
v___x_5359_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5360_ = lean_string_append(v___x_5359_, v_url_5336_);
lean_dec_ref(v_url_5336_);
v___x_5361_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_5362_ = lean_string_append(v___x_5360_, v___x_5361_);
v___x_5363_ = lean_string_append(v___x_5362_, v_a_5358_);
lean_dec_ref(v_a_5358_);
v___x_5364_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_5365_ = lean_string_append(v___x_5363_, v___x_5364_);
v___x_5366_ = lean_string_utf8_byte_size(v___y_5357_);
lean_inc(v___y_5355_);
v___x_5367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5367_, 0, v___y_5357_);
lean_ctor_set(v___x_5367_, 1, v___y_5355_);
lean_ctor_set(v___x_5367_, 2, v___x_5366_);
v___x_5368_ = l_String_Slice_trimAscii(v___x_5367_);
v___x_5369_ = l_String_Slice_toString(v___x_5368_);
lean_dec_ref(v___x_5368_);
v___x_5370_ = lean_string_append(v___x_5365_, v___x_5369_);
lean_dec_ref(v___x_5369_);
v___x_5371_ = 3;
v___x_5372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5372_, 0, v___x_5370_);
lean_ctor_set_uint8(v___x_5372_, sizeof(void*)*1, v___x_5371_);
lean_inc_ref(v___y_5339_);
v___x_5373_ = lean_apply_2(v___y_5339_, v___x_5372_, lean_box(0));
v___x_5374_ = lean_string_utf8_byte_size(v___y_5356_);
v___x_5375_ = lean_nat_dec_eq(v___x_5374_, v___y_5355_);
if (v___x_5375_ == 0)
{
lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; uint8_t v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5376_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
lean_inc(v___y_5355_);
lean_inc_ref(v___y_5356_);
v___x_5377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5377_, 0, v___y_5356_);
lean_ctor_set(v___x_5377_, 1, v___y_5355_);
lean_ctor_set(v___x_5377_, 2, v___x_5374_);
v___x_5378_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5377_, v___x_5374_);
lean_dec_ref_known(v___x_5377_, 3);
v___x_5379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5379_, 0, v___y_5356_);
lean_ctor_set(v___x_5379_, 1, v___y_5355_);
lean_ctor_set(v___x_5379_, 2, v___x_5378_);
v___x_5380_ = l_String_Slice_toString(v___x_5379_);
lean_dec_ref_known(v___x_5379_, 3);
v___x_5381_ = lean_string_append(v___x_5376_, v___x_5380_);
lean_dec_ref(v___x_5380_);
v___x_5382_ = 2;
v___x_5383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5383_, 0, v___x_5381_);
lean_ctor_set_uint8(v___x_5383_, sizeof(void*)*1, v___x_5382_);
lean_inc_ref(v___y_5339_);
v___x_5384_ = lean_apply_2(v___y_5339_, v___x_5383_, lean_box(0));
v___y_5342_ = v___y_5354_;
v___y_5343_ = v___y_5339_;
goto v___jp_5341_;
}
else
{
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
v___y_5342_ = v___y_5354_;
v___y_5343_ = v___y_5339_;
goto v___jp_5341_;
}
}
v___jp_5385_:
{
uint8_t v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5392_ = 3;
v___x_5393_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5393_, 0, v_msg_5390_);
lean_ctor_set_uint8(v___x_5393_, sizeof(void*)*1, v___x_5392_);
lean_inc_ref_n(v___y_5391_, 2);
v___x_5394_ = lean_apply_2(v___y_5391_, v___x_5393_, lean_box(0));
v___x_5395_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_5396_ = lean_string_utf8_byte_size(v___y_5388_);
lean_inc(v___y_5387_);
lean_inc_ref(v___y_5388_);
v___x_5397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5397_, 0, v___y_5388_);
lean_ctor_set(v___x_5397_, 1, v___y_5387_);
lean_ctor_set(v___x_5397_, 2, v___x_5396_);
v___x_5398_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5397_, v___x_5396_);
lean_dec_ref_known(v___x_5397_, 3);
v___x_5399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5399_, 0, v___y_5388_);
lean_ctor_set(v___x_5399_, 1, v___y_5387_);
lean_ctor_set(v___x_5399_, 2, v___x_5398_);
v___x_5400_ = l_String_Slice_toString(v___x_5399_);
lean_dec_ref_known(v___x_5399_, 3);
v___x_5401_ = lean_string_append(v___x_5395_, v___x_5400_);
lean_dec_ref(v___x_5400_);
v___x_5402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
lean_ctor_set_uint8(v___x_5402_, sizeof(void*)*1, v___y_5389_);
v___x_5403_ = lean_apply_2(v___y_5391_, v___x_5402_, lean_box(0));
v___y_5342_ = v___y_5386_;
v___y_5343_ = v___y_5391_;
goto v___jp_5341_;
}
v___jp_5404_:
{
lean_object* v___x_5412_; uint8_t v___x_5413_; 
v___x_5412_ = lean_string_utf8_byte_size(v___y_5407_);
v___x_5413_ = lean_nat_dec_eq(v___x_5412_, v___y_5406_);
if (v___x_5413_ == 0)
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5414_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5415_ = lean_string_append(v_msg_5410_, v___x_5414_);
lean_inc_n(v___y_5406_, 2);
lean_inc_ref(v___y_5407_);
v___x_5416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5416_, 0, v___y_5407_);
lean_ctor_set(v___x_5416_, 1, v___y_5406_);
lean_ctor_set(v___x_5416_, 2, v___x_5412_);
v___x_5417_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5416_, v___x_5412_);
lean_dec_ref_known(v___x_5416_, 3);
v___x_5418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5418_, 0, v___y_5407_);
lean_ctor_set(v___x_5418_, 1, v___y_5406_);
lean_ctor_set(v___x_5418_, 2, v___x_5417_);
v___x_5419_ = l_String_Slice_toString(v___x_5418_);
lean_dec_ref_known(v___x_5418_, 3);
v___x_5420_ = lean_string_append(v___x_5415_, v___x_5419_);
lean_dec_ref(v___x_5419_);
v___y_5386_ = v___y_5405_;
v___y_5387_ = v___y_5406_;
v___y_5388_ = v___y_5408_;
v___y_5389_ = v___y_5409_;
v_msg_5390_ = v___x_5420_;
v___y_5391_ = v___y_5411_;
goto v___jp_5385_;
}
else
{
lean_dec_ref(v___y_5407_);
v___y_5386_ = v___y_5405_;
v___y_5387_ = v___y_5406_;
v___y_5388_ = v___y_5408_;
v___y_5389_ = v___y_5409_;
v_msg_5390_ = v_msg_5410_;
v___y_5391_ = v___y_5411_;
goto v___jp_5385_;
}
}
v___jp_5421_:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5430_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_5431_ = lean_string_append(v_msg_5428_, v___x_5430_);
v___x_5432_ = lean_string_append(v___x_5431_, v_url_5336_);
lean_dec_ref(v_url_5336_);
v___x_5433_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_5434_ = l_Lake_JsonObject_getJson_x3f(v___y_5427_, v___x_5433_);
lean_dec(v___y_5427_);
if (lean_obj_tag(v___x_5434_) == 0)
{
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5424_;
v___y_5408_ = v___y_5425_;
v___y_5409_ = v___y_5426_;
v_msg_5410_ = v___x_5432_;
v___y_5411_ = v___y_5429_;
goto v___jp_5404_;
}
else
{
lean_object* v_val_5435_; lean_object* v___x_5436_; 
v_val_5435_ = lean_ctor_get(v___x_5434_, 0);
lean_inc(v_val_5435_);
lean_dec_ref_known(v___x_5434_, 1);
v___x_5436_ = l_Lean_Json_getStr_x3f(v_val_5435_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_dec_ref_known(v___x_5436_, 1);
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5424_;
v___y_5408_ = v___y_5425_;
v___y_5409_ = v___y_5426_;
v_msg_5410_ = v___x_5432_;
v___y_5411_ = v___y_5429_;
goto v___jp_5404_;
}
else
{
if (lean_obj_tag(v___x_5436_) == 1)
{
lean_object* v_a_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5436_, 1);
v___x_5438_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
v___x_5439_ = lean_string_append(v___x_5432_, v___x_5438_);
v___x_5440_ = lean_string_append(v___x_5439_, v_a_5437_);
lean_dec(v_a_5437_);
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5424_;
v___y_5408_ = v___y_5425_;
v___y_5409_ = v___y_5426_;
v_msg_5410_ = v___x_5440_;
v___y_5411_ = v___y_5429_;
goto v___jp_5404_;
}
else
{
lean_dec_ref_known(v___x_5436_, 1);
v___y_5405_ = v___y_5422_;
v___y_5406_ = v___y_5423_;
v___y_5407_ = v___y_5424_;
v___y_5408_ = v___y_5425_;
v___y_5409_ = v___y_5426_;
v_msg_5410_ = v___x_5432_;
v___y_5411_ = v___y_5429_;
goto v___jp_5404_;
}
}
}
}
v___jp_5441_:
{
lean_object* v___x_5447_; 
lean_inc_ref(v___y_5445_);
v___x_5447_ = l_Lean_Json_parse(v___y_5445_);
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_a_5448_; 
v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_a_5448_);
lean_dec_ref_known(v___x_5447_, 1);
v___y_5354_ = v___y_5442_;
v___y_5355_ = v___y_5443_;
v___y_5356_ = v___y_5444_;
v___y_5357_ = v___y_5445_;
v_a_5358_ = v_a_5448_;
goto v___jp_5353_;
}
else
{
lean_object* v_a_5449_; lean_object* v___x_5450_; 
v_a_5449_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_a_5449_);
lean_dec_ref_known(v___x_5447_, 1);
v___x_5450_ = l_Lean_Json_getObj_x3f(v_a_5449_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
lean_inc(v_a_5451_);
lean_dec_ref_known(v___x_5450_, 1);
v___y_5354_ = v___y_5442_;
v___y_5355_ = v___y_5443_;
v___y_5356_ = v___y_5444_;
v___y_5357_ = v___y_5445_;
v_a_5358_ = v_a_5451_;
goto v___jp_5353_;
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v_a_5452_ = lean_ctor_get(v___x_5450_, 0);
lean_inc(v_a_5452_);
lean_dec_ref_known(v___x_5450_, 1);
v___x_5453_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_5454_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_5455_ = l_Lake_JsonObject_getJson_x3f(v_a_5452_, v___x_5454_);
if (lean_obj_tag(v___x_5455_) == 0)
{
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v___y_5444_;
v___y_5425_ = v___y_5445_;
v___y_5426_ = v___y_5446_;
v___y_5427_ = v_a_5452_;
v_msg_5428_ = v___x_5453_;
v___y_5429_ = v___y_5339_;
goto v___jp_5421_;
}
else
{
lean_object* v_val_5456_; lean_object* v___x_5457_; 
v_val_5456_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_val_5456_);
lean_dec_ref_known(v___x_5455_, 1);
v___x_5457_ = l_Lean_Json_getNat_x3f(v_val_5456_);
if (lean_obj_tag(v___x_5457_) == 0)
{
lean_dec_ref_known(v___x_5457_, 1);
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v___y_5444_;
v___y_5425_ = v___y_5445_;
v___y_5426_ = v___y_5446_;
v___y_5427_ = v_a_5452_;
v_msg_5428_ = v___x_5453_;
v___y_5429_ = v___y_5339_;
goto v___jp_5421_;
}
else
{
if (lean_obj_tag(v___x_5457_) == 1)
{
lean_object* v_a_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; 
v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
lean_inc(v_a_5458_);
lean_dec_ref_known(v___x_5457_, 1);
v___x_5459_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5460_ = l_Nat_reprFast(v_a_5458_);
v___x_5461_ = lean_string_append(v___x_5459_, v___x_5460_);
lean_dec_ref(v___x_5460_);
v___x_5462_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_5463_ = lean_string_append(v___x_5461_, v___x_5462_);
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v___y_5444_;
v___y_5425_ = v___y_5445_;
v___y_5426_ = v___y_5446_;
v___y_5427_ = v_a_5452_;
v_msg_5428_ = v___x_5463_;
v___y_5429_ = v___y_5339_;
goto v___jp_5421_;
}
else
{
lean_dec_ref_known(v___x_5457_, 1);
v___y_5422_ = v___y_5442_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v___y_5444_;
v___y_5425_ = v___y_5445_;
v___y_5426_ = v___y_5446_;
v___y_5427_ = v_a_5452_;
v_msg_5428_ = v___x_5453_;
v___y_5429_ = v___y_5339_;
goto v___jp_5421_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed(lean_object* v_infos_5606_, lean_object* v_url_5607_, lean_object* v_h_5608_, lean_object* v_path_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
lean_object* v_res_5612_; 
v_res_5612_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(v_infos_5606_, v_url_5607_, v_h_5608_, v_path_5609_, v___y_5610_);
lean_dec_ref(v___y_5610_);
lean_dec_ref(v_path_5609_);
lean_dec(v_h_5608_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(lean_object* v_url_5613_, lean_object* v_infos_5614_, lean_object* v_a_5615_){
_start:
{
lean_object* v___f_5617_; lean_object* v___x_5618_; 
v___f_5617_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5617_, 0, v_infos_5614_);
lean_closure_set(v___f_5617_, 1, v_url_5613_);
v___x_5618_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5617_, v_a_5615_);
return v___x_5618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___boxed(lean_object* v_url_5619_, lean_object* v_infos_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(v_url_5619_, v_infos_5620_, v_a_5621_);
lean_dec_ref(v_a_5621_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(lean_object* v_a_5624_, lean_object* v___x_5625_, lean_object* v_n_5626_, lean_object* v_j_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_){
_start:
{
lean_object* v___x_5630_; 
v___x_5630_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5624_, v_n_5626_, v_j_5627_, v_a_5629_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___boxed(lean_object* v_a_5631_, lean_object* v___x_5632_, lean_object* v_n_5633_, lean_object* v_j_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v_res_5637_; 
v_res_5637_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(v_a_5631_, v___x_5632_, v_n_5633_, v_j_5634_, v_a_5635_, v_a_5636_);
lean_dec(v_n_5633_);
lean_dec(v___x_5632_);
lean_dec_ref(v_a_5631_);
return v_res_5637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object* v_cfg_5638_, lean_object* v_h_5639_, lean_object* v_path_5640_, lean_object* v___y_5641_){
_start:
{
uint8_t v___y_5644_; uint8_t v___y_5650_; lean_object* v___y_5651_; uint32_t v___y_5652_; lean_object* v___y_5653_; uint8_t v_kind_5662_; lean_object* v_scope_5663_; lean_object* v_infos_5664_; lean_object* v_key_5665_; uint8_t v___y_5667_; uint32_t v___y_5668_; lean_object* v___y_5669_; lean_object* v___y_5674_; lean_object* v___y_5675_; uint8_t v___y_5676_; lean_object* v___y_5677_; uint32_t v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5692_; uint8_t v___y_5693_; uint32_t v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5701_; lean_object* v___y_5702_; uint8_t v___y_5703_; uint32_t v___y_5704_; lean_object* v___y_5705_; lean_object* v___y_5706_; lean_object* v___y_5716_; uint8_t v___y_5717_; uint32_t v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v_a_5723_; lean_object* v___y_5819_; lean_object* v___y_5849_; 
v_kind_5662_ = lean_ctor_get_uint8(v_cfg_5638_, sizeof(void*)*3);
v_scope_5663_ = lean_ctor_get(v_cfg_5638_, 0);
lean_inc_ref(v_scope_5663_);
v_infos_5664_ = lean_ctor_get(v_cfg_5638_, 1);
lean_inc_ref(v_infos_5664_);
v_key_5665_ = lean_ctor_get(v_cfg_5638_, 2);
if (v_kind_5662_ == 0)
{
lean_object* v___x_5850_; lean_object* v___x_5851_; uint8_t v___x_5852_; 
v___x_5850_ = lean_unsigned_to_nat(0u);
v___x_5851_ = lean_array_get_size(v_infos_5664_);
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
v___x_5857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5639_, v_infos_5664_, v___x_5855_, v___x_5856_, v___x_5853_, v___y_5641_);
v___y_5819_ = v___x_5857_;
goto v___jp_5818_;
}
}
else
{
size_t v___x_5858_; size_t v___x_5859_; lean_object* v___x_5860_; 
v___x_5858_ = ((size_t)0ULL);
v___x_5859_ = lean_usize_of_nat(v___x_5851_);
v___x_5860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5639_, v_infos_5664_, v___x_5858_, v___x_5859_, v___x_5853_, v___y_5641_);
v___y_5819_ = v___x_5860_;
goto v___jp_5818_;
}
}
}
else
{
lean_object* v___x_5861_; lean_object* v___x_5862_; uint8_t v___x_5863_; 
v___x_5861_ = lean_unsigned_to_nat(0u);
v___x_5862_ = lean_array_get_size(v_infos_5664_);
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
v___x_5868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5639_, v_infos_5664_, v___x_5866_, v___x_5867_, v___x_5864_, v___y_5641_);
v___y_5849_ = v___x_5868_;
goto v___jp_5848_;
}
}
else
{
size_t v___x_5869_; size_t v___x_5870_; lean_object* v___x_5871_; 
v___x_5869_ = ((size_t)0ULL);
v___x_5870_ = lean_usize_of_nat(v___x_5862_);
v___x_5871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5639_, v_infos_5664_, v___x_5869_, v___x_5870_, v___x_5864_, v___y_5641_);
v___y_5849_ = v___x_5871_;
goto v___jp_5848_;
}
}
}
v___jp_5643_:
{
if (v___y_5644_ == 0)
{
lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5645_ = lean_box(0);
v___x_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5646_, 0, v___x_5645_);
return v___x_5646_;
}
else
{
lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5647_ = lean_box(0);
v___x_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
return v___x_5648_;
}
}
v___jp_5649_:
{
lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; uint8_t v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; 
v___x_5654_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_5655_ = lean_string_append(v___y_5653_, v___x_5654_);
v___x_5656_ = lean_uint32_to_nat(v___y_5652_);
v___x_5657_ = l_Nat_reprFast(v___x_5656_);
v___x_5658_ = lean_string_append(v___x_5655_, v___x_5657_);
lean_dec_ref(v___x_5657_);
v___x_5659_ = 3;
v___x_5660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5660_, 0, v___x_5658_);
lean_ctor_set_uint8(v___x_5660_, sizeof(void*)*1, v___x_5659_);
lean_inc_ref(v___y_5651_);
v___x_5661_ = lean_apply_2(v___y_5651_, v___x_5660_, lean_box(0));
v___y_5644_ = v___y_5650_;
goto v___jp_5643_;
}
v___jp_5666_:
{
uint32_t v___x_5670_; uint8_t v___x_5671_; 
v___x_5670_ = 0;
v___x_5671_ = lean_uint32_dec_eq(v___y_5668_, v___x_5670_);
if (v___x_5671_ == 0)
{
lean_object* v_s_5672_; 
v_s_5672_ = lean_ctor_get(v_scope_5663_, 0);
lean_inc_ref(v_s_5672_);
lean_dec_ref(v_scope_5663_);
v___y_5650_ = v___y_5667_;
v___y_5651_ = v___y_5669_;
v___y_5652_ = v___y_5668_;
v___y_5653_ = v_s_5672_;
goto v___jp_5649_;
}
else
{
lean_dec_ref(v_scope_5663_);
v___y_5644_ = v___y_5667_;
goto v___jp_5643_;
}
}
v___jp_5673_:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; uint8_t v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5681_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_5682_ = lean_string_append(v___y_5680_, v___x_5681_);
lean_inc(v___y_5675_);
lean_inc(v___y_5679_);
lean_inc_ref(v___y_5674_);
v___x_5683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5683_, 0, v___y_5674_);
lean_ctor_set(v___x_5683_, 1, v___y_5679_);
lean_ctor_set(v___x_5683_, 2, v___y_5675_);
v___x_5684_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5683_, v___y_5675_);
lean_dec_ref_known(v___x_5683_, 3);
v___x_5685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5685_, 0, v___y_5674_);
lean_ctor_set(v___x_5685_, 1, v___y_5679_);
lean_ctor_set(v___x_5685_, 2, v___x_5684_);
v___x_5686_ = l_String_Slice_toString(v___x_5685_);
lean_dec_ref_known(v___x_5685_, 3);
v___x_5687_ = lean_string_append(v___x_5682_, v___x_5686_);
lean_dec_ref(v___x_5686_);
v___x_5688_ = 2;
v___x_5689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5689_, 0, v___x_5687_);
lean_ctor_set_uint8(v___x_5689_, sizeof(void*)*1, v___x_5688_);
lean_inc_ref(v___y_5677_);
v___x_5690_ = lean_apply_2(v___y_5677_, v___x_5689_, lean_box(0));
v___y_5667_ = v___y_5676_;
v___y_5668_ = v___y_5678_;
v___y_5669_ = v___y_5677_;
goto v___jp_5666_;
}
v___jp_5691_:
{
lean_object* v___x_5697_; uint8_t v___x_5698_; 
v___x_5697_ = lean_string_utf8_byte_size(v___y_5692_);
v___x_5698_ = lean_nat_dec_eq(v___x_5697_, v___y_5695_);
if (v___x_5698_ == 0)
{
lean_object* v_s_5699_; 
v_s_5699_ = lean_ctor_get(v_scope_5663_, 0);
lean_inc_ref(v_s_5699_);
v___y_5674_ = v___y_5692_;
v___y_5675_ = v___x_5697_;
v___y_5676_ = v___y_5693_;
v___y_5677_ = v___y_5696_;
v___y_5678_ = v___y_5694_;
v___y_5679_ = v___y_5695_;
v___y_5680_ = v_s_5699_;
goto v___jp_5673_;
}
else
{
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5692_);
v___y_5667_ = v___y_5693_;
v___y_5668_ = v___y_5694_;
v___y_5669_ = v___y_5696_;
goto v___jp_5666_;
}
}
v___jp_5700_:
{
lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; uint8_t v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
v___x_5707_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_5708_ = lean_string_append(v___y_5706_, v___x_5707_);
v___x_5709_ = lean_string_append(v___x_5708_, v___y_5702_);
v___x_5710_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_5711_ = lean_string_append(v___x_5709_, v___x_5710_);
v___x_5712_ = 3;
v___x_5713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*1, v___x_5712_);
lean_inc_ref(v___y_5641_);
v___x_5714_ = lean_apply_2(v___y_5641_, v___x_5713_, lean_box(0));
v___y_5692_ = v___y_5701_;
v___y_5693_ = v___y_5703_;
v___y_5694_ = v___y_5704_;
v___y_5695_ = v___y_5705_;
v___y_5696_ = v___y_5641_;
goto v___jp_5691_;
}
v___jp_5715_:
{
lean_object* v_s_5721_; 
v_s_5721_ = lean_ctor_get(v_scope_5663_, 0);
lean_inc_ref(v_s_5721_);
v___y_5701_ = v___y_5716_;
v___y_5702_ = v___y_5720_;
v___y_5703_ = v___y_5717_;
v___y_5704_ = v___y_5718_;
v___y_5705_ = v___y_5719_;
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
v___x_5737_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_5638_, v_stderr_5735_, v_stdout_5734_, v___x_5736_, v___y_5641_);
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
v___x_5745_ = lean_array_get_size(v_infos_5664_);
lean_dec_ref(v_infos_5664_);
v___x_5746_ = lean_nat_dec_lt(v_numSuccesses_5744_, v___x_5745_);
lean_dec(v_numSuccesses_5744_);
if (v___x_5746_ == 0)
{
uint32_t v___x_5747_; 
v___x_5747_ = lean_unbox_uint32(v_a_5740_);
lean_dec(v_a_5740_);
v___y_5692_ = v_a_5742_;
v___y_5693_ = v_didError_5743_;
v___y_5694_ = v___x_5747_;
v___y_5695_ = v___x_5727_;
v___y_5696_ = v___y_5641_;
goto v___jp_5691_;
}
else
{
if (v_kind_5662_ == 0)
{
lean_object* v___x_5748_; uint32_t v___x_5749_; 
v___x_5748_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_5749_ = lean_unbox_uint32(v_a_5740_);
lean_dec(v_a_5740_);
v___y_5716_ = v_a_5742_;
v___y_5717_ = v_didError_5743_;
v___y_5718_ = v___x_5749_;
v___y_5719_ = v___x_5727_;
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
v___y_5717_ = v_didError_5743_;
v___y_5718_ = v___x_5751_;
v___y_5719_ = v___x_5727_;
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
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
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
lean_inc_ref(v___y_5641_);
v___x_5759_ = lean_apply_2(v___y_5641_, v___x_5758_, lean_box(0));
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
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
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
lean_inc_ref(v___y_5641_);
v___x_5772_ = lean_apply_2(v___y_5641_, v___x_5771_, lean_box(0));
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
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
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
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
lean_dec_ref(v_cfg_5638_);
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
lean_inc_ref(v___y_5641_);
v___x_5793_ = lean_apply_2(v___y_5641_, v___x_5792_, lean_box(0));
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
v___x_5800_ = lean_io_prim_handle_flush(v_h_5639_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; 
lean_dec_ref_known(v___x_5800_, 1);
v___x_5801_ = lean_unsigned_to_nat(11u);
v___x_5802_ = lean_mk_empty_array_with_capacity(v___x_5801_);
lean_dec_ref(v___x_5802_);
v___x_5803_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_5804_ = lean_array_push(v___x_5803_, v_path_5640_);
v_a_5723_ = v___x_5804_;
goto v___jp_5722_;
}
else
{
lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5817_; 
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
lean_dec_ref(v_path_5640_);
lean_dec_ref(v_cfg_5638_);
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
lean_inc_ref(v___y_5641_);
v___x_5812_ = lean_apply_2(v___y_5641_, v___x_5811_, lean_box(0));
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
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
lean_dec_ref(v_path_5640_);
lean_dec_ref(v_cfg_5638_);
return v___y_5819_;
}
}
v___jp_5820_:
{
lean_object* v___x_5821_; 
v___x_5821_ = lean_io_prim_handle_flush(v_h_5639_);
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
lean_inc_ref(v_key_5665_);
v___x_5829_ = lean_array_push(v___x_5828_, v_key_5665_);
v___x_5830_ = lean_array_push(v___x_5829_, v___x_5822_);
v___x_5831_ = lean_array_push(v___x_5830_, v___x_5823_);
v___x_5832_ = lean_array_push(v___x_5831_, v___x_5824_);
v___x_5833_ = lean_array_push(v___x_5832_, v___x_5825_);
v___x_5834_ = lean_array_push(v___x_5833_, v_path_5640_);
v_a_5723_ = v___x_5834_;
goto v___jp_5722_;
}
else
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5847_; 
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
lean_dec_ref(v_path_5640_);
lean_dec_ref(v_cfg_5638_);
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
lean_inc_ref(v___y_5641_);
v___x_5842_ = lean_apply_2(v___y_5641_, v___x_5841_, lean_box(0));
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
lean_dec_ref(v_infos_5664_);
lean_dec_ref(v_scope_5663_);
lean_dec_ref(v_path_5640_);
lean_dec_ref(v_cfg_5638_);
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
uint32_t v___y_5894_; lean_object* v___y_5895_; lean_object* v___y_5906_; lean_object* v___y_5907_; lean_object* v___y_5908_; uint32_t v___y_5909_; lean_object* v_a_5910_; lean_object* v___y_5938_; lean_object* v___y_5939_; uint32_t v___y_5940_; uint8_t v___y_5941_; lean_object* v_msg_5942_; lean_object* v___y_5943_; lean_object* v___y_5957_; lean_object* v___y_5958_; lean_object* v___y_5959_; uint32_t v___y_5960_; uint8_t v___y_5961_; lean_object* v_msg_5962_; lean_object* v___y_5963_; lean_object* v___y_5974_; lean_object* v___y_5975_; lean_object* v___y_5976_; uint32_t v___y_5977_; lean_object* v___y_5978_; uint8_t v___y_5979_; lean_object* v_msg_5980_; lean_object* v___y_5981_; lean_object* v___y_5994_; lean_object* v___y_5995_; lean_object* v___y_5996_; uint32_t v___y_5997_; uint8_t v___y_5998_; size_t v_sz_6016_; size_t v___x_6017_; lean_object* v___x_6018_; lean_object* v_body_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
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
v___y_5994_ = v___x_6029_;
v___y_5995_ = v_stderr_6045_;
v___y_5996_ = v_stdout_6044_;
v___y_5997_ = v_exitCode_6043_;
v___y_5998_ = v___x_6035_;
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
v___y_5994_ = v___x_6029_;
v___y_5995_ = v_stderr_6045_;
v___y_5996_ = v_stdout_6044_;
v___y_5997_ = v_exitCode_6043_;
v___y_5998_ = v___x_6035_;
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
v___x_5918_ = lean_string_utf8_byte_size(v___y_5907_);
lean_inc(v___y_5906_);
v___x_5919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5919_, 0, v___y_5907_);
lean_ctor_set(v___x_5919_, 1, v___y_5906_);
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
v___x_5926_ = lean_string_utf8_byte_size(v___y_5908_);
v___x_5927_ = lean_nat_dec_eq(v___x_5926_, v___y_5906_);
if (v___x_5927_ == 0)
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; uint8_t v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5928_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
lean_inc(v___y_5906_);
lean_inc_ref(v___y_5908_);
v___x_5929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5929_, 0, v___y_5908_);
lean_ctor_set(v___x_5929_, 1, v___y_5906_);
lean_ctor_set(v___x_5929_, 2, v___x_5926_);
v___x_5930_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5929_, v___x_5926_);
lean_dec_ref_known(v___x_5929_, 3);
v___x_5931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5931_, 0, v___y_5908_);
lean_ctor_set(v___x_5931_, 1, v___y_5906_);
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
lean_dec_ref(v___y_5908_);
lean_dec(v___y_5906_);
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
v___x_5948_ = lean_string_utf8_byte_size(v___y_5939_);
lean_inc(v___y_5938_);
lean_inc_ref(v___y_5939_);
v___x_5949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5949_, 0, v___y_5939_);
lean_ctor_set(v___x_5949_, 1, v___y_5938_);
lean_ctor_set(v___x_5949_, 2, v___x_5948_);
v___x_5950_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5949_, v___x_5948_);
lean_dec_ref_known(v___x_5949_, 3);
v___x_5951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5951_, 0, v___y_5939_);
lean_ctor_set(v___x_5951_, 1, v___y_5938_);
lean_ctor_set(v___x_5951_, 2, v___x_5950_);
v___x_5952_ = l_String_Slice_toString(v___x_5951_);
lean_dec_ref_known(v___x_5951_, 3);
v___x_5953_ = lean_string_append(v___x_5947_, v___x_5952_);
lean_dec_ref(v___x_5952_);
v___x_5954_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
lean_ctor_set_uint8(v___x_5954_, sizeof(void*)*1, v___y_5941_);
v___x_5955_ = lean_apply_2(v___y_5943_, v___x_5954_, lean_box(0));
v___y_5894_ = v___y_5940_;
v___y_5895_ = v___y_5943_;
goto v___jp_5893_;
}
v___jp_5956_:
{
lean_object* v___x_5964_; uint8_t v___x_5965_; 
v___x_5964_ = lean_string_utf8_byte_size(v___y_5959_);
v___x_5965_ = lean_nat_dec_eq(v___x_5964_, v___y_5957_);
if (v___x_5965_ == 0)
{
lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5966_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5967_ = lean_string_append(v_msg_5962_, v___x_5966_);
lean_inc_n(v___y_5957_, 2);
lean_inc_ref(v___y_5959_);
v___x_5968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5968_, 0, v___y_5959_);
lean_ctor_set(v___x_5968_, 1, v___y_5957_);
lean_ctor_set(v___x_5968_, 2, v___x_5964_);
v___x_5969_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5968_, v___x_5964_);
lean_dec_ref_known(v___x_5968_, 3);
v___x_5970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5970_, 0, v___y_5959_);
lean_ctor_set(v___x_5970_, 1, v___y_5957_);
lean_ctor_set(v___x_5970_, 2, v___x_5969_);
v___x_5971_ = l_String_Slice_toString(v___x_5970_);
lean_dec_ref_known(v___x_5970_, 3);
v___x_5972_ = lean_string_append(v___x_5967_, v___x_5971_);
lean_dec_ref(v___x_5971_);
v___y_5938_ = v___y_5957_;
v___y_5939_ = v___y_5958_;
v___y_5940_ = v___y_5960_;
v___y_5941_ = v___y_5961_;
v_msg_5942_ = v___x_5972_;
v___y_5943_ = v___y_5963_;
goto v___jp_5937_;
}
else
{
lean_dec_ref(v___y_5959_);
v___y_5938_ = v___y_5957_;
v___y_5939_ = v___y_5958_;
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
v___x_5986_ = l_Lake_JsonObject_getJson_x3f(v___y_5978_, v___x_5985_);
lean_dec(v___y_5978_);
if (lean_obj_tag(v___x_5986_) == 0)
{
v___y_5957_ = v___y_5974_;
v___y_5958_ = v___y_5975_;
v___y_5959_ = v___y_5976_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5979_;
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
v___y_5958_ = v___y_5975_;
v___y_5959_ = v___y_5976_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5979_;
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
v___y_5958_ = v___y_5975_;
v___y_5959_ = v___y_5976_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5979_;
v_msg_5962_ = v___x_5992_;
v___y_5963_ = v___y_5981_;
goto v___jp_5956_;
}
else
{
lean_dec_ref_known(v___x_5988_, 1);
v___y_5957_ = v___y_5974_;
v___y_5958_ = v___y_5975_;
v___y_5959_ = v___y_5976_;
v___y_5960_ = v___y_5977_;
v___y_5961_ = v___y_5979_;
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
lean_inc_ref(v___y_5995_);
v___x_5999_ = l_Lean_Json_parse(v___y_5995_);
if (lean_obj_tag(v___x_5999_) == 0)
{
lean_object* v_a_6000_; 
v_a_6000_ = lean_ctor_get(v___x_5999_, 0);
lean_inc(v_a_6000_);
lean_dec_ref_known(v___x_5999_, 1);
v___y_5906_ = v___y_5994_;
v___y_5907_ = v___y_5995_;
v___y_5908_ = v___y_5996_;
v___y_5909_ = v___y_5997_;
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
v___y_5907_ = v___y_5995_;
v___y_5908_ = v___y_5996_;
v___y_5909_ = v___y_5997_;
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
v___y_5975_ = v___y_5995_;
v___y_5976_ = v___y_5996_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v_a_6004_;
v___y_5979_ = v___y_5998_;
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
v___y_5975_ = v___y_5995_;
v___y_5976_ = v___y_5996_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v_a_6004_;
v___y_5979_ = v___y_5998_;
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
v___y_5975_ = v___y_5995_;
v___y_5976_ = v___y_5996_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v_a_6004_;
v___y_5979_ = v___y_5998_;
v_msg_5980_ = v___x_6015_;
v___y_5981_ = v___y_5891_;
goto v___jp_5973_;
}
else
{
lean_dec_ref_known(v___x_6009_, 1);
v___y_5974_ = v___y_5994_;
v___y_5975_ = v___y_5995_;
v___y_5976_ = v___y_5996_;
v___y_5977_ = v___y_5997_;
v___y_5978_ = v_a_6004_;
v___y_5979_ = v___y_5998_;
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
uint8_t v___x_6494_; lean_object* v___x_6496_; uint8_t v___x_6497_; 
v___x_6494_ = l_System_FilePath_pathExists(v_path_6444_);
v___x_6496_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6497_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_6497_ == 0)
{
goto v___jp_6495_;
}
else
{
lean_object* v___x_6498_; uint8_t v___x_6499_; 
v___x_6498_ = lean_box(0);
v___x_6499_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_6499_ == 0)
{
if (v___x_6497_ == 0)
{
goto v___jp_6495_;
}
else
{
size_t v___x_6500_; size_t v___x_6501_; lean_object* v___x_6502_; 
v___x_6500_ = ((size_t)0ULL);
v___x_6501_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6496_, v___x_6500_, v___x_6501_, v___x_6498_, v___y_6416_);
if (lean_obj_tag(v___x_6502_) == 0)
{
lean_dec_ref_known(v___x_6502_, 1);
goto v___jp_6495_;
}
else
{
lean_object* v_a_6503_; lean_object* v___x_6505_; uint8_t v_isShared_6506_; uint8_t v_isSharedCheck_6510_; 
lean_dec_ref(v_b_6415_);
v_a_6503_ = lean_ctor_get(v___x_6502_, 0);
v_isSharedCheck_6510_ = !lean_is_exclusive(v___x_6502_);
if (v_isSharedCheck_6510_ == 0)
{
v___x_6505_ = v___x_6502_;
v_isShared_6506_ = v_isSharedCheck_6510_;
goto v_resetjp_6504_;
}
else
{
lean_inc(v_a_6503_);
lean_dec(v___x_6502_);
v___x_6505_ = lean_box(0);
v_isShared_6506_ = v_isSharedCheck_6510_;
goto v_resetjp_6504_;
}
v_resetjp_6504_:
{
lean_object* v___x_6508_; 
if (v_isShared_6506_ == 0)
{
v___x_6508_ = v___x_6505_;
goto v_reusejp_6507_;
}
else
{
lean_object* v_reuseFailAlloc_6509_; 
v_reuseFailAlloc_6509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6509_, 0, v_a_6503_);
v___x_6508_ = v_reuseFailAlloc_6509_;
goto v_reusejp_6507_;
}
v_reusejp_6507_:
{
return v___x_6508_;
}
}
}
}
}
else
{
size_t v___x_6511_; size_t v___x_6512_; lean_object* v___x_6513_; 
v___x_6511_ = ((size_t)0ULL);
v___x_6512_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6496_, v___x_6511_, v___x_6512_, v___x_6498_, v___y_6416_);
if (lean_obj_tag(v___x_6513_) == 0)
{
lean_dec_ref_known(v___x_6513_, 1);
goto v___jp_6495_;
}
else
{
lean_object* v_a_6514_; lean_object* v___x_6516_; uint8_t v_isShared_6517_; uint8_t v_isSharedCheck_6521_; 
lean_dec_ref(v_b_6415_);
v_a_6514_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6521_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6521_ == 0)
{
v___x_6516_ = v___x_6513_;
v_isShared_6517_ = v_isSharedCheck_6521_;
goto v_resetjp_6515_;
}
else
{
lean_inc(v_a_6514_);
lean_dec(v___x_6513_);
v___x_6516_ = lean_box(0);
v_isShared_6517_ = v_isSharedCheck_6521_;
goto v_resetjp_6515_;
}
v_resetjp_6515_:
{
lean_object* v___x_6519_; 
if (v_isShared_6517_ == 0)
{
v___x_6519_ = v___x_6516_;
goto v_reusejp_6518_;
}
else
{
lean_object* v_reuseFailAlloc_6520_; 
v_reuseFailAlloc_6520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6520_, 0, v_a_6514_);
v___x_6519_ = v_reuseFailAlloc_6520_;
goto v_reusejp_6518_;
}
v_reusejp_6518_:
{
return v___x_6519_;
}
}
}
}
}
v___jp_6495_:
{
if (v___x_6494_ == 0)
{
goto v___jp_6425_;
}
else
{
v_a_6419_ = v_b_6415_;
goto v___jp_6418_;
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
lean_object* v___x_6522_; 
v___x_6522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6522_, 0, v_b_6415_);
return v___x_6522_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_as_6523_, lean_object* v_i_6524_, lean_object* v_stop_6525_, lean_object* v_b_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_){
_start:
{
size_t v_i_boxed_6529_; size_t v_stop_boxed_6530_; lean_object* v_res_6531_; 
v_i_boxed_6529_ = lean_unbox_usize(v_i_6524_);
lean_dec(v_i_6524_);
v_stop_boxed_6530_ = lean_unbox_usize(v_stop_6525_);
lean_dec(v_stop_6525_);
v_res_6531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_as_6523_, v_i_boxed_6529_, v_stop_boxed_6530_, v_b_6526_, v___y_6527_);
lean_dec_ref(v___y_6527_);
lean_dec_ref(v_as_6523_);
return v_res_6531_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_6536_, lean_object* v_cache_6537_, lean_object* v_service_6538_, lean_object* v_scope_6539_, uint8_t v_force_6540_, lean_object* v_a_6541_){
_start:
{
lean_object* v_a_6544_; lean_object* v_a_6566_; lean_object* v___y_6585_; lean_object* v___x_6595_; lean_object* v___x_6596_; uint8_t v___x_6597_; 
v___x_6595_ = lean_array_get_size(v_descrs_6536_);
v___x_6596_ = lean_unsigned_to_nat(0u);
v___x_6597_ = lean_nat_dec_eq(v___x_6595_, v___x_6596_);
if (v___x_6597_ == 0)
{
lean_object* v___x_6598_; lean_object* v_infos_6600_; lean_object* v___y_6611_; uint8_t v___x_6622_; 
v___x_6598_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_6622_ = lean_nat_dec_lt(v___x_6596_, v___x_6595_);
if (v___x_6622_ == 0)
{
v_infos_6600_ = v___x_6598_;
goto v___jp_6599_;
}
else
{
lean_object* v___x_6623_; uint8_t v___x_6624_; 
v___x_6623_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
v___x_6624_ = lean_nat_dec_le(v___x_6595_, v___x_6595_);
if (v___x_6624_ == 0)
{
if (v___x_6622_ == 0)
{
v_infos_6600_ = v___x_6598_;
goto v___jp_6599_;
}
else
{
size_t v___x_6625_; size_t v___x_6626_; lean_object* v___x_6627_; 
v___x_6625_ = ((size_t)0ULL);
v___x_6626_ = lean_usize_of_nat(v___x_6595_);
lean_inc_ref(v_cache_6537_);
lean_inc_ref(v_scope_6539_);
lean_inc_ref(v_service_6538_);
v___x_6627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6538_, v_scope_6539_, v_cache_6537_, v_force_6540_, v_descrs_6536_, v___x_6625_, v___x_6626_, v___x_6623_, v_a_6541_);
v___y_6611_ = v___x_6627_;
goto v___jp_6610_;
}
}
else
{
size_t v___x_6628_; size_t v___x_6629_; lean_object* v___x_6630_; 
v___x_6628_ = ((size_t)0ULL);
v___x_6629_ = lean_usize_of_nat(v___x_6595_);
lean_inc_ref(v_cache_6537_);
lean_inc_ref(v_scope_6539_);
lean_inc_ref(v_service_6538_);
v___x_6630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6538_, v_scope_6539_, v_cache_6537_, v_force_6540_, v_descrs_6536_, v___x_6628_, v___x_6629_, v___x_6623_, v_a_6541_);
v___y_6611_ = v___x_6630_;
goto v___jp_6610_;
}
}
v___jp_6599_:
{
lean_object* v___x_6601_; uint8_t v___x_6602_; 
v___x_6601_ = lean_array_get_size(v_infos_6600_);
v___x_6602_ = lean_nat_dec_lt(v___x_6596_, v___x_6601_);
if (v___x_6602_ == 0)
{
lean_dec_ref(v_infos_6600_);
v_a_6566_ = v___x_6598_;
goto v___jp_6565_;
}
else
{
uint8_t v___x_6603_; 
v___x_6603_ = lean_nat_dec_le(v___x_6601_, v___x_6601_);
if (v___x_6603_ == 0)
{
if (v___x_6602_ == 0)
{
lean_dec_ref(v_infos_6600_);
v_a_6566_ = v___x_6598_;
goto v___jp_6565_;
}
else
{
size_t v___x_6604_; size_t v___x_6605_; lean_object* v___x_6606_; 
v___x_6604_ = ((size_t)0ULL);
v___x_6605_ = lean_usize_of_nat(v___x_6601_);
v___x_6606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6600_, v___x_6604_, v___x_6605_, v___x_6598_, v_a_6541_);
lean_dec_ref(v_infos_6600_);
v___y_6585_ = v___x_6606_;
goto v___jp_6584_;
}
}
else
{
size_t v___x_6607_; size_t v___x_6608_; lean_object* v___x_6609_; 
v___x_6607_ = ((size_t)0ULL);
v___x_6608_ = lean_usize_of_nat(v___x_6601_);
v___x_6609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6600_, v___x_6607_, v___x_6608_, v___x_6598_, v_a_6541_);
lean_dec_ref(v_infos_6600_);
v___y_6585_ = v___x_6609_;
goto v___jp_6584_;
}
}
}
v___jp_6610_:
{
if (lean_obj_tag(v___y_6611_) == 0)
{
lean_object* v_a_6612_; lean_object* v_infos_6613_; 
v_a_6612_ = lean_ctor_get(v___y_6611_, 0);
lean_inc(v_a_6612_);
lean_dec_ref_known(v___y_6611_, 1);
v_infos_6613_ = lean_ctor_get(v_a_6612_, 0);
lean_inc_ref(v_infos_6613_);
lean_dec(v_a_6612_);
v_infos_6600_ = v_infos_6613_;
goto v___jp_6599_;
}
else
{
lean_object* v_a_6614_; lean_object* v___x_6616_; uint8_t v_isShared_6617_; uint8_t v_isSharedCheck_6621_; 
lean_dec_ref(v_scope_6539_);
lean_dec_ref(v_service_6538_);
lean_dec_ref(v_cache_6537_);
v_a_6614_ = lean_ctor_get(v___y_6611_, 0);
v_isSharedCheck_6621_ = !lean_is_exclusive(v___y_6611_);
if (v_isSharedCheck_6621_ == 0)
{
v___x_6616_ = v___y_6611_;
v_isShared_6617_ = v_isSharedCheck_6621_;
goto v_resetjp_6615_;
}
else
{
lean_inc(v_a_6614_);
lean_dec(v___y_6611_);
v___x_6616_ = lean_box(0);
v_isShared_6617_ = v_isSharedCheck_6621_;
goto v_resetjp_6615_;
}
v_resetjp_6615_:
{
lean_object* v___x_6619_; 
if (v_isShared_6617_ == 0)
{
v___x_6619_ = v___x_6616_;
goto v_reusejp_6618_;
}
else
{
lean_object* v_reuseFailAlloc_6620_; 
v_reuseFailAlloc_6620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6620_, 0, v_a_6614_);
v___x_6619_ = v_reuseFailAlloc_6620_;
goto v_reusejp_6618_;
}
v_reusejp_6618_:
{
return v___x_6619_;
}
}
}
}
}
else
{
lean_object* v___x_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; 
lean_dec_ref(v_scope_6539_);
lean_dec_ref(v_service_6538_);
lean_dec_ref(v_cache_6537_);
v___x_6631_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__1));
lean_inc_ref(v_a_6541_);
v___x_6632_ = lean_apply_2(v_a_6541_, v___x_6631_, lean_box(0));
v___x_6633_ = lean_box(0);
v___x_6634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6634_, 0, v___x_6633_);
return v___x_6634_;
}
v___jp_6543_:
{
lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; 
v___x_6545_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6546_ = l_System_FilePath_join(v_cache_6537_, v___x_6545_);
v___x_6547_ = l_IO_FS_createDirAll(v___x_6546_);
if (lean_obj_tag(v___x_6547_) == 0)
{
uint8_t v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; 
lean_dec_ref_known(v___x_6547_, 1);
v___x_6548_ = 0;
v___x_6549_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6550_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6550_, 0, v_scope_6539_);
lean_ctor_set(v___x_6550_, 1, v_a_6544_);
lean_ctor_set(v___x_6550_, 2, v___x_6549_);
lean_ctor_set_uint8(v___x_6550_, sizeof(void*)*3, v___x_6548_);
v___x_6551_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6541_, v___x_6550_);
return v___x_6551_;
}
else
{
lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6564_; 
lean_dec_ref(v_a_6544_);
lean_dec_ref(v_scope_6539_);
v_a_6552_ = lean_ctor_get(v___x_6547_, 0);
v_isSharedCheck_6564_ = !lean_is_exclusive(v___x_6547_);
if (v_isSharedCheck_6564_ == 0)
{
v___x_6554_ = v___x_6547_;
v_isShared_6555_ = v_isSharedCheck_6564_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_dec(v___x_6547_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6564_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6556_; uint8_t v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6562_; 
v___x_6556_ = lean_io_error_to_string(v_a_6552_);
v___x_6557_ = 3;
v___x_6558_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6558_, 0, v___x_6556_);
lean_ctor_set_uint8(v___x_6558_, sizeof(void*)*1, v___x_6557_);
lean_inc_ref(v_a_6541_);
v___x_6559_ = lean_apply_2(v_a_6541_, v___x_6558_, lean_box(0));
v___x_6560_ = lean_box(0);
if (v_isShared_6555_ == 0)
{
lean_ctor_set(v___x_6554_, 0, v___x_6560_);
v___x_6562_ = v___x_6554_;
goto v_reusejp_6561_;
}
else
{
lean_object* v_reuseFailAlloc_6563_; 
v_reuseFailAlloc_6563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6563_, 0, v___x_6560_);
v___x_6562_ = v_reuseFailAlloc_6563_;
goto v_reusejp_6561_;
}
v_reusejp_6561_:
{
return v___x_6562_;
}
}
}
}
v___jp_6565_:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; uint8_t v___x_6569_; 
v___x_6567_ = lean_array_get_size(v_a_6566_);
v___x_6568_ = lean_unsigned_to_nat(0u);
v___x_6569_ = lean_nat_dec_eq(v___x_6567_, v___x_6568_);
if (v___x_6569_ == 0)
{
uint8_t v_isReservoir_6570_; 
v_isReservoir_6570_ = lean_ctor_get_uint8(v_service_6538_, sizeof(void*)*5);
if (v_isReservoir_6570_ == 0)
{
lean_dec_ref(v_service_6538_);
v_a_6544_ = v_a_6566_;
goto v___jp_6543_;
}
else
{
lean_object* v___x_6571_; lean_object* v___x_6572_; 
lean_inc_ref(v_scope_6539_);
v___x_6571_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6538_, v_scope_6539_);
v___x_6572_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6541_, v___x_6571_, v_a_6566_);
if (lean_obj_tag(v___x_6572_) == 0)
{
lean_object* v_a_6573_; 
v_a_6573_ = lean_ctor_get(v___x_6572_, 0);
lean_inc(v_a_6573_);
lean_dec_ref_known(v___x_6572_, 1);
v_a_6544_ = v_a_6573_;
goto v___jp_6543_;
}
else
{
lean_object* v_a_6574_; lean_object* v___x_6576_; uint8_t v_isShared_6577_; uint8_t v_isSharedCheck_6581_; 
lean_dec_ref(v_scope_6539_);
lean_dec_ref(v_cache_6537_);
v_a_6574_ = lean_ctor_get(v___x_6572_, 0);
v_isSharedCheck_6581_ = !lean_is_exclusive(v___x_6572_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6576_ = v___x_6572_;
v_isShared_6577_ = v_isSharedCheck_6581_;
goto v_resetjp_6575_;
}
else
{
lean_inc(v_a_6574_);
lean_dec(v___x_6572_);
v___x_6576_ = lean_box(0);
v_isShared_6577_ = v_isSharedCheck_6581_;
goto v_resetjp_6575_;
}
v_resetjp_6575_:
{
lean_object* v___x_6579_; 
if (v_isShared_6577_ == 0)
{
v___x_6579_ = v___x_6576_;
goto v_reusejp_6578_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6574_);
v___x_6579_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6578_;
}
v_reusejp_6578_:
{
return v___x_6579_;
}
}
}
}
}
else
{
lean_object* v___x_6582_; lean_object* v___x_6583_; 
lean_dec_ref(v_a_6566_);
lean_dec_ref(v_scope_6539_);
lean_dec_ref(v_service_6538_);
lean_dec_ref(v_cache_6537_);
v___x_6582_ = lean_box(0);
v___x_6583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6583_, 0, v___x_6582_);
return v___x_6583_;
}
}
v___jp_6584_:
{
if (lean_obj_tag(v___y_6585_) == 0)
{
lean_object* v_a_6586_; 
v_a_6586_ = lean_ctor_get(v___y_6585_, 0);
lean_inc(v_a_6586_);
lean_dec_ref_known(v___y_6585_, 1);
v_a_6566_ = v_a_6586_;
goto v___jp_6565_;
}
else
{
lean_object* v_a_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6594_; 
lean_dec_ref(v_scope_6539_);
lean_dec_ref(v_service_6538_);
lean_dec_ref(v_cache_6537_);
v_a_6587_ = lean_ctor_get(v___y_6585_, 0);
v_isSharedCheck_6594_ = !lean_is_exclusive(v___y_6585_);
if (v_isSharedCheck_6594_ == 0)
{
v___x_6589_ = v___y_6585_;
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_a_6587_);
lean_dec(v___y_6585_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v___x_6592_; 
if (v_isShared_6590_ == 0)
{
v___x_6592_ = v___x_6589_;
goto v_reusejp_6591_;
}
else
{
lean_object* v_reuseFailAlloc_6593_; 
v_reuseFailAlloc_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
v___x_6592_ = v_reuseFailAlloc_6593_;
goto v_reusejp_6591_;
}
v_reusejp_6591_:
{
return v___x_6592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_6635_, lean_object* v_cache_6636_, lean_object* v_service_6637_, lean_object* v_scope_6638_, lean_object* v_force_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_){
_start:
{
uint8_t v_force_boxed_6642_; lean_object* v_res_6643_; 
v_force_boxed_6642_ = lean_unbox(v_force_6639_);
v_res_6643_ = l_Lake_CacheService_downloadArtifacts(v_descrs_6635_, v_cache_6636_, v_service_6637_, v_scope_6638_, v_force_boxed_6642_, v_a_6640_);
lean_dec_ref(v_a_6640_);
lean_dec_ref(v_descrs_6635_);
return v_res_6643_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_6644_, lean_object* v_descrs_6645_, lean_object* v_cache_6646_, lean_object* v_service_6647_, lean_object* v_scope_6648_, uint8_t v_force_6649_){
_start:
{
lean_object* v_a_6652_; lean_object* v_a_6674_; lean_object* v___y_6693_; lean_object* v___x_6703_; lean_object* v___x_6704_; uint8_t v___x_6705_; 
v___x_6703_ = lean_array_get_size(v_descrs_6645_);
v___x_6704_ = lean_unsigned_to_nat(0u);
v___x_6705_ = lean_nat_dec_eq(v___x_6703_, v___x_6704_);
if (v___x_6705_ == 0)
{
lean_object* v___x_6706_; lean_object* v_infos_6708_; lean_object* v___y_6719_; uint8_t v___x_6730_; 
v___x_6706_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_6730_ = lean_nat_dec_lt(v___x_6704_, v___x_6703_);
if (v___x_6730_ == 0)
{
v_infos_6708_ = v___x_6706_;
goto v___jp_6707_;
}
else
{
lean_object* v___x_6731_; uint8_t v___x_6732_; 
v___x_6731_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
v___x_6732_ = lean_nat_dec_le(v___x_6703_, v___x_6703_);
if (v___x_6732_ == 0)
{
if (v___x_6730_ == 0)
{
v_infos_6708_ = v___x_6706_;
goto v___jp_6707_;
}
else
{
size_t v___x_6733_; size_t v___x_6734_; lean_object* v___x_6735_; 
v___x_6733_ = ((size_t)0ULL);
v___x_6734_ = lean_usize_of_nat(v___x_6703_);
lean_inc_ref(v_cache_6646_);
lean_inc_ref(v_scope_6648_);
lean_inc_ref(v_service_6647_);
v___x_6735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6647_, v_scope_6648_, v_cache_6646_, v_force_6649_, v_descrs_6645_, v___x_6733_, v___x_6734_, v___x_6731_, v_a_6644_);
v___y_6719_ = v___x_6735_;
goto v___jp_6718_;
}
}
else
{
size_t v___x_6736_; size_t v___x_6737_; lean_object* v___x_6738_; 
v___x_6736_ = ((size_t)0ULL);
v___x_6737_ = lean_usize_of_nat(v___x_6703_);
lean_inc_ref(v_cache_6646_);
lean_inc_ref(v_scope_6648_);
lean_inc_ref(v_service_6647_);
v___x_6738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6647_, v_scope_6648_, v_cache_6646_, v_force_6649_, v_descrs_6645_, v___x_6736_, v___x_6737_, v___x_6731_, v_a_6644_);
v___y_6719_ = v___x_6738_;
goto v___jp_6718_;
}
}
v___jp_6707_:
{
lean_object* v___x_6709_; uint8_t v___x_6710_; 
v___x_6709_ = lean_array_get_size(v_infos_6708_);
v___x_6710_ = lean_nat_dec_lt(v___x_6704_, v___x_6709_);
if (v___x_6710_ == 0)
{
lean_dec_ref(v_infos_6708_);
v_a_6674_ = v___x_6706_;
goto v___jp_6673_;
}
else
{
uint8_t v___x_6711_; 
v___x_6711_ = lean_nat_dec_le(v___x_6709_, v___x_6709_);
if (v___x_6711_ == 0)
{
if (v___x_6710_ == 0)
{
lean_dec_ref(v_infos_6708_);
v_a_6674_ = v___x_6706_;
goto v___jp_6673_;
}
else
{
size_t v___x_6712_; size_t v___x_6713_; lean_object* v___x_6714_; 
v___x_6712_ = ((size_t)0ULL);
v___x_6713_ = lean_usize_of_nat(v___x_6709_);
v___x_6714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6708_, v___x_6712_, v___x_6713_, v___x_6706_, v_a_6644_);
lean_dec_ref(v_infos_6708_);
v___y_6693_ = v___x_6714_;
goto v___jp_6692_;
}
}
else
{
size_t v___x_6715_; size_t v___x_6716_; lean_object* v___x_6717_; 
v___x_6715_ = ((size_t)0ULL);
v___x_6716_ = lean_usize_of_nat(v___x_6709_);
v___x_6717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6708_, v___x_6715_, v___x_6716_, v___x_6706_, v_a_6644_);
lean_dec_ref(v_infos_6708_);
v___y_6693_ = v___x_6717_;
goto v___jp_6692_;
}
}
}
v___jp_6718_:
{
if (lean_obj_tag(v___y_6719_) == 0)
{
lean_object* v_a_6720_; lean_object* v_infos_6721_; 
v_a_6720_ = lean_ctor_get(v___y_6719_, 0);
lean_inc(v_a_6720_);
lean_dec_ref_known(v___y_6719_, 1);
v_infos_6721_ = lean_ctor_get(v_a_6720_, 0);
lean_inc_ref(v_infos_6721_);
lean_dec(v_a_6720_);
v_infos_6708_ = v_infos_6721_;
goto v___jp_6707_;
}
else
{
lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6729_; 
lean_dec_ref(v_scope_6648_);
lean_dec_ref(v_service_6647_);
lean_dec_ref(v_cache_6646_);
v_a_6722_ = lean_ctor_get(v___y_6719_, 0);
v_isSharedCheck_6729_ = !lean_is_exclusive(v___y_6719_);
if (v_isSharedCheck_6729_ == 0)
{
v___x_6724_ = v___y_6719_;
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_dec(v___y_6719_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6727_; 
if (v_isShared_6725_ == 0)
{
v___x_6727_ = v___x_6724_;
goto v_reusejp_6726_;
}
else
{
lean_object* v_reuseFailAlloc_6728_; 
v_reuseFailAlloc_6728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6728_, 0, v_a_6722_);
v___x_6727_ = v_reuseFailAlloc_6728_;
goto v_reusejp_6726_;
}
v_reusejp_6726_:
{
return v___x_6727_;
}
}
}
}
}
else
{
lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; 
lean_dec_ref(v_scope_6648_);
lean_dec_ref(v_service_6647_);
lean_dec_ref(v_cache_6646_);
v___x_6739_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__1));
lean_inc_ref(v_a_6644_);
v___x_6740_ = lean_apply_2(v_a_6644_, v___x_6739_, lean_box(0));
v___x_6741_ = lean_box(0);
v___x_6742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6742_, 0, v___x_6741_);
return v___x_6742_;
}
v___jp_6651_:
{
lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; 
v___x_6653_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6654_ = l_System_FilePath_join(v_cache_6646_, v___x_6653_);
v___x_6655_ = l_IO_FS_createDirAll(v___x_6654_);
if (lean_obj_tag(v___x_6655_) == 0)
{
uint8_t v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; 
lean_dec_ref_known(v___x_6655_, 1);
v___x_6656_ = 0;
v___x_6657_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6658_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6658_, 0, v_scope_6648_);
lean_ctor_set(v___x_6658_, 1, v_a_6652_);
lean_ctor_set(v___x_6658_, 2, v___x_6657_);
lean_ctor_set_uint8(v___x_6658_, sizeof(void*)*3, v___x_6656_);
v___x_6659_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6644_, v___x_6658_);
return v___x_6659_;
}
else
{
lean_object* v_a_6660_; lean_object* v___x_6662_; uint8_t v_isShared_6663_; uint8_t v_isSharedCheck_6672_; 
lean_dec_ref(v_a_6652_);
lean_dec_ref(v_scope_6648_);
v_a_6660_ = lean_ctor_get(v___x_6655_, 0);
v_isSharedCheck_6672_ = !lean_is_exclusive(v___x_6655_);
if (v_isSharedCheck_6672_ == 0)
{
v___x_6662_ = v___x_6655_;
v_isShared_6663_ = v_isSharedCheck_6672_;
goto v_resetjp_6661_;
}
else
{
lean_inc(v_a_6660_);
lean_dec(v___x_6655_);
v___x_6662_ = lean_box(0);
v_isShared_6663_ = v_isSharedCheck_6672_;
goto v_resetjp_6661_;
}
v_resetjp_6661_:
{
lean_object* v___x_6664_; uint8_t v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6670_; 
v___x_6664_ = lean_io_error_to_string(v_a_6660_);
v___x_6665_ = 3;
v___x_6666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6666_, 0, v___x_6664_);
lean_ctor_set_uint8(v___x_6666_, sizeof(void*)*1, v___x_6665_);
lean_inc_ref(v_a_6644_);
v___x_6667_ = lean_apply_2(v_a_6644_, v___x_6666_, lean_box(0));
v___x_6668_ = lean_box(0);
if (v_isShared_6663_ == 0)
{
lean_ctor_set(v___x_6662_, 0, v___x_6668_);
v___x_6670_ = v___x_6662_;
goto v_reusejp_6669_;
}
else
{
lean_object* v_reuseFailAlloc_6671_; 
v_reuseFailAlloc_6671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6671_, 0, v___x_6668_);
v___x_6670_ = v_reuseFailAlloc_6671_;
goto v_reusejp_6669_;
}
v_reusejp_6669_:
{
return v___x_6670_;
}
}
}
}
v___jp_6673_:
{
lean_object* v___x_6675_; lean_object* v___x_6676_; uint8_t v___x_6677_; 
v___x_6675_ = lean_array_get_size(v_a_6674_);
v___x_6676_ = lean_unsigned_to_nat(0u);
v___x_6677_ = lean_nat_dec_eq(v___x_6675_, v___x_6676_);
if (v___x_6677_ == 0)
{
uint8_t v_isReservoir_6678_; 
v_isReservoir_6678_ = lean_ctor_get_uint8(v_service_6647_, sizeof(void*)*5);
if (v_isReservoir_6678_ == 0)
{
lean_dec_ref(v_service_6647_);
v_a_6652_ = v_a_6674_;
goto v___jp_6651_;
}
else
{
lean_object* v___x_6679_; lean_object* v___x_6680_; 
lean_inc_ref(v_scope_6648_);
v___x_6679_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6647_, v_scope_6648_);
v___x_6680_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6644_, v___x_6679_, v_a_6674_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v_a_6681_; 
v_a_6681_ = lean_ctor_get(v___x_6680_, 0);
lean_inc(v_a_6681_);
lean_dec_ref_known(v___x_6680_, 1);
v_a_6652_ = v_a_6681_;
goto v___jp_6651_;
}
else
{
lean_object* v_a_6682_; lean_object* v___x_6684_; uint8_t v_isShared_6685_; uint8_t v_isSharedCheck_6689_; 
lean_dec_ref(v_scope_6648_);
lean_dec_ref(v_cache_6646_);
v_a_6682_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6689_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6689_ == 0)
{
v___x_6684_ = v___x_6680_;
v_isShared_6685_ = v_isSharedCheck_6689_;
goto v_resetjp_6683_;
}
else
{
lean_inc(v_a_6682_);
lean_dec(v___x_6680_);
v___x_6684_ = lean_box(0);
v_isShared_6685_ = v_isSharedCheck_6689_;
goto v_resetjp_6683_;
}
v_resetjp_6683_:
{
lean_object* v___x_6687_; 
if (v_isShared_6685_ == 0)
{
v___x_6687_ = v___x_6684_;
goto v_reusejp_6686_;
}
else
{
lean_object* v_reuseFailAlloc_6688_; 
v_reuseFailAlloc_6688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6688_, 0, v_a_6682_);
v___x_6687_ = v_reuseFailAlloc_6688_;
goto v_reusejp_6686_;
}
v_reusejp_6686_:
{
return v___x_6687_;
}
}
}
}
}
else
{
lean_object* v___x_6690_; lean_object* v___x_6691_; 
lean_dec_ref(v_a_6674_);
lean_dec_ref(v_scope_6648_);
lean_dec_ref(v_service_6647_);
lean_dec_ref(v_cache_6646_);
v___x_6690_ = lean_box(0);
v___x_6691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6691_, 0, v___x_6690_);
return v___x_6691_;
}
}
v___jp_6692_:
{
if (lean_obj_tag(v___y_6693_) == 0)
{
lean_object* v_a_6694_; 
v_a_6694_ = lean_ctor_get(v___y_6693_, 0);
lean_inc(v_a_6694_);
lean_dec_ref_known(v___y_6693_, 1);
v_a_6674_ = v_a_6694_;
goto v___jp_6673_;
}
else
{
lean_object* v_a_6695_; lean_object* v___x_6697_; uint8_t v_isShared_6698_; uint8_t v_isSharedCheck_6702_; 
lean_dec_ref(v_scope_6648_);
lean_dec_ref(v_service_6647_);
lean_dec_ref(v_cache_6646_);
v_a_6695_ = lean_ctor_get(v___y_6693_, 0);
v_isSharedCheck_6702_ = !lean_is_exclusive(v___y_6693_);
if (v_isSharedCheck_6702_ == 0)
{
v___x_6697_ = v___y_6693_;
v_isShared_6698_ = v_isSharedCheck_6702_;
goto v_resetjp_6696_;
}
else
{
lean_inc(v_a_6695_);
lean_dec(v___y_6693_);
v___x_6697_ = lean_box(0);
v_isShared_6698_ = v_isSharedCheck_6702_;
goto v_resetjp_6696_;
}
v_resetjp_6696_:
{
lean_object* v___x_6700_; 
if (v_isShared_6698_ == 0)
{
v___x_6700_ = v___x_6697_;
goto v_reusejp_6699_;
}
else
{
lean_object* v_reuseFailAlloc_6701_; 
v_reuseFailAlloc_6701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6701_, 0, v_a_6695_);
v___x_6700_ = v_reuseFailAlloc_6701_;
goto v_reusejp_6699_;
}
v_reusejp_6699_:
{
return v___x_6700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_6743_, lean_object* v_descrs_6744_, lean_object* v_cache_6745_, lean_object* v_service_6746_, lean_object* v_scope_6747_, lean_object* v_force_6748_, lean_object* v_a_6749_){
_start:
{
uint8_t v_force_boxed_6750_; lean_object* v_res_6751_; 
v_force_boxed_6750_ = lean_unbox(v_force_6748_);
v_res_6751_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6743_, v_descrs_6744_, v_cache_6745_, v_service_6746_, v_scope_6747_, v_force_boxed_6750_);
lean_dec_ref(v_descrs_6744_);
lean_dec_ref(v_a_6743_);
return v_res_6751_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_6752_, lean_object* v_cache_6753_, lean_object* v_service_6754_, lean_object* v_localScope_6755_, lean_object* v_remoteScope_6756_, uint8_t v_force_6757_, lean_object* v_a_6758_){
_start:
{
lean_object* v_name_x3f_6763_; lean_object* v___x_6764_; uint8_t v___x_6765_; lean_object* v___x_6766_; 
v_name_x3f_6763_ = lean_ctor_get(v_service_6754_, 0);
lean_inc_ref(v_remoteScope_6756_);
v___x_6764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6764_, 0, v_remoteScope_6756_);
v___x_6765_ = 1;
lean_inc(v_name_x3f_6763_);
lean_inc_ref(v_cache_6753_);
v___x_6766_ = l_Lake_Cache_writeMap(v_cache_6753_, v_localScope_6755_, v_map_6752_, v_name_x3f_6763_, v___x_6764_, v___x_6765_);
if (lean_obj_tag(v___x_6766_) == 0)
{
lean_object* v___x_6768_; uint8_t v_isShared_6769_; uint8_t v_isSharedCheck_6804_; 
v_isSharedCheck_6804_ = !lean_is_exclusive(v___x_6766_);
if (v_isSharedCheck_6804_ == 0)
{
lean_object* v_unused_6805_; 
v_unused_6805_ = lean_ctor_get(v___x_6766_, 0);
lean_dec(v_unused_6805_);
v___x_6768_ = v___x_6766_;
v_isShared_6769_ = v_isSharedCheck_6804_;
goto v_resetjp_6767_;
}
else
{
lean_dec(v___x_6766_);
v___x_6768_ = lean_box(0);
v_isShared_6769_ = v_isSharedCheck_6804_;
goto v_resetjp_6767_;
}
v_resetjp_6767_:
{
lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; 
v___x_6770_ = lean_unsigned_to_nat(0u);
v___x_6771_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6772_ = l_Lake_CacheMap_collectOutputDescrs(v_map_6752_, v___x_6771_);
if (lean_obj_tag(v___x_6772_) == 0)
{
lean_object* v_a_6773_; lean_object* v_a_6774_; lean_object* v___x_6775_; uint8_t v___x_6776_; 
lean_del_object(v___x_6768_);
v_a_6773_ = lean_ctor_get(v___x_6772_, 0);
lean_inc(v_a_6773_);
v_a_6774_ = lean_ctor_get(v___x_6772_, 1);
lean_inc(v_a_6774_);
lean_dec_ref_known(v___x_6772_, 2);
v___x_6775_ = lean_array_get_size(v_a_6774_);
v___x_6776_ = lean_nat_dec_lt(v___x_6770_, v___x_6775_);
if (v___x_6776_ == 0)
{
lean_object* v___x_6777_; 
lean_dec(v_a_6774_);
v___x_6777_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6758_, v_a_6773_, v_cache_6753_, v_service_6754_, v_remoteScope_6756_, v_force_6757_);
lean_dec(v_a_6773_);
return v___x_6777_;
}
else
{
lean_object* v___x_6778_; uint8_t v___x_6779_; 
v___x_6778_ = lean_box(0);
v___x_6779_ = lean_nat_dec_le(v___x_6775_, v___x_6775_);
if (v___x_6779_ == 0)
{
if (v___x_6776_ == 0)
{
lean_object* v___x_6780_; 
lean_dec(v_a_6774_);
v___x_6780_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6758_, v_a_6773_, v_cache_6753_, v_service_6754_, v_remoteScope_6756_, v_force_6757_);
lean_dec(v_a_6773_);
return v___x_6780_;
}
else
{
size_t v___x_6781_; size_t v___x_6782_; lean_object* v___x_6783_; 
v___x_6781_ = ((size_t)0ULL);
v___x_6782_ = lean_usize_of_nat(v___x_6775_);
v___x_6783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6774_, v___x_6781_, v___x_6782_, v___x_6778_, v_a_6758_);
lean_dec(v_a_6774_);
if (lean_obj_tag(v___x_6783_) == 0)
{
lean_object* v___x_6784_; 
lean_dec_ref_known(v___x_6783_, 1);
v___x_6784_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6758_, v_a_6773_, v_cache_6753_, v_service_6754_, v_remoteScope_6756_, v_force_6757_);
lean_dec(v_a_6773_);
return v___x_6784_;
}
else
{
lean_dec(v_a_6773_);
lean_dec_ref(v_remoteScope_6756_);
lean_dec_ref(v_service_6754_);
lean_dec_ref(v_cache_6753_);
return v___x_6783_;
}
}
}
else
{
size_t v___x_6785_; size_t v___x_6786_; lean_object* v___x_6787_; 
v___x_6785_ = ((size_t)0ULL);
v___x_6786_ = lean_usize_of_nat(v___x_6775_);
v___x_6787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6774_, v___x_6785_, v___x_6786_, v___x_6778_, v_a_6758_);
lean_dec(v_a_6774_);
if (lean_obj_tag(v___x_6787_) == 0)
{
lean_object* v___x_6788_; 
lean_dec_ref_known(v___x_6787_, 1);
v___x_6788_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6758_, v_a_6773_, v_cache_6753_, v_service_6754_, v_remoteScope_6756_, v_force_6757_);
lean_dec(v_a_6773_);
return v___x_6788_;
}
else
{
lean_dec(v_a_6773_);
lean_dec_ref(v_remoteScope_6756_);
lean_dec_ref(v_service_6754_);
lean_dec_ref(v_cache_6753_);
return v___x_6787_;
}
}
}
}
else
{
lean_object* v_a_6789_; lean_object* v___x_6790_; uint8_t v___x_6791_; 
lean_dec_ref(v_remoteScope_6756_);
lean_dec_ref(v_service_6754_);
lean_dec_ref(v_cache_6753_);
v_a_6789_ = lean_ctor_get(v___x_6772_, 1);
lean_inc(v_a_6789_);
lean_dec_ref_known(v___x_6772_, 2);
v___x_6790_ = lean_array_get_size(v_a_6789_);
v___x_6791_ = lean_nat_dec_lt(v___x_6770_, v___x_6790_);
if (v___x_6791_ == 0)
{
lean_object* v___x_6792_; lean_object* v___x_6794_; 
lean_dec(v_a_6789_);
v___x_6792_ = lean_box(0);
if (v_isShared_6769_ == 0)
{
lean_ctor_set_tag(v___x_6768_, 1);
lean_ctor_set(v___x_6768_, 0, v___x_6792_);
v___x_6794_ = v___x_6768_;
goto v_reusejp_6793_;
}
else
{
lean_object* v_reuseFailAlloc_6795_; 
v_reuseFailAlloc_6795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6795_, 0, v___x_6792_);
v___x_6794_ = v_reuseFailAlloc_6795_;
goto v_reusejp_6793_;
}
v_reusejp_6793_:
{
return v___x_6794_;
}
}
else
{
lean_object* v___x_6796_; uint8_t v___x_6797_; 
lean_del_object(v___x_6768_);
v___x_6796_ = lean_box(0);
v___x_6797_ = lean_nat_dec_le(v___x_6790_, v___x_6790_);
if (v___x_6797_ == 0)
{
if (v___x_6791_ == 0)
{
lean_dec(v_a_6789_);
goto v___jp_6760_;
}
else
{
size_t v___x_6798_; size_t v___x_6799_; lean_object* v___x_6800_; 
v___x_6798_ = ((size_t)0ULL);
v___x_6799_ = lean_usize_of_nat(v___x_6790_);
v___x_6800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6789_, v___x_6798_, v___x_6799_, v___x_6796_, v_a_6758_);
lean_dec(v_a_6789_);
if (lean_obj_tag(v___x_6800_) == 0)
{
lean_dec_ref_known(v___x_6800_, 1);
goto v___jp_6760_;
}
else
{
return v___x_6800_;
}
}
}
else
{
size_t v___x_6801_; size_t v___x_6802_; lean_object* v___x_6803_; 
v___x_6801_ = ((size_t)0ULL);
v___x_6802_ = lean_usize_of_nat(v___x_6790_);
v___x_6803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6789_, v___x_6801_, v___x_6802_, v___x_6796_, v_a_6758_);
lean_dec(v_a_6789_);
if (lean_obj_tag(v___x_6803_) == 0)
{
lean_dec_ref_known(v___x_6803_, 1);
goto v___jp_6760_;
}
else
{
return v___x_6803_;
}
}
}
}
}
}
else
{
lean_object* v_a_6806_; lean_object* v___x_6808_; uint8_t v_isShared_6809_; uint8_t v_isSharedCheck_6818_; 
lean_dec_ref(v_remoteScope_6756_);
lean_dec_ref(v_service_6754_);
lean_dec_ref(v_cache_6753_);
lean_dec_ref(v_map_6752_);
v_a_6806_ = lean_ctor_get(v___x_6766_, 0);
v_isSharedCheck_6818_ = !lean_is_exclusive(v___x_6766_);
if (v_isSharedCheck_6818_ == 0)
{
v___x_6808_ = v___x_6766_;
v_isShared_6809_ = v_isSharedCheck_6818_;
goto v_resetjp_6807_;
}
else
{
lean_inc(v_a_6806_);
lean_dec(v___x_6766_);
v___x_6808_ = lean_box(0);
v_isShared_6809_ = v_isSharedCheck_6818_;
goto v_resetjp_6807_;
}
v_resetjp_6807_:
{
lean_object* v___x_6810_; uint8_t v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6816_; 
v___x_6810_ = lean_io_error_to_string(v_a_6806_);
v___x_6811_ = 3;
v___x_6812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6812_, 0, v___x_6810_);
lean_ctor_set_uint8(v___x_6812_, sizeof(void*)*1, v___x_6811_);
lean_inc_ref(v_a_6758_);
v___x_6813_ = lean_apply_2(v_a_6758_, v___x_6812_, lean_box(0));
v___x_6814_ = lean_box(0);
if (v_isShared_6809_ == 0)
{
lean_ctor_set(v___x_6808_, 0, v___x_6814_);
v___x_6816_ = v___x_6808_;
goto v_reusejp_6815_;
}
else
{
lean_object* v_reuseFailAlloc_6817_; 
v_reuseFailAlloc_6817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6817_, 0, v___x_6814_);
v___x_6816_ = v_reuseFailAlloc_6817_;
goto v_reusejp_6815_;
}
v_reusejp_6815_:
{
return v___x_6816_;
}
}
}
v___jp_6760_:
{
lean_object* v___x_6761_; lean_object* v___x_6762_; 
v___x_6761_ = lean_box(0);
v___x_6762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6762_, 0, v___x_6761_);
return v___x_6762_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_6819_, lean_object* v_cache_6820_, lean_object* v_service_6821_, lean_object* v_localScope_6822_, lean_object* v_remoteScope_6823_, lean_object* v_force_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_){
_start:
{
uint8_t v_force_boxed_6827_; lean_object* v_res_6828_; 
v_force_boxed_6827_ = lean_unbox(v_force_6824_);
v_res_6828_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_6819_, v_cache_6820_, v_service_6821_, v_localScope_6822_, v_remoteScope_6823_, v_force_boxed_6827_, v_a_6825_);
lean_dec_ref(v_a_6825_);
return v_res_6828_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* v_m_6829_, uint64_t v_a_6830_){
_start:
{
lean_object* v_buckets_6831_; lean_object* v___x_6832_; uint64_t v___x_6833_; uint64_t v___x_6834_; uint64_t v_fold_6835_; uint64_t v___x_6836_; uint64_t v___x_6837_; uint64_t v___x_6838_; size_t v___x_6839_; size_t v___x_6840_; size_t v___x_6841_; size_t v___x_6842_; size_t v___x_6843_; lean_object* v___x_6844_; uint8_t v___x_6845_; 
v_buckets_6831_ = lean_ctor_get(v_m_6829_, 1);
v___x_6832_ = lean_array_get_size(v_buckets_6831_);
v___x_6833_ = 32ULL;
v___x_6834_ = lean_uint64_shift_right(v_a_6830_, v___x_6833_);
v_fold_6835_ = lean_uint64_xor(v_a_6830_, v___x_6834_);
v___x_6836_ = 16ULL;
v___x_6837_ = lean_uint64_shift_right(v_fold_6835_, v___x_6836_);
v___x_6838_ = lean_uint64_xor(v_fold_6835_, v___x_6837_);
v___x_6839_ = lean_uint64_to_usize(v___x_6838_);
v___x_6840_ = lean_usize_of_nat(v___x_6832_);
v___x_6841_ = ((size_t)1ULL);
v___x_6842_ = lean_usize_sub(v___x_6840_, v___x_6841_);
v___x_6843_ = lean_usize_land(v___x_6839_, v___x_6842_);
v___x_6844_ = lean_array_uget_borrowed(v_buckets_6831_, v___x_6843_);
v___x_6845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_6830_, v___x_6844_);
return v___x_6845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* v_m_6846_, lean_object* v_a_6847_){
_start:
{
uint64_t v_a_boxed_6848_; uint8_t v_res_6849_; lean_object* v_r_6850_; 
v_a_boxed_6848_ = lean_unbox_uint64(v_a_6847_);
lean_dec_ref(v_a_6847_);
v_res_6849_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_m_6846_, v_a_boxed_6848_);
lean_dec_ref(v_m_6846_);
v_r_6850_ = lean_box(v_res_6849_);
return v_r_6850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(lean_object* v_descrs_6851_, lean_object* v_service_6852_, lean_object* v_scope_6853_, lean_object* v_paths_6854_, lean_object* v_n_6855_, lean_object* v_i_6856_, lean_object* v_a_6857_){
_start:
{
lean_object* v_zero_6859_; uint8_t v_isZero_6860_; 
v_zero_6859_ = lean_unsigned_to_nat(0u);
v_isZero_6860_ = lean_nat_dec_eq(v_i_6856_, v_zero_6859_);
if (v_isZero_6860_ == 1)
{
lean_object* v___x_6861_; 
lean_dec(v_i_6856_);
lean_dec_ref(v_scope_6853_);
lean_dec_ref(v_service_6852_);
v___x_6861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6861_, 0, v_a_6857_);
return v___x_6861_;
}
else
{
lean_object* v_one_6862_; lean_object* v_n_6863_; lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; uint64_t v_hash_6867_; lean_object* v_infos_6868_; lean_object* v_indices_6869_; lean_object* v_url_6870_; uint8_t v___x_6871_; 
v_one_6862_ = lean_unsigned_to_nat(1u);
v_n_6863_ = lean_nat_sub(v_i_6856_, v_one_6862_);
lean_dec(v_i_6856_);
v___x_6864_ = lean_nat_sub(v_n_6855_, v_n_6863_);
v___x_6865_ = lean_nat_sub(v___x_6864_, v_one_6862_);
lean_dec(v___x_6864_);
v___x_6866_ = lean_array_fget_borrowed(v_descrs_6851_, v___x_6865_);
v_hash_6867_ = lean_ctor_get_uint64(v___x_6866_, sizeof(void*)*1);
v_infos_6868_ = lean_ctor_get(v_a_6857_, 0);
v_indices_6869_ = lean_ctor_get(v_a_6857_, 1);
lean_inc_ref(v_scope_6853_);
lean_inc_ref(v_service_6852_);
v_url_6870_ = l_Lake_CacheService_artifactUrl(v_hash_6867_, v_service_6852_, v_scope_6853_);
v___x_6871_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_indices_6869_, v_hash_6867_);
if (v___x_6871_ == 0)
{
lean_object* v___x_6873_; uint8_t v_isShared_6874_; uint8_t v_isSharedCheck_6885_; 
lean_inc_ref(v_indices_6869_);
lean_inc_ref(v_infos_6868_);
v_isSharedCheck_6885_ = !lean_is_exclusive(v_a_6857_);
if (v_isSharedCheck_6885_ == 0)
{
lean_object* v_unused_6886_; lean_object* v_unused_6887_; 
v_unused_6886_ = lean_ctor_get(v_a_6857_, 1);
lean_dec(v_unused_6886_);
v_unused_6887_ = lean_ctor_get(v_a_6857_, 0);
lean_dec(v_unused_6887_);
v___x_6873_ = v_a_6857_;
v_isShared_6874_ = v_isSharedCheck_6885_;
goto v_resetjp_6872_;
}
else
{
lean_dec(v_a_6857_);
v___x_6873_ = lean_box(0);
v_isShared_6874_ = v_isSharedCheck_6885_;
goto v_resetjp_6872_;
}
v_resetjp_6872_:
{
lean_object* v___x_6875_; lean_object* v___x_6876_; lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v___x_6879_; lean_object* v___x_6880_; lean_object* v___x_6882_; 
v___x_6875_ = lean_array_fget_borrowed(v_paths_6854_, v___x_6865_);
lean_dec(v___x_6865_);
v___x_6876_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc(v___x_6875_);
v___x_6877_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6877_, 0, v_url_6870_);
lean_ctor_set(v___x_6877_, 1, v___x_6875_);
lean_ctor_set(v___x_6877_, 2, v___x_6876_);
lean_ctor_set_uint64(v___x_6877_, sizeof(void*)*3, v_hash_6867_);
lean_inc_ref(v_infos_6868_);
v___x_6878_ = lean_array_push(v_infos_6868_, v___x_6877_);
v___x_6879_ = lean_array_get_size(v_infos_6868_);
lean_dec_ref(v_infos_6868_);
v___x_6880_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6869_, v_hash_6867_, v___x_6879_);
if (v_isShared_6874_ == 0)
{
lean_ctor_set(v___x_6873_, 1, v___x_6880_);
lean_ctor_set(v___x_6873_, 0, v___x_6878_);
v___x_6882_ = v___x_6873_;
goto v_reusejp_6881_;
}
else
{
lean_object* v_reuseFailAlloc_6884_; 
v_reuseFailAlloc_6884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6884_, 0, v___x_6878_);
lean_ctor_set(v_reuseFailAlloc_6884_, 1, v___x_6880_);
v___x_6882_ = v_reuseFailAlloc_6884_;
goto v_reusejp_6881_;
}
v_reusejp_6881_:
{
v_i_6856_ = v_n_6863_;
v_a_6857_ = v___x_6882_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_url_6870_);
lean_dec(v___x_6865_);
v_i_6856_ = v_n_6863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg___boxed(lean_object* v_descrs_6889_, lean_object* v_service_6890_, lean_object* v_scope_6891_, lean_object* v_paths_6892_, lean_object* v_n_6893_, lean_object* v_i_6894_, lean_object* v_a_6895_, lean_object* v___y_6896_){
_start:
{
lean_object* v_res_6897_; 
v_res_6897_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_6889_, v_service_6890_, v_scope_6891_, v_paths_6892_, v_n_6893_, v_i_6894_, v_a_6895_);
lean_dec(v_n_6893_);
lean_dec_ref(v_paths_6892_);
lean_dec_ref(v_descrs_6889_);
return v_res_6897_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_6902_, lean_object* v_descrs_6903_, lean_object* v_paths_6904_, lean_object* v_service_6905_, lean_object* v_scope_6906_, lean_object* v_a_6907_){
_start:
{
lean_object* v___x_6909_; uint8_t v___x_6910_; 
v___x_6909_ = lean_unsigned_to_nat(0u);
v___x_6910_ = lean_nat_dec_eq(v_n_6902_, v___x_6909_);
if (v___x_6910_ == 0)
{
lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v_a_6913_; lean_object* v_infos_6914_; lean_object* v_key_6915_; uint8_t v___x_6916_; lean_object* v___x_6917_; lean_object* v___x_6918_; 
v___x_6911_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
lean_inc(v_n_6902_);
lean_inc_ref(v_scope_6906_);
lean_inc_ref(v_service_6905_);
v___x_6912_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_6903_, v_service_6905_, v_scope_6906_, v_paths_6904_, v_n_6902_, v_n_6902_, v___x_6911_);
lean_dec(v_n_6902_);
v_a_6913_ = lean_ctor_get(v___x_6912_, 0);
lean_inc(v_a_6913_);
lean_dec_ref(v___x_6912_);
v_infos_6914_ = lean_ctor_get(v_a_6913_, 0);
lean_inc_ref(v_infos_6914_);
lean_dec(v_a_6913_);
v_key_6915_ = lean_ctor_get(v_service_6905_, 1);
lean_inc_ref(v_key_6915_);
lean_dec_ref(v_service_6905_);
v___x_6916_ = 1;
v___x_6917_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6917_, 0, v_scope_6906_);
lean_ctor_set(v___x_6917_, 1, v_infos_6914_);
lean_ctor_set(v___x_6917_, 2, v_key_6915_);
lean_ctor_set_uint8(v___x_6917_, sizeof(void*)*3, v___x_6916_);
v___x_6918_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6907_, v___x_6917_);
return v___x_6918_;
}
else
{
lean_object* v___x_6919_; lean_object* v___x_6920_; lean_object* v___x_6921_; lean_object* v___x_6922_; 
lean_dec_ref(v_scope_6906_);
lean_dec_ref(v_service_6905_);
lean_dec(v_n_6902_);
v___x_6919_ = ((lean_object*)(l_Lake_CacheService_uploadArtifacts___closed__1));
lean_inc_ref(v_a_6907_);
v___x_6920_ = lean_apply_2(v_a_6907_, v___x_6919_, lean_box(0));
v___x_6921_ = lean_box(0);
v___x_6922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6922_, 0, v___x_6921_);
return v___x_6922_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_6923_, lean_object* v_descrs_6924_, lean_object* v_paths_6925_, lean_object* v_service_6926_, lean_object* v_scope_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_){
_start:
{
lean_object* v_res_6930_; 
v_res_6930_ = l_Lake_CacheService_uploadArtifacts(v_n_6923_, v_descrs_6924_, v_paths_6925_, v_service_6926_, v_scope_6927_, v_a_6928_);
lean_dec_ref(v_a_6928_);
lean_dec_ref(v_paths_6925_);
lean_dec_ref(v_descrs_6924_);
return v_res_6930_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object* v_00_u03b2_6931_, lean_object* v_m_6932_, uint64_t v_a_6933_){
_start:
{
uint8_t v___x_6934_; 
v___x_6934_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_m_6932_, v_a_6933_);
return v___x_6934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* v_00_u03b2_6935_, lean_object* v_m_6936_, lean_object* v_a_6937_){
_start:
{
uint64_t v_a_boxed_6938_; uint8_t v_res_6939_; lean_object* v_r_6940_; 
v_a_boxed_6938_ = lean_unbox_uint64(v_a_6937_);
lean_dec_ref(v_a_6937_);
v_res_6939_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(v_00_u03b2_6935_, v_m_6936_, v_a_boxed_6938_);
lean_dec_ref(v_m_6936_);
v_r_6940_ = lean_box(v_res_6939_);
return v_r_6940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(lean_object* v_descrs_6941_, lean_object* v_service_6942_, lean_object* v_scope_6943_, lean_object* v_paths_6944_, lean_object* v_n_6945_, lean_object* v_i_6946_, lean_object* v_a_6947_, lean_object* v_a_6948_, lean_object* v___y_6949_){
_start:
{
lean_object* v___x_6951_; 
v___x_6951_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_6941_, v_service_6942_, v_scope_6943_, v_paths_6944_, v_n_6945_, v_i_6946_, v_a_6948_);
return v___x_6951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___boxed(lean_object* v_descrs_6952_, lean_object* v_service_6953_, lean_object* v_scope_6954_, lean_object* v_paths_6955_, lean_object* v_n_6956_, lean_object* v_i_6957_, lean_object* v_a_6958_, lean_object* v_a_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_){
_start:
{
lean_object* v_res_6962_; 
v_res_6962_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(v_descrs_6952_, v_service_6953_, v_scope_6954_, v_paths_6955_, v_n_6956_, v_i_6957_, v_a_6958_, v_a_6959_, v___y_6960_);
lean_dec_ref(v___y_6960_);
lean_dec(v_n_6956_);
lean_dec_ref(v_paths_6955_);
lean_dec_ref(v_descrs_6952_);
return v_res_6962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_6967_, lean_object* v_service_6968_, lean_object* v_scope_6969_, lean_object* v_platform_6970_, lean_object* v_toolchain_6971_){
_start:
{
lean_object* v_url_6973_; lean_object* v_url_6980_; 
if (lean_obj_tag(v_scope_6969_) == 0)
{
lean_object* v_s_6989_; lean_object* v_revisionEndpoint_6990_; lean_object* v___x_6991_; lean_object* v___x_6992_; lean_object* v___x_6993_; lean_object* v___x_6994_; lean_object* v___x_6995_; lean_object* v___x_6996_; 
lean_dec_ref(v_platform_6970_);
v_s_6989_ = lean_ctor_get(v_scope_6969_, 0);
lean_inc_ref(v_s_6989_);
lean_dec_ref_known(v_scope_6969_, 1);
v_revisionEndpoint_6990_ = lean_ctor_get(v_service_6968_, 3);
lean_inc_ref(v_revisionEndpoint_6990_);
lean_dec_ref(v_service_6968_);
v___x_6991_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_6990_, v_s_6989_);
v___x_6992_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_6993_ = lean_string_append(v___x_6992_, v_rev_6967_);
v___x_6994_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_6995_ = lean_string_append(v___x_6993_, v___x_6994_);
v___x_6996_ = lean_string_append(v___x_6991_, v___x_6995_);
lean_dec_ref(v___x_6995_);
return v___x_6996_;
}
else
{
lean_object* v_s_6997_; lean_object* v_revisionEndpoint_6998_; lean_object* v_url_6999_; lean_object* v___x_7000_; lean_object* v___x_7001_; uint8_t v___x_7002_; 
v_s_6997_ = lean_ctor_get(v_scope_6969_, 0);
lean_inc_ref(v_s_6997_);
lean_dec_ref_known(v_scope_6969_, 1);
v_revisionEndpoint_6998_ = lean_ctor_get(v_service_6968_, 3);
lean_inc_ref(v_revisionEndpoint_6998_);
lean_dec_ref(v_service_6968_);
v_url_6999_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_6998_, v_s_6997_);
v___x_7000_ = lean_string_utf8_byte_size(v_platform_6970_);
v___x_7001_ = lean_unsigned_to_nat(0u);
v___x_7002_ = lean_nat_dec_eq(v___x_7000_, v___x_7001_);
if (v___x_7002_ == 0)
{
lean_object* v___x_7003_; lean_object* v___x_7004_; lean_object* v_url_7005_; 
v___x_7003_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_7004_ = lean_string_append(v_url_6999_, v___x_7003_);
v_url_7005_ = l_Lake_uriEncode(v_platform_6970_, v___x_7004_);
v_url_6980_ = v_url_7005_;
goto v___jp_6979_;
}
else
{
lean_dec_ref(v_platform_6970_);
v_url_6980_ = v_url_6999_;
goto v___jp_6979_;
}
}
v___jp_6972_:
{
lean_object* v___x_6974_; lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; 
v___x_6974_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_6975_ = lean_string_append(v_url_6973_, v___x_6974_);
v___x_6976_ = lean_string_append(v___x_6975_, v_rev_6967_);
v___x_6977_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_6978_ = lean_string_append(v___x_6976_, v___x_6977_);
return v___x_6978_;
}
v___jp_6979_:
{
lean_object* v___x_6981_; lean_object* v___x_6982_; uint8_t v___x_6983_; 
v___x_6981_ = lean_string_utf8_byte_size(v_toolchain_6971_);
v___x_6982_ = lean_unsigned_to_nat(0u);
v___x_6983_ = lean_nat_dec_eq(v___x_6981_, v___x_6982_);
if (v___x_6983_ == 0)
{
lean_object* v___x_6984_; lean_object* v___x_6985_; lean_object* v___x_6986_; lean_object* v___x_6987_; lean_object* v_url_6988_; 
v___x_6984_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6985_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_6971_, v___x_6984_, v___x_6982_);
v___x_6986_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_6987_ = lean_string_append(v_url_6980_, v___x_6986_);
v_url_6988_ = l_Lake_uriEncode(v___x_6985_, v___x_6987_);
v_url_6973_ = v_url_6988_;
goto v___jp_6972_;
}
else
{
v_url_6973_ = v_url_6980_;
goto v___jp_6972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_7006_, lean_object* v_service_7007_, lean_object* v_scope_7008_, lean_object* v_platform_7009_, lean_object* v_toolchain_7010_){
_start:
{
lean_object* v_res_7011_; 
v_res_7011_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7006_, v_service_7007_, v_scope_7008_, v_platform_7009_, v_toolchain_7010_);
lean_dec_ref(v_toolchain_7010_);
lean_dec_ref(v_rev_7006_);
return v_res_7011_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_7015_, lean_object* v_service_7016_, lean_object* v_scope_7017_, lean_object* v_platform_7018_, lean_object* v_toolchain_7019_){
_start:
{
lean_object* v_url_7021_; lean_object* v___y_7029_; uint8_t v_isReservoir_7039_; 
v_isReservoir_7039_ = lean_ctor_get_uint8(v_service_7016_, sizeof(void*)*5);
if (v_isReservoir_7039_ == 0)
{
lean_object* v___x_7040_; 
v___x_7040_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7015_, v_service_7016_, v_scope_7017_, v_platform_7018_, v_toolchain_7019_);
lean_dec_ref(v_toolchain_7019_);
return v___x_7040_;
}
else
{
if (lean_obj_tag(v_scope_7017_) == 0)
{
lean_object* v_apiEndpoint_7041_; lean_object* v_s_7042_; lean_object* v___x_7043_; lean_object* v___x_7044_; lean_object* v___x_7045_; 
v_apiEndpoint_7041_ = lean_ctor_get(v_service_7016_, 4);
lean_inc_ref(v_apiEndpoint_7041_);
lean_dec_ref(v_service_7016_);
v_s_7042_ = lean_ctor_get(v_scope_7017_, 0);
lean_inc_ref(v_s_7042_);
lean_dec_ref_known(v_scope_7017_, 1);
v___x_7043_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_7044_ = lean_string_append(v_apiEndpoint_7041_, v___x_7043_);
v___x_7045_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_7044_, v_s_7042_);
v___y_7029_ = v___x_7045_;
goto v___jp_7028_;
}
else
{
lean_object* v_apiEndpoint_7046_; lean_object* v_s_7047_; lean_object* v___x_7048_; lean_object* v___x_7049_; lean_object* v___x_7050_; 
v_apiEndpoint_7046_ = lean_ctor_get(v_service_7016_, 4);
lean_inc_ref(v_apiEndpoint_7046_);
lean_dec_ref(v_service_7016_);
v_s_7047_ = lean_ctor_get(v_scope_7017_, 0);
lean_inc_ref(v_s_7047_);
lean_dec_ref_known(v_scope_7017_, 1);
v___x_7048_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_7049_ = lean_string_append(v_apiEndpoint_7046_, v___x_7048_);
v___x_7050_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_7049_, v_s_7047_);
v___y_7029_ = v___x_7050_;
goto v___jp_7028_;
}
}
v___jp_7020_:
{
lean_object* v___x_7022_; lean_object* v___x_7023_; uint8_t v___x_7024_; 
v___x_7022_ = lean_string_utf8_byte_size(v_toolchain_7019_);
v___x_7023_ = lean_unsigned_to_nat(0u);
v___x_7024_ = lean_nat_dec_eq(v___x_7022_, v___x_7023_);
if (v___x_7024_ == 0)
{
lean_object* v___x_7025_; lean_object* v___x_7026_; lean_object* v_url_7027_; 
v___x_7025_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_7026_ = lean_string_append(v_url_7021_, v___x_7025_);
v_url_7027_ = l_Lake_uriEncode(v_toolchain_7019_, v___x_7026_);
return v_url_7027_;
}
else
{
lean_dec_ref(v_toolchain_7019_);
return v_url_7021_;
}
}
v___jp_7028_:
{
lean_object* v___x_7030_; lean_object* v___x_7031_; lean_object* v_url_7032_; lean_object* v___x_7033_; lean_object* v___x_7034_; uint8_t v___x_7035_; 
v___x_7030_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_7031_ = lean_string_append(v___y_7029_, v___x_7030_);
v_url_7032_ = lean_string_append(v___x_7031_, v_rev_7015_);
v___x_7033_ = lean_string_utf8_byte_size(v_platform_7018_);
v___x_7034_ = lean_unsigned_to_nat(0u);
v___x_7035_ = lean_nat_dec_eq(v___x_7033_, v___x_7034_);
if (v___x_7035_ == 0)
{
lean_object* v___x_7036_; lean_object* v___x_7037_; lean_object* v_url_7038_; 
v___x_7036_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_7037_ = lean_string_append(v_url_7032_, v___x_7036_);
v_url_7038_ = l_Lake_uriEncode(v_platform_7018_, v___x_7037_);
v_url_7021_ = v_url_7038_;
goto v___jp_7020_;
}
else
{
lean_dec_ref(v_platform_7018_);
v_url_7021_ = v_url_7032_;
goto v___jp_7020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_7051_, lean_object* v_service_7052_, lean_object* v_scope_7053_, lean_object* v_platform_7054_, lean_object* v_toolchain_7055_){
_start:
{
lean_object* v_res_7056_; 
v_res_7056_ = l_Lake_CacheService_revisionUrl(v_rev_7051_, v_service_7052_, v_scope_7053_, v_platform_7054_, v_toolchain_7055_);
lean_dec_ref(v_rev_7051_);
return v_res_7056_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_7061_, lean_object* v_cache_7062_, lean_object* v_service_7063_, lean_object* v_localScope_7064_, lean_object* v_remoteScope_7065_, lean_object* v_platform_7066_, lean_object* v_toolchain_7067_, uint8_t v_force_7068_, lean_object* v_a_7069_){
_start:
{
lean_object* v_a_7075_; lean_object* v_a_7082_; lean_object* v___y_7086_; lean_object* v___y_7087_; lean_object* v_a_7095_; lean_object* v___x_7099_; lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; lean_object* v___x_7103_; lean_object* v_path_7104_; lean_object* v_a_7106_; lean_object* v___y_7208_; lean_object* v___y_7209_; uint8_t v___x_7258_; lean_object* v___x_7322_; uint8_t v___x_7323_; 
v___x_7099_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_7100_ = l_System_FilePath_join(v_cache_7062_, v___x_7099_);
lean_inc_ref(v_localScope_7064_);
v___x_7101_ = l_System_FilePath_join(v___x_7100_, v_localScope_7064_);
v___x_7102_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_7061_);
v___x_7103_ = lean_string_append(v_rev_7061_, v___x_7102_);
v_path_7104_ = l_System_FilePath_join(v___x_7101_, v___x_7103_);
v___x_7258_ = l_System_FilePath_pathExists(v_path_7104_);
v___x_7322_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7323_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_7323_ == 0)
{
goto v___jp_7259_;
}
else
{
lean_object* v___x_7324_; uint8_t v___x_7325_; 
v___x_7324_ = lean_box(0);
v___x_7325_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_7325_ == 0)
{
if (v___x_7323_ == 0)
{
goto v___jp_7259_;
}
else
{
size_t v___x_7326_; size_t v___x_7327_; lean_object* v___x_7328_; 
v___x_7326_ = ((size_t)0ULL);
v___x_7327_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_7328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_7322_, v___x_7326_, v___x_7327_, v___x_7324_, v_a_7069_);
if (lean_obj_tag(v___x_7328_) == 0)
{
lean_dec_ref_known(v___x_7328_, 1);
goto v___jp_7259_;
}
else
{
lean_object* v_a_7329_; lean_object* v___x_7331_; uint8_t v_isShared_7332_; uint8_t v_isSharedCheck_7336_; 
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_toolchain_7067_);
lean_dec_ref(v_platform_7066_);
lean_dec_ref(v_remoteScope_7065_);
lean_dec_ref(v_localScope_7064_);
lean_dec_ref(v_service_7063_);
lean_dec_ref(v_rev_7061_);
v_a_7329_ = lean_ctor_get(v___x_7328_, 0);
v_isSharedCheck_7336_ = !lean_is_exclusive(v___x_7328_);
if (v_isSharedCheck_7336_ == 0)
{
v___x_7331_ = v___x_7328_;
v_isShared_7332_ = v_isSharedCheck_7336_;
goto v_resetjp_7330_;
}
else
{
lean_inc(v_a_7329_);
lean_dec(v___x_7328_);
v___x_7331_ = lean_box(0);
v_isShared_7332_ = v_isSharedCheck_7336_;
goto v_resetjp_7330_;
}
v_resetjp_7330_:
{
lean_object* v___x_7334_; 
if (v_isShared_7332_ == 0)
{
v___x_7334_ = v___x_7331_;
goto v_reusejp_7333_;
}
else
{
lean_object* v_reuseFailAlloc_7335_; 
v_reuseFailAlloc_7335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7335_, 0, v_a_7329_);
v___x_7334_ = v_reuseFailAlloc_7335_;
goto v_reusejp_7333_;
}
v_reusejp_7333_:
{
return v___x_7334_;
}
}
}
}
}
else
{
size_t v___x_7337_; size_t v___x_7338_; lean_object* v___x_7339_; 
v___x_7337_ = ((size_t)0ULL);
v___x_7338_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_7339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_7322_, v___x_7337_, v___x_7338_, v___x_7324_, v_a_7069_);
if (lean_obj_tag(v___x_7339_) == 0)
{
lean_dec_ref_known(v___x_7339_, 1);
goto v___jp_7259_;
}
else
{
lean_object* v_a_7340_; lean_object* v___x_7342_; uint8_t v_isShared_7343_; uint8_t v_isSharedCheck_7347_; 
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_toolchain_7067_);
lean_dec_ref(v_platform_7066_);
lean_dec_ref(v_remoteScope_7065_);
lean_dec_ref(v_localScope_7064_);
lean_dec_ref(v_service_7063_);
lean_dec_ref(v_rev_7061_);
v_a_7340_ = lean_ctor_get(v___x_7339_, 0);
v_isSharedCheck_7347_ = !lean_is_exclusive(v___x_7339_);
if (v_isSharedCheck_7347_ == 0)
{
v___x_7342_ = v___x_7339_;
v_isShared_7343_ = v_isSharedCheck_7347_;
goto v_resetjp_7341_;
}
else
{
lean_inc(v_a_7340_);
lean_dec(v___x_7339_);
v___x_7342_ = lean_box(0);
v_isShared_7343_ = v_isSharedCheck_7347_;
goto v_resetjp_7341_;
}
v_resetjp_7341_:
{
lean_object* v___x_7345_; 
if (v_isShared_7343_ == 0)
{
v___x_7345_ = v___x_7342_;
goto v_reusejp_7344_;
}
else
{
lean_object* v_reuseFailAlloc_7346_; 
v_reuseFailAlloc_7346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7346_, 0, v_a_7340_);
v___x_7345_ = v_reuseFailAlloc_7346_;
goto v_reusejp_7344_;
}
v_reusejp_7344_:
{
return v___x_7345_;
}
}
}
}
}
v___jp_7071_:
{
lean_object* v___x_7072_; lean_object* v___x_7073_; 
v___x_7072_ = lean_box(0);
v___x_7073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7073_, 0, v___x_7072_);
return v___x_7073_;
}
v___jp_7074_:
{
lean_object* v___x_7076_; lean_object* v___x_7077_; 
v___x_7076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7076_, 0, v_a_7075_);
v___x_7077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7077_, 0, v___x_7076_);
return v___x_7077_;
}
v___jp_7078_:
{
lean_object* v___x_7079_; lean_object* v___x_7080_; 
v___x_7079_ = lean_box(0);
v___x_7080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7080_, 0, v___x_7079_);
return v___x_7080_;
}
v___jp_7081_:
{
lean_object* v___x_7083_; lean_object* v___x_7084_; 
v___x_7083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7083_, 0, v_a_7082_);
v___x_7084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7084_, 0, v___x_7083_);
return v___x_7084_;
}
v___jp_7085_:
{
lean_object* v___x_7088_; lean_object* v___x_7089_; uint8_t v___x_7090_; lean_object* v___x_7091_; lean_object* v___x_7092_; lean_object* v___x_7093_; 
v___x_7088_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_7089_ = lean_string_append(v___y_7087_, v___x_7088_);
v___x_7090_ = 3;
v___x_7091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7091_, 0, v___x_7089_);
lean_ctor_set_uint8(v___x_7091_, sizeof(void*)*1, v___x_7090_);
lean_inc_ref(v_a_7069_);
v___x_7092_ = lean_apply_2(v_a_7069_, v___x_7091_, lean_box(0));
v___x_7093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7093_, 0, v___y_7086_);
return v___x_7093_;
}
v___jp_7094_:
{
lean_object* v_s_7096_; 
v_s_7096_ = lean_ctor_get(v_remoteScope_7065_, 0);
lean_inc_ref(v_s_7096_);
lean_dec_ref(v_remoteScope_7065_);
v___y_7086_ = v_a_7095_;
v___y_7087_ = v_s_7096_;
goto v___jp_7085_;
}
v___jp_7097_:
{
lean_object* v___x_7098_; 
v___x_7098_ = lean_box(0);
v_a_7095_ = v___x_7098_;
goto v___jp_7094_;
}
v___jp_7105_:
{
if (lean_obj_tag(v_a_7106_) == 1)
{
lean_object* v_val_7107_; lean_object* v___x_7108_; 
v_val_7107_ = lean_ctor_get(v_a_7106_, 0);
lean_inc(v_val_7107_);
lean_dec_ref_known(v_a_7106_, 1);
lean_inc_ref(v_path_7104_);
v___x_7108_ = l_Lake_createParentDirs(v_path_7104_);
if (lean_obj_tag(v___x_7108_) == 0)
{
lean_object* v___x_7109_; 
lean_dec_ref_known(v___x_7108_, 1);
v___x_7109_ = l_IO_FS_writeFile(v_path_7104_, v_val_7107_);
lean_dec(v_val_7107_);
if (lean_obj_tag(v___x_7109_) == 0)
{
lean_object* v___x_7111_; uint8_t v_isShared_7112_; uint8_t v_isSharedCheck_7177_; 
v_isSharedCheck_7177_ = !lean_is_exclusive(v___x_7109_);
if (v_isSharedCheck_7177_ == 0)
{
lean_object* v_unused_7178_; 
v_unused_7178_ = lean_ctor_get(v___x_7109_, 0);
lean_dec(v_unused_7178_);
v___x_7111_ = v___x_7109_;
v_isShared_7112_ = v_isSharedCheck_7177_;
goto v_resetjp_7110_;
}
else
{
lean_dec(v___x_7109_);
v___x_7111_ = lean_box(0);
v_isShared_7112_ = v_isSharedCheck_7177_;
goto v_resetjp_7110_;
}
v_resetjp_7110_:
{
lean_object* v___x_7113_; lean_object* v___x_7114_; uint8_t v___x_7115_; lean_object* v___x_7116_; lean_object* v___x_7117_; 
v___x_7113_ = lean_string_utf8_byte_size(v_platform_7066_);
lean_dec_ref(v_platform_7066_);
v___x_7114_ = lean_unsigned_to_nat(0u);
v___x_7115_ = lean_nat_dec_eq(v___x_7113_, v___x_7114_);
v___x_7116_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7117_ = l_Lake_CacheMap_load(v_path_7104_, v___x_7115_, v___x_7116_);
if (lean_obj_tag(v___x_7117_) == 0)
{
lean_object* v_a_7118_; lean_object* v_a_7119_; lean_object* v___x_7120_; uint8_t v___x_7121_; 
lean_del_object(v___x_7111_);
v_a_7118_ = lean_ctor_get(v___x_7117_, 0);
lean_inc(v_a_7118_);
v_a_7119_ = lean_ctor_get(v___x_7117_, 1);
lean_inc(v_a_7119_);
lean_dec_ref_known(v___x_7117_, 2);
v___x_7120_ = lean_array_get_size(v_a_7119_);
v___x_7121_ = lean_nat_dec_lt(v___x_7114_, v___x_7120_);
if (v___x_7121_ == 0)
{
lean_dec(v_a_7119_);
v_a_7082_ = v_a_7118_;
goto v___jp_7081_;
}
else
{
lean_object* v___x_7122_; uint8_t v___x_7123_; 
v___x_7122_ = lean_box(0);
v___x_7123_ = lean_nat_dec_le(v___x_7120_, v___x_7120_);
if (v___x_7123_ == 0)
{
if (v___x_7121_ == 0)
{
lean_dec(v_a_7119_);
v_a_7082_ = v_a_7118_;
goto v___jp_7081_;
}
else
{
size_t v___x_7124_; size_t v___x_7125_; lean_object* v___x_7126_; 
v___x_7124_ = ((size_t)0ULL);
v___x_7125_ = lean_usize_of_nat(v___x_7120_);
v___x_7126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7119_, v___x_7124_, v___x_7125_, v___x_7122_, v_a_7069_);
lean_dec(v_a_7119_);
if (lean_obj_tag(v___x_7126_) == 0)
{
lean_dec_ref_known(v___x_7126_, 1);
v_a_7082_ = v_a_7118_;
goto v___jp_7081_;
}
else
{
lean_object* v_a_7127_; lean_object* v___x_7129_; uint8_t v_isShared_7130_; uint8_t v_isSharedCheck_7134_; 
lean_dec(v_a_7118_);
v_a_7127_ = lean_ctor_get(v___x_7126_, 0);
v_isSharedCheck_7134_ = !lean_is_exclusive(v___x_7126_);
if (v_isSharedCheck_7134_ == 0)
{
v___x_7129_ = v___x_7126_;
v_isShared_7130_ = v_isSharedCheck_7134_;
goto v_resetjp_7128_;
}
else
{
lean_inc(v_a_7127_);
lean_dec(v___x_7126_);
v___x_7129_ = lean_box(0);
v_isShared_7130_ = v_isSharedCheck_7134_;
goto v_resetjp_7128_;
}
v_resetjp_7128_:
{
lean_object* v___x_7132_; 
if (v_isShared_7130_ == 0)
{
v___x_7132_ = v___x_7129_;
goto v_reusejp_7131_;
}
else
{
lean_object* v_reuseFailAlloc_7133_; 
v_reuseFailAlloc_7133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7133_, 0, v_a_7127_);
v___x_7132_ = v_reuseFailAlloc_7133_;
goto v_reusejp_7131_;
}
v_reusejp_7131_:
{
return v___x_7132_;
}
}
}
}
}
else
{
size_t v___x_7135_; size_t v___x_7136_; lean_object* v___x_7137_; 
v___x_7135_ = ((size_t)0ULL);
v___x_7136_ = lean_usize_of_nat(v___x_7120_);
v___x_7137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7119_, v___x_7135_, v___x_7136_, v___x_7122_, v_a_7069_);
lean_dec(v_a_7119_);
if (lean_obj_tag(v___x_7137_) == 0)
{
lean_dec_ref_known(v___x_7137_, 1);
v_a_7082_ = v_a_7118_;
goto v___jp_7081_;
}
else
{
lean_object* v_a_7138_; lean_object* v___x_7140_; uint8_t v_isShared_7141_; uint8_t v_isSharedCheck_7145_; 
lean_dec(v_a_7118_);
v_a_7138_ = lean_ctor_get(v___x_7137_, 0);
v_isSharedCheck_7145_ = !lean_is_exclusive(v___x_7137_);
if (v_isSharedCheck_7145_ == 0)
{
v___x_7140_ = v___x_7137_;
v_isShared_7141_ = v_isSharedCheck_7145_;
goto v_resetjp_7139_;
}
else
{
lean_inc(v_a_7138_);
lean_dec(v___x_7137_);
v___x_7140_ = lean_box(0);
v_isShared_7141_ = v_isSharedCheck_7145_;
goto v_resetjp_7139_;
}
v_resetjp_7139_:
{
lean_object* v___x_7143_; 
if (v_isShared_7141_ == 0)
{
v___x_7143_ = v___x_7140_;
goto v_reusejp_7142_;
}
else
{
lean_object* v_reuseFailAlloc_7144_; 
v_reuseFailAlloc_7144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
v___x_7143_ = v_reuseFailAlloc_7144_;
goto v_reusejp_7142_;
}
v_reusejp_7142_:
{
return v___x_7143_;
}
}
}
}
}
}
else
{
lean_object* v_a_7146_; lean_object* v___x_7147_; uint8_t v___x_7148_; 
v_a_7146_ = lean_ctor_get(v___x_7117_, 1);
lean_inc(v_a_7146_);
lean_dec_ref_known(v___x_7117_, 2);
v___x_7147_ = lean_array_get_size(v_a_7146_);
v___x_7148_ = lean_nat_dec_lt(v___x_7114_, v___x_7147_);
if (v___x_7148_ == 0)
{
lean_object* v___x_7149_; lean_object* v___x_7151_; 
lean_dec(v_a_7146_);
v___x_7149_ = lean_box(0);
if (v_isShared_7112_ == 0)
{
lean_ctor_set_tag(v___x_7111_, 1);
lean_ctor_set(v___x_7111_, 0, v___x_7149_);
v___x_7151_ = v___x_7111_;
goto v_reusejp_7150_;
}
else
{
lean_object* v_reuseFailAlloc_7152_; 
v_reuseFailAlloc_7152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7152_, 0, v___x_7149_);
v___x_7151_ = v_reuseFailAlloc_7152_;
goto v_reusejp_7150_;
}
v_reusejp_7150_:
{
return v___x_7151_;
}
}
else
{
lean_object* v___x_7153_; uint8_t v___x_7154_; 
lean_del_object(v___x_7111_);
v___x_7153_ = lean_box(0);
v___x_7154_ = lean_nat_dec_le(v___x_7147_, v___x_7147_);
if (v___x_7154_ == 0)
{
if (v___x_7148_ == 0)
{
lean_dec(v_a_7146_);
goto v___jp_7078_;
}
else
{
size_t v___x_7155_; size_t v___x_7156_; lean_object* v___x_7157_; 
v___x_7155_ = ((size_t)0ULL);
v___x_7156_ = lean_usize_of_nat(v___x_7147_);
v___x_7157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7146_, v___x_7155_, v___x_7156_, v___x_7153_, v_a_7069_);
lean_dec(v_a_7146_);
if (lean_obj_tag(v___x_7157_) == 0)
{
lean_dec_ref_known(v___x_7157_, 1);
goto v___jp_7078_;
}
else
{
lean_object* v_a_7158_; lean_object* v___x_7160_; uint8_t v_isShared_7161_; uint8_t v_isSharedCheck_7165_; 
v_a_7158_ = lean_ctor_get(v___x_7157_, 0);
v_isSharedCheck_7165_ = !lean_is_exclusive(v___x_7157_);
if (v_isSharedCheck_7165_ == 0)
{
v___x_7160_ = v___x_7157_;
v_isShared_7161_ = v_isSharedCheck_7165_;
goto v_resetjp_7159_;
}
else
{
lean_inc(v_a_7158_);
lean_dec(v___x_7157_);
v___x_7160_ = lean_box(0);
v_isShared_7161_ = v_isSharedCheck_7165_;
goto v_resetjp_7159_;
}
v_resetjp_7159_:
{
lean_object* v___x_7163_; 
if (v_isShared_7161_ == 0)
{
v___x_7163_ = v___x_7160_;
goto v_reusejp_7162_;
}
else
{
lean_object* v_reuseFailAlloc_7164_; 
v_reuseFailAlloc_7164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7164_, 0, v_a_7158_);
v___x_7163_ = v_reuseFailAlloc_7164_;
goto v_reusejp_7162_;
}
v_reusejp_7162_:
{
return v___x_7163_;
}
}
}
}
}
else
{
size_t v___x_7166_; size_t v___x_7167_; lean_object* v___x_7168_; 
v___x_7166_ = ((size_t)0ULL);
v___x_7167_ = lean_usize_of_nat(v___x_7147_);
v___x_7168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7146_, v___x_7166_, v___x_7167_, v___x_7153_, v_a_7069_);
lean_dec(v_a_7146_);
if (lean_obj_tag(v___x_7168_) == 0)
{
lean_dec_ref_known(v___x_7168_, 1);
goto v___jp_7078_;
}
else
{
lean_object* v_a_7169_; lean_object* v___x_7171_; uint8_t v_isShared_7172_; uint8_t v_isSharedCheck_7176_; 
v_a_7169_ = lean_ctor_get(v___x_7168_, 0);
v_isSharedCheck_7176_ = !lean_is_exclusive(v___x_7168_);
if (v_isSharedCheck_7176_ == 0)
{
v___x_7171_ = v___x_7168_;
v_isShared_7172_ = v_isSharedCheck_7176_;
goto v_resetjp_7170_;
}
else
{
lean_inc(v_a_7169_);
lean_dec(v___x_7168_);
v___x_7171_ = lean_box(0);
v_isShared_7172_ = v_isSharedCheck_7176_;
goto v_resetjp_7170_;
}
v_resetjp_7170_:
{
lean_object* v___x_7174_; 
if (v_isShared_7172_ == 0)
{
v___x_7174_ = v___x_7171_;
goto v_reusejp_7173_;
}
else
{
lean_object* v_reuseFailAlloc_7175_; 
v_reuseFailAlloc_7175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7175_, 0, v_a_7169_);
v___x_7174_ = v_reuseFailAlloc_7175_;
goto v_reusejp_7173_;
}
v_reusejp_7173_:
{
return v___x_7174_;
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
lean_object* v_a_7179_; lean_object* v___x_7181_; uint8_t v_isShared_7182_; uint8_t v_isSharedCheck_7191_; 
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_platform_7066_);
v_a_7179_ = lean_ctor_get(v___x_7109_, 0);
v_isSharedCheck_7191_ = !lean_is_exclusive(v___x_7109_);
if (v_isSharedCheck_7191_ == 0)
{
v___x_7181_ = v___x_7109_;
v_isShared_7182_ = v_isSharedCheck_7191_;
goto v_resetjp_7180_;
}
else
{
lean_inc(v_a_7179_);
lean_dec(v___x_7109_);
v___x_7181_ = lean_box(0);
v_isShared_7182_ = v_isSharedCheck_7191_;
goto v_resetjp_7180_;
}
v_resetjp_7180_:
{
lean_object* v___x_7183_; uint8_t v___x_7184_; lean_object* v___x_7185_; lean_object* v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7189_; 
v___x_7183_ = lean_io_error_to_string(v_a_7179_);
v___x_7184_ = 3;
v___x_7185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7185_, 0, v___x_7183_);
lean_ctor_set_uint8(v___x_7185_, sizeof(void*)*1, v___x_7184_);
lean_inc_ref(v_a_7069_);
v___x_7186_ = lean_apply_2(v_a_7069_, v___x_7185_, lean_box(0));
v___x_7187_ = lean_box(0);
if (v_isShared_7182_ == 0)
{
lean_ctor_set(v___x_7181_, 0, v___x_7187_);
v___x_7189_ = v___x_7181_;
goto v_reusejp_7188_;
}
else
{
lean_object* v_reuseFailAlloc_7190_; 
v_reuseFailAlloc_7190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7190_, 0, v___x_7187_);
v___x_7189_ = v_reuseFailAlloc_7190_;
goto v_reusejp_7188_;
}
v_reusejp_7188_:
{
return v___x_7189_;
}
}
}
}
else
{
lean_object* v_a_7192_; lean_object* v___x_7194_; uint8_t v_isShared_7195_; uint8_t v_isSharedCheck_7204_; 
lean_dec(v_val_7107_);
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_platform_7066_);
v_a_7192_ = lean_ctor_get(v___x_7108_, 0);
v_isSharedCheck_7204_ = !lean_is_exclusive(v___x_7108_);
if (v_isSharedCheck_7204_ == 0)
{
v___x_7194_ = v___x_7108_;
v_isShared_7195_ = v_isSharedCheck_7204_;
goto v_resetjp_7193_;
}
else
{
lean_inc(v_a_7192_);
lean_dec(v___x_7108_);
v___x_7194_ = lean_box(0);
v_isShared_7195_ = v_isSharedCheck_7204_;
goto v_resetjp_7193_;
}
v_resetjp_7193_:
{
lean_object* v___x_7196_; uint8_t v___x_7197_; lean_object* v___x_7198_; lean_object* v___x_7199_; lean_object* v___x_7200_; lean_object* v___x_7202_; 
v___x_7196_ = lean_io_error_to_string(v_a_7192_);
v___x_7197_ = 3;
v___x_7198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7198_, 0, v___x_7196_);
lean_ctor_set_uint8(v___x_7198_, sizeof(void*)*1, v___x_7197_);
lean_inc_ref(v_a_7069_);
v___x_7199_ = lean_apply_2(v_a_7069_, v___x_7198_, lean_box(0));
v___x_7200_ = lean_box(0);
if (v_isShared_7195_ == 0)
{
lean_ctor_set(v___x_7194_, 0, v___x_7200_);
v___x_7202_ = v___x_7194_;
goto v_reusejp_7201_;
}
else
{
lean_object* v_reuseFailAlloc_7203_; 
v_reuseFailAlloc_7203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7203_, 0, v___x_7200_);
v___x_7202_ = v_reuseFailAlloc_7203_;
goto v_reusejp_7201_;
}
v_reusejp_7201_:
{
return v___x_7202_;
}
}
}
}
else
{
lean_object* v___x_7205_; lean_object* v___x_7206_; 
lean_dec(v_a_7106_);
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_platform_7066_);
v___x_7205_ = lean_box(0);
v___x_7206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7206_, 0, v___x_7205_);
return v___x_7206_;
}
}
v___jp_7207_:
{
lean_object* v___x_7210_; lean_object* v___x_7211_; lean_object* v___x_7212_; 
v___x_7210_ = lean_unsigned_to_nat(0u);
v___x_7211_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7212_ = l_Lake_getUrl_x3f(v___y_7208_, v___y_7209_, v___x_7211_);
if (lean_obj_tag(v___x_7212_) == 0)
{
lean_object* v_a_7213_; lean_object* v_a_7214_; lean_object* v___x_7215_; uint8_t v___x_7216_; 
v_a_7213_ = lean_ctor_get(v___x_7212_, 0);
lean_inc(v_a_7213_);
v_a_7214_ = lean_ctor_get(v___x_7212_, 1);
lean_inc(v_a_7214_);
lean_dec_ref_known(v___x_7212_, 2);
v___x_7215_ = lean_array_get_size(v_a_7214_);
v___x_7216_ = lean_nat_dec_lt(v___x_7210_, v___x_7215_);
if (v___x_7216_ == 0)
{
lean_dec(v_a_7214_);
lean_dec_ref(v_remoteScope_7065_);
v_a_7106_ = v_a_7213_;
goto v___jp_7105_;
}
else
{
lean_object* v___x_7217_; uint8_t v___x_7218_; 
v___x_7217_ = lean_box(0);
v___x_7218_ = lean_nat_dec_le(v___x_7215_, v___x_7215_);
if (v___x_7218_ == 0)
{
if (v___x_7216_ == 0)
{
lean_dec(v_a_7214_);
lean_dec_ref(v_remoteScope_7065_);
v_a_7106_ = v_a_7213_;
goto v___jp_7105_;
}
else
{
size_t v___x_7219_; size_t v___x_7220_; lean_object* v___x_7221_; 
v___x_7219_ = ((size_t)0ULL);
v___x_7220_ = lean_usize_of_nat(v___x_7215_);
v___x_7221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7214_, v___x_7219_, v___x_7220_, v___x_7217_, v_a_7069_);
lean_dec(v_a_7214_);
if (lean_obj_tag(v___x_7221_) == 0)
{
lean_dec_ref_known(v___x_7221_, 1);
lean_dec_ref(v_remoteScope_7065_);
v_a_7106_ = v_a_7213_;
goto v___jp_7105_;
}
else
{
lean_object* v_a_7222_; 
lean_dec(v_a_7213_);
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_platform_7066_);
v_a_7222_ = lean_ctor_get(v___x_7221_, 0);
lean_inc(v_a_7222_);
lean_dec_ref_known(v___x_7221_, 1);
v_a_7095_ = v_a_7222_;
goto v___jp_7094_;
}
}
}
else
{
size_t v___x_7223_; size_t v___x_7224_; lean_object* v___x_7225_; 
v___x_7223_ = ((size_t)0ULL);
v___x_7224_ = lean_usize_of_nat(v___x_7215_);
v___x_7225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7214_, v___x_7223_, v___x_7224_, v___x_7217_, v_a_7069_);
lean_dec(v_a_7214_);
if (lean_obj_tag(v___x_7225_) == 0)
{
lean_dec_ref_known(v___x_7225_, 1);
lean_dec_ref(v_remoteScope_7065_);
v_a_7106_ = v_a_7213_;
goto v___jp_7105_;
}
else
{
lean_object* v_a_7226_; 
lean_dec(v_a_7213_);
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_platform_7066_);
v_a_7226_ = lean_ctor_get(v___x_7225_, 0);
lean_inc(v_a_7226_);
lean_dec_ref_known(v___x_7225_, 1);
v_a_7095_ = v_a_7226_;
goto v___jp_7094_;
}
}
}
}
else
{
lean_object* v_a_7227_; lean_object* v___x_7228_; uint8_t v___x_7229_; 
lean_dec_ref(v_path_7104_);
lean_dec_ref(v_platform_7066_);
v_a_7227_ = lean_ctor_get(v___x_7212_, 1);
lean_inc(v_a_7227_);
lean_dec_ref_known(v___x_7212_, 2);
v___x_7228_ = lean_array_get_size(v_a_7227_);
v___x_7229_ = lean_nat_dec_lt(v___x_7210_, v___x_7228_);
if (v___x_7229_ == 0)
{
lean_object* v___x_7230_; 
lean_dec(v_a_7227_);
v___x_7230_ = lean_box(0);
v_a_7095_ = v___x_7230_;
goto v___jp_7094_;
}
else
{
lean_object* v___x_7231_; uint8_t v___x_7232_; 
v___x_7231_ = lean_box(0);
v___x_7232_ = lean_nat_dec_le(v___x_7228_, v___x_7228_);
if (v___x_7232_ == 0)
{
if (v___x_7229_ == 0)
{
lean_dec(v_a_7227_);
goto v___jp_7097_;
}
else
{
size_t v___x_7233_; size_t v___x_7234_; lean_object* v___x_7235_; 
v___x_7233_ = ((size_t)0ULL);
v___x_7234_ = lean_usize_of_nat(v___x_7228_);
v___x_7235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7227_, v___x_7233_, v___x_7234_, v___x_7231_, v_a_7069_);
lean_dec(v_a_7227_);
if (lean_obj_tag(v___x_7235_) == 0)
{
lean_dec_ref_known(v___x_7235_, 1);
goto v___jp_7097_;
}
else
{
lean_object* v_a_7236_; 
v_a_7236_ = lean_ctor_get(v___x_7235_, 0);
lean_inc(v_a_7236_);
lean_dec_ref_known(v___x_7235_, 1);
v_a_7095_ = v_a_7236_;
goto v___jp_7094_;
}
}
}
else
{
size_t v___x_7237_; size_t v___x_7238_; lean_object* v___x_7239_; 
v___x_7237_ = ((size_t)0ULL);
v___x_7238_ = lean_usize_of_nat(v___x_7228_);
v___x_7239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7227_, v___x_7237_, v___x_7238_, v___x_7231_, v_a_7069_);
lean_dec(v_a_7227_);
if (lean_obj_tag(v___x_7239_) == 0)
{
lean_dec_ref_known(v___x_7239_, 1);
goto v___jp_7097_;
}
else
{
lean_object* v_a_7240_; 
v_a_7240_ = lean_ctor_get(v___x_7239_, 0);
lean_inc(v_a_7240_);
lean_dec_ref_known(v___x_7239_, 1);
v_a_7095_ = v_a_7240_;
goto v___jp_7094_;
}
}
}
}
}
v___jp_7241_:
{
lean_object* v___x_7242_; lean_object* v___x_7243_; lean_object* v___x_7244_; lean_object* v___x_7245_; lean_object* v___x_7246_; lean_object* v___x_7247_; lean_object* v___x_7248_; lean_object* v___x_7249_; lean_object* v___x_7250_; lean_object* v___x_7251_; uint8_t v___x_7252_; lean_object* v___x_7253_; lean_object* v___x_7254_; uint8_t v_isReservoir_7255_; 
lean_inc_ref(v_platform_7066_);
lean_inc_ref(v_remoteScope_7065_);
lean_inc_ref(v_service_7063_);
v___x_7242_ = l_Lake_CacheService_revisionUrl(v_rev_7061_, v_service_7063_, v_remoteScope_7065_, v_platform_7066_, v_toolchain_7067_);
v___x_7243_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_7244_ = lean_string_append(v_localScope_7064_, v___x_7243_);
v___x_7245_ = lean_string_append(v___x_7244_, v_rev_7061_);
lean_dec_ref(v_rev_7061_);
v___x_7246_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_7247_ = lean_string_append(v___x_7245_, v___x_7246_);
v___x_7248_ = lean_string_append(v___x_7247_, v_path_7104_);
v___x_7249_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_7250_ = lean_string_append(v___x_7248_, v___x_7249_);
v___x_7251_ = lean_string_append(v___x_7250_, v___x_7242_);
v___x_7252_ = 1;
v___x_7253_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7253_, 0, v___x_7251_);
lean_ctor_set_uint8(v___x_7253_, sizeof(void*)*1, v___x_7252_);
lean_inc_ref(v_a_7069_);
v___x_7254_ = lean_apply_2(v_a_7069_, v___x_7253_, lean_box(0));
v_isReservoir_7255_ = lean_ctor_get_uint8(v_service_7063_, sizeof(void*)*5);
lean_dec_ref(v_service_7063_);
if (v_isReservoir_7255_ == 0)
{
lean_object* v___x_7256_; 
v___x_7256_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_7208_ = v___x_7242_;
v___y_7209_ = v___x_7256_;
goto v___jp_7207_;
}
else
{
lean_object* v___x_7257_; 
v___x_7257_ = l_Lake_Reservoir_lakeHeaders;
v___y_7208_ = v___x_7242_;
v___y_7209_ = v___x_7257_;
goto v___jp_7207_;
}
}
v___jp_7259_:
{
if (v___x_7258_ == 0)
{
goto v___jp_7241_;
}
else
{
if (v_force_7068_ == 0)
{
lean_object* v___x_7260_; lean_object* v___x_7261_; uint8_t v___x_7262_; lean_object* v___x_7263_; lean_object* v___x_7264_; 
lean_dec_ref(v_toolchain_7067_);
lean_dec_ref(v_remoteScope_7065_);
lean_dec_ref(v_localScope_7064_);
lean_dec_ref(v_service_7063_);
lean_dec_ref(v_rev_7061_);
v___x_7260_ = lean_string_utf8_byte_size(v_platform_7066_);
lean_dec_ref(v_platform_7066_);
v___x_7261_ = lean_unsigned_to_nat(0u);
v___x_7262_ = lean_nat_dec_eq(v___x_7260_, v___x_7261_);
v___x_7263_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_7264_ = l_Lake_CacheMap_load(v_path_7104_, v___x_7262_, v___x_7263_);
if (lean_obj_tag(v___x_7264_) == 0)
{
lean_object* v_a_7265_; lean_object* v_a_7266_; lean_object* v___x_7267_; uint8_t v___x_7268_; 
v_a_7265_ = lean_ctor_get(v___x_7264_, 0);
lean_inc(v_a_7265_);
v_a_7266_ = lean_ctor_get(v___x_7264_, 1);
lean_inc(v_a_7266_);
lean_dec_ref_known(v___x_7264_, 2);
v___x_7267_ = lean_array_get_size(v_a_7266_);
v___x_7268_ = lean_nat_dec_lt(v___x_7261_, v___x_7267_);
if (v___x_7268_ == 0)
{
lean_dec(v_a_7266_);
v_a_7075_ = v_a_7265_;
goto v___jp_7074_;
}
else
{
lean_object* v___x_7269_; uint8_t v___x_7270_; 
v___x_7269_ = lean_box(0);
v___x_7270_ = lean_nat_dec_le(v___x_7267_, v___x_7267_);
if (v___x_7270_ == 0)
{
if (v___x_7268_ == 0)
{
lean_dec(v_a_7266_);
v_a_7075_ = v_a_7265_;
goto v___jp_7074_;
}
else
{
size_t v___x_7271_; size_t v___x_7272_; lean_object* v___x_7273_; 
v___x_7271_ = ((size_t)0ULL);
v___x_7272_ = lean_usize_of_nat(v___x_7267_);
v___x_7273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7266_, v___x_7271_, v___x_7272_, v___x_7269_, v_a_7069_);
lean_dec(v_a_7266_);
if (lean_obj_tag(v___x_7273_) == 0)
{
lean_dec_ref_known(v___x_7273_, 1);
v_a_7075_ = v_a_7265_;
goto v___jp_7074_;
}
else
{
lean_object* v_a_7274_; lean_object* v___x_7276_; uint8_t v_isShared_7277_; uint8_t v_isSharedCheck_7281_; 
lean_dec(v_a_7265_);
v_a_7274_ = lean_ctor_get(v___x_7273_, 0);
v_isSharedCheck_7281_ = !lean_is_exclusive(v___x_7273_);
if (v_isSharedCheck_7281_ == 0)
{
v___x_7276_ = v___x_7273_;
v_isShared_7277_ = v_isSharedCheck_7281_;
goto v_resetjp_7275_;
}
else
{
lean_inc(v_a_7274_);
lean_dec(v___x_7273_);
v___x_7276_ = lean_box(0);
v_isShared_7277_ = v_isSharedCheck_7281_;
goto v_resetjp_7275_;
}
v_resetjp_7275_:
{
lean_object* v___x_7279_; 
if (v_isShared_7277_ == 0)
{
v___x_7279_ = v___x_7276_;
goto v_reusejp_7278_;
}
else
{
lean_object* v_reuseFailAlloc_7280_; 
v_reuseFailAlloc_7280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7280_, 0, v_a_7274_);
v___x_7279_ = v_reuseFailAlloc_7280_;
goto v_reusejp_7278_;
}
v_reusejp_7278_:
{
return v___x_7279_;
}
}
}
}
}
else
{
size_t v___x_7282_; size_t v___x_7283_; lean_object* v___x_7284_; 
v___x_7282_ = ((size_t)0ULL);
v___x_7283_ = lean_usize_of_nat(v___x_7267_);
v___x_7284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7266_, v___x_7282_, v___x_7283_, v___x_7269_, v_a_7069_);
lean_dec(v_a_7266_);
if (lean_obj_tag(v___x_7284_) == 0)
{
lean_dec_ref_known(v___x_7284_, 1);
v_a_7075_ = v_a_7265_;
goto v___jp_7074_;
}
else
{
lean_object* v_a_7285_; lean_object* v___x_7287_; uint8_t v_isShared_7288_; uint8_t v_isSharedCheck_7292_; 
lean_dec(v_a_7265_);
v_a_7285_ = lean_ctor_get(v___x_7284_, 0);
v_isSharedCheck_7292_ = !lean_is_exclusive(v___x_7284_);
if (v_isSharedCheck_7292_ == 0)
{
v___x_7287_ = v___x_7284_;
v_isShared_7288_ = v_isSharedCheck_7292_;
goto v_resetjp_7286_;
}
else
{
lean_inc(v_a_7285_);
lean_dec(v___x_7284_);
v___x_7287_ = lean_box(0);
v_isShared_7288_ = v_isSharedCheck_7292_;
goto v_resetjp_7286_;
}
v_resetjp_7286_:
{
lean_object* v___x_7290_; 
if (v_isShared_7288_ == 0)
{
v___x_7290_ = v___x_7287_;
goto v_reusejp_7289_;
}
else
{
lean_object* v_reuseFailAlloc_7291_; 
v_reuseFailAlloc_7291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7291_, 0, v_a_7285_);
v___x_7290_ = v_reuseFailAlloc_7291_;
goto v_reusejp_7289_;
}
v_reusejp_7289_:
{
return v___x_7290_;
}
}
}
}
}
}
else
{
lean_object* v_a_7293_; lean_object* v___x_7294_; uint8_t v___x_7295_; 
v_a_7293_ = lean_ctor_get(v___x_7264_, 1);
lean_inc(v_a_7293_);
lean_dec_ref_known(v___x_7264_, 2);
v___x_7294_ = lean_array_get_size(v_a_7293_);
v___x_7295_ = lean_nat_dec_lt(v___x_7261_, v___x_7294_);
if (v___x_7295_ == 0)
{
lean_object* v___x_7296_; lean_object* v___x_7297_; 
lean_dec(v_a_7293_);
v___x_7296_ = lean_box(0);
v___x_7297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7297_, 0, v___x_7296_);
return v___x_7297_;
}
else
{
lean_object* v___x_7298_; uint8_t v___x_7299_; 
v___x_7298_ = lean_box(0);
v___x_7299_ = lean_nat_dec_le(v___x_7294_, v___x_7294_);
if (v___x_7299_ == 0)
{
if (v___x_7295_ == 0)
{
lean_dec(v_a_7293_);
goto v___jp_7071_;
}
else
{
size_t v___x_7300_; size_t v___x_7301_; lean_object* v___x_7302_; 
v___x_7300_ = ((size_t)0ULL);
v___x_7301_ = lean_usize_of_nat(v___x_7294_);
v___x_7302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7293_, v___x_7300_, v___x_7301_, v___x_7298_, v_a_7069_);
lean_dec(v_a_7293_);
if (lean_obj_tag(v___x_7302_) == 0)
{
lean_dec_ref_known(v___x_7302_, 1);
goto v___jp_7071_;
}
else
{
lean_object* v_a_7303_; lean_object* v___x_7305_; uint8_t v_isShared_7306_; uint8_t v_isSharedCheck_7310_; 
v_a_7303_ = lean_ctor_get(v___x_7302_, 0);
v_isSharedCheck_7310_ = !lean_is_exclusive(v___x_7302_);
if (v_isSharedCheck_7310_ == 0)
{
v___x_7305_ = v___x_7302_;
v_isShared_7306_ = v_isSharedCheck_7310_;
goto v_resetjp_7304_;
}
else
{
lean_inc(v_a_7303_);
lean_dec(v___x_7302_);
v___x_7305_ = lean_box(0);
v_isShared_7306_ = v_isSharedCheck_7310_;
goto v_resetjp_7304_;
}
v_resetjp_7304_:
{
lean_object* v___x_7308_; 
if (v_isShared_7306_ == 0)
{
v___x_7308_ = v___x_7305_;
goto v_reusejp_7307_;
}
else
{
lean_object* v_reuseFailAlloc_7309_; 
v_reuseFailAlloc_7309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7309_, 0, v_a_7303_);
v___x_7308_ = v_reuseFailAlloc_7309_;
goto v_reusejp_7307_;
}
v_reusejp_7307_:
{
return v___x_7308_;
}
}
}
}
}
else
{
size_t v___x_7311_; size_t v___x_7312_; lean_object* v___x_7313_; 
v___x_7311_ = ((size_t)0ULL);
v___x_7312_ = lean_usize_of_nat(v___x_7294_);
v___x_7313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7293_, v___x_7311_, v___x_7312_, v___x_7298_, v_a_7069_);
lean_dec(v_a_7293_);
if (lean_obj_tag(v___x_7313_) == 0)
{
lean_dec_ref_known(v___x_7313_, 1);
goto v___jp_7071_;
}
else
{
lean_object* v_a_7314_; lean_object* v___x_7316_; uint8_t v_isShared_7317_; uint8_t v_isSharedCheck_7321_; 
v_a_7314_ = lean_ctor_get(v___x_7313_, 0);
v_isSharedCheck_7321_ = !lean_is_exclusive(v___x_7313_);
if (v_isSharedCheck_7321_ == 0)
{
v___x_7316_ = v___x_7313_;
v_isShared_7317_ = v_isSharedCheck_7321_;
goto v_resetjp_7315_;
}
else
{
lean_inc(v_a_7314_);
lean_dec(v___x_7313_);
v___x_7316_ = lean_box(0);
v_isShared_7317_ = v_isSharedCheck_7321_;
goto v_resetjp_7315_;
}
v_resetjp_7315_:
{
lean_object* v___x_7319_; 
if (v_isShared_7317_ == 0)
{
v___x_7319_ = v___x_7316_;
goto v_reusejp_7318_;
}
else
{
lean_object* v_reuseFailAlloc_7320_; 
v_reuseFailAlloc_7320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7320_, 0, v_a_7314_);
v___x_7319_ = v_reuseFailAlloc_7320_;
goto v_reusejp_7318_;
}
v_reusejp_7318_:
{
return v___x_7319_;
}
}
}
}
}
}
}
else
{
goto v___jp_7241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_7348_, lean_object* v_cache_7349_, lean_object* v_service_7350_, lean_object* v_localScope_7351_, lean_object* v_remoteScope_7352_, lean_object* v_platform_7353_, lean_object* v_toolchain_7354_, lean_object* v_force_7355_, lean_object* v_a_7356_, lean_object* v_a_7357_){
_start:
{
uint8_t v_force_boxed_7358_; lean_object* v_res_7359_; 
v_force_boxed_7358_ = lean_unbox(v_force_7355_);
v_res_7359_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_7348_, v_cache_7349_, v_service_7350_, v_localScope_7351_, v_remoteScope_7352_, v_platform_7353_, v_toolchain_7354_, v_force_boxed_7358_, v_a_7356_);
lean_dec_ref(v_a_7356_);
return v_res_7359_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_7361_, lean_object* v_outputs_7362_, lean_object* v_service_7363_, lean_object* v_scope_7364_, lean_object* v_platform_7365_, lean_object* v_toolchain_7366_, lean_object* v_a_7367_){
_start:
{
lean_object* v_url_7369_; lean_object* v___y_7371_; lean_object* v_s_7387_; 
lean_inc_ref(v_scope_7364_);
lean_inc_ref(v_service_7363_);
v_url_7369_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7361_, v_service_7363_, v_scope_7364_, v_platform_7365_, v_toolchain_7366_);
v_s_7387_ = lean_ctor_get(v_scope_7364_, 0);
lean_inc_ref(v_s_7387_);
lean_dec_ref(v_scope_7364_);
v___y_7371_ = v_s_7387_;
goto v___jp_7370_;
v___jp_7370_:
{
lean_object* v___x_7372_; lean_object* v___x_7373_; lean_object* v___x_7374_; lean_object* v___x_7375_; lean_object* v___x_7376_; lean_object* v___x_7377_; lean_object* v___x_7378_; lean_object* v___x_7379_; lean_object* v___x_7380_; uint8_t v___x_7381_; lean_object* v___x_7382_; lean_object* v___x_7383_; lean_object* v_key_7384_; lean_object* v___x_7385_; lean_object* v___x_7386_; 
v___x_7372_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_7373_ = lean_string_append(v___y_7371_, v___x_7372_);
v___x_7374_ = lean_string_append(v___x_7373_, v_rev_7361_);
v___x_7375_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_7376_ = lean_string_append(v___x_7374_, v___x_7375_);
v___x_7377_ = lean_string_append(v___x_7376_, v_outputs_7362_);
v___x_7378_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_7379_ = lean_string_append(v___x_7377_, v___x_7378_);
v___x_7380_ = lean_string_append(v___x_7379_, v_url_7369_);
v___x_7381_ = 1;
v___x_7382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7382_, 0, v___x_7380_);
lean_ctor_set_uint8(v___x_7382_, sizeof(void*)*1, v___x_7381_);
lean_inc_ref(v_a_7367_);
v___x_7383_ = lean_apply_2(v_a_7367_, v___x_7382_, lean_box(0));
v_key_7384_ = lean_ctor_get(v_service_7363_, 1);
lean_inc_ref(v_key_7384_);
lean_dec_ref(v_service_7363_);
v___x_7385_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_7386_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_7367_, v_outputs_7362_, v___x_7385_, v_url_7369_, v_key_7384_);
return v___x_7386_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_7388_, lean_object* v_outputs_7389_, lean_object* v_service_7390_, lean_object* v_scope_7391_, lean_object* v_platform_7392_, lean_object* v_toolchain_7393_, lean_object* v_a_7394_, lean_object* v_a_7395_){
_start:
{
lean_object* v_res_7396_; 
v_res_7396_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_7388_, v_outputs_7389_, v_service_7390_, v_scope_7391_, v_platform_7392_, v_toolchain_7393_, v_a_7394_);
lean_dec_ref(v_a_7394_);
lean_dec_ref(v_toolchain_7393_);
lean_dec_ref(v_rev_7388_);
return v_res_7396_;
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
