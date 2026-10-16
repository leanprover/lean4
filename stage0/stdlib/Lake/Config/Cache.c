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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_getenv(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_byte_array_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_io_rename(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Date_fromJson_x3f(lean_object*);
uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* lean_io_metadata(lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheMap_parse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_parse___closed__0;
static lean_once_cell_t l_Lake_CacheMap_parse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_parse___closed__1;
static const lean_array_object l_Lake_CacheMap_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheMap_parse___closed__2 = (const lean_object*)&l_Lake_CacheMap_parse___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheMap_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": failed to open file: "};
static const lean_object* l_Lake_CacheMap_load___closed__0 = (const lean_object*)&l_Lake_CacheMap_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object*);
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
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "curl produced invalid JSON output: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "curl's JSON output did not contain a response code; JSON received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "failed to upload artifact, error "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "response_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "http_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "http_code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "curl's JSON output contained an invalid JSON response code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "; JSON received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
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
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CURL"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32_value;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ": uploading artifact "};
static const lean_object* l_Lake_CacheService_uploadArtifact___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tmp"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ": failed to copy artifact: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1(uint64_t, uint64_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = ": failed to persist temporary artifact: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = ": failed to read downloaded artifact: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ": uploaded artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": downloaded artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "property not found: http_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__0_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = ": unidentifiable transfer completed: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "curl produced invalid JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "exitcode"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exitcode: "};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "curl JSON:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstdout:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\n  Transfer error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to fetch artifact URLs\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\n          \nInvalid curl JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "curl produced unexpected output:\n"};
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
static size_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24;
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
lean_object* v_a_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_a_32_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_30_, 1);
v___x_33_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_34_ = l_Lake_instOrdDate_ord(v_a_32_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_35_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1));
v___x_36_ = lean_string_append(v_inputName_10_, v___x_35_);
v___x_37_ = l_Lake_Date_toString(v_a_32_);
v___x_38_ = lean_string_append(v___x_36_, v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2));
v___x_40_ = lean_string_append(v___x_38_, v___x_39_);
v___x_41_ = 2;
v___x_42_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v___x_41_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_array_push(v_a_12_, v___x_42_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_a_32_);
lean_dec_ref(v_inputName_10_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v_a_12_);
return v___x_47_;
}
}
}
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec_ref(v_line_11_);
v___x_48_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3));
v___x_49_ = lean_string_append(v_inputName_10_, v___x_48_);
v___x_50_ = 3;
v___x_51_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*1, v___x_50_);
v___x_52_ = lean_array_get_size(v_a_12_);
v___x_53_ = lean_array_push(v_a_12_, v___x_51_);
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object* v_inputName_55_, lean_object* v_line_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_55_, v_line_56_, v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(uint64_t v_a_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
else
{
lean_object* v_key_63_; lean_object* v_tail_64_; uint64_t v___x_65_; uint8_t v___x_66_; 
v_key_63_ = lean_ctor_get(v_x_61_, 0);
v_tail_64_ = lean_ctor_get(v_x_61_, 2);
v___x_65_ = lean_unbox_uint64(v_key_63_);
v___x_66_ = lean_uint64_dec_eq(v___x_65_, v_a_60_);
if (v___x_66_ == 0)
{
v_x_61_ = v_tail_64_;
goto _start;
}
else
{
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
uint64_t v_a_boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_a_boxed_70_ = lean_unbox_uint64(v_a_68_);
lean_dec_ref(v_a_68_);
v_res_71_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_boxed_70_, v_x_69_);
lean_dec(v_x_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
return v_x_73_;
}
else
{
lean_object* v_key_75_; lean_object* v_value_76_; lean_object* v_tail_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_101_; 
v_key_75_ = lean_ctor_get(v_x_74_, 0);
v_value_76_ = lean_ctor_get(v_x_74_, 1);
v_tail_77_ = lean_ctor_get(v_x_74_, 2);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_101_ == 0)
{
v___x_79_ = v_x_74_;
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_tail_77_);
lean_inc(v_value_76_);
lean_inc(v_key_75_);
lean_dec(v_x_74_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v_fold_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_81_ = lean_array_get_size(v_x_73_);
v___x_82_ = 32ULL;
v___x_83_ = lean_unbox_uint64(v_key_75_);
v___x_84_ = lean_uint64_shift_right(v___x_83_, v___x_82_);
v___x_85_ = lean_unbox_uint64(v_key_75_);
v_fold_86_ = lean_uint64_xor(v___x_85_, v___x_84_);
v___x_87_ = 16ULL;
v___x_88_ = lean_uint64_shift_right(v_fold_86_, v___x_87_);
v___x_89_ = lean_uint64_xor(v_fold_86_, v___x_88_);
v___x_90_ = lean_uint64_to_usize(v___x_89_);
v___x_91_ = lean_usize_of_nat(v___x_81_);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_sub(v___x_91_, v___x_92_);
v___x_94_ = lean_usize_land(v___x_90_, v___x_93_);
v___x_95_ = lean_array_uget_borrowed(v_x_73_, v___x_94_);
lean_inc(v___x_95_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 2, v___x_95_);
v___x_97_ = v___x_79_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_key_75_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_value_76_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v___x_95_);
v___x_97_ = v_reuseFailAlloc_100_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_array_uset(v_x_73_, v___x_94_, v___x_97_);
v_x_73_ = v___x_98_;
v_x_74_ = v_tail_77_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(lean_object* v_i_102_, lean_object* v_source_103_, lean_object* v_target_104_){
_start:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_array_get_size(v_source_103_);
v___x_106_ = lean_nat_dec_lt(v_i_102_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec_ref(v_source_103_);
lean_dec(v_i_102_);
return v_target_104_;
}
else
{
lean_object* v_es_107_; lean_object* v___x_108_; lean_object* v_source_109_; lean_object* v_target_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_es_107_ = lean_array_fget(v_source_103_, v_i_102_);
v___x_108_ = lean_box(0);
v_source_109_ = lean_array_fset(v_source_103_, v_i_102_, v___x_108_);
v_target_110_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(v_target_104_, v_es_107_);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_i_102_, v___x_111_);
lean_dec(v_i_102_);
v_i_102_ = v___x_112_;
v_source_103_ = v_source_109_;
v_target_104_ = v_target_110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(lean_object* v_data_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_nbuckets_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_115_ = lean_array_get_size(v_data_114_);
v___x_116_ = lean_unsigned_to_nat(2u);
v_nbuckets_117_ = lean_nat_mul(v___x_115_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_box(0);
v___x_120_ = lean_mk_array(v_nbuckets_117_, v___x_119_);
v___x_121_ = lean_array_propagate_mark(v_data_114_, v___x_120_);
v___x_122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(v___x_118_, v_data_114_, v___x_121_);
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
lean_object* v___x_448_; uint8_t v_decide_449_; 
v___x_448_ = lean_nat_sub(v___x_443_, v___x_444_);
v_decide_449_ = lean_nat_dec_eq(v_a_446_, v___x_448_);
lean_dec(v___x_448_);
if (v_decide_449_ == 0)
{
lean_object* v___x_450_; uint32_t v___x_451_; uint32_t v___x_452_; uint8_t v___x_453_; 
v___x_450_ = lean_nat_add(v___x_444_, v_a_446_);
v___x_451_ = lean_string_utf8_get_fast(v_contents_445_, v___x_450_);
v___x_452_ = 10;
v___x_453_ = lean_uint32_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_a_446_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_string_utf8_next_fast(v_contents_445_, v___x_450_);
lean_dec(v___x_450_);
v___x_456_ = lean_nat_sub(v___x_455_, v___x_444_);
v_a_446_ = v___x_456_;
v_b_447_ = v___x_454_;
goto _start;
}
else
{
lean_object* v___x_458_; 
lean_dec(v___x_450_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_a_446_);
return v___x_458_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg___boxed(lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v_contents_461_, lean_object* v_a_462_, lean_object* v_b_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_459_, v___x_460_, v_contents_461_, v_a_462_, v_b_463_);
lean_dec(v_b_463_);
lean_dec_ref(v_contents_461_);
lean_dec(v___x_460_);
lean_dec(v___x_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object* v_a_465_, lean_object* v_inputName_466_, uint8_t v_platformIndependent_467_, lean_object* v_i_468_, lean_object* v_cache_469_, lean_object* v_contents_470_, lean_object* v_pos_471_){
_start:
{
lean_object* v___x_473_; lean_object* v___y_475_; lean_object* v_searcher_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_473_ = lean_string_utf8_byte_size(v_contents_470_);
v_searcher_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_box(0);
v___x_495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_473_, v_pos_471_, v_contents_470_, v_searcher_493_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; 
v___x_496_ = lean_nat_sub(v___x_473_, v_pos_471_);
v___y_475_ = v___x_496_;
goto v___jp_474_;
}
else
{
lean_object* v_val_497_; 
v_val_497_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v___x_495_, 1);
v___y_475_ = v_val_497_;
goto v___jp_474_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v_line_477_; lean_object* v___x_478_; lean_object* v_startInclusive_479_; lean_object* v_endExclusive_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_476_ = lean_nat_add(v_pos_471_, v___y_475_);
lean_dec(v___y_475_);
lean_inc(v___x_476_);
lean_inc(v_pos_471_);
lean_inc_ref(v_contents_470_);
v_line_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_477_, 0, v_contents_470_);
lean_ctor_set(v_line_477_, 1, v_pos_471_);
lean_ctor_set(v_line_477_, 2, v___x_476_);
v___x_478_ = l_String_Slice_trimAscii(v_line_477_);
v_startInclusive_479_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_startInclusive_479_);
v_endExclusive_480_ = lean_ctor_get(v___x_478_, 2);
lean_inc(v_endExclusive_480_);
lean_dec_ref(v___x_478_);
v___x_481_ = lean_nat_sub(v_endExclusive_480_, v_startInclusive_479_);
lean_dec(v_startInclusive_479_);
lean_dec(v_endExclusive_480_);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_nat_dec_eq(v___x_481_, v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_string_utf8_extract_fast(v_contents_470_, v_pos_471_, v___x_476_);
lean_dec(v_pos_471_);
lean_inc(v_i_468_);
lean_inc_ref(v_inputName_466_);
v___x_485_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_466_, v_i_468_, v_cache_469_, v___x_484_, v_platformIndependent_467_, v_a_465_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; uint8_t v_decide_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_decide_487_ = lean_nat_dec_eq(v___x_476_, v___x_473_);
if (v_decide_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_i_468_, v___x_488_);
lean_dec(v_i_468_);
v___x_490_ = lean_string_utf8_next_fast(v_contents_470_, v___x_476_);
lean_dec(v___x_476_);
v_i_468_ = v___x_489_;
v_cache_469_ = v_a_486_;
v_pos_471_ = v___x_490_;
goto _start;
}
else
{
lean_dec(v___x_476_);
lean_dec_ref(v_contents_470_);
lean_dec(v_i_468_);
lean_dec_ref(v_inputName_466_);
return v___x_485_;
}
}
else
{
lean_dec(v___x_476_);
lean_dec_ref(v_contents_470_);
lean_dec(v_i_468_);
lean_dec_ref(v_inputName_466_);
return v___x_485_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v___x_476_);
lean_dec(v_pos_471_);
lean_dec_ref(v_contents_470_);
lean_dec(v_i_468_);
lean_dec_ref(v_inputName_466_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v_cache_469_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___boxed(lean_object* v_a_498_, lean_object* v_inputName_499_, lean_object* v_platformIndependent_500_, lean_object* v_i_501_, lean_object* v_cache_502_, lean_object* v_contents_503_, lean_object* v_pos_504_, lean_object* v_a_505_){
_start:
{
uint8_t v_platformIndependent_boxed_506_; lean_object* v_res_507_; 
v_platformIndependent_boxed_506_ = lean_unbox(v_platformIndependent_500_);
v_res_507_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_498_, v_inputName_499_, v_platformIndependent_boxed_506_, v_i_501_, v_cache_502_, v_contents_503_, v_pos_504_);
lean_dec_ref(v_a_498_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v_contents_510_, lean_object* v_a_511_, lean_object* v_b_512_){
_start:
{
lean_object* v___x_513_; uint8_t v_decide_514_; 
v___x_513_ = lean_nat_sub(v___x_508_, v___x_509_);
v_decide_514_ = lean_nat_dec_eq(v_a_511_, v___x_513_);
lean_dec(v___x_513_);
if (v_decide_514_ == 0)
{
lean_object* v___x_515_; uint32_t v___x_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_515_ = lean_nat_add(v___x_509_, v_a_511_);
v___x_516_ = lean_string_utf8_get_fast(v_contents_510_, v___x_515_);
v___x_517_ = 10;
v___x_518_ = lean_uint32_dec_eq(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_a_511_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_string_utf8_next_fast(v_contents_510_, v___x_515_);
lean_dec(v___x_515_);
v___x_521_ = lean_nat_sub(v___x_520_, v___x_509_);
v_a_511_ = v___x_521_;
v_b_512_ = v___x_519_;
goto _start;
}
else
{
lean_object* v___x_523_; 
lean_dec(v___x_515_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_a_511_);
return v___x_523_;
}
}
else
{
lean_dec(v_a_511_);
lean_inc(v_b_512_);
return v_b_512_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v_contents_526_, lean_object* v_a_527_, lean_object* v_b_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_524_, v___x_525_, v_contents_526_, v_a_527_, v_b_528_);
lean_dec(v_b_528_);
lean_dec_ref(v_contents_526_);
lean_dec(v___x_525_);
lean_dec(v___x_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object* v_inputName_530_, uint8_t v_platformIndependent_531_, lean_object* v_i_532_, lean_object* v_cache_533_, lean_object* v_contents_534_, lean_object* v_pos_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v___y_540_; lean_object* v_searcher_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_538_ = lean_string_utf8_byte_size(v_contents_534_);
v_searcher_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_box(0);
v___x_560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_538_, v_pos_535_, v_contents_534_, v_searcher_558_, v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_nat_sub(v___x_538_, v_pos_535_);
v___y_540_ = v___x_561_;
goto v___jp_539_;
}
else
{
lean_object* v_val_562_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_560_, 1);
v___y_540_ = v_val_562_;
goto v___jp_539_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v_line_542_; lean_object* v___x_543_; lean_object* v_startInclusive_544_; lean_object* v_endExclusive_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_541_ = lean_nat_add(v_pos_535_, v___y_540_);
lean_dec(v___y_540_);
lean_inc(v___x_541_);
lean_inc(v_pos_535_);
lean_inc_ref(v_contents_534_);
v_line_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_542_, 0, v_contents_534_);
lean_ctor_set(v_line_542_, 1, v_pos_535_);
lean_ctor_set(v_line_542_, 2, v___x_541_);
v___x_543_ = l_String_Slice_trimAscii(v_line_542_);
v_startInclusive_544_ = lean_ctor_get(v___x_543_, 1);
lean_inc(v_startInclusive_544_);
v_endExclusive_545_ = lean_ctor_get(v___x_543_, 2);
lean_inc(v_endExclusive_545_);
lean_dec_ref(v___x_543_);
v___x_546_ = lean_nat_sub(v_endExclusive_545_, v_startInclusive_544_);
lean_dec(v_startInclusive_544_);
lean_dec(v_endExclusive_545_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_nat_dec_eq(v___x_546_, v___x_547_);
lean_dec(v___x_546_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_string_utf8_extract_fast(v_contents_534_, v_pos_535_, v___x_541_);
lean_dec(v_pos_535_);
lean_inc(v_i_532_);
lean_inc_ref(v_inputName_530_);
v___x_550_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_530_, v_i_532_, v_cache_533_, v___x_549_, v_platformIndependent_531_, v_a_536_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; uint8_t v_decide_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_decide_552_ = lean_nat_dec_eq(v___x_541_, v___x_538_);
if (v_decide_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_i_532_, v___x_553_);
lean_dec(v_i_532_);
v___x_555_ = lean_string_utf8_next_fast(v_contents_534_, v___x_541_);
lean_dec(v___x_541_);
v___x_556_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_536_, v_inputName_530_, v_platformIndependent_531_, v___x_554_, v_a_551_, v_contents_534_, v___x_555_);
return v___x_556_;
}
else
{
lean_dec(v___x_541_);
lean_dec_ref(v_contents_534_);
lean_dec(v_i_532_);
lean_dec_ref(v_inputName_530_);
return v___x_550_;
}
}
else
{
lean_dec(v___x_541_);
lean_dec_ref(v_contents_534_);
lean_dec(v_i_532_);
lean_dec_ref(v_inputName_530_);
return v___x_550_;
}
}
else
{
lean_object* v___x_557_; 
lean_dec(v___x_541_);
lean_dec(v_pos_535_);
lean_dec_ref(v_contents_534_);
lean_dec(v_i_532_);
lean_dec_ref(v_inputName_530_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_cache_533_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object* v_inputName_563_, lean_object* v_platformIndependent_564_, lean_object* v_i_565_, lean_object* v_cache_566_, lean_object* v_contents_567_, lean_object* v_pos_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
uint8_t v_platformIndependent_boxed_571_; lean_object* v_res_572_; 
v_platformIndependent_boxed_571_ = lean_unbox(v_platformIndependent_564_);
v_res_572_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(v_inputName_563_, v_platformIndependent_boxed_571_, v_i_565_, v_cache_566_, v_contents_567_, v_pos_568_, v_a_569_);
lean_dec_ref(v_a_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object* v___x_573_, lean_object* v___x_574_, lean_object* v___x_575_, lean_object* v_contents_576_, lean_object* v_inst_577_, lean_object* v_R_578_, lean_object* v_a_579_, lean_object* v_b_580_, lean_object* v_c_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_573_, v___x_574_, v_contents_576_, v_a_579_, v_b_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object* v___x_583_, lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v_contents_586_, lean_object* v_inst_587_, lean_object* v_R_588_, lean_object* v_a_589_, lean_object* v_b_590_, lean_object* v_c_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(v___x_583_, v___x_584_, v___x_585_, v_contents_586_, v_inst_587_, v_R_588_, v_a_589_, v_b_590_, v_c_591_);
lean_dec(v_b_590_);
lean_dec_ref(v_contents_586_);
lean_dec_ref(v___x_585_);
lean_dec(v___x_584_);
lean_dec(v___x_583_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v_contents_596_, lean_object* v_inst_597_, lean_object* v_R_598_, lean_object* v_a_599_, lean_object* v_b_600_, lean_object* v_c_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_593_, v___x_594_, v_contents_596_, v_a_599_, v_b_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___boxed(lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v_contents_606_, lean_object* v_inst_607_, lean_object* v_R_608_, lean_object* v_a_609_, lean_object* v_b_610_, lean_object* v_c_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(v___x_603_, v___x_604_, v___x_605_, v_contents_606_, v_inst_607_, v_R_608_, v_a_609_, v_b_610_, v_c_611_);
lean_dec(v_b_610_);
lean_dec_ref(v_contents_606_);
lean_dec_ref(v___x_605_);
lean_dec(v___x_604_);
lean_dec(v___x_603_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object* v_as_613_, size_t v_i_614_, size_t v_stop_615_, lean_object* v_b_616_, lean_object* v___y_617_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_eq(v_i_614_, v_stop_615_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; size_t v___x_622_; size_t v___x_623_; 
v___x_620_ = lean_array_uget_borrowed(v_as_613_, v_i_614_);
lean_inc_ref(v___y_617_);
lean_inc(v___x_620_);
v___x_621_ = lean_apply_2(v___y_617_, v___x_620_, lean_box(0));
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_614_, v___x_622_);
v_i_614_ = v___x_623_;
v_b_616_ = v___x_621_;
goto _start;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_b_616_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; lean_object* v_res_634_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_as_626_, v_i_boxed_632_, v_stop_boxed_633_, v_b_629_, v___y_630_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v_as_626_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(lean_object* v___x_635_, lean_object* v_contents_636_, lean_object* v_a_637_, lean_object* v_b_638_){
_start:
{
uint8_t v_decide_639_; 
v_decide_639_ = lean_nat_dec_eq(v_a_637_, v___x_635_);
if (v_decide_639_ == 0)
{
uint32_t v___x_640_; uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_string_utf8_get_fast(v_contents_636_, v_a_637_);
v___x_641_ = 10;
v___x_642_ = lean_uint32_dec_eq(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box(0);
v___x_644_ = lean_string_utf8_next_fast(v_contents_636_, v_a_637_);
lean_dec(v_a_637_);
v_a_637_ = v___x_644_;
v_b_638_ = v___x_643_;
goto _start;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_a_637_);
return v___x_646_;
}
}
else
{
lean_dec(v_a_637_);
lean_inc(v_b_638_);
return v_b_638_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object* v___x_647_, lean_object* v_contents_648_, lean_object* v_a_649_, lean_object* v_b_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_647_, v_contents_648_, v_a_649_, v_b_650_);
lean_dec(v_b_650_);
lean_dec_ref(v_contents_648_);
lean_dec(v___x_647_);
return v_res_651_;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__0(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_box(0);
v___x_653_ = lean_unsigned_to_nat(16u);
v___x_654_ = lean_mk_array(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__1(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* v_inputName_660_, lean_object* v_contents_661_, uint8_t v_platformIndependent_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___y_666_; lean_object* v___y_676_; lean_object* v_searcher_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_searcher_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_string_utf8_byte_size(v_contents_661_);
v___x_728_ = lean_box(0);
v___x_729_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_727_, v_contents_661_, v_searcher_726_, v___x_728_);
if (lean_obj_tag(v___x_729_) == 0)
{
v___y_676_ = v___x_727_;
goto v___jp_675_;
}
else
{
lean_object* v_val_730_; 
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_729_, 1);
v___y_676_ = v_val_730_;
goto v___jp_675_;
}
v___jp_665_:
{
lean_object* v___x_667_; uint8_t v_decide_668_; 
v___x_667_ = lean_string_utf8_byte_size(v_contents_661_);
v_decide_668_ = lean_nat_dec_eq(v___y_666_, v___x_667_);
if (v_decide_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_unsigned_to_nat(2u);
v___x_670_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_671_ = lean_string_utf8_next_fast(v_contents_661_, v___y_666_);
lean_dec(v___y_666_);
v___x_672_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_663_, v_inputName_660_, v_platformIndependent_662_, v___x_669_, v___x_670_, v_contents_661_, v___x_671_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v___y_666_);
lean_dec_ref(v_contents_661_);
lean_dec_ref(v_inputName_660_);
v___x_673_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v_line_678_; lean_object* v___x_679_; lean_object* v_str_680_; lean_object* v_startInclusive_681_; lean_object* v_endExclusive_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_677_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_676_);
lean_inc_ref(v_contents_661_);
v_line_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_678_, 0, v_contents_661_);
lean_ctor_set(v_line_678_, 1, v___x_677_);
lean_ctor_set(v_line_678_, 2, v___y_676_);
v___x_679_ = l_String_Slice_trimAscii(v_line_678_);
v_str_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_ref(v_str_680_);
v_startInclusive_681_ = lean_ctor_get(v___x_679_, 1);
lean_inc(v_startInclusive_681_);
v_endExclusive_682_ = lean_ctor_get(v___x_679_, 2);
lean_inc(v_endExclusive_682_);
lean_dec_ref(v___x_679_);
v___x_683_ = lean_string_utf8_extract_fast(v_str_680_, v_startInclusive_681_, v_endExclusive_682_);
lean_dec(v_endExclusive_682_);
lean_dec(v_startInclusive_681_);
lean_dec_ref(v_str_680_);
v___x_684_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
lean_inc_ref(v_inputName_660_);
v___x_685_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_660_, v___x_683_, v___x_684_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_a_686_ = lean_ctor_get(v___x_685_, 1);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 2);
v___x_687_ = lean_array_get_size(v_a_686_);
v___x_688_ = lean_nat_dec_lt(v___x_677_, v___x_687_);
if (v___x_688_ == 0)
{
lean_dec(v_a_686_);
v___y_666_ = v___y_676_;
goto v___jp_665_;
}
else
{
lean_object* v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_689_ = lean_box(0);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_687_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_686_, v___x_690_, v___x_691_, v___x_689_, v_a_663_);
lean_dec(v_a_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_dec_ref_known(v___x_692_, 1);
v___y_666_ = v___y_676_;
goto v___jp_665_;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v___y_676_);
lean_dec_ref(v_contents_661_);
lean_dec_ref(v_inputName_660_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
lean_dec(v___y_676_);
lean_dec_ref(v_contents_661_);
lean_dec_ref(v_inputName_660_);
v_a_701_ = lean_ctor_get(v___x_685_, 1);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_685_, 2);
v___x_702_ = lean_array_get_size(v_a_701_);
v___x_703_ = lean_nat_dec_lt(v___x_677_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_a_701_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_box(0);
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_702_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_701_, v___x_707_, v___x_708_, v___x_706_, v_a_663_);
lean_dec(v_a_701_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_709_, 0);
lean_dec(v_unused_717_);
v___x_711_ = v___x_709_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_709_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 1);
lean_ctor_set(v___x_711_, 0, v___x_706_);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_706_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_709_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_709_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* v_inputName_731_, lean_object* v_contents_732_, lean_object* v_platformIndependent_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
uint8_t v_platformIndependent_boxed_736_; lean_object* v_res_737_; 
v_platformIndependent_boxed_736_ = lean_unbox(v_platformIndependent_733_);
v_res_737_ = l_Lake_CacheMap_parse(v_inputName_731_, v_contents_732_, v_platformIndependent_boxed_736_, v_a_734_);
lean_dec_ref(v_a_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(lean_object* v___x_738_, lean_object* v___x_739_, lean_object* v_contents_740_, lean_object* v_inst_741_, lean_object* v_R_742_, lean_object* v_a_743_, lean_object* v_b_744_, lean_object* v_c_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_738_, v_contents_740_, v_a_743_, v_b_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v_contents_749_, lean_object* v_inst_750_, lean_object* v_R_751_, lean_object* v_a_752_, lean_object* v_b_753_, lean_object* v_c_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(v___x_747_, v___x_748_, v_contents_749_, v_inst_750_, v_R_751_, v_a_752_, v_b_753_, v_c_754_);
lean_dec(v_b_753_);
lean_dec_ref(v_contents_749_);
lean_dec_ref(v___x_748_);
lean_dec(v___x_747_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object* v_inputName_756_, lean_object* v_lineNo_757_, lean_object* v_cache_758_, lean_object* v_line_759_, uint8_t v_platformIndependent_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
lean_inc_ref(v_cache_758_);
v___x_763_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_758_, v_line_759_, v_platformIndependent_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_766_ = lean_string_append(v_inputName_756_, v___x_765_);
v___x_767_ = l_Nat_reprFast(v_lineNo_757_);
v___x_768_ = lean_string_append(v___x_766_, v___x_767_);
lean_dec_ref(v___x_767_);
v___x_769_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_770_ = lean_string_append(v___x_768_, v___x_769_);
v___x_771_ = lean_string_append(v___x_770_, v_a_764_);
lean_dec(v_a_764_);
v___x_772_ = 2;
v___x_773_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*1, v___x_772_);
v___x_774_ = lean_array_push(v___y_761_, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_cache_758_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
return v___x_775_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_777_; 
lean_dec_ref(v_cache_758_);
lean_dec(v_lineNo_757_);
lean_dec_ref(v_inputName_756_);
v_a_776_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_763_, 1);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_a_776_);
lean_ctor_set(v___x_777_, 1, v___y_761_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object* v_inputName_778_, lean_object* v_lineNo_779_, lean_object* v_cache_780_, lean_object* v_line_781_, lean_object* v_platformIndependent_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v_platformIndependent_boxed_785_; lean_object* v_res_786_; 
v_platformIndependent_boxed_785_ = lean_unbox(v_platformIndependent_782_);
v_res_786_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_inputName_778_, v_lineNo_779_, v_cache_780_, v_line_781_, v_platformIndependent_boxed_785_, v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* v_h_787_, lean_object* v_fileName_788_, uint8_t v_platformIndependent_789_, lean_object* v_i_790_, lean_object* v_cache_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_io_prim_handle_get_line(v_h_787_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v___x_796_ = lean_string_utf8_byte_size(v_a_795_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_nat_dec_eq(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_inc(v_i_790_);
lean_inc_ref(v_fileName_788_);
v___x_799_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_fileName_788_, v_i_790_, v_cache_791_, v_a_795_, v_platformIndependent_789_, v_a_792_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
v_a_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_799_, 2);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v_i_790_, v___x_802_);
lean_dec(v_i_790_);
v_i_790_ = v___x_803_;
v_cache_791_ = v_a_800_;
v_a_792_ = v_a_801_;
goto _start;
}
else
{
lean_dec(v_i_790_);
lean_dec_ref(v_fileName_788_);
return v___x_799_;
}
}
else
{
lean_object* v___x_805_; 
lean_dec(v_a_795_);
lean_dec(v_i_790_);
lean_dec_ref(v_fileName_788_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_cache_791_);
lean_ctor_set(v___x_805_, 1, v_a_792_);
return v___x_805_;
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_cache_791_);
lean_dec(v_i_790_);
lean_dec_ref(v_fileName_788_);
v_a_806_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_794_, 1);
v___x_807_ = lean_io_error_to_string(v_a_806_);
v___x_808_ = 3;
v___x_809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v___x_808_);
v___x_810_ = lean_array_get_size(v_a_792_);
v___x_811_ = lean_array_push(v_a_792_, v___x_809_);
v___x_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* v_h_813_, lean_object* v_fileName_814_, lean_object* v_platformIndependent_815_, lean_object* v_i_816_, lean_object* v_cache_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
uint8_t v_platformIndependent_boxed_820_; lean_object* v_res_821_; 
v_platformIndependent_boxed_820_ = lean_unbox(v_platformIndependent_815_);
v_res_821_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_813_, v_fileName_814_, v_platformIndependent_boxed_820_, v_i_816_, v_cache_817_, v_a_818_);
lean_dec(v_h_813_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* v_h_822_, lean_object* v_fileName_823_, uint8_t v_platformIndependent_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_io_prim_handle_get_line(v_h_822_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
lean_inc_ref(v_fileName_823_);
v___x_829_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_fileName_823_, v_a_828_, v_a_825_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_830_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 2);
v___x_831_ = lean_unsigned_to_nat(2u);
v___x_832_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_833_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_822_, v_fileName_823_, v_platformIndependent_824_, v___x_831_, v___x_832_, v_a_830_);
return v___x_833_;
}
else
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_fileName_823_);
v_a_834_ = lean_ctor_get(v___x_829_, 0);
v_a_835_ = lean_ctor_get(v___x_829_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_829_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_a_834_);
lean_dec(v___x_829_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_fileName_823_);
v_a_843_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_827_, 1);
v___x_844_ = lean_io_error_to_string(v_a_843_);
v___x_845_ = 3;
v___x_846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_845_);
v___x_847_ = lean_array_get_size(v_a_825_);
v___x_848_ = lean_array_push(v_a_825_, v___x_846_);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* v_h_850_, lean_object* v_fileName_851_, lean_object* v_platformIndependent_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
uint8_t v_platformIndependent_boxed_855_; lean_object* v_res_856_; 
v_platformIndependent_boxed_855_ = lean_unbox(v_platformIndependent_852_);
v_res_856_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(v_h_850_, v_fileName_851_, v_platformIndependent_boxed_855_, v_a_853_);
lean_dec(v_h_850_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* v_file_858_, uint8_t v_platformIndependent_859_, lean_object* v_a_860_){
_start:
{
uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_862_ = 0;
v___x_863_ = lean_io_prim_handle_mk(v_file_858_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; uint8_t v___x_865_; lean_object* v___x_866_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = 0;
v___x_866_ = lean_io_prim_handle_lock(v_a_864_, v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_867_; 
lean_dec_ref_known(v___x_866_, 1);
v___x_867_ = lean_io_prim_handle_get_line(v_a_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
lean_inc_ref(v_file_858_);
v___x_869_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_858_, v_a_868_, v_a_860_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_a_870_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 2);
v___x_871_ = lean_unsigned_to_nat(2u);
v___x_872_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_873_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_864_, v_file_858_, v_platformIndependent_859_, v___x_871_, v___x_872_, v_a_870_);
lean_dec(v_a_864_);
return v___x_873_;
}
else
{
lean_object* v_a_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_864_);
lean_dec_ref(v_file_858_);
v_a_874_ = lean_ctor_get(v___x_869_, 0);
v_a_875_ = lean_ctor_get(v___x_869_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_869_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_inc(v_a_874_);
lean_dec(v___x_869_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_874_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_a_864_);
lean_dec_ref(v_file_858_);
v_a_883_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_867_, 1);
v___x_884_ = lean_io_error_to_string(v_a_883_);
v___x_885_ = 3;
v___x_886_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_885_);
v___x_887_ = lean_array_get_size(v_a_860_);
v___x_888_ = lean_array_push(v_a_860_, v___x_886_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
return v___x_889_;
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec(v_a_864_);
lean_dec_ref(v_file_858_);
v_a_890_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_866_, 1);
v___x_891_ = lean_io_error_to_string(v_a_890_);
v___x_892_ = 3;
v___x_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = lean_array_get_size(v_a_860_);
v___x_895_ = lean_array_push(v_a_860_, v___x_893_);
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
return v___x_896_;
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_a_897_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_863_, 1);
v___x_898_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_899_ = lean_string_append(v_file_858_, v___x_898_);
v___x_900_ = lean_io_error_to_string(v_a_897_);
v___x_901_ = lean_string_append(v___x_899_, v___x_900_);
lean_dec_ref(v___x_900_);
v___x_902_ = 3;
v___x_903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_902_);
v___x_904_ = lean_array_get_size(v_a_860_);
v___x_905_ = lean_array_push(v_a_860_, v___x_903_);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object* v_file_907_, lean_object* v_platformIndependent_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
uint8_t v_platformIndependent_boxed_911_; lean_object* v_res_912_; 
v_platformIndependent_boxed_911_ = lean_unbox(v_platformIndependent_908_);
v_res_912_ = l_Lake_CacheMap_load(v_file_907_, v_platformIndependent_boxed_911_, v_a_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* v_file_913_, uint8_t v_platformIndependent_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_a_918_; lean_object* v_a_919_; uint8_t v___x_921_; lean_object* v___x_922_; 
v___x_921_ = 0;
v___x_922_ = lean_io_prim_handle_mk(v_file_913_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v___x_924_ = 0;
v___x_925_ = lean_io_prim_handle_lock(v_a_923_, v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; 
lean_dec_ref_known(v___x_925_, 1);
v___x_926_ = lean_io_prim_handle_get_line(v_a_923_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_952_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_952_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_952_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_952_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; 
lean_inc_ref(v_file_913_);
v___x_931_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_913_, v_a_927_, v_a_915_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_a_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 2);
v___x_933_ = lean_unsigned_to_nat(2u);
v___x_934_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_935_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_923_, v_file_913_, v_platformIndependent_914_, v___x_933_, v___x_934_, v_a_932_);
lean_dec(v_a_923_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_a_937_ = lean_ctor_get(v___x_935_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 1);
lean_ctor_set(v___x_929_, 0, v_a_936_);
v___x_942_ = v___x_929_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_936_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_a_937_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v_a_949_; 
lean_del_object(v___x_929_);
v_a_948_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_948_);
v_a_949_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_935_, 2);
v_a_918_ = v_a_948_;
v_a_919_ = v_a_949_;
goto v___jp_917_;
}
}
else
{
lean_object* v_a_950_; lean_object* v_a_951_; 
lean_del_object(v___x_929_);
lean_dec(v_a_923_);
lean_dec_ref(v_file_913_);
v_a_950_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_950_);
v_a_951_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_931_, 2);
v_a_918_ = v_a_950_;
v_a_919_ = v_a_951_;
goto v___jp_917_;
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_a_923_);
lean_dec_ref(v_file_913_);
v_a_953_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_926_, 1);
v___x_954_ = lean_io_error_to_string(v_a_953_);
v___x_955_ = 3;
v___x_956_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*1, v___x_955_);
v___x_957_ = lean_array_get_size(v_a_915_);
v___x_958_ = lean_array_push(v_a_915_, v___x_956_);
v_a_918_ = v___x_957_;
v_a_919_ = v___x_958_;
goto v___jp_917_;
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_a_923_);
lean_dec_ref(v_file_913_);
v_a_959_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_925_, 1);
v___x_960_ = lean_io_error_to_string(v_a_959_);
v___x_961_ = 3;
v___x_962_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_961_);
v___x_963_ = lean_array_get_size(v_a_915_);
v___x_964_ = lean_array_push(v_a_915_, v___x_962_);
v___x_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
return v___x_965_;
}
}
else
{
lean_object* v_a_966_; 
v_a_966_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_922_, 1);
if (lean_obj_tag(v_a_966_) == 11)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec_ref_known(v_a_966_, 2);
lean_dec_ref(v_file_913_);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_a_915_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_969_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_970_ = lean_string_append(v_file_913_, v___x_969_);
v___x_971_ = lean_io_error_to_string(v_a_966_);
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
lean_dec_ref(v___x_971_);
v___x_973_ = 3;
v___x_974_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*1, v___x_973_);
v___x_975_ = lean_array_get_size(v_a_915_);
v___x_976_ = lean_array_push(v_a_915_, v___x_974_);
v___x_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
return v___x_977_;
}
}
v___jp_917_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_918_);
lean_ctor_set(v___x_920_, 1, v_a_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object* v_file_978_, lean_object* v_platformIndependent_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
uint8_t v_platformIndependent_boxed_982_; lean_object* v_res_983_; 
v_platformIndependent_boxed_982_ = lean_unbox(v_platformIndependent_979_);
v_res_983_ = l_Lake_CacheMap_load_x3f(v_file_978_, v_platformIndependent_boxed_982_, v_a_980_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object* v_h_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_x_985_);
lean_ctor_set(v___x_989_, 1, v___y_987_);
return v___x_989_;
}
else
{
lean_object* v_value_990_; lean_object* v_key_991_; lean_object* v_tail_992_; lean_object* v_out_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1018_; 
v_value_990_ = lean_ctor_get(v_x_986_, 1);
lean_inc(v_value_990_);
v_key_991_ = lean_ctor_get(v_x_986_, 0);
lean_inc(v_key_991_);
v_tail_992_ = lean_ctor_get(v_x_986_, 2);
lean_inc(v_tail_992_);
lean_dec_ref_known(v_x_986_, 3);
v_out_993_ = lean_ctor_get(v_value_990_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_value_990_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_995_ = v_value_990_;
v_isShared_996_ = v_isSharedCheck_1018_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_out_993_);
lean_dec(v_value_990_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1018_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint64_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_997_ = lean_unbox_uint64(v_key_991_);
lean_dec(v_key_991_);
v___x_998_ = l_Lake_lowerHexUInt64(v___x_997_);
v___x_999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
v___x_1000_ = lean_unsigned_to_nat(2u);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1002_ = lean_array_push(v___x_1001_, v___x_999_);
v___x_1003_ = lean_array_push(v___x_1002_, v_out_993_);
v___x_1004_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
v___x_1005_ = l_Lean_Json_compress(v___x_1004_);
v___x_1006_ = l_IO_FS_Handle_putStrLn(v_h_984_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; 
lean_del_object(v___x_995_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v_x_985_ = v_a_1007_;
v_x_986_ = v_tail_992_;
goto _start;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1013_; 
lean_dec(v_tail_992_);
v_a_1009_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1010_ = lean_io_error_to_string(v_a_1009_);
v___x_1011_ = 3;
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1010_);
v___x_1013_ = v___x_995_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1010_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_1011_);
v___x_1014_ = lean_array_get_size(v___y_987_);
v___x_1015_ = lean_array_push(v___y_987_, v___x_1013_);
v___x_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object* v_h_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1019_, v_x_1020_, v_x_1021_, v___y_1022_);
lean_dec(v_h_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object* v_h_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
v___x_1034_ = lean_box(0);
lean_inc(v___x_1033_);
v___x_1035_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1025_, v___x_1034_, v___x_1033_, v___y_1030_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v_a_1037_; size_t v___x_1038_; size_t v___x_1039_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
v_a_1037_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1035_, 2);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_add(v_i_1027_, v___x_1038_);
v_i_1027_ = v___x_1039_;
v_b_1029_ = v_a_1036_;
v___y_1030_ = v_a_1037_;
goto _start;
}
else
{
return v___x_1035_;
}
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_b_1029_);
lean_ctor_set(v___x_1041_, 1, v___y_1030_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object* v_h_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_stop_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_i_boxed_1049_; size_t v_stop_boxed_1050_; lean_object* v_res_1051_; 
v_i_boxed_1049_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_stop_boxed_1050_ = lean_unbox_usize(v_stop_1045_);
lean_dec(v_stop_1045_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1042_, v_as_1043_, v_i_boxed_1049_, v_stop_boxed_1050_, v_b_1046_, v___y_1047_);
lean_dec_ref(v_as_1043_);
lean_dec(v_h_1042_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object* v_h_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v___y_1055_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_x_1053_);
lean_ctor_set(v___x_1057_, 1, v___y_1055_);
return v___x_1057_;
}
else
{
lean_object* v_value_1058_; uint8_t v_platformIndependent_1059_; 
v_value_1058_ = lean_ctor_get(v_x_1054_, 1);
lean_inc(v_value_1058_);
v_platformIndependent_1059_ = lean_ctor_get_uint8(v_value_1058_, sizeof(void*)*1);
if (v_platformIndependent_1059_ == 0)
{
lean_object* v_tail_1060_; lean_object* v___x_1061_; 
lean_dec(v_value_1058_);
v_tail_1060_ = lean_ctor_get(v_x_1054_, 2);
lean_inc(v_tail_1060_);
lean_dec_ref_known(v_x_1054_, 3);
v___x_1061_ = lean_box(0);
v_x_1053_ = v___x_1061_;
v_x_1054_ = v_tail_1060_;
goto _start;
}
else
{
lean_object* v_key_1063_; lean_object* v_tail_1064_; lean_object* v_out_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1090_; 
v_key_1063_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_key_1063_);
v_tail_1064_ = lean_ctor_get(v_x_1054_, 2);
lean_inc(v_tail_1064_);
lean_dec_ref_known(v_x_1054_, 3);
v_out_1065_ = lean_ctor_get(v_value_1058_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_value_1058_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1067_ = v_value_1058_;
v_isShared_1068_ = v_isSharedCheck_1090_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_out_1065_);
lean_dec(v_value_1058_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1090_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
uint64_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1069_ = lean_unbox_uint64(v_key_1063_);
lean_dec(v_key_1063_);
v___x_1070_ = l_Lake_lowerHexUInt64(v___x_1069_);
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = lean_unsigned_to_nat(2u);
v___x_1073_ = lean_mk_empty_array_with_capacity(v___x_1072_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1071_);
v___x_1075_ = lean_array_push(v___x_1074_, v_out_1065_);
v___x_1076_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
v___x_1077_ = l_Lean_Json_compress(v___x_1076_);
v___x_1078_ = l_IO_FS_Handle_putStrLn(v_h_1052_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; 
lean_del_object(v___x_1067_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_x_1053_ = v_a_1079_;
v_x_1054_ = v_tail_1064_;
goto _start;
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1085_; 
lean_dec(v_tail_1064_);
v_a_1081_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1082_ = lean_io_error_to_string(v_a_1081_);
v___x_1083_ = 3;
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1082_);
v___x_1085_ = v___x_1067_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1082_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*1, v___x_1083_);
v___x_1086_ = lean_array_get_size(v___y_1055_);
v___x_1087_ = lean_array_push(v___y_1055_, v___x_1085_);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
return v___x_1088_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object* v_h_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1091_, v_x_1092_, v_x_1093_, v___y_1094_);
lean_dec(v_h_1091_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(lean_object* v_h_1097_, lean_object* v_as_1098_, size_t v_i_1099_, size_t v_stop_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_usize_dec_eq(v_i_1099_, v_stop_1100_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_array_uget_borrowed(v_as_1098_, v_i_1099_);
v___x_1106_ = lean_box(0);
lean_inc(v___x_1105_);
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1097_, v___x_1106_, v___x_1105_, v___y_1102_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v_a_1109_; size_t v___x_1110_; size_t v___x_1111_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
v_a_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1107_, 2);
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_add(v_i_1099_, v___x_1110_);
v_i_1099_ = v___x_1111_;
v_b_1101_ = v_a_1108_;
v___y_1102_ = v_a_1109_;
goto _start;
}
else
{
return v___x_1107_;
}
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1101_);
lean_ctor_set(v___x_1113_, 1, v___y_1102_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3___boxed(lean_object* v_h_1114_, lean_object* v_as_1115_, lean_object* v_i_1116_, lean_object* v_stop_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
size_t v_i_boxed_1121_; size_t v_stop_boxed_1122_; lean_object* v_res_1123_; 
v_i_boxed_1121_ = lean_unbox_usize(v_i_1116_);
lean_dec(v_i_1116_);
v_stop_boxed_1122_ = lean_unbox_usize(v_stop_1117_);
lean_dec(v_stop_1117_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1114_, v_as_1115_, v_i_boxed_1121_, v_stop_boxed_1122_, v_b_1118_, v___y_1119_);
lean_dec_ref(v_as_1115_);
lean_dec(v_h_1114_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(lean_object* v_h_1124_, lean_object* v_cache_1125_, uint8_t v_platformIndependent_1126_, lean_object* v_a_1127_){
_start:
{
if (v_platformIndependent_1126_ == 0)
{
lean_object* v_buckets_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1143_; 
v_buckets_1129_ = lean_ctor_get(v_cache_1125_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_cache_1125_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_cache_1125_, 0);
lean_dec(v_unused_1144_);
v___x_1131_ = v_cache_1125_;
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_buckets_1129_);
lean_dec(v_cache_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_size(v_buckets_1129_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v_buckets_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_a_1127_);
lean_ctor_set(v___x_1131_, 0, v___x_1135_);
v___x_1138_ = v___x_1131_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_a_1127_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
lean_del_object(v___x_1131_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = lean_usize_of_nat(v___x_1134_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1124_, v_buckets_1129_, v___x_1140_, v___x_1141_, v___x_1135_, v_a_1127_);
lean_dec_ref(v_buckets_1129_);
return v___x_1142_;
}
}
}
else
{
lean_object* v_buckets_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1159_; 
v_buckets_1145_ = lean_ctor_get(v_cache_1125_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_cache_1125_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_cache_1125_, 0);
lean_dec(v_unused_1160_);
v___x_1147_ = v_cache_1125_;
v_isShared_1148_ = v_isSharedCheck_1159_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_buckets_1145_);
lean_dec(v_cache_1125_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1159_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_array_get_size(v_buckets_1145_);
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_nat_dec_lt(v___x_1149_, v___x_1150_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1154_; 
lean_dec_ref(v_buckets_1145_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_a_1127_);
lean_ctor_set(v___x_1147_, 0, v___x_1151_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_a_1127_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
size_t v___x_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
lean_del_object(v___x_1147_);
v___x_1156_ = ((size_t)0ULL);
v___x_1157_ = lean_usize_of_nat(v___x_1150_);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1124_, v_buckets_1145_, v___x_1156_, v___x_1157_, v___x_1151_, v_a_1127_);
lean_dec_ref(v_buckets_1145_);
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries___boxed(lean_object* v_h_1161_, lean_object* v_cache_1162_, lean_object* v_platformIndependent_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
uint8_t v_platformIndependent_boxed_1166_; lean_object* v_res_1167_; 
v_platformIndependent_boxed_1166_ = lean_unbox(v_platformIndependent_1163_);
v_res_1167_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_h_1161_, v_cache_1162_, v_platformIndependent_boxed_1166_, v_a_1164_);
lean_dec(v_h_1161_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
return v_x_1168_;
}
else
{
lean_object* v_key_1170_; lean_object* v_value_1171_; lean_object* v_tail_1172_; uint64_t v___x_1173_; lean_object* v___x_1174_; 
v_key_1170_ = lean_ctor_get(v_x_1169_, 0);
lean_inc(v_key_1170_);
v_value_1171_ = lean_ctor_get(v_x_1169_, 1);
lean_inc(v_value_1171_);
v_tail_1172_ = lean_ctor_get(v_x_1169_, 2);
lean_inc(v_tail_1172_);
lean_dec_ref_known(v_x_1169_, 3);
v___x_1173_ = lean_unbox_uint64(v_key_1170_);
lean_dec(v_key_1170_);
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_x_1168_, v___x_1173_, v_value_1171_);
v_x_1168_ = v___x_1174_;
v_x_1169_ = v_tail_1172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(lean_object* v_as_1176_, size_t v_i_1177_, size_t v_stop_1178_, lean_object* v_b_1179_){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_usize_dec_eq(v_i_1177_, v_stop_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; 
v___x_1181_ = lean_array_uget_borrowed(v_as_1176_, v_i_1177_);
lean_inc(v___x_1181_);
v___x_1182_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(v_b_1179_, v___x_1181_);
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1177_, v___x_1183_);
v_i_1177_ = v___x_1184_;
v_b_1179_ = v___x_1182_;
goto _start;
}
else
{
return v_b_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object* v_as_1186_, lean_object* v_i_1187_, lean_object* v_stop_1188_, lean_object* v_b_1189_){
_start:
{
size_t v_i_boxed_1190_; size_t v_stop_boxed_1191_; lean_object* v_res_1192_; 
v_i_boxed_1190_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_stop_boxed_1191_ = lean_unbox_usize(v_stop_1188_);
lean_dec(v_stop_1188_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_as_1186_, v_i_boxed_1190_, v_stop_boxed_1191_, v_b_1189_);
lean_dec_ref(v_as_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* v_file_1193_, lean_object* v_cache_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_a_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; 
lean_inc_ref(v_file_1193_);
v___x_1201_ = l_Lake_createParentDirs(v_file_1193_);
if (lean_obj_tag(v___x_1201_) == 0)
{
uint8_t v___x_1202_; lean_object* v___x_1203_; 
lean_dec_ref_known(v___x_1201_, 1);
v___x_1202_ = 4;
v___x_1203_ = lean_io_prim_handle_mk(v_file_1193_, v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
uint8_t v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref_known(v___x_1203_, 1);
v___x_1204_ = 3;
v___x_1205_ = lean_io_prim_handle_mk(v_file_1193_, v___x_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = 1;
v___x_1208_ = lean_io_prim_handle_lock(v_a_1206_, v___x_1207_);
if (lean_obj_tag(v___x_1208_) == 0)
{
uint8_t v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref_known(v___x_1208_, 1);
v___x_1209_ = 0;
v___x_1210_ = lean_io_prim_handle_get_line(v_a_1206_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
lean_inc_ref(v_file_1193_);
v___x_1212_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_1193_, v_a_1211_, v_a_1195_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 2);
v___x_1214_ = lean_unsigned_to_nat(2u);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_1217_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_1206_, v_file_1193_, v___x_1209_, v___x_1214_, v___x_1216_, v_a_1213_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1242_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_a_1219_ = lean_ctor_get(v___x_1217_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1221_ = v___x_1217_;
v_isShared_1222_ = v_isSharedCheck_1242_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1242_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___y_1224_; lean_object* v_buckets_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_buckets_1236_ = lean_ctor_get(v_cache_1194_, 1);
v___x_1237_ = lean_array_get_size(v_buckets_1236_);
v___x_1238_ = lean_nat_dec_lt(v___x_1215_, v___x_1237_);
if (v___x_1238_ == 0)
{
v___y_1224_ = v_a_1218_;
goto v___jp_1223_;
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1237_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1236_, v___x_1239_, v___x_1240_, v_a_1218_);
v___y_1224_ = v___x_1241_;
goto v___jp_1223_;
}
v___jp_1223_:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_io_prim_handle_rewind(v_a_1206_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1225_, 1);
lean_del_object(v___x_1221_);
v___x_1226_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1206_, v___y_1224_, v___x_1209_, v_a_1219_);
lean_dec(v_a_1206_);
return v___x_1226_;
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
lean_dec_ref(v___y_1224_);
lean_dec(v_a_1206_);
v_a_1227_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1228_ = lean_io_error_to_string(v_a_1227_);
v___x_1229_ = 3;
v___x_1230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set_uint8(v___x_1230_, sizeof(void*)*1, v___x_1229_);
v___x_1231_ = lean_array_get_size(v_a_1219_);
v___x_1232_ = lean_array_push(v_a_1219_, v___x_1230_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 1, v___x_1232_);
lean_ctor_set(v___x_1221_, 0, v___x_1231_);
v___x_1234_ = v___x_1221_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v_a_1244_; 
lean_dec(v_a_1206_);
v_a_1243_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1243_);
v_a_1244_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1217_, 2);
v_a_1198_ = v_a_1243_;
v_a_1199_ = v_a_1244_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_a_1245_; lean_object* v_a_1246_; 
lean_dec(v_a_1206_);
lean_dec_ref(v_file_1193_);
v_a_1245_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1245_);
v_a_1246_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1212_, 2);
v_a_1198_ = v_a_1245_;
v_a_1199_ = v_a_1246_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec(v_a_1206_);
lean_dec_ref(v_file_1193_);
v_a_1247_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1248_ = lean_io_error_to_string(v_a_1247_);
v___x_1249_ = 3;
v___x_1250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set_uint8(v___x_1250_, sizeof(void*)*1, v___x_1249_);
v___x_1251_ = lean_array_get_size(v_a_1195_);
v___x_1252_ = lean_array_push(v_a_1195_, v___x_1250_);
v_a_1198_ = v___x_1251_;
v_a_1199_ = v___x_1252_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_a_1206_);
lean_dec_ref(v_file_1193_);
v_a_1253_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1254_ = lean_io_error_to_string(v_a_1253_);
v___x_1255_ = 3;
v___x_1256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*1, v___x_1255_);
v___x_1257_ = lean_array_get_size(v_a_1195_);
v___x_1258_ = lean_array_push(v_a_1195_, v___x_1256_);
v___x_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
return v___x_1259_;
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_a_1260_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1261_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1262_ = lean_string_append(v_file_1193_, v___x_1261_);
v___x_1263_ = lean_io_error_to_string(v_a_1260_);
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = 3;
v___x_1266_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*1, v___x_1265_);
v___x_1267_ = lean_array_get_size(v_a_1195_);
v___x_1268_ = lean_array_push(v_a_1195_, v___x_1266_);
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
return v___x_1269_;
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v_file_1193_);
v_a_1270_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1271_ = lean_io_error_to_string(v_a_1270_);
v___x_1272_ = 3;
v___x_1273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*1, v___x_1272_);
v___x_1274_ = lean_array_get_size(v_a_1195_);
v___x_1275_ = lean_array_push(v_a_1195_, v___x_1273_);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
return v___x_1276_;
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref(v_file_1193_);
v_a_1277_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1201_, 1);
v___x_1278_ = lean_io_error_to_string(v_a_1277_);
v___x_1279_ = 3;
v___x_1280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*1, v___x_1279_);
v___x_1281_ = lean_array_get_size(v_a_1195_);
v___x_1282_ = lean_array_push(v_a_1195_, v___x_1280_);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
return v___x_1283_;
}
v___jp_1197_:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_a_1198_);
lean_ctor_set(v___x_1200_, 1, v_a_1199_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object* v_file_1284_, lean_object* v_cache_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lake_CacheMap_updateFile(v_file_1284_, v_cache_1285_, v_a_1286_);
lean_dec_ref(v_cache_1285_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__0(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_1290_ = l_Lake_Date_toString(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__0, &l_Lake_CacheMap_writeFile___closed__0_once, _init_l_Lake_CacheMap_writeFile___closed__0);
v___x_1292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__2(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__1, &l_Lake_CacheMap_writeFile___closed__1_once, _init_l_Lake_CacheMap_writeFile___closed__1);
v___x_1294_ = l_Lean_Json_compress(v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* v_file_1295_, lean_object* v_cache_1296_, uint8_t v_platformIndependent_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
lean_inc_ref(v_file_1295_);
v___x_1300_ = l_Lake_createParentDirs(v_file_1295_);
if (lean_obj_tag(v___x_1300_) == 0)
{
uint8_t v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref_known(v___x_1300_, 1);
v___x_1301_ = 1;
v___x_1302_ = lean_io_prim_handle_mk(v_file_1295_, v___x_1301_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_file_1295_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = 1;
v___x_1305_ = lean_io_prim_handle_lock(v_a_1303_, v___x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref_known(v___x_1305_, 1);
v___x_1306_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__2, &l_Lake_CacheMap_writeFile___closed__2_once, _init_l_Lake_CacheMap_writeFile___closed__2);
v___x_1307_ = l_IO_FS_Handle_putStrLn(v_a_1303_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref_known(v___x_1307_, 1);
v___x_1308_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1303_, v_cache_1296_, v_platformIndependent_1297_, v_a_1298_);
lean_dec(v_a_1303_);
return v___x_1308_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_a_1303_);
lean_dec_ref(v_cache_1296_);
v_a_1309_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1310_ = lean_io_error_to_string(v_a_1309_);
v___x_1311_ = 3;
v___x_1312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1, v___x_1311_);
v___x_1313_ = lean_array_get_size(v_a_1298_);
v___x_1314_ = lean_array_push(v_a_1298_, v___x_1312_);
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
return v___x_1315_;
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_a_1303_);
lean_dec_ref(v_cache_1296_);
v_a_1316_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1317_ = lean_io_error_to_string(v_a_1316_);
v___x_1318_ = 3;
v___x_1319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*1, v___x_1318_);
v___x_1320_ = lean_array_get_size(v_a_1298_);
v___x_1321_ = lean_array_push(v_a_1298_, v___x_1319_);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
return v___x_1322_;
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_cache_1296_);
v_a_1323_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1324_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1325_ = lean_string_append(v_file_1295_, v___x_1324_);
v___x_1326_ = lean_io_error_to_string(v_a_1323_);
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = 3;
v___x_1329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1, v___x_1328_);
v___x_1330_ = lean_array_get_size(v_a_1298_);
v___x_1331_ = lean_array_push(v_a_1298_, v___x_1329_);
v___x_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
return v___x_1332_;
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_cache_1296_);
lean_dec_ref(v_file_1295_);
v_a_1333_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1334_ = lean_io_error_to_string(v_a_1333_);
v___x_1335_ = 3;
v___x_1336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*1, v___x_1335_);
v___x_1337_ = lean_array_get_size(v_a_1298_);
v___x_1338_ = lean_array_push(v_a_1298_, v___x_1336_);
v___x_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object* v_file_1340_, lean_object* v_cache_1341_, lean_object* v_platformIndependent_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
uint8_t v_platformIndependent_boxed_1345_; lean_object* v_res_1346_; 
v_platformIndependent_boxed_1345_ = lean_unbox(v_platformIndependent_1342_);
v_res_1346_ = l_Lake_CacheMap_writeFile(v_file_1340_, v_cache_1341_, v_platformIndependent_boxed_1345_, v_a_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t v_a_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
else
{
lean_object* v_key_1350_; lean_object* v_value_1351_; lean_object* v_tail_1352_; uint64_t v___x_1353_; uint8_t v___x_1354_; 
v_key_1350_ = lean_ctor_get(v_x_1348_, 0);
v_value_1351_ = lean_ctor_get(v_x_1348_, 1);
v_tail_1352_ = lean_ctor_get(v_x_1348_, 2);
v___x_1353_ = lean_unbox_uint64(v_key_1350_);
v___x_1354_ = lean_uint64_dec_eq(v___x_1353_, v_a_1347_);
if (v___x_1354_ == 0)
{
v_x_1348_ = v_tail_1352_;
goto _start;
}
else
{
lean_object* v___x_1356_; 
lean_inc(v_value_1351_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_value_1351_);
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1357_, lean_object* v_x_1358_){
_start:
{
uint64_t v_a_boxed_1359_; lean_object* v_res_1360_; 
v_a_boxed_1359_ = lean_unbox_uint64(v_a_1357_);
lean_dec_ref(v_a_1357_);
v_res_1360_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_boxed_1359_, v_x_1358_);
lean_dec(v_x_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* v_m_1361_, uint64_t v_a_1362_){
_start:
{
lean_object* v_buckets_1363_; lean_object* v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v_fold_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_buckets_1363_ = lean_ctor_get(v_m_1361_, 1);
v___x_1364_ = lean_array_get_size(v_buckets_1363_);
v___x_1365_ = 32ULL;
v___x_1366_ = lean_uint64_shift_right(v_a_1362_, v___x_1365_);
v_fold_1367_ = lean_uint64_xor(v_a_1362_, v___x_1366_);
v___x_1368_ = 16ULL;
v___x_1369_ = lean_uint64_shift_right(v_fold_1367_, v___x_1368_);
v___x_1370_ = lean_uint64_xor(v_fold_1367_, v___x_1369_);
v___x_1371_ = lean_uint64_to_usize(v___x_1370_);
v___x_1372_ = lean_usize_of_nat(v___x_1364_);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_usize_land(v___x_1371_, v___x_1374_);
v___x_1376_ = lean_array_uget_borrowed(v_buckets_1363_, v___x_1375_);
v___x_1377_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1362_, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* v_m_1378_, lean_object* v_a_1379_){
_start:
{
uint64_t v_a_boxed_1380_; lean_object* v_res_1381_; 
v_a_boxed_1380_ = lean_unbox_uint64(v_a_1379_);
lean_dec_ref(v_a_1379_);
v_res_1381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1378_, v_a_boxed_1380_);
lean_dec_ref(v_m_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t v_inputHash_1382_, lean_object* v_cache_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_cache_1383_, v_inputHash_1382_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_box(0);
return v___x_1385_;
}
else
{
lean_object* v_val_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1394_; 
v_val_1386_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1388_ = v___x_1384_;
v_isShared_1389_ = v_isSharedCheck_1394_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_val_1386_);
lean_dec(v___x_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1394_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v_out_1390_; lean_object* v___x_1392_; 
v_out_1390_ = lean_ctor_get(v_val_1386_, 0);
lean_inc(v_out_1390_);
lean_dec(v_val_1386_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v_out_1390_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_out_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* v_inputHash_1395_, lean_object* v_cache_1396_){
_start:
{
uint64_t v_inputHash_boxed_1397_; lean_object* v_res_1398_; 
v_inputHash_boxed_1397_ = lean_unbox_uint64(v_inputHash_1395_);
lean_dec_ref(v_inputHash_1395_);
v_res_1398_ = l_Lake_CacheMap_get_x3f(v_inputHash_boxed_1397_, v_cache_1396_);
lean_dec_ref(v_cache_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_, uint64_t v_a_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1400_, v_a_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* v_00_u03b2_1403_, lean_object* v_m_1404_, lean_object* v_a_1405_){
_start:
{
uint64_t v_a_boxed_1406_; lean_object* v_res_1407_; 
v_a_boxed_1406_ = lean_unbox_uint64(v_a_1405_);
lean_dec_ref(v_a_1405_);
v_res_1407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(v_00_u03b2_1403_, v_m_1404_, v_a_boxed_1406_);
lean_dec_ref(v_m_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1408_, uint64_t v_a_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1409_, v_x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1412_, lean_object* v_a_1413_, lean_object* v_x_1414_){
_start:
{
uint64_t v_a_boxed_1415_; lean_object* v_res_1416_; 
v_a_boxed_1415_ = lean_unbox_uint64(v_a_1413_);
lean_dec_ref(v_a_1413_);
v_res_1416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(v_00_u03b2_1412_, v_a_boxed_1415_, v_x_1414_);
lean_dec(v_x_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t v_inputHash_1417_, lean_object* v_out_1418_, lean_object* v_cache_1419_, uint8_t v_platformIndependent_1420_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1421_, 0, v_out_1418_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*1, v_platformIndependent_1420_);
v___x_1422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_cache_1419_, v_inputHash_1417_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore___boxed(lean_object* v_inputHash_1423_, lean_object* v_out_1424_, lean_object* v_cache_1425_, lean_object* v_platformIndependent_1426_){
_start:
{
uint64_t v_inputHash_boxed_1427_; uint8_t v_platformIndependent_boxed_1428_; lean_object* v_res_1429_; 
v_inputHash_boxed_1427_ = lean_unbox_uint64(v_inputHash_1423_);
lean_dec_ref(v_inputHash_1423_);
v_platformIndependent_boxed_1428_ = lean_unbox(v_platformIndependent_1426_);
v_res_1429_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_boxed_1427_, v_out_1424_, v_cache_1425_, v_platformIndependent_boxed_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* v_inst_1430_, uint64_t v_inputHash_1431_, lean_object* v_val_1432_, lean_object* v_cache_1433_, uint8_t v_platformIndependent_1434_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_apply_1(v_inst_1430_, v_val_1432_);
v___x_1436_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1431_, v___x_1435_, v_cache_1433_, v_platformIndependent_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* v_inst_1437_, lean_object* v_inputHash_1438_, lean_object* v_val_1439_, lean_object* v_cache_1440_, lean_object* v_platformIndependent_1441_){
_start:
{
uint64_t v_inputHash_boxed_1442_; uint8_t v_platformIndependent_boxed_1443_; lean_object* v_res_1444_; 
v_inputHash_boxed_1442_ = lean_unbox_uint64(v_inputHash_1438_);
lean_dec_ref(v_inputHash_1438_);
v_platformIndependent_boxed_1443_ = lean_unbox(v_platformIndependent_1441_);
v_res_1444_ = l_Lake_CacheMap_insert___redArg(v_inst_1437_, v_inputHash_boxed_1442_, v_val_1439_, v_cache_1440_, v_platformIndependent_boxed_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* v_00_u03b1_1445_, lean_object* v_inst_1446_, uint64_t v_inputHash_1447_, lean_object* v_val_1448_, lean_object* v_cache_1449_, uint8_t v_platformIndependent_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_apply_1(v_inst_1446_, v_val_1448_);
v___x_1452_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1447_, v___x_1451_, v_cache_1449_, v_platformIndependent_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* v_00_u03b1_1453_, lean_object* v_inst_1454_, lean_object* v_inputHash_1455_, lean_object* v_val_1456_, lean_object* v_cache_1457_, lean_object* v_platformIndependent_1458_){
_start:
{
uint64_t v_inputHash_boxed_1459_; uint8_t v_platformIndependent_boxed_1460_; lean_object* v_res_1461_; 
v_inputHash_boxed_1459_ = lean_unbox_uint64(v_inputHash_1455_);
lean_dec_ref(v_inputHash_1455_);
v_platformIndependent_boxed_1460_ = lean_unbox(v_platformIndependent_1458_);
v_res_1461_ = l_Lake_CacheMap_insert(v_00_u03b1_1453_, v_inst_1454_, v_inputHash_boxed_1459_, v_val_1456_, v_cache_1457_, v_platformIndependent_boxed_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* v_init_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_){
_start:
{
if (lean_obj_tag(v_x_1466_) == 0)
{
lean_object* v_v_1469_; lean_object* v_l_1470_; lean_object* v_r_1471_; lean_object* v___x_1472_; 
v_v_1469_ = lean_ctor_get(v_x_1466_, 2);
lean_inc(v_v_1469_);
v_l_1470_ = lean_ctor_get(v_x_1466_, 3);
lean_inc(v_l_1470_);
v_r_1471_ = lean_ctor_get(v_x_1466_, 4);
lean_inc(v_r_1471_);
lean_dec_ref_known(v_x_1466_, 5);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1465_, v_l_1470_, v___y_1467_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
v_a_1474_ = lean_ctor_get(v___x_1472_, 1);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1472_, 2);
v___x_1475_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1473_, v_v_1469_, v_a_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_a_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v_a_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1475_, 2);
v_init_1465_ = v_a_1476_;
v_x_1466_ = v_r_1471_;
v___y_1467_ = v_a_1477_;
goto _start;
}
else
{
lean_dec(v_r_1471_);
return v___x_1475_;
}
}
else
{
lean_dec(v_r_1471_);
lean_dec(v_v_1469_);
return v___x_1472_;
}
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_init_1465_);
lean_ctor_set(v___x_1479_, 1, v___y_1467_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* v_as_1480_, lean_object* v_o_1481_, lean_object* v_a_1482_){
_start:
{
switch(lean_obj_tag(v_o_1481_))
{
case 2:
{
lean_object* v_n_1484_; lean_object* v___x_1485_; 
v_n_1484_ = lean_ctor_get(v_o_1481_, 0);
lean_inc_ref(v_n_1484_);
lean_dec_ref_known(v_o_1481_, 1);
v___x_1485_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
v___x_1488_ = lean_string_append(v___x_1487_, v_a_1486_);
lean_dec(v_a_1486_);
v___x_1489_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_1490_ = lean_string_append(v___x_1488_, v___x_1489_);
v___x_1491_ = l_Lean_JsonNumber_toString(v_n_1484_);
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = 3;
v___x_1494_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1, v___x_1493_);
v___x_1495_ = lean_array_push(v_a_1482_, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_as_1480_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
return v___x_1496_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint64_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref(v_n_1484_);
v_a_1497_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1498_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1));
v___x_1499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
v___x_1500_ = lean_unbox_uint64(v_a_1497_);
lean_dec(v_a_1497_);
lean_ctor_set_uint64(v___x_1499_, sizeof(void*)*1, v___x_1500_);
v___x_1501_ = lean_array_push(v_as_1480_, v___x_1499_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v_a_1482_);
return v___x_1502_;
}
}
case 3:
{
lean_object* v_s_1503_; lean_object* v___x_1504_; 
v_s_1503_ = lean_ctor_get(v_o_1481_, 0);
lean_inc_ref(v_s_1503_);
lean_dec_ref_known(v_o_1481_, 1);
v___x_1504_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1503_);
lean_dec_ref(v_s_1503_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2));
v___x_1507_ = lean_string_append(v___x_1506_, v_a_1505_);
lean_dec(v_a_1505_);
v___x_1508_ = 3;
v___x_1509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*1, v___x_1508_);
v___x_1510_ = lean_array_push(v_a_1482_, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_as_1480_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1512_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1513_ = lean_array_push(v_as_1480_, v_a_1512_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_a_1482_);
return v___x_1514_;
}
}
case 4:
{
lean_object* v_elems_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_elems_1515_ = lean_ctor_get(v_o_1481_, 0);
lean_inc_ref(v_elems_1515_);
lean_dec_ref_known(v_o_1481_, 1);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get_size(v_elems_1515_);
v___x_1518_ = lean_nat_dec_lt(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec_ref(v_elems_1515_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_as_1480_);
lean_ctor_set(v___x_1519_, 1, v_a_1482_);
return v___x_1519_;
}
else
{
size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = lean_usize_of_nat(v___x_1517_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1515_, v___x_1520_, v___x_1521_, v_as_1480_, v_a_1482_);
lean_dec_ref(v_elems_1515_);
return v___x_1522_;
}
}
case 5:
{
lean_object* v_kvPairs_1523_; lean_object* v___x_1524_; 
v_kvPairs_1523_ = lean_ctor_get(v_o_1481_, 0);
lean_inc(v_kvPairs_1523_);
lean_dec_ref_known(v_o_1481_, 1);
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_as_1480_, v_kvPairs_1523_, v_a_1482_);
return v___x_1524_;
}
default: 
{
lean_object* v___x_1525_; 
lean_dec(v_o_1481_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_as_1480_);
lean_ctor_set(v___x_1525_, 1, v_a_1482_);
return v___x_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* v_as_1526_, size_t v_i_1527_, size_t v_stop_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_usize_dec_eq(v_i_1527_, v_stop_1528_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_array_uget_borrowed(v_as_1526_, v_i_1527_);
lean_inc(v___x_1533_);
v___x_1534_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_b_1529_, v___x_1533_, v___y_1530_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_a_1536_; size_t v___x_1537_; size_t v___x_1538_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
v_a_1536_ = lean_ctor_get(v___x_1534_, 1);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1534_, 2);
v___x_1537_ = ((size_t)1ULL);
v___x_1538_ = lean_usize_add(v_i_1527_, v___x_1537_);
v_i_1527_ = v___x_1538_;
v_b_1529_ = v_a_1535_;
v___y_1530_ = v_a_1536_;
goto _start;
}
else
{
return v___x_1534_;
}
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_b_1529_);
lean_ctor_set(v___x_1540_, 1, v___y_1530_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* v_as_1541_, lean_object* v_i_1542_, lean_object* v_stop_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
size_t v_i_boxed_1547_; size_t v_stop_boxed_1548_; lean_object* v_res_1549_; 
v_i_boxed_1547_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_stop_boxed_1548_ = lean_unbox_usize(v_stop_1543_);
lean_dec(v_stop_1543_);
v_res_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_as_1541_, v_i_boxed_1547_, v_stop_boxed_1548_, v_b_1544_, v___y_1545_);
lean_dec_ref(v_as_1541_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* v_init_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1550_, v_x_1551_, v___y_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* v_as_1555_, lean_object* v_o_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_as_1555_, v_o_1556_, v_a_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_x_1560_);
lean_ctor_set(v___x_1564_, 1, v___y_1562_);
return v___x_1564_;
}
else
{
lean_object* v_value_1565_; lean_object* v_tail_1566_; lean_object* v_out_1567_; lean_object* v___x_1568_; 
v_value_1565_ = lean_ctor_get(v_x_1561_, 1);
lean_inc(v_value_1565_);
v_tail_1566_ = lean_ctor_get(v_x_1561_, 2);
lean_inc(v_tail_1566_);
lean_dec_ref_known(v_x_1561_, 3);
v_out_1567_ = lean_ctor_get(v_value_1565_, 0);
lean_inc(v_out_1567_);
lean_dec(v_value_1565_);
v___x_1568_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_x_1560_, v_out_1567_, v___y_1562_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_a_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
v_a_1570_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1568_, 2);
v_x_1560_ = v_a_1569_;
v_x_1561_ = v_tail_1566_;
v___y_1562_ = v_a_1570_;
goto _start;
}
else
{
lean_dec(v_tail_1566_);
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_x_1572_, v_x_1573_, v___y_1574_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* v_as_1577_, size_t v_i_1578_, size_t v_stop_1579_, lean_object* v_b_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_eq(v_i_1578_, v_stop_1579_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_array_uget_borrowed(v_as_1577_, v_i_1578_);
lean_inc(v___x_1584_);
v___x_1585_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_b_1580_, v___x_1584_, v___y_1581_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v_a_1587_; size_t v___x_1588_; size_t v___x_1589_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
v_a_1587_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1585_, 2);
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1578_, v___x_1588_);
v_i_1578_ = v___x_1589_;
v_b_1580_ = v_a_1586_;
v___y_1581_ = v_a_1587_;
goto _start;
}
else
{
return v___x_1585_;
}
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_b_1580_);
lean_ctor_set(v___x_1591_, 1, v___y_1581_);
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* v_as_1592_, lean_object* v_i_1593_, lean_object* v_stop_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
size_t v_i_boxed_1598_; size_t v_stop_boxed_1599_; lean_object* v_res_1600_; 
v_i_boxed_1598_ = lean_unbox_usize(v_i_1593_);
lean_dec(v_i_1593_);
v_stop_boxed_1599_ = lean_unbox_usize(v_stop_1594_);
lean_dec(v_stop_1594_);
v_res_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_as_1592_, v_i_boxed_1598_, v_stop_boxed_1599_, v_b_1595_, v___y_1596_);
lean_dec_ref(v_as_1592_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* v_map_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_buckets_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1628_; 
v_buckets_1606_ = lean_ctor_get(v_map_1603_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_map_1603_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_map_1603_, 0);
lean_dec(v_unused_1629_);
v___x_1608_ = v_map_1603_;
v_isShared_1609_ = v_isSharedCheck_1628_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_buckets_1606_);
lean_dec(v_map_1603_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1628_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___y_1614_; lean_object* v_a_1615_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = ((lean_object*)(l_Lake_CacheMap_collectOutputDescrs___closed__0));
v___x_1612_ = lean_array_get_size(v_a_1604_);
v___x_1621_ = lean_array_get_size(v_buckets_1606_);
v___x_1622_ = lean_nat_dec_lt(v___x_1610_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
lean_dec_ref(v_buckets_1606_);
lean_inc_ref(v_a_1604_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1611_);
lean_ctor_set(v___x_1623_, 1, v_a_1604_);
v___y_1614_ = v___x_1623_;
v_a_1615_ = v_a_1604_;
goto v___jp_1613_;
}
else
{
size_t v___x_1624_; size_t v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = ((size_t)0ULL);
v___x_1625_ = lean_usize_of_nat(v___x_1621_);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1606_, v___x_1624_, v___x_1625_, v___x_1611_, v_a_1604_);
lean_dec_ref(v_buckets_1606_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_a_1627_);
v___y_1614_ = v___x_1626_;
v_a_1615_ = v_a_1627_;
goto v___jp_1613_;
}
else
{
lean_del_object(v___x_1608_);
return v___x_1626_;
}
}
v___jp_1613_:
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = lean_array_get_size(v_a_1615_);
v___x_1617_ = lean_nat_dec_eq(v___x_1612_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v___y_1614_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 1);
lean_ctor_set(v___x_1608_, 1, v_a_1615_);
lean_ctor_set(v___x_1608_, 0, v___x_1612_);
v___x_1619_ = v___x_1608_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1615_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_dec_ref(v_a_1615_);
lean_del_object(v___x_1608_);
return v___y_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* v_map_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lake_CacheMap_collectOutputDescrs(v_map_1630_, v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* v_init_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_st_mk_ref(v_init_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* v_init_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lake_CacheRef_mk(v_init_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t v_inputHash_1640_, lean_object* v_cache_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_st_ref_take(v_cache_1641_);
v___x_1644_ = l_Lake_CacheMap_get_x3f(v_inputHash_1640_, v___x_1643_);
v___x_1645_ = lean_st_ref_put(v_cache_1641_, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* v_inputHash_1646_, lean_object* v_cache_1647_, lean_object* v_a_1648_){
_start:
{
uint64_t v_inputHash_boxed_1649_; lean_object* v_res_1650_; 
v_inputHash_boxed_1649_ = lean_unbox_uint64(v_inputHash_1646_);
lean_dec_ref(v_inputHash_1646_);
v_res_1650_ = l_Lake_CacheRef_get_x3f(v_inputHash_boxed_1649_, v_cache_1647_);
lean_dec(v_cache_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* v_inst_1651_, uint64_t v_inputHash_1652_, lean_object* v_val_1653_, lean_object* v_cache_1654_, uint8_t v_platformIndependent_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1657_ = lean_st_ref_take(v_cache_1654_);
v___x_1658_ = lean_apply_1(v_inst_1651_, v_val_1653_);
v___x_1659_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1652_, v___x_1658_, v___x_1657_, v_platformIndependent_1655_);
v___x_1660_ = lean_st_ref_put(v_cache_1654_, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* v_inst_1661_, lean_object* v_inputHash_1662_, lean_object* v_val_1663_, lean_object* v_cache_1664_, lean_object* v_platformIndependent_1665_, lean_object* v_a_1666_){
_start:
{
uint64_t v_inputHash_boxed_1667_; uint8_t v_platformIndependent_boxed_1668_; lean_object* v_res_1669_; 
v_inputHash_boxed_1667_ = lean_unbox_uint64(v_inputHash_1662_);
lean_dec_ref(v_inputHash_1662_);
v_platformIndependent_boxed_1668_ = lean_unbox(v_platformIndependent_1665_);
v_res_1669_ = l_Lake_CacheRef_insert___redArg(v_inst_1661_, v_inputHash_boxed_1667_, v_val_1663_, v_cache_1664_, v_platformIndependent_boxed_1668_);
lean_dec(v_cache_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* v_00_u03b1_1670_, lean_object* v_inst_1671_, uint64_t v_inputHash_1672_, lean_object* v_val_1673_, lean_object* v_cache_1674_, uint8_t v_platformIndependent_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_st_ref_take(v_cache_1674_);
v___x_1678_ = lean_apply_1(v_inst_1671_, v_val_1673_);
v___x_1679_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1672_, v___x_1678_, v___x_1677_, v_platformIndependent_1675_);
v___x_1680_ = lean_st_ref_put(v_cache_1674_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_inst_1682_, lean_object* v_inputHash_1683_, lean_object* v_val_1684_, lean_object* v_cache_1685_, lean_object* v_platformIndependent_1686_, lean_object* v_a_1687_){
_start:
{
uint64_t v_inputHash_boxed_1688_; uint8_t v_platformIndependent_boxed_1689_; lean_object* v_res_1690_; 
v_inputHash_boxed_1688_ = lean_unbox_uint64(v_inputHash_1683_);
lean_dec_ref(v_inputHash_1683_);
v_platformIndependent_boxed_1689_ = lean_unbox(v_platformIndependent_1686_);
v_res_1690_ = l_Lake_CacheRef_insert(v_00_u03b1_1681_, v_inst_1682_, v_inputHash_boxed_1688_, v_val_1684_, v_cache_1685_, v_platformIndependent_boxed_1689_);
lean_dec(v_cache_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object* v_s_1693_){
_start:
{
lean_inc_ref(v_s_1693_);
return v_s_1693_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object* v_s_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lake_CacheServiceName_ofString(v_s_1694_);
lean_dec_ref(v_s_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object* v_self_1696_){
_start:
{
lean_inc_ref(v_self_1696_);
return v_self_1696_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object* v_self_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lake_CacheServiceName_toString(v_self_1697_);
lean_dec_ref(v_self_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object* v_j_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Json_getStr_x3f(v_j_1701_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1702_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1702_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object* v_self_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_self_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___impl(lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_obj_tag_nat(v_x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___impl___boxed(lean_object* v_x_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___impl(v_x_1727_);
lean_dec_ref(v_x_1727_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object* v_t_1729_, lean_object* v_k_1730_){
_start:
{
lean_object* v_s_1731_; lean_object* v___x_1732_; 
v_s_1731_ = lean_ctor_get(v_t_1729_, 0);
lean_inc_ref(v_s_1731_);
lean_dec_ref(v_t_1729_);
v___x_1732_ = lean_apply_1(v_k_1730_, v_s_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object* v_motive_1733_, lean_object* v_ctorIdx_1734_, lean_object* v_t_1735_, lean_object* v_h_1736_, lean_object* v_k_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1735_, v_k_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object* v_motive_1739_, lean_object* v_ctorIdx_1740_, lean_object* v_t_1741_, lean_object* v_h_1742_, lean_object* v_k_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(v_motive_1739_, v_ctorIdx_1740_, v_t_1741_, v_h_1742_, v_k_1743_);
lean_dec(v_ctorIdx_1740_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object* v_t_1745_, lean_object* v_str_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1745_, v_str_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object* v_motive_1748_, lean_object* v_t_1749_, lean_object* v_h_1750_, lean_object* v_str_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1749_, v_str_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object* v_t_1753_, lean_object* v_repo_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1753_, v_repo_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object* v_motive_1756_, lean_object* v_t_1757_, lean_object* v_h_1758_, lean_object* v_repo_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1757_, v_repo_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object* v_s_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_s_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object* v_fullName_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_fullName_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object* v_self_1765_){
_start:
{
if (lean_obj_tag(v_self_1765_) == 1)
{
uint8_t v___x_1766_; 
v___x_1766_ = 1;
return v___x_1766_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object* v_self_1768_){
_start:
{
uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_res_1769_ = l_Lake_CacheServiceScope_isRepo(v_self_1768_);
lean_dec_ref(v_self_1768_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object* v_self_1771_){
_start:
{
lean_object* v_s_1772_; 
v_s_1772_ = lean_ctor_get(v_self_1771_, 0);
lean_inc_ref(v_s_1772_);
return v_s_1772_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object* v_self_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lake_CacheServiceScope_toString(v_self_1773_);
lean_dec_ref(v_self_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object* v_self_1777_){
_start:
{
lean_object* v_s_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_s_1778_ = lean_ctor_get(v_self_1777_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_self_1777_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v_self_1777_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_s_1778_);
lean_dec(v_self_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 3);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_s_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object* v_data_1795_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1797_, 0, v_data_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1798_){
_start:
{
if (lean_obj_tag(v_x_1798_) == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_box(0);
return v___x_1799_;
}
else
{
lean_object* v_val_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_val_1800_ = lean_ctor_get(v_x_1798_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_x_1798_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v_x_1798_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_val_1800_);
lean_dec(v_x_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 3);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_val_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
static lean_object* _init_l_Lake_CacheOutput_toJson___closed__3(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__2));
v___x_1813_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1814_ = lean_box(1);
v___x_1815_ = l_Lake_JsonObject_insertJson(v___x_1814_, v___x_1813_, v___x_1812_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object* v_out_1819_){
_start:
{
lean_object* v_data_1820_; lean_object* v_service_x3f_1821_; lean_object* v_scope_x3f_1822_; lean_object* v_obj_1824_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v_obj_1831_; 
v_data_1820_ = lean_ctor_get(v_out_1819_, 0);
lean_inc(v_data_1820_);
v_service_x3f_1821_ = lean_ctor_get(v_out_1819_, 1);
lean_inc(v_service_x3f_1821_);
v_scope_x3f_1822_ = lean_ctor_get(v_out_1819_, 2);
lean_inc(v_scope_x3f_1822_);
lean_dec_ref(v_out_1819_);
v___x_1828_ = lean_obj_once(&l_Lake_CacheOutput_toJson___closed__3, &l_Lake_CacheOutput_toJson___closed__3_once, _init_l_Lake_CacheOutput_toJson___closed__3);
v___x_1829_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1830_ = l_Lean_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1821_);
v_obj_1831_ = l_Lake_JsonObject_insertJson(v___x_1828_, v___x_1829_, v___x_1830_);
if (lean_obj_tag(v_scope_x3f_1822_) == 1)
{
lean_object* v_val_1832_; lean_object* v___y_1834_; uint8_t v___x_1837_; 
v_val_1832_ = lean_ctor_get(v_scope_x3f_1822_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v_scope_x3f_1822_, 1);
v___x_1837_ = l_Lake_CacheServiceScope_isRepo(v_val_1832_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___y_1834_ = v___x_1838_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1839_; 
v___x_1839_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___y_1834_ = v___x_1839_;
goto v___jp_1833_;
}
v___jp_1833_:
{
lean_object* v___x_1835_; lean_object* v_obj_1836_; 
v___x_1835_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(v_val_1832_);
lean_inc_ref(v___y_1834_);
v_obj_1836_ = l_Lake_JsonObject_insertJson(v_obj_1831_, v___y_1834_, v___x_1835_);
v_obj_1824_ = v_obj_1836_;
goto v___jp_1823_;
}
}
else
{
lean_dec(v_scope_x3f_1822_);
v_obj_1824_ = v_obj_1831_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1826_ = l_Lake_JsonObject_insertJson(v_obj_1824_, v___x_1825_, v_data_1820_);
v___x_1827_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_object* v___x_1845_; 
v___x_1845_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Json_getStr_x3f(v_x_1844_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
v_a_1855_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1857_ = v___x_1846_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1846_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1864_){
_start:
{
if (lean_obj_tag(v_x_1864_) == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Json_getStr_x3f(v_x_1864_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1883_; 
v_a_1875_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1877_ = v___x_1866_;
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1866_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object* v_k_1884_, lean_object* v_t_1885_){
_start:
{
if (lean_obj_tag(v_t_1885_) == 0)
{
lean_object* v_k_1886_; lean_object* v_l_1887_; lean_object* v_r_1888_; uint8_t v___x_1889_; 
v_k_1886_ = lean_ctor_get(v_t_1885_, 1);
v_l_1887_ = lean_ctor_get(v_t_1885_, 3);
v_r_1888_ = lean_ctor_get(v_t_1885_, 4);
v___x_1889_ = lean_string_compare(v_k_1884_, v_k_1886_);
switch(v___x_1889_)
{
case 0:
{
v_t_1885_ = v_l_1887_;
goto _start;
}
case 1:
{
uint8_t v___x_1891_; 
v___x_1891_ = 1;
return v___x_1891_;
}
default: 
{
v_t_1885_ = v_r_1888_;
goto _start;
}
}
}
else
{
uint8_t v___x_1893_; 
v___x_1893_ = 0;
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object* v_k_1894_, lean_object* v_t_1895_){
_start:
{
uint8_t v_res_1896_; lean_object* v_r_1897_; 
v_res_1896_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1894_, v_t_1895_);
lean_dec(v_t_1895_);
lean_dec_ref(v_k_1894_);
v_r_1897_ = lean_box(v_res_1896_);
return v_r_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object* v_json_1904_){
_start:
{
if (lean_obj_tag(v_json_1904_) == 5)
{
lean_object* v_kvPairs_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_kvPairs_1909_ = lean_ctor_get(v_json_1904_, 0);
v___x_1910_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1911_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v___x_1910_, v_kvPairs_1909_);
if (v___x_1911_ == 0)
{
goto v___jp_1905_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_inc(v_kvPairs_1909_);
lean_dec_ref_known(v_json_1904_, 1);
v___x_1912_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1913_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1909_, v___x_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_kvPairs_1909_);
v___x_1914_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__1));
return v___x_1914_;
}
else
{
lean_object* v_val_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_2009_; 
v_val_1915_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1917_ = v___x_1913_;
v_isShared_1918_ = v_isSharedCheck_2009_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_val_1915_);
lean_dec(v___x_1913_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_2009_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___y_1920_; lean_object* v_a_1921_; lean_object* v___y_1927_; lean_object* v___y_1930_; lean_object* v_a_1962_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1994_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1909_, v___x_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_box(0);
v_a_1962_ = v___x_1995_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_1996_; lean_object* v___x_1997_; 
v_val_1996_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v___x_1994_, 1);
v___x_1997_ = l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2007_; 
lean_del_object(v___x_1917_);
lean_dec(v_val_1915_);
lean_dec(v_kvPairs_1909_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__4));
v___x_2003_ = lean_string_append(v___x_2002_, v_a_1998_);
lean_dec(v_a_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v_a_2008_; 
v_a_2008_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_1997_, 1);
v_a_1962_ = v_a_2008_;
goto v___jp_1961_;
}
}
v___jp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1922_, 0, v_val_1915_);
lean_ctor_set(v___x_1922_, 1, v___y_1920_);
lean_ctor_set(v___x_1922_, 2, v_a_1921_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1922_);
v___x_1924_ = v___x_1917_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
v___jp_1926_:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_box(0);
v___y_1920_ = v___y_1927_;
v_a_1921_ = v___x_1928_;
goto v___jp_1919_;
}
v___jp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___x_1932_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1909_, v___x_1931_);
lean_dec(v_kvPairs_1909_);
if (lean_obj_tag(v___x_1932_) == 0)
{
v___y_1927_ = v___y_1930_;
goto v___jp_1926_;
}
else
{
lean_object* v_val_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1960_; 
v_val_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1960_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_val_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1960_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1933_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1935_);
lean_dec(v___y_1930_);
lean_del_object(v___x_1917_);
lean_dec(v_val_1915_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1947_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1947_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1942_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__2));
v___x_1943_ = lean_string_append(v___x_1942_, v_a_1938_);
lean_dec(v_a_1938_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1937_, 1);
if (lean_obj_tag(v_a_1948_) == 1)
{
lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1959_; 
v_val_1949_ = lean_ctor_get(v_a_1948_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1951_ = v_a_1948_;
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_dec(v_a_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set_tag(v___x_1935_, 0);
lean_ctor_set(v___x_1935_, 0, v_val_1949_);
v___x_1954_ = v___x_1935_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_val_1949_);
v___x_1954_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1954_);
v___x_1956_ = v___x_1951_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
v___y_1920_ = v___y_1930_;
v_a_1921_ = v___x_1956_;
goto v___jp_1919_;
}
}
}
}
else
{
lean_dec(v_a_1948_);
lean_del_object(v___x_1935_);
v___y_1927_ = v___y_1930_;
goto v___jp_1926_;
}
}
}
}
}
v___jp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___x_1964_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1909_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
v___y_1930_ = v_a_1962_;
goto v___jp_1929_;
}
else
{
lean_object* v_val_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1992_; 
v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1992_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_val_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1992_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1965_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1967_);
lean_dec(v_a_1962_);
lean_del_object(v___x_1917_);
lean_dec(v_val_1915_);
lean_dec(v_kvPairs_1909_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__3));
v___x_1975_ = lean_string_append(v___x_1974_, v_a_1970_);
lean_dec(v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1975_);
v___x_1977_ = v___x_1972_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1969_, 1);
if (lean_obj_tag(v_a_1980_) == 1)
{
lean_object* v_val_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_kvPairs_1909_);
v_val_1981_ = lean_ctor_get(v_a_1980_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1983_ = v_a_1980_;
v_isShared_1984_ = v_isSharedCheck_1991_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_val_1981_);
lean_dec(v_a_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1991_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_val_1981_);
v___x_1986_ = v___x_1967_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_val_1981_);
v___x_1986_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1986_);
v___x_1988_ = v___x_1983_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v___y_1920_ = v_a_1962_;
v_a_1921_ = v___x_1988_;
goto v___jp_1919_;
}
}
}
}
else
{
lean_dec(v_a_1980_);
lean_del_object(v___x_1967_);
v___y_1930_ = v_a_1962_;
goto v___jp_1929_;
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
goto v___jp_1905_;
}
v___jp_1905_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1907_, 0, v_json_1904_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object* v_00_u03b2_2010_, lean_object* v_k_2011_, lean_object* v_t_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_2011_, v_t_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object* v_00_u03b2_2014_, lean_object* v_k_2015_, lean_object* v_t_2016_){
_start:
{
uint8_t v_res_2017_; lean_object* v_r_2018_; 
v_res_2017_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(v_00_u03b2_2014_, v_k_2015_, v_t_2016_);
lean_dec(v_t_2016_);
lean_dec_ref(v_k_2015_);
v_r_2018_ = lean_box(v_res_2017_);
return v_r_2018_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2027_ = l_System_FilePath_join(v_cache_2025_, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_2029_, uint64_t v_contentHash_2030_, lean_object* v_ext_2031_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2032_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2033_ = l_System_FilePath_join(v_cache_2029_, v___x_2032_);
v___x_2034_ = lean_string_utf8_byte_size(v_ext_2031_);
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_nat_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2037_ = l_Lake_lowerHexUInt64(v_contentHash_2030_);
v___x_2038_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2039_ = lean_string_append(v___x_2037_, v___x_2038_);
v___x_2040_ = lean_string_append(v___x_2039_, v_ext_2031_);
v___x_2041_ = l_System_FilePath_join(v___x_2033_, v___x_2040_);
return v___x_2041_;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = l_Lake_lowerHexUInt64(v_contentHash_2030_);
v___x_2043_ = l_System_FilePath_join(v___x_2033_, v___x_2042_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_2044_, lean_object* v_contentHash_2045_, lean_object* v_ext_2046_){
_start:
{
uint64_t v_contentHash_boxed_2047_; lean_object* v_res_2048_; 
v_contentHash_boxed_2047_ = lean_unbox_uint64(v_contentHash_2045_);
lean_dec_ref(v_contentHash_2045_);
v_res_2048_ = l_Lake_Cache_artifactPath(v_cache_2044_, v_contentHash_boxed_2047_, v_ext_2046_);
lean_dec_ref(v_ext_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_2049_, lean_object* v_descr_2050_){
_start:
{
uint64_t v_hash_2052_; lean_object* v_ext_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___y_2057_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_hash_2052_ = lean_ctor_get_uint64(v_descr_2050_, sizeof(void*)*1);
v_ext_2053_ = lean_ctor_get(v_descr_2050_, 0);
v___x_2054_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2055_ = l_System_FilePath_join(v_cache_2049_, v___x_2054_);
v___x_2071_ = lean_string_utf8_byte_size(v_ext_2053_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_nat_dec_eq(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2074_ = l_Lake_lowerHexUInt64(v_hash_2052_);
v___x_2075_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
v___x_2077_ = lean_string_append(v___x_2076_, v_ext_2053_);
v___y_2057_ = v___x_2077_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lake_lowerHexUInt64(v_hash_2052_);
v___y_2057_ = v___x_2078_;
goto v___jp_2056_;
}
v___jp_2056_:
{
lean_object* v_path_2058_; lean_object* v___x_2059_; 
v_path_2058_ = l_System_FilePath_join(v___x_2055_, v___y_2057_);
v___x_2059_ = lean_io_metadata(v_path_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2069_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2069_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2069_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_modified_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v_modified_2064_ = lean_ctor_get(v_a_2060_, 1);
lean_inc_ref(v_modified_2064_);
lean_dec(v_a_2060_);
lean_inc_ref(v_path_2058_);
v___x_2065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2065_, 0, v_descr_2050_);
lean_ctor_set(v___x_2065_, 1, v_path_2058_);
lean_ctor_set(v___x_2065_, 2, v_path_2058_);
lean_ctor_set(v___x_2065_, 3, v_modified_2064_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
lean_ctor_set(v___x_2062_, 0, v___x_2065_);
v___x_2067_ = v___x_2062_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
else
{
lean_object* v___x_2070_; 
lean_dec_ref_known(v___x_2059_, 1);
lean_dec_ref(v_path_2058_);
lean_dec_ref(v_descr_2050_);
v___x_2070_ = lean_box(0);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_2079_, lean_object* v_descr_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lake_Cache_getArtifact_x3f(v_cache_2079_, v_descr_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_2085_, lean_object* v_descr_2086_){
_start:
{
uint64_t v_hash_2088_; lean_object* v_ext_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___y_2093_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_hash_2088_ = lean_ctor_get_uint64(v_descr_2086_, sizeof(void*)*1);
v_ext_2089_ = lean_ctor_get(v_descr_2086_, 0);
v___x_2090_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2091_ = l_System_FilePath_join(v_cache_2085_, v___x_2090_);
v___x_2122_ = lean_string_utf8_byte_size(v_ext_2089_);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_nat_dec_eq(v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = l_Lake_lowerHexUInt64(v_hash_2088_);
v___x_2126_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
v___x_2128_ = lean_string_append(v___x_2127_, v_ext_2089_);
v___y_2093_ = v___x_2128_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lake_lowerHexUInt64(v_hash_2088_);
v___y_2093_ = v___x_2129_;
goto v___jp_2092_;
}
v___jp_2092_:
{
lean_object* v_path_2094_; lean_object* v___x_2095_; 
v_path_2094_ = l_System_FilePath_join(v___x_2091_, v___y_2093_);
v___x_2095_ = lean_io_metadata(v_path_2094_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2105_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2105_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2105_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_modified_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_modified_2100_ = lean_ctor_get(v_a_2096_, 1);
lean_inc_ref(v_modified_2100_);
lean_dec(v_a_2096_);
lean_inc_ref(v_path_2094_);
v___x_2101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2101_, 0, v_descr_2086_);
lean_ctor_set(v___x_2101_, 1, v_path_2094_);
lean_ctor_set(v___x_2101_, 2, v_path_2094_);
lean_ctor_set(v___x_2101_, 3, v_modified_2100_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2101_);
v___x_2103_ = v___x_2098_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v_descr_2086_);
v_a_2106_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2108_ = v___x_2095_;
v_isShared_2109_ = v_isSharedCheck_2121_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2095_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2121_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
if (lean_obj_tag(v_a_2106_) == 11)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec_ref_known(v_a_2106_, 2);
v___x_2110_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2111_ = lean_string_append(v___x_2110_, v_path_2094_);
lean_dec_ref(v_path_2094_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2111_);
v___x_2113_ = v___x_2108_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec_ref(v_path_2094_);
v___x_2115_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_2116_ = lean_io_error_to_string(v_a_2106_);
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
lean_dec_ref(v___x_2116_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2117_);
v___x_2119_ = v___x_2108_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_2130_, lean_object* v_descr_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lake_Cache_getArtifact(v_cache_2130_, v_descr_2131_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2137_ = l_System_FilePath_join(v_cache_2135_, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2139_, lean_object* v_scope_2140_, uint64_t v_inputHash_2141_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2142_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2143_ = l_System_FilePath_join(v_cache_2139_, v___x_2142_);
v___x_2144_ = l_System_FilePath_join(v___x_2143_, v_scope_2140_);
v___x_2145_ = l_Lake_lowerHexUInt64(v_inputHash_2141_);
v___x_2146_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2147_ = lean_string_append(v___x_2145_, v___x_2146_);
v___x_2148_ = l_System_FilePath_join(v___x_2144_, v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2149_, lean_object* v_scope_2150_, lean_object* v_inputHash_2151_){
_start:
{
uint64_t v_inputHash_boxed_2152_; lean_object* v_res_2153_; 
v_inputHash_boxed_2152_ = lean_unbox_uint64(v_inputHash_2151_);
lean_dec_ref(v_inputHash_2151_);
v_res_2153_ = l_Lake_Cache_outputsFile(v_cache_2149_, v_scope_2150_, v_inputHash_boxed_2152_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2154_, lean_object* v_scope_2155_, uint64_t v_inputHash_2156_, lean_object* v_out_2157_, lean_object* v_service_x3f_2158_, lean_object* v_remoteScope_x3f_2159_, uint8_t v_overwrite_2160_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_file_2168_; lean_object* v___x_2169_; 
v___x_2162_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2163_ = l_System_FilePath_join(v_cache_2154_, v___x_2162_);
v___x_2164_ = l_System_FilePath_join(v___x_2163_, v_scope_2155_);
v___x_2165_ = l_Lake_lowerHexUInt64(v_inputHash_2156_);
v___x_2166_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2167_ = lean_string_append(v___x_2165_, v___x_2166_);
v_file_2168_ = l_System_FilePath_join(v___x_2164_, v___x_2167_);
lean_inc_ref(v_file_2168_);
v___x_2169_ = l_Lake_createParentDirs(v_file_2168_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2170_, 0, v_out_2157_);
lean_ctor_set(v___x_2170_, 1, v_service_x3f_2158_);
lean_ctor_set(v___x_2170_, 2, v_remoteScope_x3f_2159_);
v___x_2171_ = l_Lake_CacheOutput_toJson(v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(80u);
v___x_2173_ = l_Lean_Json_pretty(v___x_2171_, v___x_2172_);
if (v_overwrite_2160_ == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lake_writeFileIfNew(v_file_2168_, v___x_2173_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v_file_2168_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; 
v___x_2175_ = l_IO_FS_writeFile(v_file_2168_, v___x_2173_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v_file_2168_);
return v___x_2175_;
}
}
else
{
lean_dec_ref(v_file_2168_);
lean_dec(v_remoteScope_x3f_2159_);
lean_dec(v_service_x3f_2158_);
lean_dec(v_out_2157_);
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2176_, lean_object* v_scope_2177_, lean_object* v_inputHash_2178_, lean_object* v_out_2179_, lean_object* v_service_x3f_2180_, lean_object* v_remoteScope_x3f_2181_, lean_object* v_overwrite_2182_, lean_object* v_a_2183_){
_start:
{
uint64_t v_inputHash_boxed_2184_; uint8_t v_overwrite_boxed_2185_; lean_object* v_res_2186_; 
v_inputHash_boxed_2184_ = lean_unbox_uint64(v_inputHash_2178_);
lean_dec_ref(v_inputHash_2178_);
v_overwrite_boxed_2185_ = lean_unbox(v_overwrite_2182_);
v_res_2186_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2176_, v_scope_2177_, v_inputHash_boxed_2184_, v_out_2179_, v_service_x3f_2180_, v_remoteScope_x3f_2181_, v_overwrite_boxed_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2187_, lean_object* v_cache_2188_, lean_object* v_scope_2189_, uint64_t v_inputHash_2190_, lean_object* v_outputs_2191_, lean_object* v_service_x3f_2192_, lean_object* v_remoteScope_x3f_2193_, uint8_t v_overwrite_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_apply_1(v_inst_2187_, v_outputs_2191_);
v___x_2197_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2188_, v_scope_2189_, v_inputHash_2190_, v___x_2196_, v_service_x3f_2192_, v_remoteScope_x3f_2193_, v_overwrite_2194_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2198_, lean_object* v_cache_2199_, lean_object* v_scope_2200_, lean_object* v_inputHash_2201_, lean_object* v_outputs_2202_, lean_object* v_service_x3f_2203_, lean_object* v_remoteScope_x3f_2204_, lean_object* v_overwrite_2205_, lean_object* v_a_2206_){
_start:
{
uint64_t v_inputHash_boxed_2207_; uint8_t v_overwrite_boxed_2208_; lean_object* v_res_2209_; 
v_inputHash_boxed_2207_ = lean_unbox_uint64(v_inputHash_2201_);
lean_dec_ref(v_inputHash_2201_);
v_overwrite_boxed_2208_ = lean_unbox(v_overwrite_2205_);
v_res_2209_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2198_, v_cache_2199_, v_scope_2200_, v_inputHash_boxed_2207_, v_outputs_2202_, v_service_x3f_2203_, v_remoteScope_x3f_2204_, v_overwrite_boxed_2208_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2210_, lean_object* v_inst_2211_, lean_object* v_cache_2212_, lean_object* v_scope_2213_, uint64_t v_inputHash_2214_, lean_object* v_outputs_2215_, lean_object* v_service_x3f_2216_, lean_object* v_remoteScope_x3f_2217_, uint8_t v_overwrite_2218_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_apply_1(v_inst_2211_, v_outputs_2215_);
v___x_2221_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2212_, v_scope_2213_, v_inputHash_2214_, v___x_2220_, v_service_x3f_2216_, v_remoteScope_x3f_2217_, v_overwrite_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_inst_2223_, lean_object* v_cache_2224_, lean_object* v_scope_2225_, lean_object* v_inputHash_2226_, lean_object* v_outputs_2227_, lean_object* v_service_x3f_2228_, lean_object* v_remoteScope_x3f_2229_, lean_object* v_overwrite_2230_, lean_object* v_a_2231_){
_start:
{
uint64_t v_inputHash_boxed_2232_; uint8_t v_overwrite_boxed_2233_; lean_object* v_res_2234_; 
v_inputHash_boxed_2232_ = lean_unbox_uint64(v_inputHash_2226_);
lean_dec_ref(v_inputHash_2226_);
v_overwrite_boxed_2233_ = lean_unbox(v_overwrite_2230_);
v_res_2234_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2222_, v_inst_2223_, v_cache_2224_, v_scope_2225_, v_inputHash_boxed_2232_, v_outputs_2227_, v_service_x3f_2228_, v_remoteScope_x3f_2229_, v_overwrite_boxed_2233_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2235_, lean_object* v_scope_2236_, lean_object* v_service_x3f_2237_, lean_object* v_remoteScope_x3f_2238_, uint8_t v_overwrite_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
if (lean_obj_tag(v_x_2241_) == 0)
{
lean_object* v___x_2243_; 
lean_dec(v_remoteScope_x3f_2238_);
lean_dec(v_service_x3f_2237_);
lean_dec_ref(v_scope_2236_);
lean_dec_ref(v_cache_2235_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_x_2240_);
return v___x_2243_;
}
else
{
lean_object* v_value_2244_; lean_object* v_key_2245_; lean_object* v_tail_2246_; lean_object* v_out_2247_; uint64_t v___x_2248_; lean_object* v___x_2249_; 
v_value_2244_ = lean_ctor_get(v_x_2241_, 1);
lean_inc(v_value_2244_);
v_key_2245_ = lean_ctor_get(v_x_2241_, 0);
lean_inc(v_key_2245_);
v_tail_2246_ = lean_ctor_get(v_x_2241_, 2);
lean_inc(v_tail_2246_);
lean_dec_ref_known(v_x_2241_, 3);
v_out_2247_ = lean_ctor_get(v_value_2244_, 0);
lean_inc(v_out_2247_);
lean_dec(v_value_2244_);
v___x_2248_ = lean_unbox_uint64(v_key_2245_);
lean_dec(v_key_2245_);
lean_inc(v_remoteScope_x3f_2238_);
lean_inc(v_service_x3f_2237_);
lean_inc_ref(v_scope_2236_);
lean_inc_ref(v_cache_2235_);
v___x_2249_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2235_, v_scope_2236_, v___x_2248_, v_out_2247_, v_service_x3f_2237_, v_remoteScope_x3f_2238_, v_overwrite_2239_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v_x_2240_ = v_a_2250_;
v_x_2241_ = v_tail_2246_;
goto _start;
}
else
{
lean_dec(v_tail_2246_);
lean_dec(v_remoteScope_x3f_2238_);
lean_dec(v_service_x3f_2237_);
lean_dec_ref(v_scope_2236_);
lean_dec_ref(v_cache_2235_);
return v___x_2249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2252_, lean_object* v_scope_2253_, lean_object* v_service_x3f_2254_, lean_object* v_remoteScope_x3f_2255_, lean_object* v_overwrite_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_overwrite_boxed_2260_; lean_object* v_res_2261_; 
v_overwrite_boxed_2260_ = lean_unbox(v_overwrite_2256_);
v_res_2261_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2252_, v_scope_2253_, v_service_x3f_2254_, v_remoteScope_x3f_2255_, v_overwrite_boxed_2260_, v_x_2257_, v_x_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2262_, lean_object* v_scope_2263_, lean_object* v_service_x3f_2264_, lean_object* v_remoteScope_x3f_2265_, uint8_t v_overwrite_2266_, lean_object* v_as_2267_, size_t v_i_2268_, size_t v_stop_2269_, lean_object* v_b_2270_){
_start:
{
uint8_t v___x_2272_; 
v___x_2272_ = lean_usize_dec_eq(v_i_2268_, v_stop_2269_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_array_uget_borrowed(v_as_2267_, v_i_2268_);
v___x_2274_ = lean_box(0);
lean_inc(v___x_2273_);
lean_inc(v_remoteScope_x3f_2265_);
lean_inc(v_service_x3f_2264_);
lean_inc_ref(v_scope_2263_);
lean_inc_ref(v_cache_2262_);
v___x_2275_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2262_, v_scope_2263_, v_service_x3f_2264_, v_remoteScope_x3f_2265_, v_overwrite_2266_, v___x_2274_, v___x_2273_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; size_t v___x_2277_; size_t v___x_2278_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2268_, v___x_2277_);
v_i_2268_ = v___x_2278_;
v_b_2270_ = v_a_2276_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2265_);
lean_dec(v_service_x3f_2264_);
lean_dec_ref(v_scope_2263_);
lean_dec_ref(v_cache_2262_);
return v___x_2275_;
}
}
else
{
lean_object* v___x_2280_; 
lean_dec(v_remoteScope_x3f_2265_);
lean_dec(v_service_x3f_2264_);
lean_dec_ref(v_scope_2263_);
lean_dec_ref(v_cache_2262_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_b_2270_);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2281_, lean_object* v_scope_2282_, lean_object* v_service_x3f_2283_, lean_object* v_remoteScope_x3f_2284_, lean_object* v_overwrite_2285_, lean_object* v_as_2286_, lean_object* v_i_2287_, lean_object* v_stop_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_overwrite_boxed_2291_; size_t v_i_boxed_2292_; size_t v_stop_boxed_2293_; lean_object* v_res_2294_; 
v_overwrite_boxed_2291_ = lean_unbox(v_overwrite_2285_);
v_i_boxed_2292_ = lean_unbox_usize(v_i_2287_);
lean_dec(v_i_2287_);
v_stop_boxed_2293_ = lean_unbox_usize(v_stop_2288_);
lean_dec(v_stop_2288_);
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2281_, v_scope_2282_, v_service_x3f_2283_, v_remoteScope_x3f_2284_, v_overwrite_boxed_2291_, v_as_2286_, v_i_boxed_2292_, v_stop_boxed_2293_, v_b_2289_);
lean_dec_ref(v_as_2286_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2295_, lean_object* v_scope_2296_, lean_object* v_map_2297_, lean_object* v_service_x3f_2298_, lean_object* v_remoteScope_x3f_2299_, uint8_t v_overwrite_2300_){
_start:
{
lean_object* v_buckets_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_buckets_2302_ = lean_ctor_get(v_map_2297_, 1);
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = lean_array_get_size(v_buckets_2302_);
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_nat_dec_lt(v___x_2303_, v___x_2304_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; 
lean_dec(v_remoteScope_x3f_2299_);
lean_dec(v_service_x3f_2298_);
lean_dec_ref(v_scope_2296_);
lean_dec_ref(v_cache_2295_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
return v___x_2307_;
}
else
{
size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = lean_usize_of_nat(v___x_2304_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2295_, v_scope_2296_, v_service_x3f_2298_, v_remoteScope_x3f_2299_, v_overwrite_2300_, v_buckets_2302_, v___x_2308_, v___x_2309_, v___x_2305_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2311_, lean_object* v_scope_2312_, lean_object* v_map_2313_, lean_object* v_service_x3f_2314_, lean_object* v_remoteScope_x3f_2315_, lean_object* v_overwrite_2316_, lean_object* v_a_2317_){
_start:
{
uint8_t v_overwrite_boxed_2318_; lean_object* v_res_2319_; 
v_overwrite_boxed_2318_ = lean_unbox(v_overwrite_2316_);
v_res_2319_ = l_Lake_Cache_writeMap(v_cache_2311_, v_scope_2312_, v_map_2313_, v_service_x3f_2314_, v_remoteScope_x3f_2315_, v_overwrite_boxed_2318_);
lean_dec_ref(v_map_2313_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2322_, lean_object* v_scope_2323_, uint64_t v_inputHash_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_path_2333_; lean_object* v___x_2334_; 
v___x_2327_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2328_ = l_System_FilePath_join(v_cache_2322_, v___x_2327_);
v___x_2329_ = l_System_FilePath_join(v___x_2328_, v_scope_2323_);
v___x_2330_ = l_Lake_lowerHexUInt64(v_inputHash_2324_);
v___x_2331_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v_path_2333_ = l_System_FilePath_join(v___x_2329_, v___x_2332_);
v___x_2334_ = l_IO_FS_readFile(v_path_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v_a_2337_; lean_object* v___x_2346_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2346_ = l_Lean_Json_parse(v_a_2335_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v_a_2337_ = v_a_2347_;
goto v___jp_2336_;
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2349_ = l_Lake_CacheOutput_fromJson_x3f(v_a_2348_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v_a_2337_ = v_a_2350_;
goto v___jp_2336_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_path_2333_);
v_a_2351_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2353_ = v___x_2349_;
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v_a_2325_);
return v___x_2357_;
}
}
}
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2338_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2339_ = lean_string_append(v_path_2333_, v___x_2338_);
v___x_2340_ = lean_string_append(v___x_2339_, v_a_2337_);
lean_dec_ref(v_a_2337_);
v___x_2341_ = 3;
v___x_2342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*1, v___x_2341_);
v___x_2343_ = lean_array_get_size(v_a_2325_);
v___x_2344_ = lean_array_push(v_a_2325_, v___x_2342_);
v___x_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
return v___x_2345_;
}
}
else
{
lean_object* v_a_2360_; 
v_a_2360_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2334_, 1);
if (lean_obj_tag(v_a_2360_) == 11)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref_known(v_a_2360_, 2);
lean_dec_ref(v_path_2333_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v_a_2325_);
return v___x_2362_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2363_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2364_ = lean_string_append(v_path_2333_, v___x_2363_);
v___x_2365_ = lean_io_error_to_string(v_a_2360_);
v___x_2366_ = lean_string_append(v___x_2364_, v___x_2365_);
lean_dec_ref(v___x_2365_);
v___x_2367_ = 3;
v___x_2368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*1, v___x_2367_);
v___x_2369_ = lean_array_get_size(v_a_2325_);
v___x_2370_ = lean_array_push(v_a_2325_, v___x_2368_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
return v___x_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2372_, lean_object* v_scope_2373_, lean_object* v_inputHash_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
uint64_t v_inputHash_boxed_2377_; lean_object* v_res_2378_; 
v_inputHash_boxed_2377_ = lean_unbox_uint64(v_inputHash_2374_);
lean_dec_ref(v_inputHash_2374_);
v_res_2378_ = l_Lake_Cache_readOutputs_x3f(v_cache_2372_, v_scope_2373_, v_inputHash_boxed_2377_, v_a_2375_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2380_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2382_ = l_System_FilePath_join(v_cache_2380_, v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2384_, lean_object* v_scope_2385_, lean_object* v_rev_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2387_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2388_ = l_System_FilePath_join(v_cache_2384_, v___x_2387_);
v___x_2389_ = l_System_FilePath_join(v___x_2388_, v_scope_2385_);
v___x_2390_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2391_ = lean_string_append(v_rev_2386_, v___x_2390_);
v___x_2392_ = l_System_FilePath_join(v___x_2389_, v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2395_ = lean_string_utf8_byte_size(v_self_2394_);
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = lean_nat_dec_eq(v___x_2395_, v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2398_){
_start:
{
uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_res_2399_ = l_Lake_CachePlatform_isNone(v_self_2398_);
lean_dec_ref(v_self_2398_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_System_Platform_target;
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2402_){
_start:
{
lean_inc_ref(v_s_2402_);
return v_s_2402_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lake_CachePlatform_ofString(v_s_2403_);
lean_dec_ref(v_s_2403_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(lean_object* v___x_2405_, lean_object* v___x_2406_, lean_object* v_a_2407_, lean_object* v_b_2408_){
_start:
{
uint8_t v_decide_2409_; 
v_decide_2409_ = lean_nat_dec_eq(v_a_2407_, v___x_2405_);
if (v_decide_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_string_utf8_next_fast(v___x_2406_, v_a_2407_);
lean_dec(v_a_2407_);
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = lean_nat_add(v_b_2408_, v___x_2411_);
lean_dec(v_b_2408_);
v_a_2407_ = v___x_2410_;
v_b_2408_ = v___x_2412_;
goto _start;
}
else
{
lean_dec(v_a_2407_);
return v_b_2408_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg___boxed(lean_object* v___x_2414_, lean_object* v___x_2415_, lean_object* v_a_2416_, lean_object* v_b_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2414_, v___x_2415_, v_a_2416_, v_b_2417_);
lean_dec_ref(v___x_2415_);
lean_dec(v___x_2414_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2419_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_string_utf8_byte_size(v_self_2419_);
v___x_2422_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2421_, v_self_2419_, v___x_2420_, v___x_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object* v_self_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lake_CachePlatform_length(v_self_2423_);
lean_dec_ref(v_self_2423_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v___x_2427_, lean_object* v_inst_2428_, lean_object* v_R_2429_, lean_object* v_a_2430_, lean_object* v_b_2431_, lean_object* v_c_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2425_, v___x_2427_, v_a_2430_, v_b_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___boxed(lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v_inst_2437_, lean_object* v_R_2438_, lean_object* v_a_2439_, lean_object* v_b_2440_, lean_object* v_c_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(v___x_2434_, v___x_2435_, v___x_2436_, v_inst_2437_, v_R_2438_, v_a_2439_, v_b_2440_, v_c_2441_);
lean_dec_ref(v___x_2436_);
lean_dec_ref(v___x_2435_);
lean_dec(v___x_2434_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2444_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2445_ = lean_string_utf8_byte_size(v_self_2444_);
v___x_2446_ = lean_unsigned_to_nat(0u);
v___x_2447_ = lean_nat_dec_eq(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_inc_ref(v_self_2444_);
return v_self_2444_;
}
else
{
lean_object* v___x_2448_; 
v___x_2448_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2448_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lake_CachePlatform_toString(v_self_2449_);
lean_dec_ref(v_self_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2455_ = lean_string_utf8_byte_size(v_self_2454_);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_nat_dec_eq(v___x_2455_, v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_Lake_CacheToolchain_isNone(v_self_2458_);
lean_dec_ref(v_self_2458_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2461_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lake_normalizeToolchain(v_s_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2463_){
_start:
{
lean_inc_ref(v_s_2463_);
return v_s_2463_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2464_);
lean_dec_ref(v_s_2464_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = lean_string_utf8_byte_size(v_self_2466_);
v___x_2469_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2468_, v_self_2466_, v___x_2467_, v___x_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object* v_self_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lake_CacheToolchain_length(v_self_2470_);
lean_dec_ref(v_self_2470_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2473_ = lean_string_utf8_byte_size(v_self_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = lean_nat_dec_eq(v___x_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_inc_ref(v_self_2472_);
return v_self_2472_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lake_CacheToolchain_toString(v_self_2477_);
lean_dec_ref(v_self_2477_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2484_, lean_object* v_url_2485_, lean_object* v_path_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2486_);
v___x_2490_ = l_Lake_download(v_url_2485_, v_path_2486_, v___x_2489_, v_a_2487_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2533_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2490_, 0);
lean_dec(v_unused_2534_);
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2533_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2533_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lake_computeBinFileHash(v_path_2486_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; uint64_t v___x_2497_; uint8_t v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = lean_unbox_uint64(v_a_2496_);
v___x_2498_ = lean_uint64_dec_eq(v___x_2497_, v_hash_2484_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; uint64_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2499_ = lean_array_get_size(v_a_2491_);
v___x_2500_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_2486_);
v___x_2501_ = lean_string_append(v_path_2486_, v___x_2500_);
v___x_2502_ = lean_unbox_uint64(v_a_2496_);
lean_dec(v_a_2496_);
v___x_2503_ = l_Lake_lowerHexUInt64(v___x_2502_);
v___x_2504_ = lean_string_append(v___x_2501_, v___x_2503_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = 3;
v___x_2506_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*1, v___x_2505_);
v___x_2507_ = lean_array_push(v_a_2491_, v___x_2506_);
v___x_2508_ = lean_io_remove_file(v_path_2486_);
lean_dec_ref(v_path_2486_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2510_; 
lean_dec_ref_known(v___x_2508_, 1);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 1, v___x_2507_);
lean_ctor_set(v___x_2493_, 0, v___x_2499_);
v___x_2510_ = v___x_2493_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2507_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v_a_2512_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2513_ = lean_io_error_to_string(v_a_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*1, v___x_2505_);
v___x_2515_ = lean_array_get_size(v___x_2507_);
v___x_2516_ = lean_array_push(v___x_2507_, v___x_2514_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 1, v___x_2516_);
lean_ctor_set(v___x_2493_, 0, v___x_2515_);
v___x_2518_ = v___x_2493_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_dec(v_a_2496_);
lean_dec_ref(v_path_2486_);
v___x_2520_ = lean_box(0);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2520_);
v___x_2522_ = v___x_2493_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_a_2491_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
lean_dec_ref(v_path_2486_);
v_a_2524_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2525_ = lean_io_error_to_string(v_a_2524_);
v___x_2526_ = 3;
v___x_2527_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*1, v___x_2526_);
v___x_2528_ = lean_array_get_size(v_a_2491_);
v___x_2529_ = lean_array_push(v_a_2491_, v___x_2527_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
lean_ctor_set(v___x_2493_, 1, v___x_2529_);
lean_ctor_set(v___x_2493_, 0, v___x_2528_);
v___x_2531_ = v___x_2493_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_dec_ref(v_path_2486_);
return v___x_2490_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2535_, lean_object* v_url_2536_, lean_object* v_path_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
uint64_t v_hash_boxed_2540_; lean_object* v_res_2541_; 
v_hash_boxed_2540_ = lean_unbox_uint64(v_hash_2535_);
lean_dec_ref(v_hash_2535_);
v_res_2541_ = l_Lake_downloadArtifactCore(v_hash_boxed_2540_, v_url_2536_, v_path_2537_, v_a_2538_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_x_2544_) == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Json_getNat_x3f(v_x_2544_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
v_a_2555_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2557_ = v___x_2546_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2546_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_a_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2586_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2587_ = lean_unsigned_to_nat(14u);
v___x_2588_ = lean_mk_empty_array_with_capacity(v___x_2587_);
v___x_2589_ = lean_array_push(v___x_2588_, v___x_2586_);
return v___x_2589_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2591_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2592_ = lean_array_push(v___x_2591_, v___x_2590_);
return v___x_2592_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2594_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2595_ = lean_array_push(v___x_2594_, v___x_2593_);
return v___x_2595_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2597_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2598_ = lean_array_push(v___x_2597_, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2600_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2601_ = lean_array_push(v___x_2600_, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2603_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2604_ = lean_array_push(v___x_2603_, v___x_2602_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_2608_ = lean_array_get_size(v___x_2607_);
return v___x_2608_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2609_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_nat_dec_lt(v___x_2610_, v___x_2609_);
return v___x_2611_;
}
}
static size_t _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30(void){
_start:
{
lean_object* v___x_2612_; size_t v___x_2613_; 
v___x_2612_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28);
v___x_2613_ = lean_usize_of_nat(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2616_, lean_object* v_contentType_2617_, lean_object* v_url_2618_, lean_object* v_key_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_stderr_2623_; lean_object* v_a_2624_; lean_object* v_stderr_2636_; lean_object* v___y_2645_; lean_object* v_a_2646_; lean_object* v_a_2674_; lean_object* v_a_2712_; lean_object* v___x_2761_; lean_object* v_val_2763_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2761_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_2769_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31));
v___x_2770_ = lean_io_getenv(v___x_2769_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v___x_2771_; 
v___x_2771_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32));
v_val_2763_ = v___x_2771_;
goto v___jp_2762_;
}
else
{
lean_object* v_val_2772_; 
v_val_2772_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_val_2772_);
lean_dec_ref_known(v___x_2770_, 1);
v_val_2763_ = v_val_2772_;
goto v___jp_2762_;
}
v___jp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2625_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2626_ = lean_string_append(v___x_2625_, v_a_2624_);
lean_dec_ref(v_a_2624_);
v___x_2627_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2628_ = lean_string_append(v___x_2626_, v___x_2627_);
v___x_2629_ = lean_string_append(v___x_2628_, v_stderr_2623_);
lean_dec_ref(v_stderr_2623_);
v___x_2630_ = 3;
v___x_2631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set_uint8(v___x_2631_, sizeof(void*)*1, v___x_2630_);
lean_inc_ref(v_a_2620_);
v___x_2632_ = lean_apply_2(v_a_2620_, v___x_2631_, lean_box(0));
v___x_2633_ = lean_box(0);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2637_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2638_ = lean_string_append(v___x_2637_, v_stderr_2636_);
lean_dec_ref(v_stderr_2636_);
v___x_2639_ = 3;
v___x_2640_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*1, v___x_2639_);
lean_inc_ref(v_a_2620_);
v___x_2641_ = lean_apply_2(v_a_2620_, v___x_2640_, lean_box(0));
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
return v___x_2643_;
}
v___jp_2644_:
{
if (lean_obj_tag(v_a_2646_) == 0)
{
lean_object* v_stderr_2647_; 
v_stderr_2647_ = lean_ctor_get(v___y_2645_, 1);
lean_inc_ref(v_stderr_2647_);
lean_dec_ref(v___y_2645_);
v_stderr_2636_ = v_stderr_2647_;
goto v___jp_2635_;
}
else
{
lean_object* v_val_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2672_; 
v_val_2648_ = lean_ctor_get(v_a_2646_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_a_2646_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2650_ = v_a_2646_;
v_isShared_2651_ = v_isSharedCheck_2672_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_val_2648_);
lean_dec(v_a_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2672_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = lean_unsigned_to_nat(200u);
v___x_2653_ = lean_nat_dec_eq(v_val_2648_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v_stdout_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v_stdout_2654_ = lean_ctor_get(v___y_2645_, 0);
lean_inc_ref(v_stdout_2654_);
lean_dec_ref(v___y_2645_);
v___x_2655_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2656_ = l_Nat_reprFast(v_val_2648_);
v___x_2657_ = lean_string_append(v___x_2655_, v___x_2656_);
lean_dec_ref(v___x_2656_);
v___x_2658_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2659_ = lean_string_append(v___x_2657_, v___x_2658_);
v___x_2660_ = lean_string_append(v___x_2659_, v_stdout_2654_);
lean_dec_ref(v_stdout_2654_);
v___x_2661_ = 3;
v___x_2662_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*1, v___x_2661_);
lean_inc_ref(v_a_2620_);
v___x_2663_ = lean_apply_2(v_a_2620_, v___x_2662_, lean_box(0));
v___x_2664_ = lean_box(0);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2664_);
v___x_2666_ = v___x_2650_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_dec(v_val_2648_);
lean_dec_ref(v___y_2645_);
v___x_2668_ = lean_box(0);
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2668_);
v___x_2670_ = v___x_2650_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
v___jp_2673_:
{
lean_object* v_stderr_2675_; lean_object* v___x_2676_; 
v_stderr_2675_ = lean_ctor_get(v_a_2674_, 1);
lean_inc_ref(v_stderr_2675_);
v___x_2676_ = l_Lean_Json_parse(v_stderr_2675_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; 
lean_inc_ref(v_stderr_2675_);
lean_dec_ref(v_a_2674_);
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v_stderr_2623_ = v_stderr_2675_;
v_a_2624_ = v_a_2677_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2679_ = l_Lean_Json_getObj_x3f(v_a_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; 
lean_inc_ref(v_stderr_2675_);
lean_dec_ref(v_a_2674_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v_stderr_2623_ = v_stderr_2675_;
v_a_2624_ = v_a_2680_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_a_2681_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2682_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2683_ = l_Lake_JsonObject_getJson_x3f(v_a_2681_, v___x_2682_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_inc_ref(v_stderr_2675_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2674_);
v_stderr_2636_ = v_stderr_2675_;
goto v___jp_2635_;
}
else
{
lean_object* v_val_2684_; lean_object* v___x_2685_; 
v_val_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_val_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2685_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref_known(v___x_2685_, 1);
v___x_2686_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2687_ = l_Lake_JsonObject_getJson_x3f(v_a_2681_, v___x_2686_);
lean_dec(v_a_2681_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_inc_ref(v_stderr_2675_);
lean_dec_ref(v_a_2674_);
v_stderr_2636_ = v_stderr_2675_;
goto v___jp_2635_;
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2689_; 
v_val_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2708_; 
lean_inc_ref(v_stderr_2675_);
lean_dec_ref(v_a_2674_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2708_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2708_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2694_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2695_ = lean_string_append(v___x_2694_, v_a_2690_);
lean_dec(v_a_2690_);
v___x_2696_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2697_ = lean_string_append(v___x_2696_, v___x_2695_);
lean_dec_ref(v___x_2695_);
v___x_2698_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2699_ = lean_string_append(v___x_2697_, v___x_2698_);
v___x_2700_ = lean_string_append(v___x_2699_, v_stderr_2675_);
lean_dec_ref(v_stderr_2675_);
v___x_2701_ = 3;
v___x_2702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*1, v___x_2701_);
lean_inc_ref(v_a_2620_);
v___x_2703_ = lean_apply_2(v_a_2620_, v___x_2702_, lean_box(0));
v___x_2704_ = lean_box(0);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2704_);
v___x_2706_ = v___x_2692_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
lean_object* v_a_2709_; 
v_a_2709_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2689_, 1);
v___y_2645_ = v_a_2674_;
v_a_2646_ = v_a_2709_;
goto v___jp_2644_;
}
}
}
else
{
lean_object* v_a_2710_; 
lean_dec(v_a_2681_);
v_a_2710_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2685_, 1);
v___y_2645_ = v_a_2674_;
v_a_2646_ = v_a_2710_;
goto v___jp_2644_;
}
}
}
}
}
v___jp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2713_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2714_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2715_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2716_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2717_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2718_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2719_ = lean_string_append(v___x_2718_, v_contentType_2617_);
v___x_2720_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2721_ = lean_array_push(v___x_2720_, v_key_2619_);
v___x_2722_ = lean_array_push(v___x_2721_, v___x_2714_);
v___x_2723_ = lean_array_push(v___x_2722_, v___x_2715_);
v___x_2724_ = lean_array_push(v___x_2723_, v___x_2716_);
v___x_2725_ = lean_array_push(v___x_2724_, v_file_2616_);
v___x_2726_ = lean_array_push(v___x_2725_, v_url_2618_);
v___x_2727_ = lean_array_push(v___x_2726_, v___x_2717_);
v___x_2728_ = lean_array_push(v___x_2727_, v___x_2719_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2732_ = 1;
v___x_2733_ = 0;
v___x_2734_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2734_, 0, v___x_2713_);
lean_ctor_set(v___x_2734_, 1, v_a_2712_);
lean_ctor_set(v___x_2734_, 2, v___x_2728_);
lean_ctor_set(v___x_2734_, 3, v___x_2729_);
lean_ctor_set(v___x_2734_, 4, v___x_2731_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*5, v___x_2732_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*5 + 1, v___x_2733_);
v___x_2735_ = l_Lake_captureProc_x27(v___x_2734_, v___x_2731_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v_a_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
v_a_2737_ = lean_ctor_get(v___x_2735_, 1);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2735_, 2);
v___x_2738_ = lean_array_get_size(v_a_2737_);
v___x_2739_ = lean_nat_dec_lt(v___x_2730_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_dec(v_a_2737_);
v_a_2674_ = v_a_2736_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2740_; size_t v___x_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
v___x_2740_ = lean_box(0);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = lean_usize_of_nat(v___x_2738_);
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2737_, v___x_2741_, v___x_2742_, v___x_2740_, v_a_2620_);
lean_dec(v_a_2737_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_dec_ref_known(v___x_2743_, 1);
v_a_2674_ = v_a_2736_;
goto v___jp_2673_;
}
else
{
lean_dec(v_a_2736_);
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v_a_2744_ = lean_ctor_get(v___x_2735_, 1);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2735_, 2);
v___x_2745_ = lean_array_get_size(v_a_2744_);
v___x_2746_ = lean_nat_dec_lt(v___x_2730_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v_a_2744_);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
else
{
lean_object* v___x_2749_; size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2749_ = lean_box(0);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = lean_usize_of_nat(v___x_2745_);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2744_, v___x_2750_, v___x_2751_, v___x_2749_, v_a_2620_);
lean_dec(v_a_2744_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v___x_2752_, 0);
lean_dec(v_unused_2760_);
v___x_2754_ = v___x_2752_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v___x_2752_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set_tag(v___x_2754_, 1);
lean_ctor_set(v___x_2754_, 0, v___x_2749_);
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2749_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
return v___x_2752_;
}
}
}
}
v___jp_2762_:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_2764_ == 0)
{
v_a_2712_ = v_val_2763_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_2761_, v___x_2766_, v___x_2767_, v___x_2765_, v_a_2620_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_dec_ref_known(v___x_2768_, 1);
v_a_2712_ = v_val_2763_;
goto v___jp_2711_;
}
else
{
lean_dec_ref(v_val_2763_);
lean_dec_ref(v_key_2619_);
lean_dec_ref(v_url_2618_);
lean_dec_ref(v_file_2616_);
return v___x_2768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2773_, lean_object* v_contentType_2774_, lean_object* v_url_2775_, lean_object* v_key_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2773_, v_contentType_2774_, v_url_2775_, v_key_2776_, v_a_2777_);
lean_dec_ref(v_a_2777_);
lean_dec_ref(v_contentType_2774_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2780_){
_start:
{
lean_object* v_name_x3f_2781_; 
v_name_x3f_2781_ = lean_ctor_get(v_service_2780_, 0);
lean_inc(v_name_x3f_2781_);
return v_name_x3f_2781_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lake_CacheService_name_x3f(v_service_2782_);
lean_dec_ref(v_service_2782_);
return v_res_2783_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2784_){
_start:
{
uint8_t v_isReservoir_2785_; 
v_isReservoir_2785_ = lean_ctor_get_uint8(v_service_2784_, sizeof(void*)*5);
return v_isReservoir_2785_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l_Lake_CacheService_isReservoir(v_service_2786_);
lean_dec_ref(v_service_2786_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2789_, lean_object* v_name_x3f_2790_){
_start:
{
lean_object* v___x_2791_; uint8_t v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2792_ = 1;
v___x_2793_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2793_, 0, v_name_x3f_2790_);
lean_ctor_set(v___x_2793_, 1, v___x_2791_);
lean_ctor_set(v___x_2793_, 2, v___x_2791_);
lean_ctor_set(v___x_2793_, 3, v___x_2791_);
lean_ctor_set(v___x_2793_, 4, v_apiEndpoint_2789_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*5, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2794_, lean_object* v_artifactEndpoint_2795_, lean_object* v_revisionEndpoint_2796_){
_start:
{
lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = 0;
v___x_2799_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2800_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2800_, 0, v___x_2797_);
lean_ctor_set(v___x_2800_, 1, v_key_2794_);
lean_ctor_set(v___x_2800_, 2, v_artifactEndpoint_2795_);
lean_ctor_set(v___x_2800_, 3, v_revisionEndpoint_2796_);
lean_ctor_set(v___x_2800_, 4, v___x_2799_);
lean_ctor_set_uint8(v___x_2800_, sizeof(void*)*5, v___x_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2801_, lean_object* v_revisionEndpoint_2802_, lean_object* v_name_x3f_2803_){
_start:
{
lean_object* v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2805_ = 0;
v___x_2806_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2806_, 0, v_name_x3f_2803_);
lean_ctor_set(v___x_2806_, 1, v___x_2804_);
lean_ctor_set(v___x_2806_, 2, v_artifactEndpoint_2801_);
lean_ctor_set(v___x_2806_, 3, v_revisionEndpoint_2802_);
lean_ctor_set(v___x_2806_, 4, v___x_2804_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*5, v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2807_, lean_object* v_name_x3f_2808_){
_start:
{
lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; 
v___x_2809_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2810_ = 0;
v___x_2811_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2811_, 0, v_name_x3f_2808_);
lean_ctor_set(v___x_2811_, 1, v___x_2809_);
lean_ctor_set(v___x_2811_, 2, v_artifactEndpoint_2807_);
lean_ctor_set(v___x_2811_, 3, v___x_2809_);
lean_ctor_set(v___x_2811_, 4, v___x_2809_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*5, v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2812_, lean_object* v_key_2813_){
_start:
{
lean_object* v_name_x3f_2814_; lean_object* v_artifactEndpoint_2815_; lean_object* v_revisionEndpoint_2816_; uint8_t v_isReservoir_2817_; lean_object* v_apiEndpoint_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_name_x3f_2814_ = lean_ctor_get(v_service_2812_, 0);
v_artifactEndpoint_2815_ = lean_ctor_get(v_service_2812_, 2);
v_revisionEndpoint_2816_ = lean_ctor_get(v_service_2812_, 3);
v_isReservoir_2817_ = lean_ctor_get_uint8(v_service_2812_, sizeof(void*)*5);
v_apiEndpoint_2818_ = lean_ctor_get(v_service_2812_, 4);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_service_2812_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_service_2812_, 1);
lean_dec(v_unused_2826_);
v___x_2820_ = v_service_2812_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_apiEndpoint_2818_);
lean_inc(v_revisionEndpoint_2816_);
lean_inc(v_artifactEndpoint_2815_);
lean_inc(v_name_x3f_2814_);
lean_dec(v_service_2812_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 1, v_key_2813_);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_name_x3f_2814_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_key_2813_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_artifactEndpoint_2815_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_revisionEndpoint_2816_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_apiEndpoint_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2824_, sizeof(void*)*5, v_isReservoir_2817_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg(){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg___closed__0));
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg___boxed(lean_object* v___dummy_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg();
return v_res_2834_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___redArg();
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2838_);
lean_dec_ref(v_s_2838_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2840_, lean_object* v___x_2841_, lean_object* v___x_2842_, lean_object* v_a_2843_, lean_object* v_b_2844_){
_start:
{
if (lean_obj_tag(v_a_2843_) == 0)
{
lean_object* v_currPos_2845_; lean_object* v_searcher_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2877_; 
v_currPos_2845_ = lean_ctor_get(v_a_2843_, 0);
v_searcher_2846_ = lean_ctor_get(v_a_2843_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_a_2843_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2848_ = v_a_2843_;
v_isShared_2849_ = v_isSharedCheck_2877_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_searcher_2846_);
lean_inc(v_currPos_2845_);
lean_dec(v_a_2843_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2877_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
uint32_t v___x_2850_; lean_object* v_it_2852_; lean_object* v_startInclusive_2853_; lean_object* v_endExclusive_2854_; uint8_t v_decide_2859_; 
v___x_2850_ = 47;
v_decide_2859_ = lean_nat_dec_eq(v_searcher_2846_, v___x_2842_);
if (v_decide_2859_ == 0)
{
uint32_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2860_ = lean_string_utf8_get_fast(v_scope_2840_, v_searcher_2846_);
v___x_2861_ = lean_uint32_dec_eq(v___x_2860_, v___x_2850_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_string_utf8_next_fast(v_scope_2840_, v_searcher_2846_);
lean_dec(v_searcher_2846_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 1, v___x_2862_);
v___x_2864_ = v___x_2848_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_currPos_2845_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
v_a_2843_ = v___x_2864_;
goto _start;
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v_slice_2870_; lean_object* v_nextIt_2872_; 
v___x_2867_ = lean_string_utf8_next_fast(v_scope_2840_, v_searcher_2846_);
v___x_2868_ = lean_nat_sub(v___x_2867_, v_searcher_2846_);
v___x_2869_ = lean_nat_add(v_searcher_2846_, v___x_2868_);
lean_dec(v___x_2868_);
v_slice_2870_ = l_String_Slice_subslice_x21(v___x_2841_, v_currPos_2845_, v_searcher_2846_);
lean_inc(v___x_2869_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 1, v___x_2869_);
lean_ctor_set(v___x_2848_, 0, v___x_2869_);
v_nextIt_2872_ = v___x_2848_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2869_);
v_nextIt_2872_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v_startInclusive_2873_; lean_object* v_endExclusive_2874_; 
v_startInclusive_2873_ = lean_ctor_get(v_slice_2870_, 0);
lean_inc(v_startInclusive_2873_);
v_endExclusive_2874_ = lean_ctor_get(v_slice_2870_, 1);
lean_inc(v_endExclusive_2874_);
lean_dec_ref(v_slice_2870_);
v_it_2852_ = v_nextIt_2872_;
v_startInclusive_2853_ = v_startInclusive_2873_;
v_endExclusive_2854_ = v_endExclusive_2874_;
goto v___jp_2851_;
}
}
}
else
{
lean_object* v___x_2876_; 
lean_del_object(v___x_2848_);
lean_dec(v_searcher_2846_);
v___x_2876_ = lean_box(1);
lean_inc(v___x_2842_);
v_it_2852_ = v___x_2876_;
v_startInclusive_2853_ = v_currPos_2845_;
v_endExclusive_2854_ = v___x_2842_;
goto v___jp_2851_;
}
v___jp_2851_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = lean_string_utf8_extract_fast(v_scope_2840_, v_startInclusive_2853_, v_endExclusive_2854_);
lean_dec(v_endExclusive_2854_);
lean_dec(v_startInclusive_2853_);
v___x_2856_ = lean_string_push(v_b_2844_, v___x_2850_);
v___x_2857_ = l_Lake_uriEncode(v___x_2855_, v___x_2856_);
lean_dec_ref(v___x_2855_);
v_a_2843_ = v_it_2852_;
v_b_2844_ = v___x_2857_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2842_);
return v_b_2844_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2878_, v___x_2879_, v___x_2880_, v_a_2881_, v_b_2882_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v_scope_2878_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_2884_, lean_object* v_scope_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_string_utf8_byte_size(v_scope_2885_);
lean_inc_ref(v_scope_2885_);
v___x_2888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2888_, 0, v_scope_2885_);
lean_ctor_set(v___x_2888_, 1, v___x_2886_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
v___x_2889_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0);
v___x_2890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2885_, v___x_2888_, v___x_2887_, v___x_2889_, v_endpoint_2884_);
lean_dec_ref_known(v___x_2888_, 3);
lean_dec_ref(v_scope_2885_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_2891_, lean_object* v___x_2892_, lean_object* v___x_2893_, lean_object* v_inst_2894_, lean_object* v_R_2895_, lean_object* v_a_2896_, lean_object* v_b_2897_, lean_object* v_c_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2891_, v___x_2892_, v___x_2893_, v_a_2896_, v_b_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_2900_, lean_object* v___x_2901_, lean_object* v___x_2902_, lean_object* v_inst_2903_, lean_object* v_R_2904_, lean_object* v_a_2905_, lean_object* v_b_2906_, lean_object* v_c_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_2900_, v___x_2901_, v___x_2902_, v_inst_2903_, v_R_2904_, v_a_2905_, v_b_2906_, v_c_2907_);
lean_dec_ref(v___x_2901_);
lean_dec_ref(v_scope_2900_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_2909_, lean_object* v_scope_2910_){
_start:
{
lean_object* v_artifactEndpoint_2911_; lean_object* v___x_2912_; 
v_artifactEndpoint_2911_ = lean_ctor_get(v_service_2909_, 2);
lean_inc_ref(v_artifactEndpoint_2911_);
lean_dec_ref(v_service_2909_);
v___x_2912_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_2911_, v_scope_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_2915_, lean_object* v_service_2916_, lean_object* v_scope_2917_){
_start:
{
lean_object* v___y_2919_; lean_object* v_s_2926_; lean_object* v___x_2927_; 
v_s_2926_ = lean_ctor_get(v_scope_2917_, 0);
lean_inc_ref(v_s_2926_);
lean_dec_ref(v_scope_2917_);
v___x_2927_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_2916_, v_s_2926_);
v___y_2919_ = v___x_2927_;
goto v___jp_2918_;
v___jp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2920_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_2921_ = lean_string_append(v___y_2919_, v___x_2920_);
v___x_2922_ = l_Lake_lowerHexUInt64(v_contentHash_2915_);
v___x_2923_ = lean_string_append(v___x_2921_, v___x_2922_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2925_ = lean_string_append(v___x_2923_, v___x_2924_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_2928_, lean_object* v_service_2929_, lean_object* v_scope_2930_){
_start:
{
uint64_t v_contentHash_boxed_2931_; lean_object* v_res_2932_; 
v_contentHash_boxed_2931_ = lean_unbox_uint64(v_contentHash_2928_);
lean_dec_ref(v_contentHash_2928_);
v_res_2932_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_2931_, v_service_2929_, v_scope_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_2936_, lean_object* v_service_2937_, lean_object* v_scope_2938_){
_start:
{
lean_object* v___y_2940_; uint8_t v_isReservoir_2947_; 
v_isReservoir_2947_ = lean_ctor_get_uint8(v_service_2937_, sizeof(void*)*5);
if (v_isReservoir_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_2936_, v_service_2937_, v_scope_2938_);
return v___x_2948_;
}
else
{
if (lean_obj_tag(v_scope_2938_) == 0)
{
lean_object* v_apiEndpoint_2949_; lean_object* v_s_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_apiEndpoint_2949_ = lean_ctor_get(v_service_2937_, 4);
lean_inc_ref(v_apiEndpoint_2949_);
lean_dec_ref(v_service_2937_);
v_s_2950_ = lean_ctor_get(v_scope_2938_, 0);
lean_inc_ref(v_s_2950_);
lean_dec_ref_known(v_scope_2938_, 1);
v___x_2951_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_2952_ = lean_string_append(v_apiEndpoint_2949_, v___x_2951_);
v___x_2953_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2952_, v_s_2950_);
v___y_2940_ = v___x_2953_;
goto v___jp_2939_;
}
else
{
lean_object* v_apiEndpoint_2954_; lean_object* v_s_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_apiEndpoint_2954_ = lean_ctor_get(v_service_2937_, 4);
lean_inc_ref(v_apiEndpoint_2954_);
lean_dec_ref(v_service_2937_);
v_s_2955_ = lean_ctor_get(v_scope_2938_, 0);
lean_inc_ref(v_s_2955_);
lean_dec_ref_known(v_scope_2938_, 1);
v___x_2956_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_2957_ = lean_string_append(v_apiEndpoint_2954_, v___x_2956_);
v___x_2958_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2957_, v_s_2955_);
v___y_2940_ = v___x_2958_;
goto v___jp_2939_;
}
}
v___jp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2941_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_2942_ = lean_string_append(v___y_2940_, v___x_2941_);
v___x_2943_ = l_Lake_lowerHexUInt64(v_contentHash_2936_);
v___x_2944_ = lean_string_append(v___x_2942_, v___x_2943_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2946_ = lean_string_append(v___x_2944_, v___x_2945_);
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_2959_, lean_object* v_service_2960_, lean_object* v_scope_2961_){
_start:
{
uint64_t v_contentHash_boxed_2962_; lean_object* v_res_2963_; 
v_contentHash_boxed_2962_ = lean_unbox_uint64(v_contentHash_2959_);
lean_dec_ref(v_contentHash_2959_);
v_res_2963_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_2962_, v_service_2960_, v_scope_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_2967_, lean_object* v_cache_2968_, lean_object* v_service_2969_, lean_object* v_scope_2970_, uint8_t v_force_2971_, lean_object* v_a_2972_){
_start:
{
uint64_t v_hash_2974_; lean_object* v_ext_2975_; lean_object* v_url_2976_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_3031_; lean_object* v___y_3034_; uint8_t v_a_3035_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___y_3041_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v_hash_2974_ = lean_ctor_get_uint64(v_descr_2967_, sizeof(void*)*1);
v_ext_2975_ = lean_ctor_get(v_descr_2967_, 0);
lean_inc_ref(v_scope_2970_);
v_url_2976_ = l_Lake_CacheService_artifactUrl(v_hash_2974_, v_service_2969_, v_scope_2970_);
v___x_3038_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3039_ = l_System_FilePath_join(v_cache_2968_, v___x_3038_);
v___x_3050_ = lean_string_utf8_byte_size(v_ext_2975_);
v___x_3051_ = lean_unsigned_to_nat(0u);
v___x_3052_ = lean_nat_dec_eq(v___x_3050_, v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = l_Lake_lowerHexUInt64(v_hash_2974_);
v___x_3054_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3055_ = lean_string_append(v___x_3053_, v___x_3054_);
v___x_3056_ = lean_string_append(v___x_3055_, v_ext_2975_);
v___y_3041_ = v___x_3056_;
goto v___jp_3040_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lake_lowerHexUInt64(v_hash_2974_);
v___y_3041_ = v___x_3057_;
goto v___jp_3040_;
}
v___jp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2980_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_2981_ = lean_string_append(v___y_2979_, v___x_2980_);
v___x_2982_ = l_Lake_lowerHexUInt64(v_hash_2974_);
v___x_2983_ = lean_string_append(v___x_2981_, v___x_2982_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_2985_ = lean_string_append(v___x_2983_, v___x_2984_);
v___x_2986_ = lean_string_append(v___x_2985_, v___y_2978_);
v___x_2987_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_2988_ = lean_string_append(v___x_2986_, v___x_2987_);
v___x_2989_ = lean_string_append(v___x_2988_, v_url_2976_);
v___x_2990_ = 1;
v___x_2991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*1, v___x_2990_);
lean_inc_ref(v_a_2972_);
v___x_2992_ = lean_apply_2(v_a_2972_, v___x_2991_, lean_box(0));
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_2995_ = l_Lake_downloadArtifactCore(v_hash_2974_, v_url_2976_, v___y_2978_, v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v_a_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
v_a_2997_ = lean_ctor_get(v___x_2995_, 1);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2995_, 2);
v___x_2998_ = lean_array_get_size(v_a_2997_);
v___x_2999_ = lean_nat_dec_lt(v___x_2993_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v_a_2997_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2996_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_3004_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = lean_usize_of_nat(v___x_2998_);
v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2997_, v___x_3002_, v___x_3003_, v___x_3001_, v_a_2972_);
lean_dec(v_a_2997_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v___x_3004_, 0);
lean_dec(v_unused_3012_);
v___x_3006_ = v___x_3004_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_dec(v___x_3004_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v_a_2996_);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_2996_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
else
{
lean_dec(v_a_2996_);
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_2995_, 1);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_2995_, 2);
v___x_3014_ = lean_array_get_size(v_a_3013_);
v___x_3015_ = lean_nat_dec_lt(v___x_2993_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec(v_a_3013_);
v___x_3016_ = lean_box(0);
v___x_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
else
{
lean_object* v___x_3018_; size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3018_ = lean_box(0);
v___x_3019_ = ((size_t)0ULL);
v___x_3020_ = lean_usize_of_nat(v___x_3014_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3013_, v___x_3019_, v___x_3020_, v___x_3018_, v_a_2972_);
lean_dec(v_a_3013_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v___x_3021_, 0);
lean_dec(v_unused_3029_);
v___x_3023_ = v___x_3021_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v___x_3021_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set_tag(v___x_3023_, 1);
lean_ctor_set(v___x_3023_, 0, v___x_3018_);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3018_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
return v___x_3021_;
}
}
}
}
v___jp_3030_:
{
lean_object* v_s_3032_; 
v_s_3032_ = lean_ctor_get(v_scope_2970_, 0);
lean_inc_ref(v_s_3032_);
lean_dec_ref(v_scope_2970_);
v___y_2978_ = v___y_3031_;
v___y_2979_ = v_s_3032_;
goto v___jp_2977_;
}
v___jp_3033_:
{
if (v_a_3035_ == 0)
{
v___y_3031_ = v___y_3034_;
goto v___jp_3030_;
}
else
{
if (v_force_2971_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec_ref(v___y_3034_);
lean_dec_ref(v_url_2976_);
lean_dec_ref(v_scope_2970_);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
else
{
v___y_3031_ = v___y_3034_;
goto v___jp_3030_;
}
}
}
v___jp_3040_:
{
lean_object* v_path_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; uint8_t v___x_3045_; 
v_path_3042_ = l_System_FilePath_join(v___x_3039_, v___y_3041_);
v___x_3043_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_3044_ = l_System_FilePath_pathExists(v_path_3042_);
v___x_3045_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_3045_ == 0)
{
v___y_3034_ = v_path_3042_;
v_a_3035_ = v___x_3044_;
goto v___jp_3033_;
}
else
{
lean_object* v___x_3046_; size_t v___x_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = ((size_t)0ULL);
v___x_3048_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3043_, v___x_3047_, v___x_3048_, v___x_3046_, v_a_2972_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_dec_ref_known(v___x_3049_, 1);
v___y_3034_ = v_path_3042_;
v_a_3035_ = v___x_3044_;
goto v___jp_3033_;
}
else
{
lean_dec_ref(v_path_3042_);
lean_dec_ref(v_url_2976_);
lean_dec_ref(v_scope_2970_);
return v___x_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3058_, lean_object* v_cache_3059_, lean_object* v_service_3060_, lean_object* v_scope_3061_, lean_object* v_force_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
uint8_t v_force_boxed_3065_; lean_object* v_res_3066_; 
v_force_boxed_3065_ = lean_unbox(v_force_3062_);
v_res_3066_ = l_Lake_CacheService_downloadArtifact(v_descr_3058_, v_cache_3059_, v_service_3060_, v_scope_3061_, v_force_boxed_3065_, v_a_3063_);
lean_dec_ref(v_a_3063_);
lean_dec_ref(v_descr_3058_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3067_, lean_object* v_file_3068_, lean_object* v_contentType_3069_, lean_object* v_url_3070_, lean_object* v_key_3071_){
_start:
{
lean_object* v_stderr_3074_; lean_object* v_a_3075_; lean_object* v_stderr_3087_; lean_object* v___y_3096_; lean_object* v_a_3097_; lean_object* v_a_3125_; lean_object* v_a_3163_; lean_object* v___x_3214_; lean_object* v_val_3216_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3214_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_3222_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31));
v___x_3223_ = lean_io_getenv(v___x_3222_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32));
v_val_3216_ = v___x_3224_;
goto v___jp_3215_;
}
else
{
lean_object* v_val_3225_; 
v_val_3225_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_val_3225_);
lean_dec_ref_known(v___x_3223_, 1);
v_val_3216_ = v_val_3225_;
goto v___jp_3215_;
}
v___jp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3076_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3077_ = lean_string_append(v___x_3076_, v_a_3075_);
lean_dec_ref(v_a_3075_);
v___x_3078_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3079_ = lean_string_append(v___x_3077_, v___x_3078_);
v___x_3080_ = lean_string_append(v___x_3079_, v_stderr_3074_);
lean_dec_ref(v_stderr_3074_);
v___x_3081_ = 3;
v___x_3082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*1, v___x_3081_);
lean_inc_ref(v_a_3067_);
v___x_3083_ = lean_apply_2(v_a_3067_, v___x_3082_, lean_box(0));
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
v___jp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3088_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3089_ = lean_string_append(v___x_3088_, v_stderr_3087_);
lean_dec_ref(v_stderr_3087_);
v___x_3090_ = 3;
v___x_3091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*1, v___x_3090_);
lean_inc_ref(v_a_3067_);
v___x_3092_ = lean_apply_2(v_a_3067_, v___x_3091_, lean_box(0));
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
v___jp_3095_:
{
if (lean_obj_tag(v_a_3097_) == 0)
{
lean_object* v_stderr_3098_; 
v_stderr_3098_ = lean_ctor_get(v___y_3096_, 1);
lean_inc_ref(v_stderr_3098_);
lean_dec_ref(v___y_3096_);
v_stderr_3087_ = v_stderr_3098_;
goto v___jp_3086_;
}
else
{
lean_object* v_val_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3123_; 
v_val_3099_ = lean_ctor_get(v_a_3097_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_a_3097_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3101_ = v_a_3097_;
v_isShared_3102_ = v_isSharedCheck_3123_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_val_3099_);
lean_dec(v_a_3097_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3123_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3103_ = lean_unsigned_to_nat(200u);
v___x_3104_ = lean_nat_dec_eq(v_val_3099_, v___x_3103_);
if (v___x_3104_ == 0)
{
lean_object* v_stdout_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v_stdout_3105_ = lean_ctor_get(v___y_3096_, 0);
lean_inc_ref(v_stdout_3105_);
lean_dec_ref(v___y_3096_);
v___x_3106_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3107_ = l_Nat_reprFast(v_val_3099_);
v___x_3108_ = lean_string_append(v___x_3106_, v___x_3107_);
lean_dec_ref(v___x_3107_);
v___x_3109_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3110_ = lean_string_append(v___x_3108_, v___x_3109_);
v___x_3111_ = lean_string_append(v___x_3110_, v_stdout_3105_);
lean_dec_ref(v_stdout_3105_);
v___x_3112_ = 3;
v___x_3113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*1, v___x_3112_);
lean_inc_ref(v_a_3067_);
v___x_3114_ = lean_apply_2(v_a_3067_, v___x_3113_, lean_box(0));
v___x_3115_ = lean_box(0);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v___x_3115_);
v___x_3117_ = v___x_3101_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
lean_dec(v_val_3099_);
lean_dec_ref(v___y_3096_);
v___x_3119_ = lean_box(0);
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3119_);
v___x_3121_ = v___x_3101_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
v___jp_3124_:
{
lean_object* v_stderr_3126_; lean_object* v___x_3127_; 
v_stderr_3126_ = lean_ctor_get(v_a_3125_, 1);
lean_inc_ref(v_stderr_3126_);
v___x_3127_ = l_Lean_Json_parse(v_stderr_3126_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; 
lean_inc_ref(v_stderr_3126_);
lean_dec_ref(v_a_3125_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_stderr_3074_ = v_stderr_3126_;
v_a_3075_ = v_a_3128_;
goto v___jp_3073_;
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3127_, 1);
v___x_3130_ = l_Lean_Json_getObj_x3f(v_a_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; 
lean_inc_ref(v_stderr_3126_);
lean_dec_ref(v_a_3125_);
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v_stderr_3074_ = v_stderr_3126_;
v_a_3075_ = v_a_3131_;
goto v___jp_3073_;
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_a_3132_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3133_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3134_ = l_Lake_JsonObject_getJson_x3f(v_a_3132_, v___x_3133_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_inc_ref(v_stderr_3126_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3125_);
v_stderr_3087_ = v_stderr_3126_;
goto v___jp_3086_;
}
else
{
lean_object* v_val_3135_; lean_object* v___x_3136_; 
v_val_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_val_3135_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3136_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3135_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec_ref_known(v___x_3136_, 1);
v___x_3137_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3138_ = l_Lake_JsonObject_getJson_x3f(v_a_3132_, v___x_3137_);
lean_dec(v_a_3132_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_inc_ref(v_stderr_3126_);
lean_dec_ref(v_a_3125_);
v_stderr_3087_ = v_stderr_3126_;
goto v___jp_3086_;
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3140_; 
v_val_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v___x_3138_, 1);
v___x_3140_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3159_; 
lean_inc_ref(v_stderr_3126_);
lean_dec_ref(v_a_3125_);
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3159_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3159_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3145_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3146_ = lean_string_append(v___x_3145_, v_a_3141_);
lean_dec(v_a_3141_);
v___x_3147_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3148_ = lean_string_append(v___x_3147_, v___x_3146_);
lean_dec_ref(v___x_3146_);
v___x_3149_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3150_ = lean_string_append(v___x_3148_, v___x_3149_);
v___x_3151_ = lean_string_append(v___x_3150_, v_stderr_3126_);
lean_dec_ref(v_stderr_3126_);
v___x_3152_ = 3;
v___x_3153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set_uint8(v___x_3153_, sizeof(void*)*1, v___x_3152_);
lean_inc_ref(v_a_3067_);
v___x_3154_ = lean_apply_2(v_a_3067_, v___x_3153_, lean_box(0));
v___x_3155_ = lean_box(0);
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 1);
lean_ctor_set(v___x_3143_, 0, v___x_3155_);
v___x_3157_ = v___x_3143_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_a_3160_; 
v_a_3160_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3140_, 1);
v___y_3096_ = v_a_3125_;
v_a_3097_ = v_a_3160_;
goto v___jp_3095_;
}
}
}
else
{
lean_object* v_a_3161_; 
lean_dec(v_a_3132_);
v_a_3161_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3136_, 1);
v___y_3096_ = v_a_3125_;
v_a_3097_ = v_a_3161_;
goto v___jp_3095_;
}
}
}
}
}
v___jp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3164_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3165_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3166_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3167_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3168_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3169_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3170_ = lean_string_append(v___x_3169_, v_contentType_3069_);
v___x_3171_ = lean_unsigned_to_nat(14u);
v___x_3172_ = lean_mk_empty_array_with_capacity(v___x_3171_);
lean_dec_ref(v___x_3172_);
v___x_3173_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3174_ = lean_array_push(v___x_3173_, v_key_3071_);
v___x_3175_ = lean_array_push(v___x_3174_, v___x_3165_);
v___x_3176_ = lean_array_push(v___x_3175_, v___x_3166_);
v___x_3177_ = lean_array_push(v___x_3176_, v___x_3167_);
v___x_3178_ = lean_array_push(v___x_3177_, v_file_3068_);
v___x_3179_ = lean_array_push(v___x_3178_, v_url_3070_);
v___x_3180_ = lean_array_push(v___x_3179_, v___x_3168_);
v___x_3181_ = lean_array_push(v___x_3180_, v___x_3170_);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3185_ = 1;
v___x_3186_ = 0;
v___x_3187_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3187_, 0, v___x_3164_);
lean_ctor_set(v___x_3187_, 1, v_a_3163_);
lean_ctor_set(v___x_3187_, 2, v___x_3181_);
lean_ctor_set(v___x_3187_, 3, v___x_3182_);
lean_ctor_set(v___x_3187_, 4, v___x_3184_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*5, v___x_3185_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*5 + 1, v___x_3186_);
v___x_3188_ = l_Lake_captureProc_x27(v___x_3187_, v___x_3184_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v_a_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 1);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3188_, 2);
v___x_3191_ = lean_array_get_size(v_a_3190_);
v___x_3192_ = lean_nat_dec_lt(v___x_3183_, v___x_3191_);
if (v___x_3192_ == 0)
{
lean_dec(v_a_3190_);
v_a_3125_ = v_a_3189_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3193_; size_t v___x_3194_; size_t v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_box(0);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = lean_usize_of_nat(v___x_3191_);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3190_, v___x_3194_, v___x_3195_, v___x_3193_, v_a_3067_);
lean_dec(v_a_3190_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_dec_ref_known(v___x_3196_, 1);
v_a_3125_ = v_a_3189_;
goto v___jp_3124_;
}
else
{
lean_dec(v_a_3189_);
return v___x_3196_;
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v_a_3197_ = lean_ctor_get(v___x_3188_, 1);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3188_, 2);
v___x_3198_ = lean_array_get_size(v_a_3197_);
v___x_3199_ = lean_nat_dec_lt(v___x_3183_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec(v_a_3197_);
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; size_t v___x_3203_; size_t v___x_3204_; lean_object* v___x_3205_; 
v___x_3202_ = lean_box(0);
v___x_3203_ = ((size_t)0ULL);
v___x_3204_ = lean_usize_of_nat(v___x_3198_);
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3197_, v___x_3203_, v___x_3204_, v___x_3202_, v_a_3067_);
lean_dec(v_a_3197_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3213_);
v___x_3207_ = v___x_3205_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v___x_3205_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set_tag(v___x_3207_, 1);
lean_ctor_set(v___x_3207_, 0, v___x_3202_);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3202_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
else
{
return v___x_3205_;
}
}
}
}
v___jp_3215_:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_3217_ == 0)
{
v_a_3163_ = v_val_3216_;
goto v___jp_3162_;
}
else
{
lean_object* v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3218_ = lean_box(0);
v___x_3219_ = ((size_t)0ULL);
v___x_3220_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3214_, v___x_3219_, v___x_3220_, v___x_3218_, v_a_3067_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_dec_ref_known(v___x_3221_, 1);
v_a_3163_ = v_val_3216_;
goto v___jp_3162_;
}
else
{
lean_dec_ref(v_val_3216_);
lean_dec_ref(v_key_3071_);
lean_dec_ref(v_url_3070_);
lean_dec_ref(v_file_3068_);
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3226_, lean_object* v_file_3227_, lean_object* v_contentType_3228_, lean_object* v_url_3229_, lean_object* v_key_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3226_, v_file_3227_, v_contentType_3228_, v_url_3229_, v_key_3230_);
lean_dec_ref(v_contentType_3228_);
lean_dec_ref(v_a_3226_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3234_, lean_object* v_art_3235_, lean_object* v_service_3236_, lean_object* v_scope_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_url_3240_; lean_object* v___y_3242_; lean_object* v_s_3259_; 
lean_inc_ref(v_scope_3237_);
lean_inc_ref(v_service_3236_);
v_url_3240_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3234_, v_service_3236_, v_scope_3237_);
v_s_3259_ = lean_ctor_get(v_scope_3237_, 0);
lean_inc_ref(v_s_3259_);
lean_dec_ref(v_scope_3237_);
v___y_3242_ = v_s_3259_;
goto v___jp_3241_;
v___jp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v_key_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3243_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3244_ = lean_string_append(v___y_3242_, v___x_3243_);
v___x_3245_ = l_Lake_lowerHexUInt64(v_contentHash_3234_);
v___x_3246_ = lean_string_append(v___x_3244_, v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3248_ = lean_string_append(v___x_3246_, v___x_3247_);
v___x_3249_ = lean_string_append(v___x_3248_, v_art_3235_);
v___x_3250_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3251_ = lean_string_append(v___x_3249_, v___x_3250_);
v___x_3252_ = lean_string_append(v___x_3251_, v_url_3240_);
v___x_3253_ = 1;
v___x_3254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*1, v___x_3253_);
lean_inc_ref(v_a_3238_);
v___x_3255_ = lean_apply_2(v_a_3238_, v___x_3254_, lean_box(0));
v_key_3256_ = lean_ctor_get(v_service_3236_, 1);
lean_inc_ref(v_key_3256_);
lean_dec_ref(v_service_3236_);
v___x_3257_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3258_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3238_, v_art_3235_, v___x_3257_, v_url_3240_, v_key_3256_);
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3260_, lean_object* v_art_3261_, lean_object* v_service_3262_, lean_object* v_scope_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
uint64_t v_contentHash_boxed_3266_; lean_object* v_res_3267_; 
v_contentHash_boxed_3266_ = lean_unbox_uint64(v_contentHash_3260_);
lean_dec_ref(v_contentHash_3260_);
v_res_3267_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3266_, v_art_3261_, v_service_3262_, v_scope_3263_, v_a_3264_);
lean_dec_ref(v_a_3264_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___impl(uint8_t v_x_3268_){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_box(v_x_3268_);
v___x_3270_ = lean_obj_tag_nat(v___x_3269_);
lean_dec(v___x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___impl___boxed(lean_object* v_x_3271_){
_start:
{
uint8_t v_x_4__boxed_3272_; lean_object* v_res_3273_; 
v_x_4__boxed_3272_ = lean_unbox(v_x_3271_);
v_res_3273_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___impl(v_x_4__boxed_3272_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object* v_k_3274_){
_start:
{
lean_inc(v_k_3274_);
return v_k_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object* v_k_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(v_k_3275_);
lean_dec(v_k_3275_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object* v_motive_3277_, lean_object* v_ctorIdx_3278_, uint8_t v_t_3279_, lean_object* v_h_3280_, lean_object* v_k_3281_){
_start:
{
lean_inc(v_k_3281_);
return v_k_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object* v_motive_3282_, lean_object* v_ctorIdx_3283_, lean_object* v_t_3284_, lean_object* v_h_3285_, lean_object* v_k_3286_){
_start:
{
uint8_t v_t_boxed_3287_; lean_object* v_res_3288_; 
v_t_boxed_3287_ = lean_unbox(v_t_3284_);
v_res_3288_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(v_motive_3282_, v_ctorIdx_3283_, v_t_boxed_3287_, v_h_3285_, v_k_3286_);
lean_dec(v_k_3286_);
lean_dec(v_ctorIdx_3283_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object* v_get_3289_){
_start:
{
lean_inc(v_get_3289_);
return v_get_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object* v_get_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(v_get_3290_);
lean_dec(v_get_3290_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object* v_motive_3292_, uint8_t v_t_3293_, lean_object* v_h_3294_, lean_object* v_get_3295_){
_start:
{
lean_inc(v_get_3295_);
return v_get_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object* v_motive_3296_, lean_object* v_t_3297_, lean_object* v_h_3298_, lean_object* v_get_3299_){
_start:
{
uint8_t v_t_boxed_3300_; lean_object* v_res_3301_; 
v_t_boxed_3300_ = lean_unbox(v_t_3297_);
v_res_3301_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(v_motive_3296_, v_t_boxed_3300_, v_h_3298_, v_get_3299_);
lean_dec(v_get_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object* v_put_3302_){
_start:
{
lean_inc(v_put_3302_);
return v_put_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object* v_put_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(v_put_3303_);
lean_dec(v_put_3303_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object* v_motive_3305_, uint8_t v_t_3306_, lean_object* v_h_3307_, lean_object* v_put_3308_){
_start:
{
lean_inc(v_put_3308_);
return v_put_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object* v_motive_3309_, lean_object* v_t_3310_, lean_object* v_h_3311_, lean_object* v_put_3312_){
_start:
{
uint8_t v_t_boxed_3313_; lean_object* v_res_3314_; 
v_t_boxed_3313_ = lean_unbox(v_t_3310_);
v_res_3314_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(v_motive_3309_, v_t_boxed_3313_, v_h_3311_, v_put_3312_);
lean_dec(v_put_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object* v_n_3315_){
_start:
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = lean_unsigned_to_nat(0u);
v___x_3317_ = lean_nat_dec_le(v_n_3315_, v___x_3316_);
if (v___x_3317_ == 0)
{
uint8_t v___x_3318_; 
v___x_3318_ = 1;
return v___x_3318_;
}
else
{
uint8_t v___x_3319_; 
v___x_3319_ = 0;
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object* v_n_3320_){
_start:
{
uint8_t v_res_3321_; lean_object* v_r_3322_; 
v_res_3321_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(v_n_3320_);
lean_dec(v_n_3320_);
v_r_3322_ = lean_box(v_res_3321_);
return v_r_3322_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t v_x_3323_, uint8_t v_y_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3325_ = lean_box(v_x_3323_);
v___x_3326_ = lean_obj_tag_nat(v___x_3325_);
lean_dec(v___x_3325_);
v___x_3327_ = lean_box(v_y_3324_);
v___x_3328_ = lean_obj_tag_nat(v___x_3327_);
lean_dec(v___x_3327_);
v___x_3329_ = lean_nat_dec_eq(v___x_3326_, v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object* v_x_3330_, lean_object* v_y_3331_){
_start:
{
uint8_t v_x_23__boxed_3332_; uint8_t v_y_24__boxed_3333_; uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_x_23__boxed_3332_ = lean_unbox(v_x_3330_);
v_y_24__boxed_3333_ = lean_unbox(v_y_3331_);
v_res_3334_ = l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(v_x_23__boxed_3332_, v_y_24__boxed_3333_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(lean_object* v_self_3336_, lean_object* v_path_3337_, uint8_t v_extra_3338_){
_start:
{
if (v_extra_3338_ == 0)
{
lean_object* v_url_3339_; uint64_t v_hash_3340_; lean_object* v_path_3341_; lean_object* v_extraPaths_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
v_url_3339_ = lean_ctor_get(v_self_3336_, 0);
v_hash_3340_ = lean_ctor_get_uint64(v_self_3336_, sizeof(void*)*3);
v_path_3341_ = lean_ctor_get(v_self_3336_, 1);
v_extraPaths_3342_ = lean_ctor_get(v_self_3336_, 2);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_self_3336_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3344_ = v_self_3336_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_extraPaths_3342_);
lean_inc(v_path_3341_);
lean_inc(v_url_3339_);
lean_dec(v_self_3336_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_array_push(v_extraPaths_3342_, v_path_3341_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 2, v___x_3346_);
lean_ctor_set(v___x_3344_, 1, v_path_3337_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_url_3339_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_path_3337_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v___x_3346_);
lean_ctor_set_uint64(v_reuseFailAlloc_3349_, sizeof(void*)*3, v_hash_3340_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
else
{
lean_object* v_url_3351_; uint64_t v_hash_3352_; lean_object* v_path_3353_; lean_object* v_extraPaths_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3362_; 
v_url_3351_ = lean_ctor_get(v_self_3336_, 0);
v_hash_3352_ = lean_ctor_get_uint64(v_self_3336_, sizeof(void*)*3);
v_path_3353_ = lean_ctor_get(v_self_3336_, 1);
v_extraPaths_3354_ = lean_ctor_get(v_self_3336_, 2);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_self_3336_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3356_ = v_self_3336_;
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_extraPaths_3354_);
lean_inc(v_path_3353_);
lean_inc(v_url_3351_);
lean_dec(v_self_3336_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3358_ = lean_array_push(v_extraPaths_3354_, v_path_3337_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 2, v___x_3358_);
v___x_3360_ = v___x_3356_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_url_3351_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_path_3353_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v___x_3358_);
lean_ctor_set_uint64(v_reuseFailAlloc_3361_, sizeof(void*)*3, v_hash_3352_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath___boxed(lean_object* v_self_3363_, lean_object* v_path_3364_, lean_object* v_extra_3365_){
_start:
{
uint8_t v_extra_boxed_3366_; lean_object* v_res_3367_; 
v_extra_boxed_3366_ = lean_unbox(v_extra_3365_);
v_res_3367_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferInfo_addPath(v_self_3363_, v_path_3364_, v_extra_boxed_3366_);
return v_res_3367_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__1, &l_Lake_CacheMap_parse___closed__1_once, _init_l_Lake_CacheMap_parse___closed__1);
v___x_3371_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v___x_3370_);
return v___x_3372_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty(void){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
return v___x_3373_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___f_3376_; 
v___x_3375_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_3376_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3376_, 0, v___x_3375_);
return v___f_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(lean_object* v_self_3377_, lean_object* v_url_3378_, uint64_t v_hash_3379_, lean_object* v_path_3380_){
_start:
{
lean_object* v_infos_3381_; lean_object* v_indices_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3397_; 
v_infos_3381_ = lean_ctor_get(v_self_3377_, 0);
v_indices_3382_ = lean_ctor_get(v_self_3377_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_self_3377_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3384_ = v_self_3377_;
v_isShared_3385_ = v_isSharedCheck_3397_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_indices_3382_);
lean_inc(v_infos_3381_);
lean_dec(v_self_3377_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3397_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___f_3386_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___x_3387_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3388_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3388_, 0, v_url_3378_);
lean_ctor_set(v___x_3388_, 1, v_path_3380_);
lean_ctor_set(v___x_3388_, 2, v___x_3387_);
lean_ctor_set_uint64(v___x_3388_, sizeof(void*)*3, v_hash_3379_);
lean_inc_ref(v_infos_3381_);
v___x_3389_ = lean_array_push(v_infos_3381_, v___x_3388_);
v___f_3390_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3391_ = lean_array_get_size(v_infos_3381_);
lean_dec_ref(v_infos_3381_);
v___x_3392_ = lean_box_uint64(v_hash_3379_);
v___x_3393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3390_, v___f_3386_, v_indices_3382_, v___x_3392_, v___x_3391_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v___x_3393_);
lean_ctor_set(v___x_3384_, 0, v___x_3389_);
v___x_3395_ = v___x_3384_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___boxed(lean_object* v_self_3398_, lean_object* v_url_3399_, lean_object* v_hash_3400_, lean_object* v_path_3401_){
_start:
{
uint64_t v_hash_boxed_3402_; lean_object* v_res_3403_; 
v_hash_boxed_3402_ = lean_unbox_uint64(v_hash_3400_);
lean_dec_ref(v_hash_3400_);
v_res_3403_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push(v_self_3398_, v_url_3399_, v_hash_boxed_3402_, v_path_3401_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(lean_object* v_self_3404_, lean_object* v_url_3405_, uint64_t v_hash_3406_, lean_object* v_path_3407_){
_start:
{
lean_object* v_infos_3408_; lean_object* v_indices_3409_; lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_infos_3408_ = lean_ctor_get(v_self_3404_, 0);
v_indices_3409_ = lean_ctor_get(v_self_3404_, 1);
v___f_3410_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___f_3411_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3412_ = lean_box_uint64(v_hash_3406_);
v___x_3413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_3411_, v___f_3410_, v_indices_3409_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3426_; 
lean_inc_ref(v_indices_3409_);
lean_inc_ref(v_infos_3408_);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_self_3404_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; lean_object* v_unused_3428_; 
v_unused_3427_ = lean_ctor_get(v_self_3404_, 1);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_self_3404_, 0);
lean_dec(v_unused_3428_);
v___x_3415_ = v_self_3404_;
v_isShared_3416_ = v_isSharedCheck_3426_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v_self_3404_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3426_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3417_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3418_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3418_, 0, v_url_3405_);
lean_ctor_set(v___x_3418_, 1, v_path_3407_);
lean_ctor_set(v___x_3418_, 2, v___x_3417_);
lean_ctor_set_uint64(v___x_3418_, sizeof(void*)*3, v_hash_3406_);
lean_inc_ref(v_infos_3408_);
v___x_3419_ = lean_array_push(v_infos_3408_, v___x_3418_);
v___x_3420_ = lean_array_get_size(v_infos_3408_);
lean_dec_ref(v_infos_3408_);
v___x_3421_ = lean_box_uint64(v_hash_3406_);
v___x_3422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3411_, v___f_3410_, v_indices_3409_, v___x_3421_, v___x_3420_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3422_);
lean_ctor_set(v___x_3415_, 0, v___x_3419_);
v___x_3424_ = v___x_3415_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
else
{
lean_dec_ref(v_path_3407_);
lean_dec_ref(v_url_3405_);
return v_self_3404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew___boxed(lean_object* v_self_3429_, lean_object* v_url_3430_, lean_object* v_hash_3431_, lean_object* v_path_3432_){
_start:
{
uint64_t v_hash_boxed_3433_; lean_object* v_res_3434_; 
v_hash_boxed_3433_ = lean_unbox_uint64(v_hash_3431_);
lean_dec_ref(v_hash_3431_);
v_res_3434_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_addIfNew(v_self_3429_, v_url_3430_, v_hash_boxed_3433_, v_path_3432_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(lean_object* v_self_3435_, lean_object* v_url_3436_, uint64_t v_hash_3437_, lean_object* v_path_3438_, uint8_t v_extra_3439_){
_start:
{
lean_object* v_infos_3440_; lean_object* v_indices_3441_; lean_object* v___f_3442_; lean_object* v___f_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_infos_3440_ = lean_ctor_get(v_self_3435_, 0);
v_indices_3441_ = lean_ctor_get(v_self_3435_, 1);
v___f_3442_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__0));
v___f_3443_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_push___closed__1);
v___x_3444_ = lean_box_uint64(v_hash_3437_);
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3443_, v___f_3442_, v_indices_3441_, v___x_3444_);
if (lean_obj_tag(v___x_3445_) == 1)
{
lean_object* v_val_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
lean_dec_ref(v_url_3436_);
v_val_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_val_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___x_3447_ = lean_array_get_size(v_infos_3440_);
v___x_3448_ = lean_nat_dec_lt(v_val_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_dec(v_val_3446_);
lean_dec_ref(v_path_3438_);
return v_self_3435_;
}
else
{
lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3485_; 
lean_inc_ref(v_indices_3441_);
lean_inc_ref(v_infos_3440_);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_self_3435_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; lean_object* v_unused_3487_; 
v_unused_3486_ = lean_ctor_get(v_self_3435_, 1);
lean_dec(v_unused_3486_);
v_unused_3487_ = lean_ctor_get(v_self_3435_, 0);
lean_dec(v_unused_3487_);
v___x_3450_ = v_self_3435_;
v_isShared_3451_ = v_isSharedCheck_3485_;
goto v_resetjp_3449_;
}
else
{
lean_dec(v_self_3435_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3485_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_v_3452_; lean_object* v___x_3453_; lean_object* v_xs_x27_3454_; lean_object* v___y_3456_; 
v_v_3452_ = lean_array_fget(v_infos_3440_, v_val_3446_);
v___x_3453_ = lean_box(0);
v_xs_x27_3454_ = lean_array_fset(v_infos_3440_, v_val_3446_, v___x_3453_);
if (v_extra_3439_ == 0)
{
lean_object* v_url_3461_; uint64_t v_hash_3462_; lean_object* v_path_3463_; lean_object* v_extraPaths_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3472_; 
v_url_3461_ = lean_ctor_get(v_v_3452_, 0);
v_hash_3462_ = lean_ctor_get_uint64(v_v_3452_, sizeof(void*)*3);
v_path_3463_ = lean_ctor_get(v_v_3452_, 1);
v_extraPaths_3464_ = lean_ctor_get(v_v_3452_, 2);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_v_3452_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3466_ = v_v_3452_;
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_extraPaths_3464_);
lean_inc(v_path_3463_);
lean_inc(v_url_3461_);
lean_dec(v_v_3452_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3468_ = lean_array_push(v_extraPaths_3464_, v_path_3463_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 2, v___x_3468_);
lean_ctor_set(v___x_3466_, 1, v_path_3438_);
v___x_3470_ = v___x_3466_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_url_3461_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_path_3438_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v___x_3468_);
lean_ctor_set_uint64(v_reuseFailAlloc_3471_, sizeof(void*)*3, v_hash_3462_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
v___y_3456_ = v___x_3470_;
goto v___jp_3455_;
}
}
}
else
{
lean_object* v_url_3473_; uint64_t v_hash_3474_; lean_object* v_path_3475_; lean_object* v_extraPaths_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3484_; 
v_url_3473_ = lean_ctor_get(v_v_3452_, 0);
v_hash_3474_ = lean_ctor_get_uint64(v_v_3452_, sizeof(void*)*3);
v_path_3475_ = lean_ctor_get(v_v_3452_, 1);
v_extraPaths_3476_ = lean_ctor_get(v_v_3452_, 2);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_v_3452_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3478_ = v_v_3452_;
v_isShared_3479_ = v_isSharedCheck_3484_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_extraPaths_3476_);
lean_inc(v_path_3475_);
lean_inc(v_url_3473_);
lean_dec(v_v_3452_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3484_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3480_ = lean_array_push(v_extraPaths_3476_, v_path_3438_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 2, v___x_3480_);
v___x_3482_ = v___x_3478_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_url_3473_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_path_3475_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v___x_3480_);
lean_ctor_set_uint64(v_reuseFailAlloc_3483_, sizeof(void*)*3, v_hash_3474_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
v___y_3456_ = v___x_3482_;
goto v___jp_3455_;
}
}
}
v___jp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3457_ = lean_array_fset(v_xs_x27_3454_, v_val_3446_, v___y_3456_);
lean_dec(v_val_3446_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3457_);
v___x_3459_ = v___x_3450_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_indices_3441_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
else
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3500_; 
lean_inc_ref(v_indices_3441_);
lean_inc_ref(v_infos_3440_);
lean_dec(v___x_3445_);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_self_3435_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; lean_object* v_unused_3502_; 
v_unused_3501_ = lean_ctor_get(v_self_3435_, 1);
lean_dec(v_unused_3501_);
v_unused_3502_ = lean_ctor_get(v_self_3435_, 0);
lean_dec(v_unused_3502_);
v___x_3489_ = v_self_3435_;
v_isShared_3490_ = v_isSharedCheck_3500_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v_self_3435_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3500_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3491_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_3492_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3492_, 0, v_url_3436_);
lean_ctor_set(v___x_3492_, 1, v_path_3438_);
lean_ctor_set(v___x_3492_, 2, v___x_3491_);
lean_ctor_set_uint64(v___x_3492_, sizeof(void*)*3, v_hash_3437_);
lean_inc_ref(v_infos_3440_);
v___x_3493_ = lean_array_push(v_infos_3440_, v___x_3492_);
v___x_3494_ = lean_array_get_size(v_infos_3440_);
lean_dec_ref(v_infos_3440_);
v___x_3495_ = lean_box_uint64(v_hash_3437_);
v___x_3496_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3443_, v___f_3442_, v_indices_3441_, v___x_3495_, v___x_3494_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v___x_3496_);
lean_ctor_set(v___x_3489_, 0, v___x_3493_);
v___x_3498_ = v___x_3489_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add___boxed(lean_object* v_self_3503_, lean_object* v_url_3504_, lean_object* v_hash_3505_, lean_object* v_path_3506_, lean_object* v_extra_3507_){
_start:
{
uint64_t v_hash_boxed_3508_; uint8_t v_extra_boxed_3509_; lean_object* v_res_3510_; 
v_hash_boxed_3508_ = lean_unbox_uint64(v_hash_3505_);
lean_dec_ref(v_hash_3505_);
v_extra_boxed_3509_ = lean_unbox(v_extra_3507_);
v_res_3510_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_add(v_self_3503_, v_url_3504_, v_hash_boxed_3508_, v_path_3506_, v_extra_boxed_3509_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath(lean_object* v_path_3512_){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0));
v___x_3514_ = l_System_FilePath_addExtension(v_path_3512_, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object* v_cfg_3516_, lean_object* v_out_3517_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0));
v___x_3519_ = l_Lake_JsonObject_getJson_x3f(v_out_3517_, v___x_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v___x_3520_; 
v___x_3520_ = lean_box(0);
return v___x_3520_;
}
else
{
lean_object* v_val_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3536_; 
v_val_3521_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3523_ = v___x_3519_;
v_isShared_3524_ = v_isSharedCheck_3536_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_val_3521_);
lean_dec(v___x_3519_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3536_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_Json_getNat_x3f(v_val_3521_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v___x_3526_; 
lean_dec_ref_known(v___x_3525_, 1);
lean_del_object(v___x_3523_);
v___x_3526_ = lean_box(0);
return v___x_3526_;
}
else
{
lean_object* v_a_3527_; lean_object* v_infos_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_a_3527_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3525_, 1);
v_infos_3528_ = lean_ctor_get(v_cfg_3516_, 1);
v___x_3529_ = lean_array_get_size(v_infos_3528_);
v___x_3530_ = lean_nat_dec_lt(v_a_3527_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; 
lean_dec(v_a_3527_);
lean_del_object(v___x_3523_);
v___x_3531_ = lean_box(0);
return v___x_3531_;
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_array_fget_borrowed(v_infos_3528_, v_a_3527_);
lean_dec(v_a_3527_);
lean_inc(v___x_3532_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3532_);
v___x_3534_ = v___x_3523_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object* v_cfg_3537_, lean_object* v_out_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3537_, v_out_3538_);
lean_dec(v_out_3538_);
lean_dec_ref(v_cfg_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object* v_s_3540_, lean_object* v_pos_3541_){
_start:
{
lean_object* v_str_3542_; lean_object* v_startInclusive_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v_decide_3547_; 
v_str_3542_ = lean_ctor_get(v_s_3540_, 0);
v_startInclusive_3543_ = lean_ctor_get(v_s_3540_, 1);
v___x_3544_ = lean_nat_add(v_startInclusive_3543_, v_pos_3541_);
v___x_3545_ = lean_nat_sub(v___x_3544_, v_startInclusive_3543_);
v___x_3546_ = lean_unsigned_to_nat(0u);
v_decide_3547_ = lean_nat_dec_eq(v___x_3545_, v___x_3546_);
if (v_decide_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3556_; uint32_t v___x_3557_; uint32_t v___x_3558_; uint8_t v___x_3559_; 
lean_inc(v_startInclusive_3543_);
lean_inc_ref(v_str_3542_);
v___x_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3548_, 0, v_str_3542_);
lean_ctor_set(v___x_3548_, 1, v_startInclusive_3543_);
lean_ctor_set(v___x_3548_, 2, v___x_3544_);
v___x_3549_ = lean_unsigned_to_nat(1u);
v___x_3550_ = lean_nat_sub(v___x_3545_, v___x_3549_);
lean_dec(v___x_3545_);
v___x_3551_ = l_String_Slice_posLE(v___x_3548_, v___x_3550_);
lean_dec_ref_known(v___x_3548_, 3);
v___x_3556_ = lean_nat_add(v_startInclusive_3543_, v___x_3551_);
v___x_3557_ = lean_string_utf8_get_fast(v_str_3542_, v___x_3556_);
lean_dec(v___x_3556_);
v___x_3558_ = 32;
v___x_3559_ = lean_uint32_dec_eq(v___x_3557_, v___x_3558_);
if (v___x_3559_ == 0)
{
uint32_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = 9;
v___x_3561_ = lean_uint32_dec_eq(v___x_3557_, v___x_3560_);
if (v___x_3561_ == 0)
{
uint32_t v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = 13;
v___x_3563_ = lean_uint32_dec_eq(v___x_3557_, v___x_3562_);
if (v___x_3563_ == 0)
{
uint32_t v___x_3564_; uint8_t v___x_3565_; 
v___x_3564_ = 10;
v___x_3565_ = lean_uint32_dec_eq(v___x_3557_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_dec(v___x_3551_);
return v_pos_3541_;
}
else
{
goto v___jp_3552_;
}
}
else
{
goto v___jp_3552_;
}
}
else
{
goto v___jp_3552_;
}
}
else
{
goto v___jp_3552_;
}
v___jp_3552_:
{
lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3553_ = lean_nat_add(v___x_3551_, v___x_3549_);
v___x_3554_ = lean_nat_dec_le(v___x_3553_, v_pos_3541_);
lean_dec(v___x_3553_);
if (v___x_3554_ == 0)
{
lean_dec(v___x_3551_);
return v_pos_3541_;
}
else
{
lean_dec(v_pos_3541_);
v_pos_3541_ = v___x_3551_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3545_);
lean_dec(v___x_3544_);
return v_pos_3541_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object* v_s_3566_, lean_object* v_pos_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v_s_3566_, v_pos_3567_);
lean_dec_ref(v_s_3566_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object* v_cfg_3581_, lean_object* v_hOut_3582_, lean_object* v_info_3583_, lean_object* v_code_x3f_3584_, lean_object* v_out_3585_, lean_object* v_line_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v_msg_3590_; lean_object* v___y_3591_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v_a_3610_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v_val_3620_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; uint8_t v_kind_3659_; lean_object* v_scope_3660_; lean_object* v_msg_3662_; lean_object* v___y_3663_; lean_object* v_msg_3706_; lean_object* v___y_3707_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3735_; 
v_kind_3659_ = lean_ctor_get_uint8(v_cfg_3581_, sizeof(void*)*3);
v_scope_3660_ = lean_ctor_get(v_cfg_3581_, 0);
lean_inc_ref(v_scope_3660_);
lean_dec_ref(v_cfg_3581_);
if (v_kind_3659_ == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___y_3735_ = v___x_3737_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3738_; 
v___x_3738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___y_3735_ = v___x_3738_;
goto v___jp_3734_;
}
v___jp_3589_:
{
uint8_t v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3592_ = 3;
v___x_3593_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3593_, 0, v_msg_3590_);
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*1, v___x_3592_);
lean_inc_ref_n(v___y_3591_, 2);
v___x_3594_ = lean_apply_2(v___y_3591_, v___x_3593_, lean_box(0));
v___x_3595_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0));
v___x_3596_ = lean_unsigned_to_nat(0u);
v___x_3597_ = lean_string_utf8_byte_size(v_line_3586_);
lean_inc_ref(v_line_3586_);
v___x_3598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3598_, 0, v_line_3586_);
lean_ctor_set(v___x_3598_, 1, v___x_3596_);
lean_ctor_set(v___x_3598_, 2, v___x_3597_);
v___x_3599_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_3598_, v___x_3597_);
lean_dec_ref_known(v___x_3598_, 3);
v___x_3600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3600_, 0, v_line_3586_);
lean_ctor_set(v___x_3600_, 1, v___x_3596_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
v___x_3601_ = l_String_Slice_toString(v___x_3600_);
lean_dec_ref_known(v___x_3600_, 3);
v___x_3602_ = lean_string_append(v___x_3595_, v___x_3601_);
lean_dec_ref(v___x_3601_);
v___x_3603_ = 0;
v___x_3604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set_uint8(v___x_3604_, sizeof(void*)*1, v___x_3603_);
v___x_3605_ = lean_apply_2(v___y_3591_, v___x_3604_, lean_box(0));
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
}
v___jp_3607_:
{
if (lean_obj_tag(v_a_3610_) == 1)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3611_ = lean_ctor_get(v_a_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v_a_3610_, 1);
v___x_3612_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3613_ = lean_string_append(v___y_3609_, v___x_3612_);
v___x_3614_ = lean_string_append(v___x_3613_, v_a_3611_);
lean_dec(v_a_3611_);
v_msg_3590_ = v___x_3614_;
v___y_3591_ = v___y_3608_;
goto v___jp_3589_;
}
else
{
lean_dec_ref(v_a_3610_);
v_msg_3590_ = v___y_3609_;
v___y_3591_ = v___y_3608_;
goto v___jp_3589_;
}
}
v___jp_3615_:
{
lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3621_ = lean_array_get_size(v___y_3618_);
v___x_3622_ = lean_nat_dec_lt(v___y_3616_, v___x_3621_);
if (v___x_3622_ == 0)
{
v___y_3608_ = v___y_3617_;
v___y_3609_ = v___y_3619_;
v_a_3610_ = v_val_3620_;
goto v___jp_3607_;
}
else
{
lean_object* v___x_3623_; size_t v___x_3624_; size_t v___x_3625_; lean_object* v___x_3626_; 
v___x_3623_ = lean_box(0);
v___x_3624_ = ((size_t)0ULL);
v___x_3625_ = lean_usize_of_nat(v___x_3621_);
v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3618_, v___x_3624_, v___x_3625_, v___x_3623_, v___y_3617_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_dec_ref_known(v___x_3626_, 1);
v___y_3608_ = v___y_3617_;
v___y_3609_ = v___y_3619_;
v_a_3610_ = v_val_3620_;
goto v___jp_3607_;
}
else
{
lean_dec_ref(v_val_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_line_3586_);
return v___x_3626_;
}
}
}
v___jp_3627_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3632_ = l_Lake_JsonObject_getJson_x3f(v_out_3585_, v___x_3631_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_dec_ref(v___y_3629_);
v_msg_3590_ = v___y_3630_;
v___y_3591_ = v___y_3628_;
goto v___jp_3589_;
}
else
{
lean_object* v_val_3633_; lean_object* v___x_3634_; 
v_val_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_val_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3634_ = l_Lean_Json_getNat_x3f(v_val_3633_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_dec_ref_known(v___x_3634_, 1);
lean_dec_ref(v___y_3629_);
v_msg_3590_ = v___y_3630_;
v___y_3591_ = v___y_3628_;
goto v___jp_3589_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
v___x_3636_ = lean_unsigned_to_nat(0u);
v___x_3637_ = lean_nat_dec_lt(v___x_3636_, v_a_3635_);
lean_dec(v_a_3635_);
if (v___x_3637_ == 0)
{
lean_dec_ref(v___y_3629_);
v_msg_3590_ = v___y_3630_;
v___y_3591_ = v___y_3628_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3));
v___x_3639_ = l_Lake_JsonObject_getJson_x3f(v_out_3585_, v___x_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_dec_ref(v___y_3629_);
v_msg_3590_ = v___y_3630_;
v___y_3591_ = v___y_3628_;
goto v___jp_3589_;
}
else
{
lean_object* v_val_3640_; lean_object* v___x_3641_; 
v_val_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_val_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v___x_3641_ = l_Lean_Json_getStr_x3f(v_val_3640_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_dec_ref_known(v___x_3641_, 1);
lean_dec_ref(v___y_3629_);
v_msg_3590_ = v___y_3630_;
v___y_3591_ = v___y_3628_;
goto v___jp_3589_;
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3658_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3658_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3658_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3647_ = lean_string_dec_eq(v_a_3642_, v___x_3646_);
lean_dec(v_a_3642_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_3649_ = l_IO_FS_readFile(v___y_3629_);
lean_dec_ref(v___y_3629_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_a_3650_);
v___x_3652_ = v___x_3644_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
v___y_3616_ = v___x_3636_;
v___y_3617_ = v___y_3628_;
v___y_3618_ = v___x_3648_;
v___y_3619_ = v___y_3630_;
v_val_3620_ = v___x_3652_;
goto v___jp_3615_;
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; 
v_a_3654_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3649_, 1);
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 0);
lean_ctor_set(v___x_3644_, 0, v_a_3654_);
v___x_3656_ = v___x_3644_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
v___y_3616_ = v___x_3636_;
v___y_3617_ = v___y_3628_;
v___y_3618_ = v___x_3648_;
v___y_3619_ = v___y_3630_;
v_val_3620_ = v___x_3656_;
goto v___jp_3615_;
}
}
}
else
{
lean_del_object(v___x_3644_);
lean_dec_ref(v___y_3629_);
v_msg_3590_ = v___y_3630_;
v___y_3591_ = v___y_3628_;
goto v___jp_3589_;
}
}
}
}
}
}
}
}
v___jp_3661_:
{
lean_object* v_url_3664_; lean_object* v_path_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v_msg_3671_; 
v_url_3664_ = lean_ctor_get(v_info_3583_, 0);
lean_inc_ref(v_url_3664_);
v_path_3665_ = lean_ctor_get(v_info_3583_, 1);
lean_inc_ref(v_path_3665_);
lean_dec_ref(v_info_3583_);
v___x_3666_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3667_ = lean_string_append(v_msg_3662_, v___x_3666_);
v___x_3668_ = lean_string_append(v___x_3667_, v_path_3665_);
v___x_3669_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3670_ = lean_string_append(v___x_3668_, v___x_3669_);
v_msg_3671_ = lean_string_append(v___x_3670_, v_url_3664_);
lean_dec_ref(v_url_3664_);
if (v_kind_3659_ == 0)
{
lean_object* v___x_3672_; lean_object* v_tmpPath_3673_; 
v___x_3672_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0));
v_tmpPath_3673_ = l_System_FilePath_addExtension(v_path_3665_, v___x_3672_);
if (lean_obj_tag(v_code_x3f_3584_) == 1)
{
lean_object* v_a_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_a_3674_ = lean_ctor_get(v_code_x3f_3584_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v_code_x3f_3584_, 1);
v___x_3675_ = lean_unsigned_to_nat(404u);
v___x_3676_ = lean_nat_dec_eq(v_a_3674_, v___x_3675_);
lean_dec(v_a_3674_);
if (v___x_3676_ == 0)
{
v___y_3628_ = v___y_3663_;
v___y_3629_ = v_tmpPath_3673_;
v___y_3630_ = v_msg_3671_;
goto v___jp_3627_;
}
else
{
lean_dec_ref(v_tmpPath_3673_);
v_msg_3590_ = v_msg_3671_;
v___y_3591_ = v___y_3663_;
goto v___jp_3589_;
}
}
else
{
lean_dec_ref(v_code_x3f_3584_);
v___y_3628_ = v___y_3663_;
v___y_3629_ = v_tmpPath_3673_;
v___y_3630_ = v_msg_3671_;
goto v___jp_3627_;
}
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec_ref(v_path_3665_);
lean_dec_ref(v_code_x3f_3584_);
v___x_3677_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3678_ = l_Lake_JsonObject_getJson_x3f(v_out_3585_, v___x_3677_);
if (lean_obj_tag(v___x_3678_) == 0)
{
v_msg_3590_ = v_msg_3671_;
v___y_3591_ = v___y_3663_;
goto v___jp_3589_;
}
else
{
lean_object* v_val_3679_; lean_object* v___x_3680_; 
v_val_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_val_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = l_Lean_Json_getNat_x3f(v_val_3679_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_dec_ref_known(v___x_3680_, 1);
v_msg_3590_ = v_msg_3671_;
v___y_3591_ = v___y_3663_;
goto v___jp_3589_;
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
v___x_3682_ = lean_unsigned_to_nat(0u);
v___x_3683_ = lean_nat_dec_lt(v___x_3682_, v_a_3681_);
if (v___x_3683_ == 0)
{
lean_dec(v_a_3681_);
v_msg_3590_ = v_msg_3671_;
v___y_3591_ = v___y_3663_;
goto v___jp_3589_;
}
else
{
size_t v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_usize_of_nat(v_a_3681_);
lean_dec(v_a_3681_);
v___x_3685_ = lean_io_prim_handle_read(v_hOut_3582_, v___x_3684_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; uint8_t v___x_3687_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = lean_string_validate_utf8(v_a_3686_);
if (v___x_3687_ == 0)
{
lean_dec(v_a_3686_);
v_msg_3590_ = v_msg_3671_;
v___y_3591_ = v___y_3663_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3688_ = lean_string_from_utf8_unchecked(v_a_3686_);
v___x_3689_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3690_ = lean_string_append(v_msg_3671_, v___x_3689_);
v___x_3691_ = lean_string_append(v___x_3690_, v___x_3688_);
lean_dec_ref(v___x_3688_);
v_msg_3590_ = v___x_3691_;
v___y_3591_ = v___y_3663_;
goto v___jp_3589_;
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3704_; 
lean_dec_ref(v_msg_3671_);
lean_dec_ref(v_line_3586_);
v_a_3692_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3694_ = v___x_3685_;
v_isShared_3695_ = v_isSharedCheck_3704_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3685_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3704_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3696_ = lean_io_error_to_string(v_a_3692_);
v___x_3697_ = 3;
v___x_3698_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*1, v___x_3697_);
lean_inc_ref(v___y_3663_);
v___x_3699_ = lean_apply_2(v___y_3663_, v___x_3698_, lean_box(0));
v___x_3700_ = lean_box(0);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3700_);
v___x_3702_ = v___x_3694_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
}
}
v___jp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_3709_ = l_Lake_JsonObject_getJson_x3f(v_out_3585_, v___x_3708_);
if (lean_obj_tag(v___x_3709_) == 0)
{
v_msg_3662_ = v_msg_3706_;
v___y_3663_ = v___y_3707_;
goto v___jp_3661_;
}
else
{
lean_object* v_val_3710_; lean_object* v___x_3711_; 
v_val_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_val_3710_);
lean_dec_ref_known(v___x_3709_, 1);
v___x_3711_ = l_Lean_Json_getStr_x3f(v_val_3710_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_dec_ref_known(v___x_3711_, 1);
v_msg_3662_ = v_msg_3706_;
v___y_3663_ = v___y_3707_;
goto v___jp_3661_;
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_msg_3715_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5));
v___x_3714_ = lean_string_append(v_msg_3706_, v___x_3713_);
v_msg_3715_ = lean_string_append(v___x_3714_, v_a_3712_);
lean_dec(v_a_3712_);
v_msg_3662_ = v_msg_3715_;
v___y_3663_ = v___y_3707_;
goto v___jp_3661_;
}
}
}
v___jp_3716_:
{
uint64_t v_hash_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v_msg_3726_; 
v_hash_3719_ = lean_ctor_get_uint64(v_info_3583_, sizeof(void*)*3);
v___x_3720_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_3721_ = lean_string_append(v___y_3718_, v___x_3720_);
v___x_3722_ = lean_string_append(v___x_3721_, v___y_3717_);
v___x_3723_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7));
v___x_3724_ = lean_string_append(v___x_3722_, v___x_3723_);
v___x_3725_ = l_Lake_lowerHexUInt64(v_hash_3719_);
v_msg_3726_ = lean_string_append(v___x_3724_, v___x_3725_);
lean_dec_ref(v___x_3725_);
if (lean_obj_tag(v_code_x3f_3584_) == 1)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v_msg_3733_; 
v_a_3727_ = lean_ctor_get(v_code_x3f_3584_, 0);
v___x_3728_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8));
v___x_3729_ = lean_string_append(v_msg_3726_, v___x_3728_);
lean_inc(v_a_3727_);
v___x_3730_ = l_Nat_reprFast(v_a_3727_);
v___x_3731_ = lean_string_append(v___x_3729_, v___x_3730_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v_msg_3733_ = lean_string_append(v___x_3731_, v___x_3732_);
v_msg_3706_ = v_msg_3733_;
v___y_3707_ = v_a_3587_;
goto v___jp_3705_;
}
else
{
v_msg_3706_ = v_msg_3726_;
v___y_3707_ = v_a_3587_;
goto v___jp_3705_;
}
}
v___jp_3734_:
{
lean_object* v_s_3736_; 
v_s_3736_ = lean_ctor_get(v_scope_3660_, 0);
lean_inc_ref(v_s_3736_);
lean_dec_ref(v_scope_3660_);
v___y_3717_ = v___y_3735_;
v___y_3718_ = v_s_3736_;
goto v___jp_3716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object* v_cfg_3739_, lean_object* v_hOut_3740_, lean_object* v_info_3741_, lean_object* v_code_x3f_3742_, lean_object* v_out_3743_, lean_object* v_line_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3739_, v_hOut_3740_, v_info_3741_, v_code_x3f_3742_, v_out_3743_, v_line_3744_, v_a_3745_);
lean_dec_ref(v_a_3745_);
lean_dec(v_out_3743_);
lean_dec(v_hOut_3740_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__0(lean_object* v_a_3748_, lean_object* v_cfg_3749_, lean_object* v_hOut_3750_, lean_object* v_info_3751_, lean_object* v_code_x3f_3752_, lean_object* v_out_3753_, lean_object* v_line_3754_){
_start:
{
lean_object* v_msg_3757_; lean_object* v___y_3758_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v_a_3777_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v_val_3787_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v_kind_3826_; lean_object* v_scope_3827_; lean_object* v_msg_3829_; lean_object* v___y_3830_; lean_object* v_msg_3873_; lean_object* v___y_3874_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3902_; 
v_kind_3826_ = lean_ctor_get_uint8(v_cfg_3749_, sizeof(void*)*3);
v_scope_3827_ = lean_ctor_get(v_cfg_3749_, 0);
lean_inc_ref(v_scope_3827_);
lean_dec_ref(v_cfg_3749_);
if (v_kind_3826_ == 0)
{
lean_object* v___x_3904_; 
v___x_3904_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___y_3902_ = v___x_3904_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3905_; 
v___x_3905_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___y_3902_ = v___x_3905_;
goto v___jp_3901_;
}
v___jp_3756_:
{
uint8_t v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3759_ = 3;
v___x_3760_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3760_, 0, v_msg_3757_);
lean_ctor_set_uint8(v___x_3760_, sizeof(void*)*1, v___x_3759_);
lean_inc_ref_n(v___y_3758_, 2);
v___x_3761_ = lean_apply_2(v___y_3758_, v___x_3760_, lean_box(0));
v___x_3762_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0));
v___x_3763_ = lean_unsigned_to_nat(0u);
v___x_3764_ = lean_string_utf8_byte_size(v_line_3754_);
lean_inc_ref(v_line_3754_);
v___x_3765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3765_, 0, v_line_3754_);
lean_ctor_set(v___x_3765_, 1, v___x_3763_);
lean_ctor_set(v___x_3765_, 2, v___x_3764_);
v___x_3766_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_3765_, v___x_3764_);
lean_dec_ref_known(v___x_3765_, 3);
v___x_3767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3767_, 0, v_line_3754_);
lean_ctor_set(v___x_3767_, 1, v___x_3763_);
lean_ctor_set(v___x_3767_, 2, v___x_3766_);
v___x_3768_ = l_String_Slice_toString(v___x_3767_);
lean_dec_ref_known(v___x_3767_, 3);
v___x_3769_ = lean_string_append(v___x_3762_, v___x_3768_);
lean_dec_ref(v___x_3768_);
v___x_3770_ = 0;
v___x_3771_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set_uint8(v___x_3771_, sizeof(void*)*1, v___x_3770_);
v___x_3772_ = lean_apply_2(v___y_3758_, v___x_3771_, lean_box(0));
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
v___jp_3774_:
{
if (lean_obj_tag(v_a_3777_) == 1)
{
lean_object* v_a_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_a_3778_ = lean_ctor_get(v_a_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v_a_3777_, 1);
v___x_3779_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3780_ = lean_string_append(v___y_3776_, v___x_3779_);
v___x_3781_ = lean_string_append(v___x_3780_, v_a_3778_);
lean_dec(v_a_3778_);
v_msg_3757_ = v___x_3781_;
v___y_3758_ = v___y_3775_;
goto v___jp_3756_;
}
else
{
lean_dec_ref(v_a_3777_);
v_msg_3757_ = v___y_3776_;
v___y_3758_ = v___y_3775_;
goto v___jp_3756_;
}
}
v___jp_3782_:
{
lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3788_ = lean_array_get_size(v___y_3786_);
v___x_3789_ = lean_nat_dec_lt(v___y_3785_, v___x_3788_);
if (v___x_3789_ == 0)
{
v___y_3775_ = v___y_3784_;
v___y_3776_ = v___y_3783_;
v_a_3777_ = v_val_3787_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3790_; size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v___x_3790_ = lean_box(0);
v___x_3791_ = ((size_t)0ULL);
v___x_3792_ = lean_usize_of_nat(v___x_3788_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3786_, v___x_3791_, v___x_3792_, v___x_3790_, v___y_3784_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_dec_ref_known(v___x_3793_, 1);
v___y_3775_ = v___y_3784_;
v___y_3776_ = v___y_3783_;
v_a_3777_ = v_val_3787_;
goto v___jp_3774_;
}
else
{
lean_dec_ref(v_val_3787_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_line_3754_);
return v___x_3793_;
}
}
}
v___jp_3794_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3799_ = l_Lake_JsonObject_getJson_x3f(v_out_3753_, v___x_3798_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref(v___y_3797_);
v_msg_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
goto v___jp_3756_;
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
lean_dec_ref(v___y_3797_);
v_msg_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
goto v___jp_3756_;
}
else
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
lean_dec_ref(v___y_3797_);
v_msg_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3));
v___x_3806_ = l_Lake_JsonObject_getJson_x3f(v_out_3753_, v___x_3805_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref(v___y_3797_);
v_msg_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
goto v___jp_3756_;
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
lean_dec_ref(v___y_3797_);
v_msg_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
goto v___jp_3756_;
}
else
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
v___x_3815_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_3816_ = l_IO_FS_readFile(v___y_3797_);
lean_dec_ref(v___y_3797_);
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
v___y_3783_ = v___y_3796_;
v___y_3784_ = v___y_3795_;
v___y_3785_ = v___x_3803_;
v___y_3786_ = v___x_3815_;
v_val_3787_ = v___x_3819_;
goto v___jp_3782_;
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
v___y_3783_ = v___y_3796_;
v___y_3784_ = v___y_3795_;
v___y_3785_ = v___x_3803_;
v___y_3786_ = v___x_3815_;
v_val_3787_ = v___x_3823_;
goto v___jp_3782_;
}
}
}
else
{
lean_del_object(v___x_3811_);
lean_dec_ref(v___y_3797_);
v_msg_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
goto v___jp_3756_;
}
}
}
}
}
}
}
}
v___jp_3828_:
{
lean_object* v_url_3831_; lean_object* v_path_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v_msg_3838_; 
v_url_3831_ = lean_ctor_get(v_info_3751_, 0);
lean_inc_ref(v_url_3831_);
v_path_3832_ = lean_ctor_get(v_info_3751_, 1);
lean_inc_ref(v_path_3832_);
lean_dec_ref(v_info_3751_);
v___x_3833_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3834_ = lean_string_append(v_msg_3829_, v___x_3833_);
v___x_3835_ = lean_string_append(v___x_3834_, v_path_3832_);
v___x_3836_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3837_ = lean_string_append(v___x_3835_, v___x_3836_);
v_msg_3838_ = lean_string_append(v___x_3837_, v_url_3831_);
lean_dec_ref(v_url_3831_);
if (v_kind_3826_ == 0)
{
lean_object* v___x_3839_; lean_object* v_tmpPath_3840_; 
v___x_3839_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0));
v_tmpPath_3840_ = l_System_FilePath_addExtension(v_path_3832_, v___x_3839_);
if (lean_obj_tag(v_code_x3f_3752_) == 1)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v_a_3841_ = lean_ctor_get(v_code_x3f_3752_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v_code_x3f_3752_, 1);
v___x_3842_ = lean_unsigned_to_nat(404u);
v___x_3843_ = lean_nat_dec_eq(v_a_3841_, v___x_3842_);
lean_dec(v_a_3841_);
if (v___x_3843_ == 0)
{
v___y_3795_ = v___y_3830_;
v___y_3796_ = v_msg_3838_;
v___y_3797_ = v_tmpPath_3840_;
goto v___jp_3794_;
}
else
{
lean_dec_ref(v_tmpPath_3840_);
v_msg_3757_ = v_msg_3838_;
v___y_3758_ = v___y_3830_;
goto v___jp_3756_;
}
}
else
{
lean_dec_ref(v_code_x3f_3752_);
v___y_3795_ = v___y_3830_;
v___y_3796_ = v_msg_3838_;
v___y_3797_ = v_tmpPath_3840_;
goto v___jp_3794_;
}
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec_ref(v_path_3832_);
lean_dec_ref(v_code_x3f_3752_);
v___x_3844_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3845_ = l_Lake_JsonObject_getJson_x3f(v_out_3753_, v___x_3844_);
if (lean_obj_tag(v___x_3845_) == 0)
{
v_msg_3757_ = v_msg_3838_;
v___y_3758_ = v___y_3830_;
goto v___jp_3756_;
}
else
{
lean_object* v_val_3846_; lean_object* v___x_3847_; 
v_val_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_val_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = l_Lean_Json_getNat_x3f(v_val_3846_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_dec_ref_known(v___x_3847_, 1);
v_msg_3757_ = v_msg_3838_;
v___y_3758_ = v___y_3830_;
goto v___jp_3756_;
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = lean_unsigned_to_nat(0u);
v___x_3850_ = lean_nat_dec_lt(v___x_3849_, v_a_3848_);
if (v___x_3850_ == 0)
{
lean_dec(v_a_3848_);
v_msg_3757_ = v_msg_3838_;
v___y_3758_ = v___y_3830_;
goto v___jp_3756_;
}
else
{
size_t v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_usize_of_nat(v_a_3848_);
lean_dec(v_a_3848_);
v___x_3852_ = lean_io_prim_handle_read(v_hOut_3750_, v___x_3851_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; uint8_t v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = lean_string_validate_utf8(v_a_3853_);
if (v___x_3854_ == 0)
{
lean_dec(v_a_3853_);
v_msg_3757_ = v_msg_3838_;
v___y_3758_ = v___y_3830_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3855_ = lean_string_from_utf8_unchecked(v_a_3853_);
v___x_3856_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3857_ = lean_string_append(v_msg_3838_, v___x_3856_);
v___x_3858_ = lean_string_append(v___x_3857_, v___x_3855_);
lean_dec_ref(v___x_3855_);
v_msg_3757_ = v___x_3858_;
v___y_3758_ = v___y_3830_;
goto v___jp_3756_;
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3871_; 
lean_dec_ref(v_msg_3838_);
lean_dec_ref(v_line_3754_);
v_a_3859_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3861_ = v___x_3852_;
v_isShared_3862_ = v_isSharedCheck_3871_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3852_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3871_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; uint8_t v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3863_ = lean_io_error_to_string(v_a_3859_);
v___x_3864_ = 3;
v___x_3865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*1, v___x_3864_);
lean_inc_ref(v___y_3830_);
v___x_3866_ = lean_apply_2(v___y_3830_, v___x_3865_, lean_box(0));
v___x_3867_ = lean_box(0);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3867_);
v___x_3869_ = v___x_3861_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
}
}
}
v___jp_3872_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_3876_ = l_Lake_JsonObject_getJson_x3f(v_out_3753_, v___x_3875_);
if (lean_obj_tag(v___x_3876_) == 0)
{
v_msg_3829_ = v_msg_3873_;
v___y_3830_ = v___y_3874_;
goto v___jp_3828_;
}
else
{
lean_object* v_val_3877_; lean_object* v___x_3878_; 
v_val_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = l_Lean_Json_getStr_x3f(v_val_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_dec_ref_known(v___x_3878_, 1);
v_msg_3829_ = v_msg_3873_;
v___y_3830_ = v___y_3874_;
goto v___jp_3828_;
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v_msg_3882_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___x_3880_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5));
v___x_3881_ = lean_string_append(v_msg_3873_, v___x_3880_);
v_msg_3882_ = lean_string_append(v___x_3881_, v_a_3879_);
lean_dec(v_a_3879_);
v_msg_3829_ = v_msg_3882_;
v___y_3830_ = v___y_3874_;
goto v___jp_3828_;
}
}
}
v___jp_3883_:
{
uint64_t v_hash_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_msg_3893_; 
v_hash_3886_ = lean_ctor_get_uint64(v_info_3751_, sizeof(void*)*3);
v___x_3887_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_3888_ = lean_string_append(v___y_3885_, v___x_3887_);
v___x_3889_ = lean_string_append(v___x_3888_, v___y_3884_);
v___x_3890_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7));
v___x_3891_ = lean_string_append(v___x_3889_, v___x_3890_);
v___x_3892_ = l_Lake_lowerHexUInt64(v_hash_3886_);
v_msg_3893_ = lean_string_append(v___x_3891_, v___x_3892_);
lean_dec_ref(v___x_3892_);
if (lean_obj_tag(v_code_x3f_3752_) == 1)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v_msg_3900_; 
v_a_3894_ = lean_ctor_get(v_code_x3f_3752_, 0);
v___x_3895_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8));
v___x_3896_ = lean_string_append(v_msg_3893_, v___x_3895_);
lean_inc(v_a_3894_);
v___x_3897_ = l_Nat_reprFast(v_a_3894_);
v___x_3898_ = lean_string_append(v___x_3896_, v___x_3897_);
lean_dec_ref(v___x_3897_);
v___x_3899_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v_msg_3900_ = lean_string_append(v___x_3898_, v___x_3899_);
v_msg_3873_ = v_msg_3900_;
v___y_3874_ = v_a_3748_;
goto v___jp_3872_;
}
else
{
v_msg_3873_ = v_msg_3893_;
v___y_3874_ = v_a_3748_;
goto v___jp_3872_;
}
}
v___jp_3901_:
{
lean_object* v_s_3903_; 
v_s_3903_ = lean_ctor_get(v_scope_3827_, 0);
lean_inc_ref(v_s_3903_);
lean_dec_ref(v_scope_3827_);
v___y_3884_ = v___y_3902_;
v___y_3885_ = v_s_3903_;
goto v___jp_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__0___boxed(lean_object* v_a_3906_, lean_object* v_cfg_3907_, lean_object* v_hOut_3908_, lean_object* v_info_3909_, lean_object* v_code_x3f_3910_, lean_object* v_out_3911_, lean_object* v_line_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__0(v_a_3906_, v_cfg_3907_, v_hOut_3908_, v_info_3909_, v_code_x3f_3910_, v_out_3911_, v_line_3912_);
lean_dec(v_out_3911_);
lean_dec(v_hOut_3908_);
lean_dec_ref(v_a_3906_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1(uint64_t v___x_3916_, uint64_t v_hash_3917_, lean_object* v_a_3918_, lean_object* v_as_3919_, size_t v_sz_3920_, size_t v_i_3921_, lean_object* v_b_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_a_3927_; lean_object* v_snd_3928_; uint8_t v___x_3932_; 
v___x_3932_ = lean_usize_dec_lt(v_i_3921_, v_sz_3920_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v_b_3922_);
lean_ctor_set(v___x_3933_, 1, v___y_3923_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
else
{
uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v_a_3937_; lean_object* v_fst_3939_; lean_object* v_snd_3940_; lean_object* v___x_3957_; lean_object* v_val_3959_; lean_object* v___x_3972_; 
v___x_3935_ = lean_uint64_dec_eq(v___x_3916_, v_hash_3917_);
v___x_3936_ = lean_box(0);
v_a_3937_ = lean_array_uget_borrowed(v_as_3919_, v_i_3921_);
v___x_3957_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_3972_ = l_IO_FS_writeBinFile(v_a_3937_, v_a_3918_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set_tag(v___x_3975_, 1);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
v_val_3959_ = v___x_3978_;
goto v___jp_3958_;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3972_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3972_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set_tag(v___x_3983_, 0);
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
v_val_3959_ = v___x_3986_;
goto v___jp_3958_;
}
}
}
v___jp_3938_:
{
if (lean_obj_tag(v_fst_3939_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v_numSuccesses_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
v_a_3941_ = lean_ctor_get(v_fst_3939_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v_fst_3939_, 1);
v___x_3942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1___closed__0));
lean_inc(v_a_3937_);
v___x_3943_ = lean_string_append(v_a_3937_, v___x_3942_);
v___x_3944_ = lean_io_error_to_string(v_a_3941_);
v___x_3945_ = lean_string_append(v___x_3943_, v___x_3944_);
lean_dec_ref(v___x_3944_);
v___x_3946_ = 3;
v___x_3947_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set_uint8(v___x_3947_, sizeof(void*)*1, v___x_3946_);
lean_inc_ref(v___y_3924_);
v___x_3948_ = lean_apply_2(v___y_3924_, v___x_3947_, lean_box(0));
v_numSuccesses_3949_ = lean_ctor_get(v_snd_3940_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_snd_3940_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v_snd_3940_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_numSuccesses_3949_);
lean_dec(v_snd_3940_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_numSuccesses_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*1, v___x_3935_);
v_a_3927_ = v___x_3936_;
v_snd_3928_ = v___x_3954_;
goto v___jp_3926_;
}
}
}
else
{
lean_dec_ref(v_fst_3939_);
v_a_3927_ = v___x_3936_;
v_snd_3928_ = v_snd_3940_;
goto v___jp_3926_;
}
}
v___jp_3958_:
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_3960_ == 0)
{
v_fst_3939_ = v_val_3959_;
v_snd_3940_ = v___y_3923_;
goto v___jp_3938_;
}
else
{
size_t v___x_3961_; size_t v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = ((size_t)0ULL);
v___x_3962_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3957_, v___x_3961_, v___x_3962_, v___x_3936_, v___y_3924_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_dec_ref_known(v___x_3963_, 1);
v_fst_3939_ = v_val_3959_;
v_snd_3940_ = v___y_3923_;
goto v___jp_3938_;
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_val_3959_);
lean_dec_ref(v___y_3923_);
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
}
v___jp_3926_:
{
size_t v___x_3929_; size_t v___x_3930_; 
v___x_3929_ = ((size_t)1ULL);
v___x_3930_ = lean_usize_add(v_i_3921_, v___x_3929_);
v_i_3921_ = v___x_3930_;
v_b_3922_ = v_a_3927_;
v___y_3923_ = v_snd_3928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1___boxed(lean_object* v___x_3989_, lean_object* v_hash_3990_, lean_object* v_a_3991_, lean_object* v_as_3992_, lean_object* v_sz_3993_, lean_object* v_i_3994_, lean_object* v_b_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
uint64_t v___x_21267__boxed_3999_; uint64_t v_hash_21268__boxed_4000_; size_t v_sz_boxed_4001_; size_t v_i_boxed_4002_; lean_object* v_res_4003_; 
v___x_21267__boxed_3999_ = lean_unbox_uint64(v___x_3989_);
lean_dec_ref(v___x_3989_);
v_hash_21268__boxed_4000_ = lean_unbox_uint64(v_hash_3990_);
lean_dec_ref(v_hash_3990_);
v_sz_boxed_4001_ = lean_unbox_usize(v_sz_3993_);
lean_dec(v_sz_3993_);
v_i_boxed_4002_ = lean_unbox_usize(v_i_3994_);
lean_dec(v_i_3994_);
v_res_4003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1(v___x_21267__boxed_3999_, v_hash_21268__boxed_4000_, v_a_3991_, v_as_3992_, v_sz_boxed_4001_, v_i_boxed_4002_, v_b_3995_, v___y_3996_, v___y_3997_);
lean_dec_ref(v___y_3997_);
lean_dec_ref(v_as_3992_);
lean_dec_ref(v_a_3991_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer(lean_object* v_cfg_4008_, lean_object* v_hOut_4009_, lean_object* v_info_4010_, lean_object* v_code_4011_, lean_object* v_out_4012_, lean_object* v_line_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v___y_4018_; lean_object* v_url_4033_; uint64_t v_hash_4034_; lean_object* v_path_4035_; lean_object* v_extraPaths_4036_; uint8_t v___y_4038_; lean_object* v___y_4039_; uint64_t v___y_4040_; lean_object* v_fst_4041_; lean_object* v_snd_4042_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4080_; lean_object* v___y_4081_; uint64_t v___y_4082_; lean_object* v___y_4083_; lean_object* v_val_4084_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v_fst_4102_; lean_object* v_snd_4103_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v_val_4205_; lean_object* v___y_4221_; lean_object* v___y_4250_; uint8_t v_kind_4284_; 
v_url_4033_ = lean_ctor_get(v_info_4010_, 0);
v_hash_4034_ = lean_ctor_get_uint64(v_info_4010_, sizeof(void*)*3);
v_path_4035_ = lean_ctor_get(v_info_4010_, 1);
v_extraPaths_4036_ = lean_ctor_get(v_info_4010_, 2);
v_kind_4284_ = lean_ctor_get_uint8(v_cfg_4008_, sizeof(void*)*3);
if (v_kind_4284_ == 0)
{
lean_object* v_scope_4285_; lean_object* v_s_4286_; 
v_scope_4285_ = lean_ctor_get(v_cfg_4008_, 0);
v_s_4286_ = lean_ctor_get(v_scope_4285_, 0);
lean_inc_ref(v_s_4286_);
v___y_4250_ = v_s_4286_;
goto v___jp_4249_;
}
else
{
lean_object* v_scope_4287_; lean_object* v_s_4288_; 
lean_inc_ref(v_path_4035_);
lean_inc_ref(v_url_4033_);
lean_dec_ref(v_line_4013_);
lean_dec(v_code_4011_);
lean_dec_ref(v_info_4010_);
v_scope_4287_ = lean_ctor_get(v_cfg_4008_, 0);
lean_inc_ref(v_scope_4287_);
lean_dec_ref(v_cfg_4008_);
v_s_4288_ = lean_ctor_get(v_scope_4287_, 0);
lean_inc_ref(v_s_4288_);
lean_dec_ref(v_scope_4287_);
v___y_4221_ = v_s_4288_;
goto v___jp_4220_;
}
v___jp_4017_:
{
uint8_t v_didError_4019_; lean_object* v_numSuccesses_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4032_; 
v_didError_4019_ = lean_ctor_get_uint8(v___y_4018_, sizeof(void*)*1);
v_numSuccesses_4020_ = lean_ctor_get(v___y_4018_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___y_4018_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4022_ = v___y_4018_;
v_isShared_4023_ = v_isSharedCheck_4032_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_numSuccesses_4020_);
lean_dec(v___y_4018_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4032_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4024_ = lean_box(0);
v___x_4025_ = lean_unsigned_to_nat(1u);
v___x_4026_ = lean_nat_add(v_numSuccesses_4020_, v___x_4025_);
lean_dec(v_numSuccesses_4020_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4026_);
v___x_4028_ = v___x_4022_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4026_);
lean_ctor_set_uint8(v_reuseFailAlloc_4031_, sizeof(void*)*1, v_didError_4019_);
v___x_4028_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4024_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
v___jp_4037_:
{
if (lean_obj_tag(v_fst_4041_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v___y_4039_);
lean_dec_ref(v_extraPaths_4036_);
v_a_4043_ = lean_ctor_get(v_fst_4041_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_fst_4041_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4045_ = v_fst_4041_;
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v_fst_4041_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4067_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v_numSuccesses_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4066_; 
v___x_4047_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__0));
v___x_4048_ = lean_string_append(v_path_4035_, v___x_4047_);
v___x_4049_ = lean_io_error_to_string(v_a_4043_);
v___x_4050_ = lean_string_append(v___x_4048_, v___x_4049_);
lean_dec_ref(v___x_4049_);
v___x_4051_ = 3;
v___x_4052_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set_uint8(v___x_4052_, sizeof(void*)*1, v___x_4051_);
lean_inc_ref(v_a_4015_);
v___x_4053_ = lean_apply_2(v_a_4015_, v___x_4052_, lean_box(0));
v_numSuccesses_4054_ = lean_ctor_get(v_snd_4042_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_snd_4042_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4056_ = v_snd_4042_;
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_numSuccesses_4054_);
lean_dec(v_snd_4042_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4058_ = lean_box(0);
if (v_isShared_4057_ == 0)
{
v___x_4060_ = v___x_4056_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_numSuccesses_4054_);
v___x_4060_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_ctor_set_uint8(v___x_4060_, sizeof(void*)*1, v___y_4038_);
v___x_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4058_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4061_);
v___x_4063_ = v___x_4045_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
else
{
lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
lean_dec_ref(v_fst_4041_);
lean_dec_ref(v_path_4035_);
v___x_4068_ = lean_array_get_size(v_extraPaths_4036_);
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = lean_nat_dec_eq(v___x_4068_, v___x_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; size_t v_sz_4072_; size_t v___x_4073_; lean_object* v___x_4074_; 
v___x_4071_ = lean_box(0);
v_sz_4072_ = lean_array_size(v_extraPaths_4036_);
v___x_4073_ = ((size_t)0ULL);
v___x_4074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__1(v___y_4040_, v_hash_4034_, v___y_4039_, v_extraPaths_4036_, v_sz_4072_, v___x_4073_, v___x_4071_, v_snd_4042_, v_a_4015_);
lean_dec_ref(v_extraPaths_4036_);
lean_dec_ref(v___y_4039_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v_snd_4076_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v_snd_4076_ = lean_ctor_get(v_a_4075_, 1);
lean_inc(v_snd_4076_);
lean_dec(v_a_4075_);
v___y_4018_ = v_snd_4076_;
goto v___jp_4017_;
}
else
{
return v___x_4074_;
}
}
else
{
lean_dec_ref(v___y_4039_);
lean_dec_ref(v_extraPaths_4036_);
v___y_4018_ = v_snd_4042_;
goto v___jp_4017_;
}
}
}
v___jp_4077_:
{
lean_object* v___x_4085_; uint8_t v___x_4086_; 
v___x_4085_ = lean_array_get_size(v___y_4079_);
v___x_4086_ = lean_nat_dec_lt(v___y_4078_, v___x_4085_);
if (v___x_4086_ == 0)
{
v___y_4038_ = v___y_4080_;
v___y_4039_ = v___y_4081_;
v___y_4040_ = v___y_4082_;
v_fst_4041_ = v_val_4084_;
v_snd_4042_ = v___y_4083_;
goto v___jp_4037_;
}
else
{
lean_object* v___x_4087_; size_t v___x_4088_; size_t v___x_4089_; lean_object* v___x_4090_; 
v___x_4087_ = lean_box(0);
v___x_4088_ = ((size_t)0ULL);
v___x_4089_ = lean_usize_of_nat(v___x_4085_);
v___x_4090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_4079_, v___x_4088_, v___x_4089_, v___x_4087_, v_a_4015_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_dec_ref_known(v___x_4090_, 1);
v___y_4038_ = v___y_4080_;
v___y_4039_ = v___y_4081_;
v___y_4040_ = v___y_4082_;
v_fst_4041_ = v_val_4084_;
v_snd_4042_ = v___y_4083_;
goto v___jp_4037_;
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v_val_4084_);
lean_dec_ref(v___y_4083_);
lean_dec_ref(v___y_4081_);
lean_dec_ref(v_extraPaths_4036_);
lean_dec_ref(v_path_4035_);
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
v___jp_4099_:
{
if (lean_obj_tag(v_fst_4102_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4159_; 
v_a_4104_ = lean_ctor_get(v_fst_4102_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_fst_4102_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4106_ = v_fst_4102_;
v_isShared_4107_ = v_isSharedCheck_4159_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v_fst_4102_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4159_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
if (lean_obj_tag(v_a_4104_) == 11)
{
lean_object* v___x_4109_; 
lean_dec_ref_known(v_a_4104_, 2);
lean_dec_ref(v___y_4101_);
lean_dec_ref(v___y_4100_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set_tag(v___x_4106_, 1);
lean_ctor_set(v___x_4106_, 0, v_code_4011_);
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_code_4011_);
v___x_4109_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; 
v___x_4110_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer_spec__0(v_a_4015_, v_cfg_4008_, v_hOut_4009_, v_info_4010_, v___x_4109_, v_out_4012_, v_line_4013_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4128_; 
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; 
v_unused_4129_ = lean_ctor_get(v___x_4110_, 0);
lean_dec(v_unused_4129_);
v___x_4112_ = v___x_4110_;
v_isShared_4113_ = v_isSharedCheck_4128_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v___x_4110_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4128_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v_numSuccesses_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4127_; 
v_numSuccesses_4114_ = lean_ctor_get(v_snd_4103_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_snd_4103_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4116_ = v_snd_4103_;
v_isShared_4117_ = v_isSharedCheck_4127_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_numSuccesses_4114_);
lean_dec(v_snd_4103_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4127_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; uint8_t v___x_4119_; lean_object* v___x_4121_; 
v___x_4118_ = lean_box(0);
v___x_4119_ = 1;
if (v_isShared_4117_ == 0)
{
v___x_4121_ = v___x_4116_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_numSuccesses_4114_);
v___x_4121_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4122_; lean_object* v___x_4124_; 
lean_ctor_set_uint8(v___x_4121_, sizeof(void*)*1, v___x_4119_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4118_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v___x_4122_);
v___x_4124_ = v___x_4112_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v_snd_4103_);
v_a_4130_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4110_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4110_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v_numSuccesses_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4158_; 
lean_del_object(v___x_4106_);
lean_dec_ref(v_line_4013_);
lean_dec(v_code_4011_);
lean_dec_ref(v_info_4010_);
lean_dec_ref(v_cfg_4008_);
lean_inc_ref_n(v_a_4015_, 2);
v___x_4139_ = lean_apply_2(v_a_4015_, v___y_4100_, lean_box(0));
v___x_4140_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__1));
v___x_4141_ = lean_string_append(v___y_4101_, v___x_4140_);
v___x_4142_ = lean_io_error_to_string(v_a_4104_);
v___x_4143_ = lean_string_append(v___x_4141_, v___x_4142_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = 3;
v___x_4145_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set_uint8(v___x_4145_, sizeof(void*)*1, v___x_4144_);
v___x_4146_ = lean_apply_2(v_a_4015_, v___x_4145_, lean_box(0));
v_numSuccesses_4147_ = lean_ctor_get(v_snd_4103_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v_snd_4103_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4149_ = v_snd_4103_;
v_isShared_4150_ = v_isSharedCheck_4158_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_numSuccesses_4147_);
lean_dec(v_snd_4103_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4158_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; uint8_t v___x_4152_; lean_object* v___x_4154_; 
v___x_4151_ = lean_box(0);
v___x_4152_ = 1;
if (v_isShared_4150_ == 0)
{
v___x_4154_ = v___x_4149_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_numSuccesses_4147_);
v___x_4154_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_ctor_set_uint8(v___x_4154_, sizeof(void*)*1, v___x_4152_);
v___x_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4151_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
return v___x_4156_;
}
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4199_; 
lean_inc_ref(v_extraPaths_4036_);
lean_inc_ref(v_path_4035_);
lean_dec_ref(v_line_4013_);
lean_dec(v_code_4011_);
lean_dec_ref(v_info_4010_);
lean_dec_ref(v_cfg_4008_);
v_a_4160_ = lean_ctor_get(v_fst_4102_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_fst_4102_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4162_ = v_fst_4102_;
v_isShared_4163_ = v_isSharedCheck_4199_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v_fst_4102_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4199_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; uint64_t v___x_4165_; uint64_t v___x_4166_; uint64_t v___x_4167_; uint8_t v___x_4168_; 
lean_inc_ref(v_a_4015_);
v___x_4164_ = lean_apply_2(v_a_4015_, v___y_4100_, lean_box(0));
v___x_4165_ = l_Lake_Hash_nil;
v___x_4166_ = lean_byte_array_hash(v_a_4160_);
v___x_4167_ = lean_uint64_mix_hash(v___x_4165_, v___x_4166_);
v___x_4168_ = lean_uint64_dec_eq(v___x_4167_, v_hash_4034_);
if (v___x_4168_ == 0)
{
uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v_numSuccesses_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4187_; 
lean_del_object(v___x_4162_);
lean_dec(v_a_4160_);
lean_dec_ref(v_extraPaths_4036_);
lean_dec_ref(v_path_4035_);
v___x_4169_ = 1;
v___x_4170_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
v___x_4171_ = lean_string_append(v___y_4101_, v___x_4170_);
v___x_4172_ = l_Lake_lowerHexUInt64(v___x_4167_);
v___x_4173_ = lean_string_append(v___x_4171_, v___x_4172_);
lean_dec_ref(v___x_4172_);
v___x_4174_ = 3;
v___x_4175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set_uint8(v___x_4175_, sizeof(void*)*1, v___x_4174_);
lean_inc_ref(v_a_4015_);
v___x_4176_ = lean_apply_2(v_a_4015_, v___x_4175_, lean_box(0));
v_numSuccesses_4177_ = lean_ctor_get(v_snd_4103_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_snd_4103_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4179_ = v_snd_4103_;
v_isShared_4180_ = v_isSharedCheck_4187_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_numSuccesses_4177_);
lean_dec(v_snd_4103_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4187_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4181_ = lean_box(0);
if (v_isShared_4180_ == 0)
{
v___x_4183_ = v___x_4179_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_numSuccesses_4177_);
v___x_4183_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_ctor_set_uint8(v___x_4183_, sizeof(void*)*1, v___x_4169_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4181_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
}
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_4190_ = lean_io_rename(v___y_4101_, v_path_4035_);
lean_dec_ref(v___y_4101_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4190_, 1);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v_a_4191_);
v___x_4193_ = v___x_4162_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
v___y_4078_ = v___x_4188_;
v___y_4079_ = v___x_4189_;
v___y_4080_ = v___x_4168_;
v___y_4081_ = v_a_4160_;
v___y_4082_ = v___x_4167_;
v___y_4083_ = v_snd_4103_;
v_val_4084_ = v___x_4193_;
goto v___jp_4077_;
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; 
v_a_4195_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4190_, 1);
if (v_isShared_4163_ == 0)
{
lean_ctor_set_tag(v___x_4162_, 0);
lean_ctor_set(v___x_4162_, 0, v_a_4195_);
v___x_4197_ = v___x_4162_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
v___y_4078_ = v___x_4188_;
v___y_4079_ = v___x_4189_;
v___y_4080_ = v___x_4168_;
v___y_4081_ = v_a_4160_;
v___y_4082_ = v___x_4167_;
v___y_4083_ = v_snd_4103_;
v_val_4084_ = v___x_4197_;
goto v___jp_4077_;
}
}
}
}
}
}
v___jp_4200_:
{
lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4206_ = lean_array_get_size(v___y_4203_);
v___x_4207_ = lean_nat_dec_lt(v___y_4202_, v___x_4206_);
if (v___x_4207_ == 0)
{
v___y_4100_ = v___y_4201_;
v___y_4101_ = v___y_4204_;
v_fst_4102_ = v_val_4205_;
v_snd_4103_ = v_a_4014_;
goto v___jp_4099_;
}
else
{
lean_object* v___x_4208_; size_t v___x_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
v___x_4208_ = lean_box(0);
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = lean_usize_of_nat(v___x_4206_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_4203_, v___x_4209_, v___x_4210_, v___x_4208_, v_a_4015_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_dec_ref_known(v___x_4211_, 1);
v___y_4100_ = v___y_4201_;
v___y_4101_ = v___y_4204_;
v_fst_4102_ = v_val_4205_;
v_snd_4103_ = v_a_4014_;
goto v___jp_4099_;
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec_ref(v_val_4205_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v___y_4201_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_line_4013_);
lean_dec(v_code_4011_);
lean_dec_ref(v_info_4010_);
lean_dec_ref(v_cfg_4008_);
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4211_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4211_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
v___jp_4220_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v_didError_4235_; lean_object* v_numSuccesses_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4248_; 
v___x_4222_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__2));
v___x_4223_ = lean_string_append(v___y_4221_, v___x_4222_);
v___x_4224_ = l_Lake_lowerHexUInt64(v_hash_4034_);
v___x_4225_ = lean_string_append(v___x_4223_, v___x_4224_);
lean_dec_ref(v___x_4224_);
v___x_4226_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4227_ = lean_string_append(v___x_4225_, v___x_4226_);
v___x_4228_ = lean_string_append(v___x_4227_, v_path_4035_);
lean_dec_ref(v_path_4035_);
v___x_4229_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4230_ = lean_string_append(v___x_4228_, v___x_4229_);
v___x_4231_ = lean_string_append(v___x_4230_, v_url_4033_);
lean_dec_ref(v_url_4033_);
v___x_4232_ = 1;
v___x_4233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4233_, 0, v___x_4231_);
lean_ctor_set_uint8(v___x_4233_, sizeof(void*)*1, v___x_4232_);
lean_inc_ref(v_a_4015_);
v___x_4234_ = lean_apply_2(v_a_4015_, v___x_4233_, lean_box(0));
v_didError_4235_ = lean_ctor_get_uint8(v_a_4014_, sizeof(void*)*1);
v_numSuccesses_4236_ = lean_ctor_get(v_a_4014_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_a_4014_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4238_ = v_a_4014_;
v_isShared_4239_ = v_isSharedCheck_4248_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_numSuccesses_4236_);
lean_dec(v_a_4014_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4248_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4240_ = lean_box(0);
v___x_4241_ = lean_unsigned_to_nat(1u);
v___x_4242_ = lean_nat_add(v_numSuccesses_4236_, v___x_4241_);
lean_dec(v_numSuccesses_4236_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4242_);
v___x_4244_ = v___x_4238_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4242_);
lean_ctor_set_uint8(v_reuseFailAlloc_4247_, sizeof(void*)*1, v_didError_4235_);
v___x_4244_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4240_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
}
}
v___jp_4249_:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v_tmpPath_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4251_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___closed__3));
v___x_4252_ = lean_string_append(v___y_4250_, v___x_4251_);
v___x_4253_ = l_Lake_lowerHexUInt64(v_hash_4034_);
v___x_4254_ = lean_string_append(v___x_4252_, v___x_4253_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4256_ = lean_string_append(v___x_4254_, v___x_4255_);
v___x_4257_ = lean_string_append(v___x_4256_, v_path_4035_);
v___x_4258_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4259_ = lean_string_append(v___x_4257_, v___x_4258_);
v___x_4260_ = lean_string_append(v___x_4259_, v_url_4033_);
v___x_4261_ = 1;
v___x_4262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set_uint8(v___x_4262_, sizeof(void*)*1, v___x_4261_);
v___x_4263_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0));
lean_inc_ref(v_path_4035_);
v_tmpPath_4264_ = l_System_FilePath_addExtension(v_path_4035_, v___x_4263_);
v___x_4265_ = lean_unsigned_to_nat(0u);
v___x_4266_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_4267_ = l_IO_FS_readBinFile(v_tmpPath_4264_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4267_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4267_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
lean_ctor_set_tag(v___x_4270_, 1);
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
v___y_4201_ = v___x_4262_;
v___y_4202_ = v___x_4265_;
v___y_4203_ = v___x_4266_;
v___y_4204_ = v_tmpPath_4264_;
v_val_4205_ = v___x_4273_;
goto v___jp_4200_;
}
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
v_a_4276_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4267_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4267_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 0);
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
v___y_4201_ = v___x_4262_;
v___y_4202_ = v___x_4265_;
v___y_4203_ = v___x_4266_;
v___y_4204_ = v_tmpPath_4264_;
v_val_4205_ = v___x_4281_;
goto v___jp_4200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer___boxed(lean_object* v_cfg_4289_, lean_object* v_hOut_4290_, lean_object* v_info_4291_, lean_object* v_code_4292_, lean_object* v_out_4293_, lean_object* v_line_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer(v_cfg_4289_, v_hOut_4290_, v_info_4291_, v_code_4292_, v_out_4293_, v_line_4294_, v_a_4295_, v_a_4296_);
lean_dec_ref(v_a_4296_);
lean_dec(v_out_4293_);
lean_dec(v_hOut_4290_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object* v_cfg_4302_, lean_object* v_hOut_4303_, lean_object* v_val_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, uint8_t v___x_4307_, lean_object* v_00___4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_code_x3f_4313_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4342_ = l_Lake_JsonObject_getJson_x3f(v_a_4305_, v___x_4341_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v___x_4343_; 
v___x_4343_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__1));
v_code_x3f_4313_ = v___x_4343_;
goto v___jp_4312_;
}
else
{
lean_object* v_val_4344_; lean_object* v___x_4345_; 
v_val_4344_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_val_4344_);
lean_dec_ref_known(v___x_4342_, 1);
v___x_4345_ = l_Lean_Json_getNat_x3f(v_val_4344_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4355_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4348_ = v___x_4345_;
v_isShared_4349_ = v_isSharedCheck_4355_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4345_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4355_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4350_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4351_ = lean_string_append(v___x_4350_, v_a_4346_);
lean_dec(v_a_4346_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 0, v___x_4351_);
v___x_4353_ = v___x_4348_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
v_code_x3f_4313_ = v___x_4353_;
goto v___jp_4312_;
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_a_4356_ = lean_ctor_get(v___x_4345_, 0);
v___x_4357_ = lean_unsigned_to_nat(200u);
v___x_4358_ = lean_nat_dec_eq(v_a_4356_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4359_ = lean_unsigned_to_nat(201u);
v___x_4360_ = lean_nat_dec_eq(v_a_4356_, v___x_4359_);
if (v___x_4360_ == 0)
{
v_code_x3f_4313_ = v___x_4345_;
goto v___jp_4312_;
}
else
{
lean_object* v___x_4361_; 
lean_dec_ref_known(v___x_4345_, 1);
v___x_4361_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer(v_cfg_4302_, v_hOut_4303_, v_val_4304_, v___x_4359_, v_a_4305_, v_a_4306_, v___y_4309_, v___y_4310_);
return v___x_4361_;
}
}
else
{
lean_object* v___x_4362_; 
lean_dec_ref_known(v___x_4345_, 1);
v___x_4362_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleTransfer(v_cfg_4302_, v_hOut_4303_, v_val_4304_, v___x_4357_, v_a_4305_, v_a_4306_, v___y_4309_, v___y_4310_);
return v___x_4362_;
}
}
}
v___jp_4312_:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_4302_, v_hOut_4303_, v_val_4304_, v_code_x3f_4313_, v_a_4305_, v_a_4306_, v___y_4310_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4331_; 
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4331_ == 0)
{
lean_object* v_unused_4332_; 
v_unused_4332_ = lean_ctor_get(v___x_4314_, 0);
lean_dec(v_unused_4332_);
v___x_4316_ = v___x_4314_;
v_isShared_4317_ = v_isSharedCheck_4331_;
goto v_resetjp_4315_;
}
else
{
lean_dec(v___x_4314_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4331_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_numSuccesses_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4330_; 
v_numSuccesses_4318_ = lean_ctor_get(v___y_4309_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___y_4309_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4320_ = v___y_4309_;
v_isShared_4321_ = v_isSharedCheck_4330_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_numSuccesses_4318_);
lean_dec(v___y_4309_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4330_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4322_; lean_object* v___x_4324_; 
v___x_4322_ = lean_box(0);
if (v_isShared_4321_ == 0)
{
v___x_4324_ = v___x_4320_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_numSuccesses_4318_);
v___x_4324_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; lean_object* v___x_4327_; 
lean_ctor_set_uint8(v___x_4324_, sizeof(void*)*1, v___x_4307_);
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4322_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___x_4325_);
v___x_4327_ = v___x_4316_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4325_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v___y_4309_);
v_a_4333_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4314_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4314_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object* v_cfg_4363_, lean_object* v_hOut_4364_, lean_object* v_val_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v___x_4368_, lean_object* v_00___4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
uint8_t v___x_12677__boxed_4373_; lean_object* v_res_4374_; 
v___x_12677__boxed_4373_ = lean_unbox(v___x_4368_);
v_res_4374_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4363_, v_hOut_4364_, v_val_4365_, v_a_4366_, v_a_4367_, v___x_12677__boxed_4373_, v_00___4369_, v___y_4370_, v___y_4371_);
lean_dec_ref(v___y_4371_);
lean_dec(v_a_4366_);
lean_dec(v_hOut_4364_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object* v_cfg_4375_, lean_object* v_hOut_4376_, lean_object* v_val_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, uint8_t v___x_4380_, lean_object* v_x_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___y_4386_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4415_ = l_Lake_JsonObject_getJson_x3f(v_a_4378_, v___x_4414_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v___x_4416_; 
v___x_4416_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___closed__1));
v___y_4386_ = v___x_4416_;
goto v___jp_4385_;
}
else
{
lean_object* v_val_4417_; lean_object* v___x_4418_; 
v_val_4417_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_val_4417_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4418_ = l_Lean_Json_getNat_x3f(v_val_4417_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4428_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4428_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4428_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4423_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4424_ = lean_string_append(v___x_4423_, v_a_4419_);
lean_dec(v_a_4419_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4424_);
v___x_4426_ = v___x_4421_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
v___y_4386_ = v___x_4426_;
goto v___jp_4385_;
}
}
}
else
{
v___y_4386_ = v___x_4418_;
goto v___jp_4385_;
}
}
v___jp_4385_:
{
lean_object* v___x_4387_; 
v___x_4387_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_4375_, v_hOut_4376_, v_val_4377_, v___y_4386_, v_a_4378_, v_a_4379_, v___y_4383_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4404_; 
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v___x_4387_, 0);
lean_dec(v_unused_4405_);
v___x_4389_ = v___x_4387_;
v_isShared_4390_ = v_isSharedCheck_4404_;
goto v_resetjp_4388_;
}
else
{
lean_dec(v___x_4387_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4404_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v_numSuccesses_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4403_; 
v_numSuccesses_4391_ = lean_ctor_get(v___y_4382_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___y_4382_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4393_ = v___y_4382_;
v_isShared_4394_ = v_isSharedCheck_4403_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_numSuccesses_4391_);
lean_dec(v___y_4382_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4403_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4395_ = lean_box(0);
if (v_isShared_4394_ == 0)
{
v___x_4397_ = v___x_4393_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_numSuccesses_4391_);
v___x_4397_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
lean_ctor_set_uint8(v___x_4397_, sizeof(void*)*1, v___x_4380_);
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4395_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 0, v___x_4398_);
v___x_4400_ = v___x_4389_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec_ref(v___y_4382_);
v_a_4406_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4387_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4387_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object* v_cfg_4429_, lean_object* v_hOut_4430_, lean_object* v_val_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v___x_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
uint8_t v___x_12804__boxed_4439_; lean_object* v_res_4440_; 
v___x_12804__boxed_4439_ = lean_unbox(v___x_4434_);
v_res_4440_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4429_, v_hOut_4430_, v_val_4431_, v_a_4432_, v_a_4433_, v___x_12804__boxed_4439_, v_x_4435_, v___y_4436_, v___y_4437_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_x_4435_);
lean_dec(v_a_4432_);
lean_dec(v_hOut_4430_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object* v_a_4446_, lean_object* v_cfg_4447_, lean_object* v_h_4448_, lean_object* v_hOut_4449_, lean_object* v_s_4450_){
_start:
{
lean_object* v___y_4453_; lean_object* v___x_4465_; 
v___x_4465_ = lean_io_prim_handle_get_line(v_h_4448_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4557_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4468_ = v___x_4465_;
v_isShared_4469_ = v_isSharedCheck_4557_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4465_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4557_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___y_4471_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v_startInclusive_4478_; lean_object* v_endExclusive_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4474_ = lean_unsigned_to_nat(0u);
v___x_4475_ = lean_string_utf8_byte_size(v_a_4466_);
lean_inc(v_a_4466_);
v___x_4476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4476_, 0, v_a_4466_);
lean_ctor_set(v___x_4476_, 1, v___x_4474_);
lean_ctor_set(v___x_4476_, 2, v___x_4475_);
v___x_4477_ = l_String_Slice_trimAscii(v___x_4476_);
v_startInclusive_4478_ = lean_ctor_get(v___x_4477_, 1);
v_endExclusive_4479_ = lean_ctor_get(v___x_4477_, 2);
v___x_4480_ = lean_nat_sub(v_endExclusive_4479_, v_startInclusive_4478_);
v___x_4481_ = lean_nat_dec_eq(v___x_4480_, v___x_4474_);
lean_dec(v___x_4480_);
if (v___x_4481_ == 0)
{
uint8_t v___x_4482_; lean_object* v___y_4484_; lean_object* v_a_4502_; lean_object* v___x_4521_; 
lean_del_object(v___x_4468_);
v___x_4482_ = 1;
lean_inc(v_a_4466_);
v___x_4521_ = l_Lean_Json_parse(v_a_4466_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; 
lean_dec(v_a_4466_);
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v_a_4502_ = v_a_4522_;
goto v___jp_4501_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4524_; 
v_a_4523_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4521_, 1);
v___x_4524_ = l_Lean_Json_getObj_x3f(v_a_4523_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; 
lean_dec(v_a_4466_);
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref_known(v___x_4524_, 1);
v_a_4502_ = v_a_4525_;
goto v___jp_4501_;
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4527_; 
v_a_4526_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4524_, 1);
v___x_4527_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4447_, v_a_4526_);
if (lean_obj_tag(v___x_4527_) == 1)
{
lean_object* v_val_4528_; lean_object* v___x_4529_; lean_object* v___f_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_dec_ref(v___x_4477_);
v_val_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc_n(v_val_4528_, 2);
lean_dec_ref_known(v___x_4527_, 1);
v___x_4529_ = lean_box(v___x_4482_);
lean_inc(v_a_4466_);
lean_inc(v_a_4526_);
lean_inc(v_hOut_4449_);
lean_inc_ref(v_cfg_4447_);
v___f_4530_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed), 10, 6);
lean_closure_set(v___f_4530_, 0, v_cfg_4447_);
lean_closure_set(v___f_4530_, 1, v_hOut_4449_);
lean_closure_set(v___f_4530_, 2, v_val_4528_);
lean_closure_set(v___f_4530_, 3, v_a_4526_);
lean_closure_set(v___f_4530_, 4, v_a_4466_);
lean_closure_set(v___f_4530_, 5, v___x_4529_);
v___x_4531_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3));
v___x_4532_ = l_Lake_JsonObject_getJson_x3f(v_a_4526_, v___x_4531_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_dec(v_val_4528_);
lean_dec(v_a_4526_);
lean_dec(v_a_4466_);
v___y_4471_ = v___f_4530_;
goto v___jp_4470_;
}
else
{
lean_object* v_val_4533_; lean_object* v___x_4534_; 
v_val_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_val_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___x_4534_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_4533_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v___f_4530_);
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4537_ = v___x_4534_;
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4534_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4542_; 
v___x_4539_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___x_4540_ = lean_string_append(v___x_4539_, v_a_4535_);
lean_dec(v_a_4535_);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v___x_4540_);
v___x_4542_ = v___x_4537_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; 
lean_inc_ref(v_cfg_4447_);
v___x_4543_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4447_, v_hOut_4449_, v_val_4528_, v_a_4526_, v_a_4466_, v___x_4482_, v___x_4542_, v_s_4450_, v_a_4446_);
lean_dec_ref(v___x_4542_);
lean_dec(v_a_4526_);
v___y_4453_ = v___x_4543_;
goto v___jp_4452_;
}
}
}
else
{
lean_object* v_a_4546_; 
v_a_4546_ = lean_ctor_get(v___x_4534_, 0);
if (lean_obj_tag(v_a_4546_) == 0)
{
lean_dec_ref_known(v___x_4534_, 1);
lean_dec(v_val_4528_);
lean_dec(v_a_4526_);
lean_dec(v_a_4466_);
v___y_4471_ = v___f_4530_;
goto v___jp_4470_;
}
else
{
lean_object* v_val_4547_; uint8_t v___x_4548_; 
lean_dec_ref(v___f_4530_);
v_val_4547_ = lean_ctor_get(v_a_4546_, 0);
v___x_4548_ = lean_nat_dec_eq(v_val_4547_, v___x_4474_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
lean_inc_ref(v_cfg_4447_);
v___x_4549_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4447_, v_hOut_4449_, v_val_4528_, v_a_4526_, v_a_4466_, v___x_4482_, v___x_4534_, v_s_4450_, v_a_4446_);
lean_dec_ref_known(v___x_4534_, 1);
lean_dec(v_a_4526_);
v___y_4453_ = v___x_4549_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
lean_dec_ref_known(v___x_4534_, 1);
v___x_4550_ = lean_box(0);
lean_inc_ref(v_cfg_4447_);
v___x_4551_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4447_, v_hOut_4449_, v_val_4528_, v_a_4526_, v_a_4466_, v___x_4482_, v___x_4550_, v_s_4450_, v_a_4446_);
lean_dec(v_a_4526_);
v___y_4453_ = v___x_4551_;
goto v___jp_4452_;
}
}
}
}
}
else
{
lean_object* v_scope_4552_; lean_object* v_s_4553_; 
lean_dec(v___x_4527_);
lean_dec(v_a_4526_);
lean_dec(v_a_4466_);
v_scope_4552_ = lean_ctor_get(v_cfg_4447_, 0);
v_s_4553_ = lean_ctor_get(v_scope_4552_, 0);
lean_inc_ref(v_s_4553_);
v___y_4484_ = v_s_4553_;
goto v___jp_4483_;
}
}
}
v___jp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v_numSuccesses_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4500_; 
v___x_4485_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4486_ = lean_string_append(v___y_4484_, v___x_4485_);
v___x_4487_ = l_String_Slice_toString(v___x_4477_);
lean_dec_ref(v___x_4477_);
v___x_4488_ = lean_string_append(v___x_4486_, v___x_4487_);
lean_dec_ref(v___x_4487_);
v___x_4489_ = 3;
v___x_4490_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4490_, 0, v___x_4488_);
lean_ctor_set_uint8(v___x_4490_, sizeof(void*)*1, v___x_4489_);
lean_inc_ref(v_a_4446_);
v___x_4491_ = lean_apply_2(v_a_4446_, v___x_4490_, lean_box(0));
v_numSuccesses_4492_ = lean_ctor_get(v_s_4450_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_s_4450_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4494_ = v_s_4450_;
v_isShared_4495_ = v_isSharedCheck_4500_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_numSuccesses_4492_);
lean_dec(v_s_4450_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4500_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_numSuccesses_4492_);
v___x_4497_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_ctor_set_uint8(v___x_4497_, sizeof(void*)*1, v___x_4482_);
v_s_4450_ = v___x_4497_;
goto _start;
}
}
}
v___jp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v_numSuccesses_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4520_; 
v___x_4503_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4504_ = lean_string_append(v___x_4503_, v_a_4502_);
lean_dec_ref(v_a_4502_);
v___x_4505_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4506_ = lean_string_append(v___x_4504_, v___x_4505_);
v___x_4507_ = l_String_Slice_toString(v___x_4477_);
lean_dec_ref(v___x_4477_);
v___x_4508_ = lean_string_append(v___x_4506_, v___x_4507_);
lean_dec_ref(v___x_4507_);
v___x_4509_ = 3;
v___x_4510_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*1, v___x_4509_);
lean_inc_ref(v_a_4446_);
v___x_4511_ = lean_apply_2(v_a_4446_, v___x_4510_, lean_box(0));
v_numSuccesses_4512_ = lean_ctor_get(v_s_4450_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_s_4450_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4514_ = v_s_4450_;
v_isShared_4515_ = v_isSharedCheck_4520_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_numSuccesses_4512_);
lean_dec(v_s_4450_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4520_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_numSuccesses_4512_);
v___x_4517_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*1, v___x_4482_);
v_s_4450_ = v___x_4517_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4555_; 
lean_dec_ref(v___x_4477_);
lean_dec(v_a_4466_);
lean_dec(v_hOut_4449_);
lean_dec_ref(v_cfg_4447_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 0, v_s_4450_);
v___x_4555_ = v___x_4468_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_s_4450_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
v___jp_4470_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4472_ = lean_box(0);
lean_inc_ref(v_a_4446_);
v___x_4473_ = lean_apply_4(v___y_4471_, v___x_4472_, v_s_4450_, v_a_4446_, lean_box(0));
v___y_4453_ = v___x_4473_;
goto v___jp_4452_;
}
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4570_; 
lean_dec_ref(v_s_4450_);
lean_dec(v_hOut_4449_);
lean_dec_ref(v_cfg_4447_);
v_a_4558_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4560_ = v___x_4465_;
v_isShared_4561_ = v_isSharedCheck_4570_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4465_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4570_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4562_; uint8_t v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4562_ = lean_io_error_to_string(v_a_4558_);
v___x_4563_ = 3;
v___x_4564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4564_, 0, v___x_4562_);
lean_ctor_set_uint8(v___x_4564_, sizeof(void*)*1, v___x_4563_);
lean_inc_ref(v_a_4446_);
v___x_4565_ = lean_apply_2(v_a_4446_, v___x_4564_, lean_box(0));
v___x_4566_ = lean_box(0);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4566_);
v___x_4568_ = v___x_4560_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
v___jp_4452_:
{
if (lean_obj_tag(v___y_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v_snd_4455_; 
v_a_4454_ = lean_ctor_get(v___y_4453_, 0);
lean_inc(v_a_4454_);
lean_dec_ref_known(v___y_4453_, 1);
v_snd_4455_ = lean_ctor_get(v_a_4454_, 1);
lean_inc(v_snd_4455_);
lean_dec(v_a_4454_);
v_s_4450_ = v_snd_4455_;
goto _start;
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v_hOut_4449_);
lean_dec_ref(v_cfg_4447_);
v_a_4457_ = lean_ctor_get(v___y_4453_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___y_4453_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___y_4453_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___y_4453_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object* v_a_4571_, lean_object* v_cfg_4572_, lean_object* v_h_4573_, lean_object* v_hOut_4574_, lean_object* v_s_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4571_, v_cfg_4572_, v_h_4573_, v_hOut_4574_, v_s_4575_);
lean_dec(v_h_4573_);
lean_dec_ref(v_a_4571_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object* v_cfg_4578_, lean_object* v_h_4579_, lean_object* v_hOut_4580_, lean_object* v_s_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v___y_4585_; lean_object* v___x_4597_; 
v___x_4597_ = lean_io_prim_handle_get_line(v_h_4579_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4686_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4686_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4686_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v_startInclusive_4606_; lean_object* v_endExclusive_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = lean_string_utf8_byte_size(v_a_4598_);
lean_inc(v_a_4598_);
v___x_4604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4604_, 0, v_a_4598_);
lean_ctor_set(v___x_4604_, 1, v___x_4602_);
lean_ctor_set(v___x_4604_, 2, v___x_4603_);
v___x_4605_ = l_String_Slice_trimAscii(v___x_4604_);
v_startInclusive_4606_ = lean_ctor_get(v___x_4605_, 1);
v_endExclusive_4607_ = lean_ctor_get(v___x_4605_, 2);
v___x_4608_ = lean_nat_sub(v_endExclusive_4607_, v_startInclusive_4606_);
v___x_4609_ = lean_nat_dec_eq(v___x_4608_, v___x_4602_);
lean_dec(v___x_4608_);
if (v___x_4609_ == 0)
{
uint8_t v___x_4610_; lean_object* v___y_4612_; lean_object* v_a_4630_; lean_object* v___x_4649_; 
lean_del_object(v___x_4600_);
v___x_4610_ = 1;
lean_inc(v_a_4598_);
v___x_4649_ = l_Lean_Json_parse(v_a_4598_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; 
lean_dec(v_a_4598_);
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4650_);
lean_dec_ref_known(v___x_4649_, 1);
v_a_4630_ = v_a_4650_;
goto v___jp_4629_;
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4652_; 
v_a_4651_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4649_, 1);
v___x_4652_ = l_Lean_Json_getObj_x3f(v_a_4651_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; 
lean_dec(v_a_4598_);
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref_known(v___x_4652_, 1);
v_a_4630_ = v_a_4653_;
goto v___jp_4629_;
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4655_; 
v_a_4654_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v___x_4652_, 1);
v___x_4655_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4578_, v_a_4654_);
if (lean_obj_tag(v___x_4655_) == 1)
{
lean_object* v_val_4656_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
lean_dec_ref(v___x_4605_);
v_val_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_val_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v___x_4660_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3));
v___x_4661_ = l_Lake_JsonObject_getJson_x3f(v_a_4654_, v___x_4660_);
if (lean_obj_tag(v___x_4661_) == 0)
{
goto v___jp_4657_;
}
else
{
lean_object* v_val_4662_; lean_object* v___x_4663_; 
v_val_4662_ = lean_ctor_get(v___x_4661_, 0);
lean_inc(v_val_4662_);
lean_dec_ref_known(v___x_4661_, 1);
v___x_4663_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_4662_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4674_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4674_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4674_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4668_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___x_4669_ = lean_string_append(v___x_4668_, v_a_4664_);
lean_dec(v_a_4664_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v___x_4669_);
v___x_4671_ = v___x_4666_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4672_; 
lean_inc_ref(v_cfg_4578_);
v___x_4672_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4578_, v_hOut_4580_, v_val_4656_, v_a_4654_, v_a_4598_, v___x_4610_, v___x_4671_, v_s_4581_, v_a_4582_);
lean_dec_ref(v___x_4671_);
lean_dec(v_a_4654_);
v___y_4585_ = v___x_4672_;
goto v___jp_4584_;
}
}
}
else
{
lean_object* v_a_4675_; 
v_a_4675_ = lean_ctor_get(v___x_4663_, 0);
if (lean_obj_tag(v_a_4675_) == 0)
{
lean_dec_ref_known(v___x_4663_, 1);
goto v___jp_4657_;
}
else
{
lean_object* v_val_4676_; uint8_t v___x_4677_; 
v_val_4676_ = lean_ctor_get(v_a_4675_, 0);
v___x_4677_ = lean_nat_dec_eq(v_val_4676_, v___x_4602_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4678_; 
lean_inc_ref(v_cfg_4578_);
v___x_4678_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4578_, v_hOut_4580_, v_val_4656_, v_a_4654_, v_a_4598_, v___x_4610_, v___x_4663_, v_s_4581_, v_a_4582_);
lean_dec_ref_known(v___x_4663_, 1);
lean_dec(v_a_4654_);
v___y_4585_ = v___x_4678_;
goto v___jp_4584_;
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
lean_dec_ref_known(v___x_4663_, 1);
v___x_4679_ = lean_box(0);
lean_inc_ref(v_cfg_4578_);
v___x_4680_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4578_, v_hOut_4580_, v_val_4656_, v_a_4654_, v_a_4598_, v___x_4610_, v___x_4679_, v_s_4581_, v_a_4582_);
lean_dec(v_a_4654_);
v___y_4585_ = v___x_4680_;
goto v___jp_4584_;
}
}
}
}
v___jp_4657_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = lean_box(0);
lean_inc_ref(v_cfg_4578_);
v___x_4659_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4578_, v_hOut_4580_, v_val_4656_, v_a_4654_, v_a_4598_, v___x_4610_, v___x_4658_, v_s_4581_, v_a_4582_);
lean_dec(v_a_4654_);
v___y_4585_ = v___x_4659_;
goto v___jp_4584_;
}
}
else
{
lean_object* v_scope_4681_; lean_object* v_s_4682_; 
lean_dec(v___x_4655_);
lean_dec(v_a_4654_);
lean_dec(v_a_4598_);
v_scope_4681_ = lean_ctor_get(v_cfg_4578_, 0);
v_s_4682_ = lean_ctor_get(v_scope_4681_, 0);
lean_inc_ref(v_s_4682_);
v___y_4612_ = v_s_4682_;
goto v___jp_4611_;
}
}
}
v___jp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v_numSuccesses_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4628_; 
v___x_4613_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4614_ = lean_string_append(v___y_4612_, v___x_4613_);
v___x_4615_ = l_String_Slice_toString(v___x_4605_);
lean_dec_ref(v___x_4605_);
v___x_4616_ = lean_string_append(v___x_4614_, v___x_4615_);
lean_dec_ref(v___x_4615_);
v___x_4617_ = 3;
v___x_4618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4618_, 0, v___x_4616_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*1, v___x_4617_);
lean_inc_ref(v_a_4582_);
v___x_4619_ = lean_apply_2(v_a_4582_, v___x_4618_, lean_box(0));
v_numSuccesses_4620_ = lean_ctor_get(v_s_4581_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_s_4581_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4622_ = v_s_4581_;
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_numSuccesses_4620_);
lean_dec(v_s_4581_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_numSuccesses_4620_);
v___x_4625_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; 
lean_ctor_set_uint8(v___x_4625_, sizeof(void*)*1, v___x_4610_);
v___x_4626_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4582_, v_cfg_4578_, v_h_4579_, v_hOut_4580_, v___x_4625_);
return v___x_4626_;
}
}
}
v___jp_4629_:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v_numSuccesses_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4648_; 
v___x_4631_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4632_ = lean_string_append(v___x_4631_, v_a_4630_);
lean_dec_ref(v_a_4630_);
v___x_4633_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4634_ = lean_string_append(v___x_4632_, v___x_4633_);
v___x_4635_ = l_String_Slice_toString(v___x_4605_);
lean_dec_ref(v___x_4605_);
v___x_4636_ = lean_string_append(v___x_4634_, v___x_4635_);
lean_dec_ref(v___x_4635_);
v___x_4637_ = 3;
v___x_4638_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4638_, 0, v___x_4636_);
lean_ctor_set_uint8(v___x_4638_, sizeof(void*)*1, v___x_4637_);
lean_inc_ref(v_a_4582_);
v___x_4639_ = lean_apply_2(v_a_4582_, v___x_4638_, lean_box(0));
v_numSuccesses_4640_ = lean_ctor_get(v_s_4581_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v_s_4581_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4642_ = v_s_4581_;
v_isShared_4643_ = v_isSharedCheck_4648_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_numSuccesses_4640_);
lean_dec(v_s_4581_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4648_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_numSuccesses_4640_);
v___x_4645_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
lean_object* v___x_4646_; 
lean_ctor_set_uint8(v___x_4645_, sizeof(void*)*1, v___x_4610_);
v___x_4646_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4582_, v_cfg_4578_, v_h_4579_, v_hOut_4580_, v___x_4645_);
return v___x_4646_;
}
}
}
}
else
{
lean_object* v___x_4684_; 
lean_dec_ref(v___x_4605_);
lean_dec(v_a_4598_);
lean_dec(v_hOut_4580_);
lean_dec_ref(v_cfg_4578_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v_s_4581_);
v___x_4684_ = v___x_4600_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_s_4581_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4699_; 
lean_dec_ref(v_s_4581_);
lean_dec(v_hOut_4580_);
lean_dec_ref(v_cfg_4578_);
v_a_4687_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4689_ = v___x_4597_;
v_isShared_4690_ = v_isSharedCheck_4699_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4597_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4699_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
v___x_4691_ = lean_io_error_to_string(v_a_4687_);
v___x_4692_ = 3;
v___x_4693_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4693_, 0, v___x_4691_);
lean_ctor_set_uint8(v___x_4693_, sizeof(void*)*1, v___x_4692_);
lean_inc_ref(v_a_4582_);
v___x_4694_ = lean_apply_2(v_a_4582_, v___x_4693_, lean_box(0));
v___x_4695_ = lean_box(0);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v___x_4695_);
v___x_4697_ = v___x_4689_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
v___jp_4584_:
{
if (lean_obj_tag(v___y_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v_snd_4587_; lean_object* v___x_4588_; 
v_a_4586_ = lean_ctor_get(v___y_4585_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___y_4585_, 1);
v_snd_4587_ = lean_ctor_get(v_a_4586_, 1);
lean_inc(v_snd_4587_);
lean_dec(v_a_4586_);
v___x_4588_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4582_, v_cfg_4578_, v_h_4579_, v_hOut_4580_, v_snd_4587_);
return v___x_4588_;
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec(v_hOut_4580_);
lean_dec_ref(v_cfg_4578_);
v_a_4589_ = lean_ctor_get(v___y_4585_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___y_4585_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___y_4585_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___y_4585_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object* v_cfg_4700_, lean_object* v_h_4701_, lean_object* v_hOut_4702_, lean_object* v_s_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4700_, v_h_4701_, v_hOut_4702_, v_s_4703_, v_a_4704_);
lean_dec_ref(v_a_4704_);
lean_dec(v_h_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object* v_snd_4707_, lean_object* v___y_4708_, lean_object* v_a_x3f_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = lean_io_remove_file(v_snd_4707_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4711_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4732_; 
v_a_4720_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4722_ = v___x_4711_;
v_isShared_4723_ = v_isSharedCheck_4732_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4711_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4732_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4724_; uint8_t v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
v___x_4724_ = lean_io_error_to_string(v_a_4720_);
v___x_4725_ = 3;
v___x_4726_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4726_, 0, v___x_4724_);
lean_ctor_set_uint8(v___x_4726_, sizeof(void*)*1, v___x_4725_);
lean_inc_ref(v___y_4708_);
v___x_4727_ = lean_apply_2(v___y_4708_, v___x_4726_, lean_box(0));
v___x_4728_ = lean_box(0);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 0, v___x_4728_);
v___x_4730_ = v___x_4722_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object* v_snd_4733_, lean_object* v___y_4734_, lean_object* v_a_x3f_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4733_, v___y_4734_, v_a_x3f_4735_);
lean_dec(v_a_x3f_4735_);
lean_dec_ref(v___y_4734_);
lean_dec_ref(v_snd_4733_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object* v_f_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v_fst_4743_; lean_object* v_snd_4744_; lean_object* v_r_4745_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref_known(v___x_4741_, 1);
v_fst_4743_ = lean_ctor_get(v_a_4742_, 0);
lean_inc(v_fst_4743_);
v_snd_4744_ = lean_ctor_get(v_a_4742_, 1);
lean_inc_n(v_snd_4744_, 2);
lean_dec(v_a_4742_);
lean_inc_ref(v___y_4739_);
v_r_4745_ = lean_apply_4(v_f_4738_, v_fst_4743_, v_snd_4744_, v___y_4739_, lean_box(0));
if (lean_obj_tag(v_r_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4770_; 
v_a_4746_ = lean_ctor_get(v_r_4745_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_r_4745_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4748_ = v_r_4745_;
v_isShared_4749_ = v_isSharedCheck_4770_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v_r_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4770_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
lean_inc(v_a_4746_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set_tag(v___x_4748_, 1);
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4744_, v___y_4739_, v___x_4751_);
lean_dec_ref(v___x_4751_);
lean_dec(v_snd_4744_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v___x_4752_, 0);
lean_dec(v_unused_4760_);
v___x_4754_ = v___x_4752_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_dec(v___x_4752_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v_a_4746_);
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4746_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec(v_a_4746_);
v_a_4761_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4752_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4752_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v_a_4771_ = lean_ctor_get(v_r_4745_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v_r_4745_, 1);
v___x_4772_ = lean_box(0);
v___x_4773_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4744_, v___y_4739_, v___x_4772_);
lean_dec(v_snd_4744_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4780_ == 0)
{
lean_object* v_unused_4781_; 
v_unused_4781_ = lean_ctor_get(v___x_4773_, 0);
lean_dec(v_unused_4781_);
v___x_4775_ = v___x_4773_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_dec(v___x_4773_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
lean_ctor_set_tag(v___x_4775_, 1);
lean_ctor_set(v___x_4775_, 0, v_a_4771_);
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4771_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4771_);
v_a_4782_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4773_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4773_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v_f_4738_);
v_a_4790_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4792_ = v___x_4741_;
v_isShared_4793_ = v_isSharedCheck_4802_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4741_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4802_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4794_ = lean_io_error_to_string(v_a_4790_);
v___x_4795_ = 3;
v___x_4796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set_uint8(v___x_4796_, sizeof(void*)*1, v___x_4795_);
lean_inc_ref(v___y_4739_);
v___x_4797_ = lean_apply_2(v___y_4739_, v___x_4796_, lean_box(0));
v___x_4798_ = lean_box(0);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4798_);
v___x_4800_ = v___x_4792_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object* v_f_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4803_, v___y_4804_);
lean_dec_ref(v___y_4804_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object* v_00_u03b1_4807_, lean_object* v_f_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v___x_4811_; 
v___x_4811_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4808_, v___y_4809_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object* v_00_u03b1_4812_, lean_object* v_f_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(v_00_u03b1_4812_, v_f_4813_, v___y_4814_);
lean_dec_ref(v___y_4814_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object* v_h_4819_, lean_object* v_as_4820_, size_t v_i_4821_, size_t v_stop_4822_, lean_object* v_b_4823_, lean_object* v___y_4824_){
_start:
{
uint8_t v___x_4826_; 
v___x_4826_ = lean_usize_dec_eq(v_i_4821_, v_stop_4822_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; lean_object* v_url_4828_; lean_object* v_path_4829_; lean_object* v___x_4830_; lean_object* v_tmpPath_4831_; lean_object* v___x_4832_; 
v___x_4827_ = lean_array_uget_borrowed(v_as_4820_, v_i_4821_);
v_url_4828_ = lean_ctor_get(v___x_4827_, 0);
v_path_4829_ = lean_ctor_get(v___x_4827_, 1);
v___x_4830_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_tmpPath___closed__0));
lean_inc_ref(v_path_4829_);
v_tmpPath_4831_ = l_System_FilePath_addExtension(v_path_4829_, v___x_4830_);
v___x_4832_ = l_Lake_removeFileIfExists(v_tmpPath_4831_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
lean_dec_ref_known(v___x_4832_, 1);
v___x_4833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4828_);
v___x_4834_ = l_String_quote(v_url_4828_);
v___x_4835_ = lean_string_append(v___x_4833_, v___x_4834_);
lean_dec_ref(v___x_4834_);
v___x_4836_ = l_IO_FS_Handle_putStrLn(v_h_4819_, v___x_4835_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
lean_dec_ref_known(v___x_4836_, 1);
v___x_4837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1));
v___x_4838_ = l_String_quote(v_tmpPath_4831_);
v___x_4839_ = lean_string_append(v___x_4837_, v___x_4838_);
lean_dec_ref(v___x_4838_);
v___x_4840_ = l_IO_FS_Handle_putStrLn(v_h_4819_, v___x_4839_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; size_t v___x_4842_; size_t v___x_4843_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v___x_4840_, 1);
v___x_4842_ = ((size_t)1ULL);
v___x_4843_ = lean_usize_add(v_i_4821_, v___x_4842_);
v_i_4821_ = v___x_4843_;
v_b_4823_ = v_a_4841_;
goto _start;
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4857_; 
v_a_4845_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4847_ = v___x_4840_;
v_isShared_4848_ = v_isSharedCheck_4857_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4840_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4857_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4849_; uint8_t v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4849_ = lean_io_error_to_string(v_a_4845_);
v___x_4850_ = 3;
v___x_4851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4851_, 0, v___x_4849_);
lean_ctor_set_uint8(v___x_4851_, sizeof(void*)*1, v___x_4850_);
lean_inc_ref(v___y_4824_);
v___x_4852_ = lean_apply_2(v___y_4824_, v___x_4851_, lean_box(0));
v___x_4853_ = lean_box(0);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4853_);
v___x_4855_ = v___x_4847_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v_tmpPath_4831_);
v_a_4858_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4860_ = v___x_4836_;
v_isShared_4861_ = v_isSharedCheck_4870_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4836_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4870_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4862_ = lean_io_error_to_string(v_a_4858_);
v___x_4863_ = 3;
v___x_4864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set_uint8(v___x_4864_, sizeof(void*)*1, v___x_4863_);
lean_inc_ref(v___y_4824_);
v___x_4865_ = lean_apply_2(v___y_4824_, v___x_4864_, lean_box(0));
v___x_4866_ = lean_box(0);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 0, v___x_4866_);
v___x_4868_ = v___x_4860_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4866_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4883_; 
lean_dec_ref(v_tmpPath_4831_);
v_a_4871_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4873_ = v___x_4832_;
v_isShared_4874_ = v_isSharedCheck_4883_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4832_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4883_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4875_ = lean_io_error_to_string(v_a_4871_);
v___x_4876_ = 3;
v___x_4877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set_uint8(v___x_4877_, sizeof(void*)*1, v___x_4876_);
lean_inc_ref(v___y_4824_);
v___x_4878_ = lean_apply_2(v___y_4824_, v___x_4877_, lean_box(0));
v___x_4879_ = lean_box(0);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4879_);
v___x_4881_ = v___x_4873_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4884_, 0, v_b_4823_);
return v___x_4884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object* v_h_4885_, lean_object* v_as_4886_, lean_object* v_i_4887_, lean_object* v_stop_4888_, lean_object* v_b_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
size_t v_i_boxed_4892_; size_t v_stop_boxed_4893_; lean_object* v_res_4894_; 
v_i_boxed_4892_ = lean_unbox_usize(v_i_4887_);
lean_dec(v_i_4887_);
v_stop_boxed_4893_ = lean_unbox_usize(v_stop_4888_);
lean_dec(v_stop_4888_);
v_res_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4885_, v_as_4886_, v_i_boxed_4892_, v_stop_boxed_4893_, v_b_4889_, v___y_4890_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v_as_4886_);
lean_dec(v_h_4885_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object* v_h_4896_, lean_object* v_as_4897_, size_t v_i_4898_, size_t v_stop_4899_, lean_object* v_b_4900_, lean_object* v___y_4901_){
_start:
{
uint8_t v___x_4903_; 
v___x_4903_ = lean_usize_dec_eq(v_i_4898_, v_stop_4899_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v_url_4905_; lean_object* v_path_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4904_ = lean_array_uget_borrowed(v_as_4897_, v_i_4898_);
v_url_4905_ = lean_ctor_get(v___x_4904_, 0);
v_path_4906_ = lean_ctor_get(v___x_4904_, 1);
v___x_4907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0));
lean_inc_ref(v_path_4906_);
v___x_4908_ = l_String_quote(v_path_4906_);
v___x_4909_ = lean_string_append(v___x_4907_, v___x_4908_);
lean_dec_ref(v___x_4908_);
v___x_4910_ = l_IO_FS_Handle_putStrLn(v_h_4896_, v___x_4909_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
lean_dec_ref_known(v___x_4910_, 1);
v___x_4911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4905_);
v___x_4912_ = l_String_quote(v_url_4905_);
v___x_4913_ = lean_string_append(v___x_4911_, v___x_4912_);
lean_dec_ref(v___x_4912_);
v___x_4914_ = l_IO_FS_Handle_putStrLn(v_h_4896_, v___x_4913_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; size_t v___x_4916_; size_t v___x_4917_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = ((size_t)1ULL);
v___x_4917_ = lean_usize_add(v_i_4898_, v___x_4916_);
v_i_4898_ = v___x_4917_;
v_b_4900_ = v_a_4915_;
goto _start;
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4931_; 
v_a_4919_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4921_ = v___x_4914_;
v_isShared_4922_ = v_isSharedCheck_4931_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4914_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4931_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4923_; uint8_t v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4929_; 
v___x_4923_ = lean_io_error_to_string(v_a_4919_);
v___x_4924_ = 3;
v___x_4925_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*1, v___x_4924_);
lean_inc_ref(v___y_4901_);
v___x_4926_ = lean_apply_2(v___y_4901_, v___x_4925_, lean_box(0));
v___x_4927_ = lean_box(0);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4927_);
v___x_4929_ = v___x_4921_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4927_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4944_; 
v_a_4932_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4934_ = v___x_4910_;
v_isShared_4935_ = v_isSharedCheck_4944_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4910_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4944_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4936_; uint8_t v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4936_ = lean_io_error_to_string(v_a_4932_);
v___x_4937_ = 3;
v___x_4938_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*1, v___x_4937_);
lean_inc_ref(v___y_4901_);
v___x_4939_ = lean_apply_2(v___y_4901_, v___x_4938_, lean_box(0));
v___x_4940_ = lean_box(0);
if (v_isShared_4935_ == 0)
{
lean_ctor_set(v___x_4934_, 0, v___x_4940_);
v___x_4942_ = v___x_4934_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v___x_4945_; 
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v_b_4900_);
return v___x_4945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object* v_h_4946_, lean_object* v_as_4947_, lean_object* v_i_4948_, lean_object* v_stop_4949_, lean_object* v_b_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
size_t v_i_boxed_4953_; size_t v_stop_boxed_4954_; lean_object* v_res_4955_; 
v_i_boxed_4953_ = lean_unbox_usize(v_i_4948_);
lean_dec(v_i_4948_);
v_stop_boxed_4954_ = lean_unbox_usize(v_stop_4949_);
lean_dec(v_stop_4949_);
v_res_4955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4946_, v_as_4947_, v_i_boxed_4953_, v_stop_boxed_4954_, v_b_4950_, v___y_4951_);
lean_dec_ref(v___y_4951_);
lean_dec_ref(v_as_4947_);
lean_dec(v_h_4946_);
return v_res_4955_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4971_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4972_ = lean_unsigned_to_nat(11u);
v___x_4973_ = lean_mk_empty_array_with_capacity(v___x_4972_);
v___x_4974_ = lean_array_push(v___x_4973_, v___x_4971_);
return v___x_4974_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4975_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4976_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11);
v___x_4977_ = lean_array_push(v___x_4976_, v___x_4975_);
return v___x_4977_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4978_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6));
v___x_4979_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12);
v___x_4980_ = lean_array_push(v___x_4979_, v___x_4978_);
return v___x_4980_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4981_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4982_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13);
v___x_4983_ = lean_array_push(v___x_4982_, v___x_4981_);
return v___x_4983_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4984_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4985_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14);
v___x_4986_ = lean_array_push(v___x_4985_, v___x_4984_);
return v___x_4986_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4988_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15);
v___x_4989_ = lean_array_push(v___x_4988_, v___x_4987_);
return v___x_4989_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4991_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16);
v___x_4992_ = lean_array_push(v___x_4991_, v___x_4990_);
return v___x_4992_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4993_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4994_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17);
v___x_4995_ = lean_array_push(v___x_4994_, v___x_4993_);
return v___x_4995_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19(void){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4996_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4997_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18);
v___x_4998_ = lean_array_push(v___x_4997_, v___x_4996_);
return v___x_4998_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_4999_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_5000_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19);
v___x_5001_ = lean_array_push(v___x_5000_, v___x_4999_);
return v___x_5001_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5003_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_5004_ = lean_unsigned_to_nat(17u);
v___x_5005_ = lean_mk_empty_array_with_capacity(v___x_5004_);
v___x_5006_ = lean_array_push(v___x_5005_, v___x_5003_);
return v___x_5006_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23(void){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5007_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_5008_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22);
v___x_5009_ = lean_array_push(v___x_5008_, v___x_5007_);
return v___x_5009_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_5011_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23);
v___x_5012_ = lean_array_push(v___x_5011_, v___x_5010_);
return v___x_5012_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25(void){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5013_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_5014_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24);
v___x_5015_ = lean_array_push(v___x_5014_, v___x_5013_);
return v___x_5015_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26(void){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5016_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5017_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25);
v___x_5018_ = lean_array_push(v___x_5017_, v___x_5016_);
return v___x_5018_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5019_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21));
v___x_5020_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26);
v___x_5021_ = lean_array_push(v___x_5020_, v___x_5019_);
return v___x_5021_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5022_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_5023_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27);
v___x_5024_ = lean_array_push(v___x_5023_, v___x_5022_);
return v___x_5024_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5025_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_5026_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28);
v___x_5027_ = lean_array_push(v___x_5026_, v___x_5025_);
return v___x_5027_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_5029_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29);
v___x_5030_ = lean_array_push(v___x_5029_, v___x_5028_);
return v___x_5030_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5031_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_5032_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30);
v___x_5033_ = lean_array_push(v___x_5032_, v___x_5031_);
return v___x_5033_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32(void){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5034_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_5035_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31);
v___x_5036_ = lean_array_push(v___x_5035_, v___x_5034_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object* v_cfg_5037_, lean_object* v_h_5038_, lean_object* v_path_5039_, lean_object* v___y_5040_){
_start:
{
uint32_t v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; uint8_t v_kind_5057_; lean_object* v_scope_5058_; lean_object* v_infos_5059_; lean_object* v_key_5060_; uint32_t v___y_5062_; uint8_t v___y_5063_; lean_object* v___y_5064_; lean_object* v___y_5071_; uint32_t v___y_5072_; lean_object* v___y_5073_; uint8_t v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5089_; uint32_t v___y_5090_; lean_object* v___y_5091_; uint8_t v_didError_5092_; lean_object* v___y_5093_; lean_object* v___y_5098_; lean_object* v___y_5099_; uint32_t v___y_5100_; lean_object* v___y_5101_; uint8_t v___y_5102_; lean_object* v___y_5103_; lean_object* v___y_5113_; uint32_t v___y_5114_; lean_object* v___y_5115_; uint8_t v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5120_; lean_object* v_a_5121_; lean_object* v___y_5197_; lean_object* v___y_5198_; lean_object* v___y_5199_; lean_object* v_val_5200_; lean_object* v_a_5208_; 
v_kind_5057_ = lean_ctor_get_uint8(v_cfg_5037_, sizeof(void*)*3);
v_scope_5058_ = lean_ctor_get(v_cfg_5037_, 0);
lean_inc_ref(v_scope_5058_);
v_infos_5059_ = lean_ctor_get(v_cfg_5037_, 1);
lean_inc_ref(v_infos_5059_);
v_key_5060_ = lean_ctor_get(v_cfg_5037_, 2);
if (v_kind_5057_ == 0)
{
lean_object* v___x_5258_; lean_object* v___x_5259_; uint8_t v___x_5260_; 
v___x_5258_ = lean_unsigned_to_nat(0u);
v___x_5259_ = lean_array_get_size(v_infos_5059_);
v___x_5260_ = lean_nat_dec_lt(v___x_5258_, v___x_5259_);
if (v___x_5260_ == 0)
{
goto v___jp_5215_;
}
else
{
lean_object* v___x_5261_; size_t v___x_5262_; size_t v___x_5263_; lean_object* v___x_5264_; 
v___x_5261_ = lean_box(0);
v___x_5262_ = ((size_t)0ULL);
v___x_5263_ = lean_usize_of_nat(v___x_5259_);
v___x_5264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5038_, v_infos_5059_, v___x_5262_, v___x_5263_, v___x_5261_, v___y_5040_);
if (lean_obj_tag(v___x_5264_) == 0)
{
lean_dec_ref_known(v___x_5264_, 1);
goto v___jp_5215_;
}
else
{
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
lean_dec_ref(v_path_5039_);
lean_dec_ref(v_cfg_5037_);
return v___x_5264_;
}
}
}
else
{
lean_object* v___x_5265_; lean_object* v___x_5266_; uint8_t v___x_5267_; 
v___x_5265_ = lean_unsigned_to_nat(0u);
v___x_5266_ = lean_array_get_size(v_infos_5059_);
v___x_5267_ = lean_nat_dec_lt(v___x_5265_, v___x_5266_);
if (v___x_5267_ == 0)
{
goto v___jp_5232_;
}
else
{
lean_object* v___x_5268_; size_t v___x_5269_; size_t v___x_5270_; lean_object* v___x_5271_; 
v___x_5268_ = lean_box(0);
v___x_5269_ = ((size_t)0ULL);
v___x_5270_ = lean_usize_of_nat(v___x_5266_);
v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5038_, v_infos_5059_, v___x_5269_, v___x_5270_, v___x_5268_, v___y_5040_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_dec_ref_known(v___x_5271_, 1);
goto v___jp_5232_;
}
else
{
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
lean_dec_ref(v_path_5039_);
lean_dec_ref(v_cfg_5037_);
return v___x_5271_;
}
}
}
v___jp_5042_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = lean_box(0);
v___x_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
return v___x_5044_;
}
v___jp_5045_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; uint8_t v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5049_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_5050_ = lean_string_append(v___y_5048_, v___x_5049_);
v___x_5051_ = lean_uint32_to_nat(v___y_5046_);
v___x_5052_ = l_Nat_reprFast(v___x_5051_);
v___x_5053_ = lean_string_append(v___x_5050_, v___x_5052_);
lean_dec_ref(v___x_5052_);
v___x_5054_ = 3;
v___x_5055_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5055_, 0, v___x_5053_);
lean_ctor_set_uint8(v___x_5055_, sizeof(void*)*1, v___x_5054_);
lean_inc_ref(v___y_5047_);
v___x_5056_ = lean_apply_2(v___y_5047_, v___x_5055_, lean_box(0));
goto v___jp_5042_;
}
v___jp_5061_:
{
uint32_t v___x_5065_; uint8_t v___x_5066_; 
v___x_5065_ = 0;
v___x_5066_ = lean_uint32_dec_eq(v___y_5062_, v___x_5065_);
if (v___x_5066_ == 0)
{
lean_object* v_s_5067_; 
v_s_5067_ = lean_ctor_get(v_scope_5058_, 0);
lean_inc_ref(v_s_5067_);
lean_dec_ref(v_scope_5058_);
v___y_5046_ = v___y_5062_;
v___y_5047_ = v___y_5064_;
v___y_5048_ = v_s_5067_;
goto v___jp_5045_;
}
else
{
lean_dec_ref(v_scope_5058_);
if (v___y_5063_ == 0)
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = lean_box(0);
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
return v___x_5069_;
}
else
{
goto v___jp_5042_;
}
}
}
v___jp_5070_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; uint8_t v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5078_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_5079_ = lean_string_append(v___y_5077_, v___x_5078_);
lean_inc(v___y_5073_);
lean_inc(v___y_5071_);
lean_inc_ref(v___y_5076_);
v___x_5080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5080_, 0, v___y_5076_);
lean_ctor_set(v___x_5080_, 1, v___y_5071_);
lean_ctor_set(v___x_5080_, 2, v___y_5073_);
v___x_5081_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5080_, v___y_5073_);
lean_dec_ref_known(v___x_5080_, 3);
v___x_5082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5082_, 0, v___y_5076_);
lean_ctor_set(v___x_5082_, 1, v___y_5071_);
lean_ctor_set(v___x_5082_, 2, v___x_5081_);
v___x_5083_ = l_String_Slice_toString(v___x_5082_);
lean_dec_ref_known(v___x_5082_, 3);
v___x_5084_ = lean_string_append(v___x_5079_, v___x_5083_);
lean_dec_ref(v___x_5083_);
v___x_5085_ = 2;
v___x_5086_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5086_, 0, v___x_5084_);
lean_ctor_set_uint8(v___x_5086_, sizeof(void*)*1, v___x_5085_);
lean_inc_ref(v___y_5075_);
v___x_5087_ = lean_apply_2(v___y_5075_, v___x_5086_, lean_box(0));
v___y_5062_ = v___y_5072_;
v___y_5063_ = v___y_5074_;
v___y_5064_ = v___y_5075_;
goto v___jp_5061_;
}
v___jp_5088_:
{
lean_object* v___x_5094_; uint8_t v___x_5095_; 
v___x_5094_ = lean_string_utf8_byte_size(v___y_5091_);
v___x_5095_ = lean_nat_dec_eq(v___x_5094_, v___y_5089_);
if (v___x_5095_ == 0)
{
lean_object* v_s_5096_; 
v_s_5096_ = lean_ctor_get(v_scope_5058_, 0);
lean_inc_ref(v_s_5096_);
v___y_5071_ = v___y_5089_;
v___y_5072_ = v___y_5090_;
v___y_5073_ = v___x_5094_;
v___y_5074_ = v_didError_5092_;
v___y_5075_ = v___y_5093_;
v___y_5076_ = v___y_5091_;
v___y_5077_ = v_s_5096_;
goto v___jp_5070_;
}
else
{
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5089_);
v___y_5062_ = v___y_5090_;
v___y_5063_ = v_didError_5092_;
v___y_5064_ = v___y_5093_;
goto v___jp_5061_;
}
}
v___jp_5097_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5104_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_5105_ = lean_string_append(v___y_5103_, v___x_5104_);
v___x_5106_ = lean_string_append(v___x_5105_, v___y_5098_);
v___x_5107_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_5108_ = lean_string_append(v___x_5106_, v___x_5107_);
v___x_5109_ = 3;
v___x_5110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5110_, 0, v___x_5108_);
lean_ctor_set_uint8(v___x_5110_, sizeof(void*)*1, v___x_5109_);
lean_inc_ref(v___y_5040_);
v___x_5111_ = lean_apply_2(v___y_5040_, v___x_5110_, lean_box(0));
v___y_5089_ = v___y_5099_;
v___y_5090_ = v___y_5100_;
v___y_5091_ = v___y_5101_;
v_didError_5092_ = v___y_5102_;
v___y_5093_ = v___y_5040_;
goto v___jp_5088_;
}
v___jp_5112_:
{
lean_object* v_s_5118_; 
v_s_5118_ = lean_ctor_get(v_scope_5058_, 0);
lean_inc_ref(v_s_5118_);
v___y_5098_ = v___y_5117_;
v___y_5099_ = v___y_5113_;
v___y_5100_ = v___y_5114_;
v___y_5101_ = v___y_5115_;
v___y_5102_ = v___y_5116_;
v___y_5103_ = v_s_5118_;
goto v___jp_5097_;
}
v___jp_5119_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; uint8_t v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5122_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5123_ = lean_box(0);
v___x_5124_ = lean_unsigned_to_nat(0u);
v___x_5125_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5126_ = 1;
v___x_5127_ = 0;
v___x_5128_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5128_, 0, v___x_5122_);
lean_ctor_set(v___x_5128_, 1, v_a_5121_);
lean_ctor_set(v___x_5128_, 2, v___y_5120_);
lean_ctor_set(v___x_5128_, 3, v___x_5123_);
lean_ctor_set(v___x_5128_, 4, v___x_5125_);
lean_ctor_set_uint8(v___x_5128_, sizeof(void*)*5, v___x_5126_);
lean_ctor_set_uint8(v___x_5128_, sizeof(void*)*5 + 1, v___x_5127_);
v___x_5129_ = lean_io_process_spawn(v___x_5128_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v_stdout_5131_; lean_object* v_stderr_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v_stdout_5131_ = lean_ctor_get(v_a_5130_, 1);
lean_inc_n(v_stdout_5131_, 2);
v_stderr_5132_ = lean_ctor_get(v_a_5130_, 2);
v___x_5133_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_5134_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_5037_, v_stderr_5132_, v_stdout_5131_, v___x_5133_, v___y_5040_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5136_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = lean_io_process_child_wait(v___x_5122_, v_a_5130_);
lean_dec(v_a_5130_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_object* v_a_5137_; lean_object* v___x_5138_; 
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
lean_inc(v_a_5137_);
lean_dec_ref_known(v___x_5136_, 1);
v___x_5138_ = l_IO_FS_Handle_readToEnd(v_stdout_5131_);
lean_dec(v_stdout_5131_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; uint8_t v_didError_5140_; lean_object* v_numSuccesses_5141_; lean_object* v___x_5142_; uint8_t v___x_5143_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
lean_dec_ref_known(v___x_5138_, 1);
v_didError_5140_ = lean_ctor_get_uint8(v_a_5135_, sizeof(void*)*1);
v_numSuccesses_5141_ = lean_ctor_get(v_a_5135_, 0);
lean_inc(v_numSuccesses_5141_);
lean_dec(v_a_5135_);
v___x_5142_ = lean_array_get_size(v_infos_5059_);
lean_dec_ref(v_infos_5059_);
v___x_5143_ = lean_nat_dec_lt(v_numSuccesses_5141_, v___x_5142_);
lean_dec(v_numSuccesses_5141_);
if (v___x_5143_ == 0)
{
uint32_t v___x_5144_; 
v___x_5144_ = lean_unbox_uint32(v_a_5137_);
lean_dec(v_a_5137_);
v___y_5089_ = v___x_5124_;
v___y_5090_ = v___x_5144_;
v___y_5091_ = v_a_5139_;
v_didError_5092_ = v_didError_5140_;
v___y_5093_ = v___y_5040_;
goto v___jp_5088_;
}
else
{
if (v_kind_5057_ == 0)
{
lean_object* v___x_5145_; uint32_t v___x_5146_; 
v___x_5145_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_5146_ = lean_unbox_uint32(v_a_5137_);
lean_dec(v_a_5137_);
v___y_5113_ = v___x_5124_;
v___y_5114_ = v___x_5146_;
v___y_5115_ = v_a_5139_;
v___y_5116_ = v___x_5126_;
v___y_5117_ = v___x_5145_;
goto v___jp_5112_;
}
else
{
lean_object* v___x_5147_; uint32_t v___x_5148_; 
v___x_5147_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_5148_ = lean_unbox_uint32(v_a_5137_);
lean_dec(v_a_5137_);
v___y_5113_ = v___x_5124_;
v___y_5114_ = v___x_5148_;
v___y_5115_ = v_a_5139_;
v___y_5116_ = v___x_5126_;
v___y_5117_ = v___x_5147_;
goto v___jp_5112_;
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5161_; 
lean_dec(v_a_5137_);
lean_dec(v_a_5135_);
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
v_a_5149_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5151_ = v___x_5138_;
v_isShared_5152_ = v_isSharedCheck_5161_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5138_);
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
lean_inc_ref(v___y_5040_);
v___x_5156_ = lean_apply_2(v___y_5040_, v___x_5155_, lean_box(0));
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
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5174_; 
lean_dec(v_a_5135_);
lean_dec(v_stdout_5131_);
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
v_a_5162_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5164_ = v___x_5136_;
v_isShared_5165_ = v_isSharedCheck_5174_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5136_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5174_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5166_; uint8_t v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5172_; 
v___x_5166_ = lean_io_error_to_string(v_a_5162_);
v___x_5167_ = 3;
v___x_5168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set_uint8(v___x_5168_, sizeof(void*)*1, v___x_5167_);
lean_inc_ref(v___y_5040_);
v___x_5169_ = lean_apply_2(v___y_5040_, v___x_5168_, lean_box(0));
v___x_5170_ = lean_box(0);
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 0, v___x_5170_);
v___x_5172_ = v___x_5164_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5170_);
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
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec(v_stdout_5131_);
lean_dec(v_a_5130_);
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
v_a_5175_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5134_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5134_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5195_; 
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
lean_dec_ref(v_cfg_5037_);
v_a_5183_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5185_ = v___x_5129_;
v_isShared_5186_ = v_isSharedCheck_5195_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5129_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5195_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5187_; uint8_t v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5193_; 
v___x_5187_ = lean_io_error_to_string(v_a_5183_);
v___x_5188_ = 3;
v___x_5189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5189_, 0, v___x_5187_);
lean_ctor_set_uint8(v___x_5189_, sizeof(void*)*1, v___x_5188_);
lean_inc_ref(v___y_5040_);
v___x_5190_ = lean_apply_2(v___y_5040_, v___x_5189_, lean_box(0));
v___x_5191_ = lean_box(0);
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 0, v___x_5191_);
v___x_5193_ = v___x_5185_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v___x_5191_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
v___jp_5196_:
{
lean_object* v___x_5201_; uint8_t v___x_5202_; 
v___x_5201_ = lean_array_get_size(v___y_5197_);
v___x_5202_ = lean_nat_dec_lt(v___y_5198_, v___x_5201_);
if (v___x_5202_ == 0)
{
v___y_5120_ = v___y_5199_;
v_a_5121_ = v_val_5200_;
goto v___jp_5119_;
}
else
{
lean_object* v___x_5203_; size_t v___x_5204_; size_t v___x_5205_; lean_object* v___x_5206_; 
v___x_5203_ = lean_box(0);
v___x_5204_ = ((size_t)0ULL);
v___x_5205_ = lean_usize_of_nat(v___x_5201_);
v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_5197_, v___x_5204_, v___x_5205_, v___x_5203_, v___y_5040_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_dec_ref_known(v___x_5206_, 1);
v___y_5120_ = v___y_5199_;
v_a_5121_ = v_val_5200_;
goto v___jp_5119_;
}
else
{
lean_dec_ref(v_val_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
lean_dec_ref(v_cfg_5037_);
return v___x_5206_;
}
}
}
v___jp_5207_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5209_ = lean_unsigned_to_nat(0u);
v___x_5210_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_5211_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31));
v___x_5212_ = lean_io_getenv(v___x_5211_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v___x_5213_; 
v___x_5213_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32));
v___y_5197_ = v___x_5210_;
v___y_5198_ = v___x_5209_;
v___y_5199_ = v_a_5208_;
v_val_5200_ = v___x_5213_;
goto v___jp_5196_;
}
else
{
lean_object* v_val_5214_; 
v_val_5214_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_val_5214_);
lean_dec_ref_known(v___x_5212_, 1);
v___y_5197_ = v___x_5210_;
v___y_5198_ = v___x_5209_;
v___y_5199_ = v_a_5208_;
v_val_5200_ = v_val_5214_;
goto v___jp_5196_;
}
}
v___jp_5215_:
{
lean_object* v___x_5216_; 
v___x_5216_ = lean_io_prim_handle_flush(v_h_5038_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; 
lean_dec_ref_known(v___x_5216_, 1);
v___x_5217_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_5218_ = lean_array_push(v___x_5217_, v_path_5039_);
v_a_5208_ = v___x_5218_;
goto v___jp_5207_;
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5231_; 
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
lean_dec_ref(v_path_5039_);
lean_dec_ref(v_cfg_5037_);
v_a_5219_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5221_ = v___x_5216_;
v_isShared_5222_ = v_isSharedCheck_5231_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5216_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5231_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5229_; 
v___x_5223_ = lean_io_error_to_string(v_a_5219_);
v___x_5224_ = 3;
v___x_5225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5225_, 0, v___x_5223_);
lean_ctor_set_uint8(v___x_5225_, sizeof(void*)*1, v___x_5224_);
lean_inc_ref(v___y_5040_);
v___x_5226_ = lean_apply_2(v___y_5040_, v___x_5225_, lean_box(0));
v___x_5227_ = lean_box(0);
if (v_isShared_5222_ == 0)
{
lean_ctor_set(v___x_5221_, 0, v___x_5227_);
v___x_5229_ = v___x_5221_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
v___jp_5232_:
{
lean_object* v___x_5233_; 
v___x_5233_ = lean_io_prim_handle_flush(v_h_5038_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
lean_dec_ref_known(v___x_5233_, 1);
v___x_5234_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5235_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5236_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5237_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_5238_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_5060_);
v___x_5239_ = lean_array_push(v___x_5238_, v_key_5060_);
v___x_5240_ = lean_array_push(v___x_5239_, v___x_5234_);
v___x_5241_ = lean_array_push(v___x_5240_, v___x_5235_);
v___x_5242_ = lean_array_push(v___x_5241_, v___x_5236_);
v___x_5243_ = lean_array_push(v___x_5242_, v___x_5237_);
v___x_5244_ = lean_array_push(v___x_5243_, v_path_5039_);
v_a_5208_ = v___x_5244_;
goto v___jp_5207_;
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5257_; 
lean_dec_ref(v_infos_5059_);
lean_dec_ref(v_scope_5058_);
lean_dec_ref(v_path_5039_);
lean_dec_ref(v_cfg_5037_);
v_a_5245_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5247_ = v___x_5233_;
v_isShared_5248_ = v_isSharedCheck_5257_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5233_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5257_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5249_; uint8_t v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5255_; 
v___x_5249_ = lean_io_error_to_string(v_a_5245_);
v___x_5250_ = 3;
v___x_5251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5251_, 0, v___x_5249_);
lean_ctor_set_uint8(v___x_5251_, sizeof(void*)*1, v___x_5250_);
lean_inc_ref(v___y_5040_);
v___x_5252_ = lean_apply_2(v___y_5040_, v___x_5251_, lean_box(0));
v___x_5253_ = lean_box(0);
if (v_isShared_5248_ == 0)
{
lean_ctor_set(v___x_5247_, 0, v___x_5253_);
v___x_5255_ = v___x_5247_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5253_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object* v_cfg_5272_, lean_object* v_h_5273_, lean_object* v_path_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(v_cfg_5272_, v_h_5273_, v_path_5274_, v___y_5275_);
lean_dec_ref(v___y_5275_);
lean_dec(v_h_5273_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object* v_cfg_5278_, lean_object* v_a_5279_){
_start:
{
lean_object* v___f_5281_; lean_object* v___x_5282_; 
v___f_5281_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed), 5, 1);
lean_closure_set(v___f_5281_, 0, v_cfg_5278_);
v___x_5282_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5281_, v_a_5279_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object* v_cfg_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(v_cfg_5283_, v_a_5284_);
lean_dec_ref(v_a_5284_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(lean_object* v_service_5288_, lean_object* v_scope_5289_){
_start:
{
lean_object* v___y_5291_; 
if (lean_obj_tag(v_scope_5289_) == 0)
{
lean_object* v_s_5294_; lean_object* v_apiEndpoint_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v_s_5294_ = lean_ctor_get(v_scope_5289_, 0);
lean_inc_ref(v_s_5294_);
lean_dec_ref_known(v_scope_5289_, 1);
v_apiEndpoint_5295_ = lean_ctor_get(v_service_5288_, 4);
lean_inc_ref(v_apiEndpoint_5295_);
lean_dec_ref(v_service_5288_);
v___x_5296_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_5297_ = lean_string_append(v_apiEndpoint_5295_, v___x_5296_);
v___x_5298_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_5297_, v_s_5294_);
v___y_5291_ = v___x_5298_;
goto v___jp_5290_;
}
else
{
lean_object* v_s_5299_; lean_object* v_apiEndpoint_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; 
v_s_5299_ = lean_ctor_get(v_scope_5289_, 0);
lean_inc_ref(v_s_5299_);
lean_dec_ref_known(v_scope_5289_, 1);
v_apiEndpoint_5300_ = lean_ctor_get(v_service_5288_, 4);
lean_inc_ref(v_apiEndpoint_5300_);
lean_dec_ref(v_service_5288_);
v___x_5301_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_5302_ = lean_string_append(v_apiEndpoint_5300_, v___x_5301_);
v___x_5303_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_5302_, v_s_5299_);
v___y_5291_ = v___x_5303_;
goto v___jp_5290_;
}
v___jp_5290_:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5292_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0));
v___x_5293_ = lean_string_append(v___y_5291_, v___x_5292_);
return v___x_5293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths_spec__0(lean_object* v_a_5304_, lean_object* v_as_5305_, size_t v_sz_5306_, size_t v_i_5307_, lean_object* v_b_5308_){
_start:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_usize_dec_lt(v_i_5307_, v_sz_5306_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v_b_5308_);
return v___x_5311_;
}
else
{
lean_object* v___x_5312_; lean_object* v_a_5313_; lean_object* v___x_5314_; 
v___x_5312_ = lean_box(0);
v_a_5313_ = lean_array_uget_borrowed(v_as_5305_, v_i_5307_);
v___x_5314_ = l_IO_FS_writeBinFile(v_a_5313_, v_a_5304_);
if (lean_obj_tag(v___x_5314_) == 0)
{
size_t v___x_5315_; size_t v___x_5316_; 
lean_dec_ref_known(v___x_5314_, 1);
v___x_5315_ = ((size_t)1ULL);
v___x_5316_ = lean_usize_add(v_i_5307_, v___x_5315_);
v_i_5307_ = v___x_5316_;
v_b_5308_ = v___x_5312_;
goto _start;
}
else
{
return v___x_5314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths_spec__0___boxed(lean_object* v_a_5318_, lean_object* v_as_5319_, lean_object* v_sz_5320_, lean_object* v_i_5321_, lean_object* v_b_5322_, lean_object* v___y_5323_){
_start:
{
size_t v_sz_boxed_5324_; size_t v_i_boxed_5325_; lean_object* v_res_5326_; 
v_sz_boxed_5324_ = lean_unbox_usize(v_sz_5320_);
lean_dec(v_sz_5320_);
v_i_boxed_5325_ = lean_unbox_usize(v_i_5321_);
lean_dec(v_i_5321_);
v_res_5326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths_spec__0(v_a_5318_, v_as_5319_, v_sz_boxed_5324_, v_i_boxed_5325_, v_b_5322_);
lean_dec_ref(v_as_5319_);
lean_dec_ref(v_a_5318_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths(lean_object* v_path_5327_, lean_object* v_extraPaths_5328_){
_start:
{
lean_object* v___x_5330_; 
v___x_5330_ = l_IO_FS_readBinFile(v_path_5327_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5332_; size_t v_sz_5333_; size_t v___x_5334_; lean_object* v___x_5335_; 
v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
lean_inc(v_a_5331_);
lean_dec_ref_known(v___x_5330_, 1);
v___x_5332_ = lean_box(0);
v_sz_5333_ = lean_array_size(v_extraPaths_5328_);
v___x_5334_ = ((size_t)0ULL);
v___x_5335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths_spec__0(v_a_5331_, v_extraPaths_5328_, v_sz_5333_, v___x_5334_, v___x_5332_);
lean_dec(v_a_5331_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5342_ == 0)
{
lean_object* v_unused_5343_; 
v_unused_5343_ = lean_ctor_get(v___x_5335_, 0);
lean_dec(v_unused_5343_);
v___x_5337_ = v___x_5335_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_dec(v___x_5335_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 0, v___x_5332_);
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5332_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
else
{
return v___x_5335_;
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
v_a_5344_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5330_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5330_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths___boxed(lean_object* v_path_5352_, lean_object* v_extraPaths_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths(v_path_5352_, v_extraPaths_5353_);
lean_dec_ref(v_extraPaths_5353_);
lean_dec_ref(v_path_5352_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(size_t v_sz_5356_, size_t v_i_5357_, lean_object* v_bs_5358_){
_start:
{
uint8_t v___x_5359_; 
v___x_5359_ = lean_usize_dec_lt(v_i_5357_, v_sz_5356_);
if (v___x_5359_ == 0)
{
return v_bs_5358_;
}
else
{
lean_object* v_v_5360_; uint64_t v_hash_5361_; lean_object* v___x_5362_; lean_object* v_bs_x27_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; size_t v___x_5366_; size_t v___x_5367_; lean_object* v___x_5368_; 
v_v_5360_ = lean_array_uget_borrowed(v_bs_5358_, v_i_5357_);
v_hash_5361_ = lean_ctor_get_uint64(v_v_5360_, sizeof(void*)*3);
v___x_5362_ = lean_unsigned_to_nat(0u);
v_bs_x27_5363_ = lean_array_uset(v_bs_5358_, v_i_5357_, v___x_5362_);
v___x_5364_ = l_Lake_lowerHexUInt64(v_hash_5361_);
v___x_5365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5364_);
v___x_5366_ = ((size_t)1ULL);
v___x_5367_ = lean_usize_add(v_i_5357_, v___x_5366_);
v___x_5368_ = lean_array_uset(v_bs_x27_5363_, v_i_5357_, v___x_5365_);
v_i_5357_ = v___x_5367_;
v_bs_5358_ = v___x_5368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0___boxed(lean_object* v_sz_5370_, lean_object* v_i_5371_, lean_object* v_bs_5372_){
_start:
{
size_t v_sz_boxed_5373_; size_t v_i_boxed_5374_; lean_object* v_res_5375_; 
v_sz_boxed_5373_ = lean_unbox_usize(v_sz_5370_);
lean_dec(v_sz_5370_);
v_i_boxed_5374_ = lean_unbox_usize(v_i_5371_);
lean_dec(v_i_5371_);
v_res_5375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_boxed_5373_, v_i_boxed_5374_, v_bs_5372_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(lean_object* v_a_5376_, lean_object* v_n_5377_, lean_object* v_j_5378_, lean_object* v_a_5379_){
_start:
{
lean_object* v_zero_5380_; uint8_t v_isZero_5381_; 
v_zero_5380_ = lean_unsigned_to_nat(0u);
v_isZero_5381_ = lean_nat_dec_eq(v_j_5378_, v_zero_5380_);
if (v_isZero_5381_ == 1)
{
lean_dec(v_j_5378_);
return v_a_5379_;
}
else
{
lean_object* v___x_5382_; lean_object* v___x_5383_; uint64_t v_hash_5384_; lean_object* v_path_5385_; lean_object* v_extraPaths_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5398_; 
v___x_5382_ = lean_nat_sub(v_n_5377_, v_j_5378_);
v___x_5383_ = lean_array_fget(v_a_5379_, v___x_5382_);
v_hash_5384_ = lean_ctor_get_uint64(v___x_5383_, sizeof(void*)*3);
v_path_5385_ = lean_ctor_get(v___x_5383_, 1);
v_extraPaths_5386_ = lean_ctor_get(v___x_5383_, 2);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5398_ == 0)
{
lean_object* v_unused_5399_; 
v_unused_5399_ = lean_ctor_get(v___x_5383_, 0);
lean_dec(v_unused_5399_);
v___x_5388_ = v___x_5383_;
v_isShared_5389_ = v_isSharedCheck_5398_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_extraPaths_5386_);
lean_inc(v_path_5385_);
lean_dec(v___x_5383_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5398_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v_one_5390_; lean_object* v_n_5391_; lean_object* v___x_5392_; lean_object* v___x_5394_; 
v_one_5390_ = lean_unsigned_to_nat(1u);
v_n_5391_ = lean_nat_sub(v_j_5378_, v_one_5390_);
lean_dec(v_j_5378_);
v___x_5392_ = lean_array_fget_borrowed(v_a_5376_, v___x_5382_);
lean_inc(v___x_5392_);
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 0, v___x_5392_);
v___x_5394_ = v___x_5388_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v___x_5392_);
lean_ctor_set(v_reuseFailAlloc_5397_, 1, v_path_5385_);
lean_ctor_set(v_reuseFailAlloc_5397_, 2, v_extraPaths_5386_);
lean_ctor_set_uint64(v_reuseFailAlloc_5397_, sizeof(void*)*3, v_hash_5384_);
v___x_5394_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5395_; 
v___x_5395_ = lean_array_fset(v_a_5379_, v___x_5382_, v___x_5394_);
lean_dec(v___x_5382_);
v_j_5378_ = v_n_5391_;
v_a_5379_ = v___x_5395_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg___boxed(lean_object* v_a_5400_, lean_object* v_n_5401_, lean_object* v_j_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5400_, v_n_5401_, v_j_5402_, v_a_5403_);
lean_dec(v_n_5401_);
lean_dec_ref(v_a_5400_);
return v_res_5404_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5405_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5406_ = lean_unsigned_to_nat(2u);
v___x_5407_ = lean_mk_empty_array_with_capacity(v___x_5406_);
v___x_5408_ = lean_array_push(v___x_5407_, v___x_5405_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(lean_object* v_as_5409_, size_t v_i_5410_, size_t v_stop_5411_, lean_object* v_b_5412_){
_start:
{
uint8_t v___x_5413_; 
v___x_5413_ = lean_usize_dec_eq(v_i_5410_, v_stop_5411_);
if (v___x_5413_ == 0)
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; size_t v___x_5418_; size_t v___x_5419_; 
v___x_5414_ = lean_array_uget_borrowed(v_as_5409_, v_i_5410_);
v___x_5415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0);
lean_inc(v___x_5414_);
v___x_5416_ = lean_array_push(v___x_5415_, v___x_5414_);
v___x_5417_ = l_Array_append___redArg(v_b_5412_, v___x_5416_);
lean_dec_ref(v___x_5416_);
v___x_5418_ = ((size_t)1ULL);
v___x_5419_ = lean_usize_add(v_i_5410_, v___x_5418_);
v_i_5410_ = v___x_5419_;
v_b_5412_ = v___x_5417_;
goto _start;
}
else
{
return v_b_5412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___boxed(lean_object* v_as_5421_, lean_object* v_i_5422_, lean_object* v_stop_5423_, lean_object* v_b_5424_){
_start:
{
size_t v_i_boxed_5425_; size_t v_stop_boxed_5426_; lean_object* v_res_5427_; 
v_i_boxed_5425_ = lean_unbox_usize(v_i_5422_);
lean_dec(v_i_5422_);
v_stop_boxed_5426_ = lean_unbox_usize(v_stop_5423_);
lean_dec(v_stop_5423_);
v_res_5427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v_as_5421_, v_i_boxed_5425_, v_stop_boxed_5426_, v_b_5424_);
lean_dec_ref(v_as_5421_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object* v_x_5430_){
_start:
{
if (lean_obj_tag(v_x_5430_) == 0)
{
lean_object* v___x_5431_; 
v___x_5431_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0));
return v___x_5431_;
}
else
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5432_, 0, v_x_5430_);
v___x_5433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
return v___x_5433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object* v_x_5436_){
_start:
{
if (lean_obj_tag(v_x_5436_) == 0)
{
lean_object* v___x_5437_; 
v___x_5437_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0));
return v___x_5437_;
}
else
{
lean_object* v___x_5438_; 
v___x_5438_ = l_Lean_Json_getObj_x3f(v_x_5436_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5455_; 
v_a_5447_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5449_ = v___x_5438_;
v_isShared_5450_ = v_isSharedCheck_5455_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5438_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5455_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5451_; lean_object* v___x_5453_; 
v___x_5451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5451_, 0, v_a_5447_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 0, v___x_5451_);
v___x_5453_ = v___x_5449_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5451_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t v_sz_5456_, size_t v_i_5457_, lean_object* v_bs_5458_){
_start:
{
uint8_t v___x_5459_; 
v___x_5459_ = lean_usize_dec_lt(v_i_5457_, v_sz_5456_);
if (v___x_5459_ == 0)
{
lean_object* v___x_5460_; 
v___x_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5460_, 0, v_bs_5458_);
return v___x_5460_;
}
else
{
lean_object* v_v_5461_; lean_object* v___x_5462_; 
v_v_5461_ = lean_array_uget_borrowed(v_bs_5458_, v_i_5457_);
lean_inc(v_v_5461_);
v___x_5462_ = l_Lean_Json_getStr_x3f(v_v_5461_);
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_dec_ref(v_bs_5458_);
v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5462_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5462_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5462_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
else
{
lean_object* v_a_5471_; lean_object* v___x_5472_; lean_object* v_bs_x27_5473_; size_t v___x_5474_; size_t v___x_5475_; lean_object* v___x_5476_; 
v_a_5471_ = lean_ctor_get(v___x_5462_, 0);
lean_inc(v_a_5471_);
lean_dec_ref_known(v___x_5462_, 1);
v___x_5472_ = lean_unsigned_to_nat(0u);
v_bs_x27_5473_ = lean_array_uset(v_bs_5458_, v_i_5457_, v___x_5472_);
v___x_5474_ = ((size_t)1ULL);
v___x_5475_ = lean_usize_add(v_i_5457_, v___x_5474_);
v___x_5476_ = lean_array_uset(v_bs_x27_5473_, v_i_5457_, v_a_5471_);
v_i_5457_ = v___x_5475_;
v_bs_5458_ = v___x_5476_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_5478_, lean_object* v_i_5479_, lean_object* v_bs_5480_){
_start:
{
size_t v_sz_boxed_5481_; size_t v_i_boxed_5482_; lean_object* v_res_5483_; 
v_sz_boxed_5481_ = lean_unbox_usize(v_sz_5478_);
lean_dec(v_sz_5478_);
v_i_boxed_5482_ = lean_unbox_usize(v_i_5479_);
lean_dec(v_i_5479_);
v_res_5483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_boxed_5481_, v_i_boxed_5482_, v_bs_5480_);
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object* v_x_5484_){
_start:
{
if (lean_obj_tag(v_x_5484_) == 4)
{
lean_object* v_elems_5485_; size_t v_sz_5486_; size_t v___x_5487_; lean_object* v___x_5488_; 
v_elems_5485_ = lean_ctor_get(v_x_5484_, 0);
lean_inc_ref(v_elems_5485_);
lean_dec_ref_known(v_x_5484_, 1);
v_sz_5486_ = lean_array_size(v_elems_5485_);
v___x_5487_ = ((size_t)0ULL);
v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_5486_, v___x_5487_, v_elems_5485_);
return v___x_5488_;
}
else
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5489_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_5490_ = lean_unsigned_to_nat(80u);
v___x_5491_ = l_Lean_Json_pretty(v_x_5484_, v___x_5490_);
v___x_5492_ = lean_string_append(v___x_5489_, v___x_5491_);
lean_dec_ref(v___x_5491_);
v___x_5493_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
v___x_5494_ = lean_string_append(v___x_5492_, v___x_5493_);
v___x_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
return v___x_5495_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(lean_object* v_val_5508_){
_start:
{
lean_object* v___x_5528_; 
lean_inc(v_val_5508_);
v___x_5528_ = l_Lean_Json_getObj_x3f(v_val_5508_);
if (lean_obj_tag(v___x_5528_) == 1)
{
lean_object* v_a_5529_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
v_a_5529_ = lean_ctor_get(v___x_5528_, 0);
lean_inc(v_a_5529_);
lean_dec_ref_known(v___x_5528_, 1);
v___x_5561_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0));
v___x_5562_ = l_Lake_JsonObject_getJson_x3f(v_a_5529_, v___x_5561_);
if (lean_obj_tag(v___x_5562_) == 0)
{
goto v___jp_5530_;
}
else
{
lean_object* v_val_5563_; lean_object* v___x_5564_; 
v_val_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_val_5563_);
lean_dec_ref_known(v___x_5562_, 1);
v___x_5564_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(v_val_5563_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5574_; 
lean_dec(v_a_5529_);
lean_dec(v_val_5508_);
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5567_ = v___x_5564_;
v_isShared_5568_ = v_isSharedCheck_5574_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5564_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5574_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5572_; 
v___x_5569_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1));
v___x_5570_ = lean_string_append(v___x_5569_, v_a_5565_);
lean_dec(v_a_5565_);
if (v_isShared_5568_ == 0)
{
lean_ctor_set(v___x_5567_, 0, v___x_5570_);
v___x_5572_ = v___x_5567_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
else
{
lean_object* v_a_5575_; 
v_a_5575_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_a_5575_);
lean_dec_ref_known(v___x_5564_, 1);
if (lean_obj_tag(v_a_5575_) == 1)
{
lean_object* v_val_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
lean_dec(v_a_5529_);
lean_dec(v_val_5508_);
v_val_5576_ = lean_ctor_get(v_a_5575_, 0);
lean_inc(v_val_5576_);
lean_dec_ref_known(v_a_5575_, 1);
v___x_5577_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2));
v___x_5578_ = l_Lake_JsonObject_getJson_x3f(v_val_5576_, v___x_5577_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v___x_5579_; 
lean_dec(v_val_5576_);
v___x_5579_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4));
return v___x_5579_;
}
else
{
lean_object* v_val_5580_; lean_object* v___x_5581_; 
v_val_5580_ = lean_ctor_get(v___x_5578_, 0);
lean_inc(v_val_5580_);
lean_dec_ref_known(v___x_5578_, 1);
v___x_5581_ = l_Lean_Json_getNat_x3f(v_val_5580_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5591_; 
lean_dec(v_val_5576_);
v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5581_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5584_ = v___x_5581_;
v_isShared_5585_ = v_isSharedCheck_5591_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_a_5582_);
lean_dec(v___x_5581_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5591_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5589_; 
v___x_5586_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5));
v___x_5587_ = lean_string_append(v___x_5586_, v_a_5582_);
lean_dec(v_a_5582_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 0, v___x_5587_);
v___x_5589_ = v___x_5584_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v_a_5592_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_a_5592_);
lean_dec_ref_known(v___x_5581_, 1);
v___x_5593_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6));
v___x_5594_ = l_Lake_JsonObject_getJson_x3f(v_val_5576_, v___x_5593_);
lean_dec(v_val_5576_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v___x_5595_; 
lean_dec(v_a_5592_);
v___x_5595_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8));
return v___x_5595_;
}
else
{
lean_object* v_val_5596_; lean_object* v___x_5597_; 
v_val_5596_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_val_5596_);
lean_dec_ref_known(v___x_5594_, 1);
v___x_5597_ = l_Lean_Json_getStr_x3f(v_val_5596_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5607_; 
lean_dec(v_a_5592_);
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5600_ = v___x_5597_;
v_isShared_5601_ = v_isSharedCheck_5607_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_a_5598_);
lean_dec(v___x_5597_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5607_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5605_; 
v___x_5602_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9));
v___x_5603_ = lean_string_append(v___x_5602_, v_a_5598_);
lean_dec(v_a_5598_);
if (v_isShared_5601_ == 0)
{
lean_ctor_set(v___x_5600_, 0, v___x_5603_);
v___x_5605_ = v___x_5600_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5603_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
else
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5616_; 
v_a_5608_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5610_ = v___x_5597_;
v_isShared_5611_ = v_isSharedCheck_5616_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5597_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5616_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5612_; lean_object* v___x_5614_; 
v___x_5612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5612_, 0, v_a_5592_);
lean_ctor_set(v___x_5612_, 1, v_a_5608_);
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 0, v___x_5612_);
v___x_5614_ = v___x_5610_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5612_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_5575_);
goto v___jp_5530_;
}
}
}
v___jp_5530_:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5531_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_5532_ = l_Lake_JsonObject_getJson_x3f(v_a_5529_, v___x_5531_);
lean_dec(v_a_5529_);
if (lean_obj_tag(v___x_5532_) == 0)
{
goto v___jp_5509_;
}
else
{
lean_object* v_val_5533_; lean_object* v___x_5534_; lean_object* v_a_5535_; 
v_val_5533_ = lean_ctor_get(v___x_5532_, 0);
lean_inc(v_val_5533_);
lean_dec_ref_known(v___x_5532_, 1);
v___x_5534_ = l_Lean_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(v_val_5533_);
v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_a_5535_);
lean_dec_ref(v___x_5534_);
if (lean_obj_tag(v_a_5535_) == 1)
{
lean_object* v_val_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5560_; 
lean_dec(v_val_5508_);
v_val_5536_ = lean_ctor_get(v_a_5535_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v_a_5535_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5538_ = v_a_5535_;
v_isShared_5539_ = v_isSharedCheck_5560_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_val_5536_);
lean_dec(v_a_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5560_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5540_; 
v___x_5540_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5536_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_del_object(v___x_5538_);
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5540_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5540_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
else
{
lean_object* v_a_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5559_; 
v_a_5549_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5551_ = v___x_5540_;
v_isShared_5552_ = v_isSharedCheck_5559_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_a_5549_);
lean_dec(v___x_5540_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5559_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set_tag(v___x_5538_, 0);
lean_ctor_set(v___x_5538_, 0, v_a_5549_);
v___x_5554_ = v___x_5538_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5549_);
v___x_5554_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5556_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 0, v___x_5554_);
v___x_5556_ = v___x_5551_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5535_);
goto v___jp_5509_;
}
}
}
}
else
{
lean_object* v___x_5617_; 
lean_dec_ref(v___x_5528_);
v___x_5617_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5508_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5625_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5620_ = v___x_5617_;
v_isShared_5621_ = v_isSharedCheck_5625_;
goto v_resetjp_5619_;
}
else
{
lean_inc(v_a_5618_);
lean_dec(v___x_5617_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5625_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5623_; 
if (v_isShared_5621_ == 0)
{
v___x_5623_ = v___x_5620_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_a_5618_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
else
{
lean_object* v_a_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5634_; 
v_a_5626_ = lean_ctor_get(v___x_5617_, 0);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5628_ = v___x_5617_;
v_isShared_5629_ = v_isSharedCheck_5634_;
goto v_resetjp_5627_;
}
else
{
lean_inc(v_a_5626_);
lean_dec(v___x_5617_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5634_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v___x_5630_; lean_object* v___x_5632_; 
v___x_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5630_, 0, v_a_5626_);
if (v_isShared_5629_ == 0)
{
lean_ctor_set(v___x_5628_, 0, v___x_5630_);
v___x_5632_ = v___x_5628_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
v___jp_5509_:
{
lean_object* v___x_5510_; 
v___x_5510_ = l_Lean_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_5508_);
if (lean_obj_tag(v___x_5510_) == 0)
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
v_a_5511_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5510_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5510_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5527_; 
v_a_5519_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5527_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5527_ == 0)
{
v___x_5521_ = v___x_5510_;
v_isShared_5522_ = v_isSharedCheck_5527_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5510_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5527_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; lean_object* v___x_5525_; 
v___x_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5523_, 0, v_a_5519_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 0, v___x_5523_);
v___x_5525_ = v___x_5521_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18(void){
_start:
{
lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v___x_5653_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_5654_ = lean_unsigned_to_nat(12u);
v___x_5655_ = lean_mk_empty_array_with_capacity(v___x_5654_);
v___x_5656_ = lean_array_push(v___x_5655_, v___x_5653_);
return v___x_5656_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19(void){
_start:
{
lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v___x_5657_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14));
v___x_5658_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18);
v___x_5659_ = lean_array_push(v___x_5658_, v___x_5657_);
return v___x_5659_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20(void){
_start:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
v___x_5660_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_5661_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19);
v___x_5662_ = lean_array_push(v___x_5661_, v___x_5660_);
return v___x_5662_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21(void){
_start:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5663_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15));
v___x_5664_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20);
v___x_5665_ = lean_array_push(v___x_5664_, v___x_5663_);
return v___x_5665_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22(void){
_start:
{
lean_object* v___x_5666_; lean_object* v___x_5667_; 
v___x_5666_ = l_Lake_Reservoir_lakeHeaders;
v___x_5667_ = lean_array_get_size(v___x_5666_);
return v___x_5667_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23(void){
_start:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; uint8_t v___x_5670_; 
v___x_5668_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5669_ = lean_unsigned_to_nat(0u);
v___x_5670_ = lean_nat_dec_lt(v___x_5669_, v___x_5668_);
return v___x_5670_;
}
}
static size_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24(void){
_start:
{
lean_object* v___x_5671_; size_t v___x_5672_; 
v___x_5671_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5672_ = lean_usize_of_nat(v___x_5671_);
return v___x_5672_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(lean_object* v_url_5673_, lean_object* v_infos_5674_, lean_object* v_h_5675_, lean_object* v_path_5676_, lean_object* v___y_5677_){
_start:
{
uint32_t v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5692_; uint8_t v___y_5693_; uint32_t v___y_5694_; lean_object* v___y_5695_; lean_object* v_msg_5696_; lean_object* v___y_5697_; lean_object* v___y_5711_; uint8_t v___y_5712_; uint32_t v___y_5713_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v_msg_5716_; lean_object* v___y_5717_; lean_object* v___y_5728_; uint8_t v___y_5729_; uint32_t v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v_msg_5734_; lean_object* v___y_5747_; uint32_t v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5750_; lean_object* v_a_5751_; lean_object* v___y_5779_; uint8_t v___y_5780_; uint32_t v___y_5781_; lean_object* v___y_5782_; lean_object* v___y_5783_; lean_object* v___y_5802_; lean_object* v_a_5803_; size_t v_sz_5885_; size_t v___x_5886_; lean_object* v___y_5888_; lean_object* v___y_5889_; lean_object* v___y_5890_; lean_object* v_val_5891_; lean_object* v___x_5905_; lean_object* v_body_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v_sz_5885_ = lean_array_size(v_infos_5674_);
v___x_5886_ = ((size_t)0ULL);
lean_inc_ref(v_infos_5674_);
v___x_5905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_5885_, v___x_5886_, v_infos_5674_);
v_body_5906_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_5906_, 0, v___x_5905_);
v___x_5907_ = l_Lean_Json_compress(v_body_5906_);
v___x_5908_ = lean_io_prim_handle_put_str(v_h_5675_, v___x_5907_);
lean_dec_ref(v___x_5907_);
if (lean_obj_tag(v___x_5908_) == 0)
{
lean_object* v___x_5909_; 
lean_dec_ref_known(v___x_5908_, 1);
v___x_5909_ = lean_io_prim_handle_flush(v_h_5675_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v___y_5911_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; uint8_t v___x_5937_; 
lean_dec_ref_known(v___x_5909_, 1);
v___x_5918_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_5919_ = lean_string_append(v___x_5918_, v_path_5676_);
v___x_5920_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_5921_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_5922_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5923_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5924_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5925_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5926_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_5927_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_5928_ = lean_array_push(v___x_5927_, v___x_5919_);
v___x_5929_ = lean_array_push(v___x_5928_, v___x_5920_);
v___x_5930_ = lean_array_push(v___x_5929_, v___x_5921_);
v___x_5931_ = lean_array_push(v___x_5930_, v___x_5922_);
v___x_5932_ = lean_array_push(v___x_5931_, v___x_5923_);
v___x_5933_ = lean_array_push(v___x_5932_, v___x_5924_);
v___x_5934_ = lean_array_push(v___x_5933_, v___x_5925_);
v___x_5935_ = lean_array_push(v___x_5934_, v___x_5926_);
v___x_5936_ = l_Lake_Reservoir_lakeHeaders;
v___x_5937_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_5937_ == 0)
{
v___y_5911_ = v___x_5935_;
goto v___jp_5910_;
}
else
{
size_t v___x_5938_; lean_object* v___x_5939_; 
v___x_5938_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
v___x_5939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5936_, v___x_5886_, v___x_5938_, v___x_5935_);
v___y_5911_ = v___x_5939_;
goto v___jp_5910_;
}
v___jp_5910_:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; 
v___x_5912_ = lean_unsigned_to_nat(0u);
v___x_5913_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_5914_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31));
v___x_5915_ = lean_io_getenv(v___x_5914_);
if (lean_obj_tag(v___x_5915_) == 0)
{
lean_object* v___x_5916_; 
v___x_5916_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32));
v___y_5888_ = v___y_5911_;
v___y_5889_ = v___x_5913_;
v___y_5890_ = v___x_5912_;
v_val_5891_ = v___x_5916_;
goto v___jp_5887_;
}
else
{
lean_object* v_val_5917_; 
v_val_5917_ = lean_ctor_get(v___x_5915_, 0);
lean_inc(v_val_5917_);
lean_dec_ref_known(v___x_5915_, 1);
v___y_5888_ = v___y_5911_;
v___y_5889_ = v___x_5913_;
v___y_5890_ = v___x_5912_;
v_val_5891_ = v_val_5917_;
goto v___jp_5887_;
}
}
}
else
{
lean_object* v_a_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5952_; 
lean_dec_ref(v_infos_5674_);
lean_dec_ref(v_url_5673_);
v_a_5940_ = lean_ctor_get(v___x_5909_, 0);
v_isSharedCheck_5952_ = !lean_is_exclusive(v___x_5909_);
if (v_isSharedCheck_5952_ == 0)
{
v___x_5942_ = v___x_5909_;
v_isShared_5943_ = v_isSharedCheck_5952_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_a_5940_);
lean_dec(v___x_5909_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5952_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5944_; uint8_t v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5950_; 
v___x_5944_ = lean_io_error_to_string(v_a_5940_);
v___x_5945_ = 3;
v___x_5946_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set_uint8(v___x_5946_, sizeof(void*)*1, v___x_5945_);
lean_inc_ref(v___y_5677_);
v___x_5947_ = lean_apply_2(v___y_5677_, v___x_5946_, lean_box(0));
v___x_5948_ = lean_box(0);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 0, v___x_5948_);
v___x_5950_ = v___x_5942_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5951_; 
v_reuseFailAlloc_5951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5951_, 0, v___x_5948_);
v___x_5950_ = v_reuseFailAlloc_5951_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
return v___x_5950_;
}
}
}
}
else
{
lean_object* v_a_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5965_; 
lean_dec_ref(v_infos_5674_);
lean_dec_ref(v_url_5673_);
v_a_5953_ = lean_ctor_get(v___x_5908_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v___x_5908_);
if (v_isSharedCheck_5965_ == 0)
{
v___x_5955_ = v___x_5908_;
v_isShared_5956_ = v_isSharedCheck_5965_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_a_5953_);
lean_dec(v___x_5908_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_5965_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v___x_5957_; uint8_t v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5963_; 
v___x_5957_ = lean_io_error_to_string(v_a_5953_);
v___x_5958_ = 3;
v___x_5959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5959_, 0, v___x_5957_);
lean_ctor_set_uint8(v___x_5959_, sizeof(void*)*1, v___x_5958_);
lean_inc_ref(v___y_5677_);
v___x_5960_ = lean_apply_2(v___y_5677_, v___x_5959_, lean_box(0));
v___x_5961_ = lean_box(0);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 0, v___x_5961_);
v___x_5963_ = v___x_5955_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v___x_5961_);
v___x_5963_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
return v___x_5963_;
}
}
}
v___jp_5679_:
{
lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; uint8_t v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5682_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_5683_ = lean_uint32_to_nat(v___y_5680_);
v___x_5684_ = l_Nat_reprFast(v___x_5683_);
v___x_5685_ = lean_string_append(v___x_5682_, v___x_5684_);
lean_dec_ref(v___x_5684_);
v___x_5686_ = 3;
v___x_5687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5687_, 0, v___x_5685_);
lean_ctor_set_uint8(v___x_5687_, sizeof(void*)*1, v___x_5686_);
lean_inc_ref(v___y_5681_);
v___x_5688_ = lean_apply_2(v___y_5681_, v___x_5687_, lean_box(0));
v___x_5689_ = lean_box(0);
v___x_5690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
return v___x_5690_;
}
v___jp_5691_:
{
uint8_t v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; 
v___x_5698_ = 3;
v___x_5699_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5699_, 0, v_msg_5696_);
lean_ctor_set_uint8(v___x_5699_, sizeof(void*)*1, v___x_5698_);
lean_inc_ref_n(v___y_5697_, 2);
v___x_5700_ = lean_apply_2(v___y_5697_, v___x_5699_, lean_box(0));
v___x_5701_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5702_ = lean_string_utf8_byte_size(v___y_5695_);
lean_inc(v___y_5692_);
lean_inc_ref(v___y_5695_);
v___x_5703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5703_, 0, v___y_5695_);
lean_ctor_set(v___x_5703_, 1, v___y_5692_);
lean_ctor_set(v___x_5703_, 2, v___x_5702_);
v___x_5704_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5703_, v___x_5702_);
lean_dec_ref_known(v___x_5703_, 3);
v___x_5705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5705_, 0, v___y_5695_);
lean_ctor_set(v___x_5705_, 1, v___y_5692_);
lean_ctor_set(v___x_5705_, 2, v___x_5704_);
v___x_5706_ = l_String_Slice_toString(v___x_5705_);
lean_dec_ref_known(v___x_5705_, 3);
v___x_5707_ = lean_string_append(v___x_5701_, v___x_5706_);
lean_dec_ref(v___x_5706_);
v___x_5708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5708_, 0, v___x_5707_);
lean_ctor_set_uint8(v___x_5708_, sizeof(void*)*1, v___y_5693_);
v___x_5709_ = lean_apply_2(v___y_5697_, v___x_5708_, lean_box(0));
v___y_5680_ = v___y_5694_;
v___y_5681_ = v___y_5697_;
goto v___jp_5679_;
}
v___jp_5710_:
{
lean_object* v___x_5718_; uint8_t v___x_5719_; 
v___x_5718_ = lean_string_utf8_byte_size(v___y_5715_);
v___x_5719_ = lean_nat_dec_eq(v___x_5718_, v___y_5711_);
if (v___x_5719_ == 0)
{
lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; 
v___x_5720_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_5721_ = lean_string_append(v_msg_5716_, v___x_5720_);
lean_inc_n(v___y_5711_, 2);
lean_inc_ref(v___y_5715_);
v___x_5722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5722_, 0, v___y_5715_);
lean_ctor_set(v___x_5722_, 1, v___y_5711_);
lean_ctor_set(v___x_5722_, 2, v___x_5718_);
v___x_5723_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5722_, v___x_5718_);
lean_dec_ref_known(v___x_5722_, 3);
v___x_5724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5724_, 0, v___y_5715_);
lean_ctor_set(v___x_5724_, 1, v___y_5711_);
lean_ctor_set(v___x_5724_, 2, v___x_5723_);
v___x_5725_ = l_String_Slice_toString(v___x_5724_);
lean_dec_ref_known(v___x_5724_, 3);
v___x_5726_ = lean_string_append(v___x_5721_, v___x_5725_);
lean_dec_ref(v___x_5725_);
v___y_5692_ = v___y_5711_;
v___y_5693_ = v___y_5712_;
v___y_5694_ = v___y_5713_;
v___y_5695_ = v___y_5714_;
v_msg_5696_ = v___x_5726_;
v___y_5697_ = v___y_5717_;
goto v___jp_5691_;
}
else
{
lean_dec_ref(v___y_5715_);
v___y_5692_ = v___y_5711_;
v___y_5693_ = v___y_5712_;
v___y_5694_ = v___y_5713_;
v___y_5695_ = v___y_5714_;
v_msg_5696_ = v_msg_5716_;
v___y_5697_ = v___y_5717_;
goto v___jp_5691_;
}
}
v___jp_5727_:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; 
v___x_5735_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
v___x_5736_ = lean_string_append(v_msg_5734_, v___x_5735_);
v___x_5737_ = lean_string_append(v___x_5736_, v_url_5673_);
lean_dec_ref(v_url_5673_);
v___x_5738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_5739_ = l_Lake_JsonObject_getJson_x3f(v___y_5731_, v___x_5738_);
lean_dec(v___y_5731_);
if (lean_obj_tag(v___x_5739_) == 0)
{
v___y_5711_ = v___y_5728_;
v___y_5712_ = v___y_5729_;
v___y_5713_ = v___y_5730_;
v___y_5714_ = v___y_5732_;
v___y_5715_ = v___y_5733_;
v_msg_5716_ = v___x_5737_;
v___y_5717_ = v___y_5677_;
goto v___jp_5710_;
}
else
{
lean_object* v_val_5740_; lean_object* v___x_5741_; 
v_val_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_val_5740_);
lean_dec_ref_known(v___x_5739_, 1);
v___x_5741_ = l_Lean_Json_getStr_x3f(v_val_5740_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_dec_ref_known(v___x_5741_, 1);
v___y_5711_ = v___y_5728_;
v___y_5712_ = v___y_5729_;
v___y_5713_ = v___y_5730_;
v___y_5714_ = v___y_5732_;
v___y_5715_ = v___y_5733_;
v_msg_5716_ = v___x_5737_;
v___y_5717_ = v___y_5677_;
goto v___jp_5710_;
}
else
{
lean_object* v_a_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref_known(v___x_5741_, 1);
v___x_5743_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_5744_ = lean_string_append(v___x_5737_, v___x_5743_);
v___x_5745_ = lean_string_append(v___x_5744_, v_a_5742_);
lean_dec(v_a_5742_);
v___y_5711_ = v___y_5728_;
v___y_5712_ = v___y_5729_;
v___y_5713_ = v___y_5730_;
v___y_5714_ = v___y_5732_;
v___y_5715_ = v___y_5733_;
v_msg_5716_ = v___x_5745_;
v___y_5717_ = v___y_5677_;
goto v___jp_5710_;
}
}
}
v___jp_5746_:
{
lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; uint8_t v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; uint8_t v___x_5768_; 
v___x_5752_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5753_ = lean_string_append(v___x_5752_, v_url_5673_);
lean_dec_ref(v_url_5673_);
v___x_5754_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_5755_ = lean_string_append(v___x_5753_, v___x_5754_);
v___x_5756_ = lean_string_append(v___x_5755_, v_a_5751_);
lean_dec_ref(v_a_5751_);
v___x_5757_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_5758_ = lean_string_append(v___x_5756_, v___x_5757_);
v___x_5759_ = lean_string_utf8_byte_size(v___y_5749_);
lean_inc(v___y_5747_);
v___x_5760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5760_, 0, v___y_5749_);
lean_ctor_set(v___x_5760_, 1, v___y_5747_);
lean_ctor_set(v___x_5760_, 2, v___x_5759_);
v___x_5761_ = l_String_Slice_trimAscii(v___x_5760_);
v___x_5762_ = l_String_Slice_toString(v___x_5761_);
lean_dec_ref(v___x_5761_);
v___x_5763_ = lean_string_append(v___x_5758_, v___x_5762_);
lean_dec_ref(v___x_5762_);
v___x_5764_ = 3;
v___x_5765_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5765_, 0, v___x_5763_);
lean_ctor_set_uint8(v___x_5765_, sizeof(void*)*1, v___x_5764_);
lean_inc_ref(v___y_5677_);
v___x_5766_ = lean_apply_2(v___y_5677_, v___x_5765_, lean_box(0));
v___x_5767_ = lean_string_utf8_byte_size(v___y_5750_);
v___x_5768_ = lean_nat_dec_eq(v___x_5767_, v___y_5747_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; uint8_t v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; 
v___x_5769_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
lean_inc(v___y_5747_);
lean_inc_ref(v___y_5750_);
v___x_5770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5770_, 0, v___y_5750_);
lean_ctor_set(v___x_5770_, 1, v___y_5747_);
lean_ctor_set(v___x_5770_, 2, v___x_5767_);
v___x_5771_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5770_, v___x_5767_);
lean_dec_ref_known(v___x_5770_, 3);
v___x_5772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5772_, 0, v___y_5750_);
lean_ctor_set(v___x_5772_, 1, v___y_5747_);
lean_ctor_set(v___x_5772_, 2, v___x_5771_);
v___x_5773_ = l_String_Slice_toString(v___x_5772_);
lean_dec_ref_known(v___x_5772_, 3);
v___x_5774_ = lean_string_append(v___x_5769_, v___x_5773_);
lean_dec_ref(v___x_5773_);
v___x_5775_ = 2;
v___x_5776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5776_, 0, v___x_5774_);
lean_ctor_set_uint8(v___x_5776_, sizeof(void*)*1, v___x_5775_);
lean_inc_ref(v___y_5677_);
v___x_5777_ = lean_apply_2(v___y_5677_, v___x_5776_, lean_box(0));
v___y_5680_ = v___y_5748_;
v___y_5681_ = v___y_5677_;
goto v___jp_5679_;
}
else
{
lean_dec_ref(v___y_5750_);
lean_dec(v___y_5747_);
v___y_5680_ = v___y_5748_;
v___y_5681_ = v___y_5677_;
goto v___jp_5679_;
}
}
v___jp_5778_:
{
lean_object* v___x_5784_; 
lean_inc_ref(v___y_5782_);
v___x_5784_ = l_Lean_Json_parse(v___y_5782_);
if (lean_obj_tag(v___x_5784_) == 0)
{
lean_object* v_a_5785_; 
v_a_5785_ = lean_ctor_get(v___x_5784_, 0);
lean_inc(v_a_5785_);
lean_dec_ref_known(v___x_5784_, 1);
v___y_5747_ = v___y_5779_;
v___y_5748_ = v___y_5781_;
v___y_5749_ = v___y_5782_;
v___y_5750_ = v___y_5783_;
v_a_5751_ = v_a_5785_;
goto v___jp_5746_;
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5787_; 
v_a_5786_ = lean_ctor_get(v___x_5784_, 0);
lean_inc(v_a_5786_);
lean_dec_ref_known(v___x_5784_, 1);
v___x_5787_ = l_Lean_Json_getObj_x3f(v_a_5786_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v_a_5788_; 
v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
lean_inc(v_a_5788_);
lean_dec_ref_known(v___x_5787_, 1);
v___y_5747_ = v___y_5779_;
v___y_5748_ = v___y_5781_;
v___y_5749_ = v___y_5782_;
v___y_5750_ = v___y_5783_;
v_a_5751_ = v_a_5788_;
goto v___jp_5746_;
}
else
{
lean_object* v_a_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; 
v_a_5789_ = lean_ctor_get(v___x_5787_, 0);
lean_inc(v_a_5789_);
lean_dec_ref_known(v___x_5787_, 1);
v___x_5790_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_5791_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_5792_ = l_Lake_JsonObject_getJson_x3f(v_a_5789_, v___x_5791_);
if (lean_obj_tag(v___x_5792_) == 0)
{
v___y_5728_ = v___y_5779_;
v___y_5729_ = v___y_5780_;
v___y_5730_ = v___y_5781_;
v___y_5731_ = v_a_5789_;
v___y_5732_ = v___y_5782_;
v___y_5733_ = v___y_5783_;
v_msg_5734_ = v___x_5790_;
goto v___jp_5727_;
}
else
{
lean_object* v_val_5793_; lean_object* v___x_5794_; 
v_val_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_val_5793_);
lean_dec_ref_known(v___x_5792_, 1);
v___x_5794_ = l_Lean_Json_getNat_x3f(v_val_5793_);
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_dec_ref_known(v___x_5794_, 1);
v___y_5728_ = v___y_5779_;
v___y_5729_ = v___y_5780_;
v___y_5730_ = v___y_5781_;
v___y_5731_ = v_a_5789_;
v___y_5732_ = v___y_5782_;
v___y_5733_ = v___y_5783_;
v_msg_5734_ = v___x_5790_;
goto v___jp_5727_;
}
else
{
lean_object* v_a_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v_a_5795_ = lean_ctor_get(v___x_5794_, 0);
lean_inc(v_a_5795_);
lean_dec_ref_known(v___x_5794_, 1);
v___x_5796_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5797_ = l_Nat_reprFast(v_a_5795_);
v___x_5798_ = lean_string_append(v___x_5796_, v___x_5797_);
lean_dec_ref(v___x_5797_);
v___x_5799_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_5800_ = lean_string_append(v___x_5798_, v___x_5799_);
v___y_5728_ = v___y_5779_;
v___y_5729_ = v___y_5780_;
v___y_5730_ = v___y_5781_;
v___y_5731_ = v_a_5789_;
v___y_5732_ = v___y_5782_;
v___y_5733_ = v___y_5783_;
v_msg_5734_ = v___x_5800_;
goto v___jp_5727_;
}
}
}
}
}
v___jp_5801_:
{
lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; uint8_t v___x_5809_; uint8_t v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; uint8_t v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; 
v___x_5804_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
lean_inc_ref(v_url_5673_);
v___x_5805_ = lean_array_push(v___y_5802_, v_url_5673_);
v___x_5806_ = lean_box(0);
v___x_5807_ = lean_unsigned_to_nat(0u);
v___x_5808_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5809_ = 1;
v___x_5810_ = 0;
v___x_5811_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5811_, 0, v___x_5804_);
lean_ctor_set(v___x_5811_, 1, v_a_5803_);
lean_ctor_set(v___x_5811_, 2, v___x_5805_);
lean_ctor_set(v___x_5811_, 3, v___x_5806_);
lean_ctor_set(v___x_5811_, 4, v___x_5808_);
lean_ctor_set_uint8(v___x_5811_, sizeof(void*)*5, v___x_5809_);
lean_ctor_set_uint8(v___x_5811_, sizeof(void*)*5 + 1, v___x_5810_);
lean_inc_ref(v___x_5811_);
v___x_5812_ = l_Lake_mkCmdLog(v___x_5811_);
v___x_5813_ = 0;
v___x_5814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5814_, 0, v___x_5812_);
lean_ctor_set_uint8(v___x_5814_, sizeof(void*)*1, v___x_5813_);
lean_inc_ref(v___y_5677_);
v___x_5815_ = lean_apply_2(v___y_5677_, v___x_5814_, lean_box(0));
v___x_5816_ = l_IO_Process_output(v___x_5811_, v___x_5806_);
if (lean_obj_tag(v___x_5816_) == 0)
{
lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5871_; 
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5819_ = v___x_5816_;
v_isShared_5820_ = v_isSharedCheck_5871_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5816_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5871_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
uint32_t v_exitCode_5821_; lean_object* v_stdout_5822_; lean_object* v_stderr_5823_; lean_object* v___x_5824_; 
v_exitCode_5821_ = lean_ctor_get_uint32(v_a_5817_, sizeof(void*)*2);
v_stdout_5822_ = lean_ctor_get(v_a_5817_, 0);
lean_inc_ref_n(v_stdout_5822_, 2);
v_stderr_5823_ = lean_ctor_get(v_a_5817_, 1);
lean_inc_ref(v_stderr_5823_);
lean_dec(v_a_5817_);
v___x_5824_ = l_Lean_Json_parse(v_stdout_5822_);
if (lean_obj_tag(v___x_5824_) == 0)
{
lean_dec_ref_known(v___x_5824_, 1);
lean_del_object(v___x_5819_);
lean_dec_ref(v_infos_5674_);
v___y_5779_ = v___x_5807_;
v___y_5780_ = v___x_5813_;
v___y_5781_ = v_exitCode_5821_;
v___y_5782_ = v_stderr_5823_;
v___y_5783_ = v_stdout_5822_;
goto v___jp_5778_;
}
else
{
lean_object* v_a_5825_; lean_object* v___x_5826_; 
v_a_5825_ = lean_ctor_get(v___x_5824_, 0);
lean_inc(v_a_5825_);
lean_dec_ref_known(v___x_5824_, 1);
v___x_5826_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_5825_);
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_dec_ref_known(v___x_5826_, 1);
lean_del_object(v___x_5819_);
lean_dec_ref(v_infos_5674_);
v___y_5779_ = v___x_5807_;
v___y_5780_ = v___x_5813_;
v___y_5781_ = v_exitCode_5821_;
v___y_5782_ = v_stderr_5823_;
v___y_5783_ = v_stdout_5822_;
goto v___jp_5778_;
}
else
{
lean_object* v_a_5827_; 
lean_dec_ref(v_stderr_5823_);
lean_dec_ref(v_stdout_5822_);
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
lean_inc(v_a_5827_);
lean_dec_ref_known(v___x_5826_, 1);
if (lean_obj_tag(v_a_5827_) == 0)
{
lean_object* v_a_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; uint8_t v___x_5831_; 
v_a_5828_ = lean_ctor_get(v_a_5827_, 0);
lean_inc(v_a_5828_);
lean_dec_ref_known(v_a_5827_, 1);
v___x_5829_ = lean_array_get_size(v_infos_5674_);
v___x_5830_ = lean_array_get_size(v_a_5828_);
v___x_5831_ = lean_nat_dec_eq(v___x_5829_, v___x_5830_);
if (v___x_5831_ == 0)
{
lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; uint8_t v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5847_; 
lean_dec(v_a_5828_);
lean_dec_ref(v_infos_5674_);
v___x_5832_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5833_ = lean_string_append(v___x_5832_, v_url_5673_);
lean_dec_ref(v_url_5673_);
v___x_5834_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_5835_ = lean_string_append(v___x_5833_, v___x_5834_);
v___x_5836_ = l_Nat_reprFast(v___x_5829_);
v___x_5837_ = lean_string_append(v___x_5835_, v___x_5836_);
lean_dec_ref(v___x_5836_);
v___x_5838_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_5839_ = lean_string_append(v___x_5837_, v___x_5838_);
v___x_5840_ = l_Nat_reprFast(v___x_5830_);
v___x_5841_ = lean_string_append(v___x_5839_, v___x_5840_);
lean_dec_ref(v___x_5840_);
v___x_5842_ = 3;
v___x_5843_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5843_, 0, v___x_5841_);
lean_ctor_set_uint8(v___x_5843_, sizeof(void*)*1, v___x_5842_);
lean_inc_ref(v___y_5677_);
v___x_5844_ = lean_apply_2(v___y_5677_, v___x_5843_, lean_box(0));
v___x_5845_ = lean_box(0);
if (v_isShared_5820_ == 0)
{
lean_ctor_set_tag(v___x_5819_, 1);
lean_ctor_set(v___x_5819_, 0, v___x_5845_);
v___x_5847_ = v___x_5819_;
goto v_reusejp_5846_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5845_);
v___x_5847_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5846_;
}
v_reusejp_5846_:
{
return v___x_5847_;
}
}
else
{
lean_object* v___x_5849_; lean_object* v___x_5851_; 
lean_dec_ref(v_url_5673_);
v___x_5849_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5828_, v___x_5829_, v___x_5829_, v_infos_5674_);
lean_dec(v_a_5828_);
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 0, v___x_5849_);
v___x_5851_ = v___x_5819_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5849_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
}
else
{
lean_object* v_status_5853_; lean_object* v_message_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; uint8_t v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5869_; 
lean_dec_ref(v_infos_5674_);
v_status_5853_ = lean_ctor_get(v_a_5827_, 0);
lean_inc(v_status_5853_);
v_message_5854_ = lean_ctor_get(v_a_5827_, 1);
lean_inc_ref(v_message_5854_);
lean_dec_ref_known(v_a_5827_, 2);
v___x_5855_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5856_ = l_Nat_reprFast(v_status_5853_);
v___x_5857_ = lean_string_append(v___x_5855_, v___x_5856_);
lean_dec_ref(v___x_5856_);
v___x_5858_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_5859_ = lean_string_append(v___x_5857_, v___x_5858_);
v___x_5860_ = lean_string_append(v___x_5859_, v_url_5673_);
lean_dec_ref(v_url_5673_);
v___x_5861_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_5862_ = lean_string_append(v___x_5860_, v___x_5861_);
v___x_5863_ = lean_string_append(v___x_5862_, v_message_5854_);
lean_dec_ref(v_message_5854_);
v___x_5864_ = 3;
v___x_5865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5865_, 0, v___x_5863_);
lean_ctor_set_uint8(v___x_5865_, sizeof(void*)*1, v___x_5864_);
lean_inc_ref(v___y_5677_);
v___x_5866_ = lean_apply_2(v___y_5677_, v___x_5865_, lean_box(0));
v___x_5867_ = lean_box(0);
if (v_isShared_5820_ == 0)
{
lean_ctor_set_tag(v___x_5819_, 1);
lean_ctor_set(v___x_5819_, 0, v___x_5867_);
v___x_5869_ = v___x_5819_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v___x_5867_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
}
}
}
}
}
}
else
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5884_; 
lean_dec_ref(v_infos_5674_);
lean_dec_ref(v_url_5673_);
v_a_5872_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5884_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5884_ == 0)
{
v___x_5874_ = v___x_5816_;
v_isShared_5875_ = v_isSharedCheck_5884_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___x_5816_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5884_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v___x_5876_; uint8_t v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5882_; 
v___x_5876_ = lean_io_error_to_string(v_a_5872_);
v___x_5877_ = 3;
v___x_5878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5878_, 0, v___x_5876_);
lean_ctor_set_uint8(v___x_5878_, sizeof(void*)*1, v___x_5877_);
lean_inc_ref(v___y_5677_);
v___x_5879_ = lean_apply_2(v___y_5677_, v___x_5878_, lean_box(0));
v___x_5880_ = lean_box(0);
if (v_isShared_5875_ == 0)
{
lean_ctor_set(v___x_5874_, 0, v___x_5880_);
v___x_5882_ = v___x_5874_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v___x_5880_);
v___x_5882_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
return v___x_5882_;
}
}
}
}
v___jp_5887_:
{
lean_object* v___x_5892_; uint8_t v___x_5893_; 
v___x_5892_ = lean_array_get_size(v___y_5889_);
v___x_5893_ = lean_nat_dec_lt(v___y_5890_, v___x_5892_);
if (v___x_5893_ == 0)
{
v___y_5802_ = v___y_5888_;
v_a_5803_ = v_val_5891_;
goto v___jp_5801_;
}
else
{
lean_object* v___x_5894_; size_t v___x_5895_; lean_object* v___x_5896_; 
v___x_5894_ = lean_box(0);
v___x_5895_ = lean_usize_of_nat(v___x_5892_);
v___x_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_5889_, v___x_5886_, v___x_5895_, v___x_5894_, v___y_5677_);
if (lean_obj_tag(v___x_5896_) == 0)
{
lean_dec_ref_known(v___x_5896_, 1);
v___y_5802_ = v___y_5888_;
v_a_5803_ = v_val_5891_;
goto v___jp_5801_;
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec_ref(v_val_5891_);
lean_dec_ref(v___y_5888_);
lean_dec_ref(v_infos_5674_);
lean_dec_ref(v_url_5673_);
v_a_5897_ = lean_ctor_get(v___x_5896_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5896_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5896_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5896_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed(lean_object* v_url_5966_, lean_object* v_infos_5967_, lean_object* v_h_5968_, lean_object* v_path_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_){
_start:
{
lean_object* v_res_5972_; 
v_res_5972_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(v_url_5966_, v_infos_5967_, v_h_5968_, v_path_5969_, v___y_5970_);
lean_dec_ref(v___y_5970_);
lean_dec_ref(v_path_5969_);
lean_dec(v_h_5968_);
return v_res_5972_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(lean_object* v_url_5973_, lean_object* v_infos_5974_, lean_object* v_a_5975_){
_start:
{
lean_object* v___f_5977_; lean_object* v___x_5978_; 
v___f_5977_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5977_, 0, v_url_5973_);
lean_closure_set(v___f_5977_, 1, v_infos_5974_);
v___x_5978_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5977_, v_a_5975_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___boxed(lean_object* v_url_5979_, lean_object* v_infos_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_){
_start:
{
lean_object* v_res_5983_; 
v_res_5983_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(v_url_5979_, v_infos_5980_, v_a_5981_);
lean_dec_ref(v_a_5981_);
return v_res_5983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(lean_object* v_a_5984_, lean_object* v___x_5985_, lean_object* v_n_5986_, lean_object* v_j_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5984_, v_n_5986_, v_j_5987_, v_a_5989_);
return v___x_5990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___boxed(lean_object* v_a_5991_, lean_object* v___x_5992_, lean_object* v_n_5993_, lean_object* v_j_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_){
_start:
{
lean_object* v_res_5997_; 
v_res_5997_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(v_a_5991_, v___x_5992_, v_n_5993_, v_j_5994_, v_a_5995_, v_a_5996_);
lean_dec(v_n_5993_);
lean_dec(v___x_5992_);
lean_dec_ref(v_a_5991_);
return v_res_5997_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object* v_cfg_5998_, lean_object* v_h_5999_, lean_object* v_path_6000_, lean_object* v___y_6001_){
_start:
{
uint32_t v___y_6007_; lean_object* v___y_6008_; lean_object* v___y_6009_; uint8_t v_kind_6018_; lean_object* v_scope_6019_; lean_object* v_infos_6020_; lean_object* v_key_6021_; uint32_t v___y_6023_; uint8_t v___y_6024_; lean_object* v___y_6025_; lean_object* v___y_6032_; uint32_t v___y_6033_; lean_object* v___y_6034_; uint8_t v___y_6035_; lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v___y_6038_; lean_object* v___y_6050_; uint32_t v___y_6051_; lean_object* v___y_6052_; uint8_t v_didError_6053_; lean_object* v___y_6054_; lean_object* v___y_6059_; uint8_t v___y_6060_; uint32_t v___y_6061_; lean_object* v___y_6062_; lean_object* v___y_6063_; lean_object* v___y_6064_; lean_object* v___y_6074_; uint8_t v___y_6075_; uint32_t v___y_6076_; lean_object* v___y_6077_; lean_object* v___y_6078_; lean_object* v___y_6081_; lean_object* v_a_6082_; lean_object* v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6160_; lean_object* v_val_6161_; lean_object* v_a_6169_; 
v_kind_6018_ = lean_ctor_get_uint8(v_cfg_5998_, sizeof(void*)*3);
v_scope_6019_ = lean_ctor_get(v_cfg_5998_, 0);
lean_inc_ref(v_scope_6019_);
v_infos_6020_ = lean_ctor_get(v_cfg_5998_, 1);
lean_inc_ref(v_infos_6020_);
v_key_6021_ = lean_ctor_get(v_cfg_5998_, 2);
if (v_kind_6018_ == 0)
{
lean_object* v___x_6223_; lean_object* v___x_6224_; uint8_t v___x_6225_; 
v___x_6223_ = lean_unsigned_to_nat(0u);
v___x_6224_ = lean_array_get_size(v_infos_6020_);
v___x_6225_ = lean_nat_dec_lt(v___x_6223_, v___x_6224_);
if (v___x_6225_ == 0)
{
goto v___jp_6176_;
}
else
{
lean_object* v___x_6226_; size_t v___x_6227_; size_t v___x_6228_; lean_object* v___x_6229_; 
v___x_6226_ = lean_box(0);
v___x_6227_ = ((size_t)0ULL);
v___x_6228_ = lean_usize_of_nat(v___x_6224_);
v___x_6229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5999_, v_infos_6020_, v___x_6227_, v___x_6228_, v___x_6226_, v___y_6001_);
if (lean_obj_tag(v___x_6229_) == 0)
{
lean_dec_ref_known(v___x_6229_, 1);
goto v___jp_6176_;
}
else
{
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
lean_dec_ref(v_path_6000_);
lean_dec_ref(v_cfg_5998_);
return v___x_6229_;
}
}
}
else
{
lean_object* v___x_6230_; lean_object* v___x_6231_; uint8_t v___x_6232_; 
v___x_6230_ = lean_unsigned_to_nat(0u);
v___x_6231_ = lean_array_get_size(v_infos_6020_);
v___x_6232_ = lean_nat_dec_lt(v___x_6230_, v___x_6231_);
if (v___x_6232_ == 0)
{
goto v___jp_6195_;
}
else
{
lean_object* v___x_6233_; size_t v___x_6234_; size_t v___x_6235_; lean_object* v___x_6236_; 
v___x_6233_ = lean_box(0);
v___x_6234_ = ((size_t)0ULL);
v___x_6235_ = lean_usize_of_nat(v___x_6231_);
v___x_6236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5999_, v_infos_6020_, v___x_6234_, v___x_6235_, v___x_6233_, v___y_6001_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_dec_ref_known(v___x_6236_, 1);
goto v___jp_6195_;
}
else
{
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
lean_dec_ref(v_path_6000_);
lean_dec_ref(v_cfg_5998_);
return v___x_6236_;
}
}
}
v___jp_6003_:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6004_ = lean_box(0);
v___x_6005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
return v___x_6005_;
}
v___jp_6006_:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; uint8_t v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6010_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_6011_ = lean_string_append(v___y_6009_, v___x_6010_);
v___x_6012_ = lean_uint32_to_nat(v___y_6007_);
v___x_6013_ = l_Nat_reprFast(v___x_6012_);
v___x_6014_ = lean_string_append(v___x_6011_, v___x_6013_);
lean_dec_ref(v___x_6013_);
v___x_6015_ = 3;
v___x_6016_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set_uint8(v___x_6016_, sizeof(void*)*1, v___x_6015_);
lean_inc_ref(v___y_6008_);
v___x_6017_ = lean_apply_2(v___y_6008_, v___x_6016_, lean_box(0));
goto v___jp_6003_;
}
v___jp_6022_:
{
uint32_t v___x_6026_; uint8_t v___x_6027_; 
v___x_6026_ = 0;
v___x_6027_ = lean_uint32_dec_eq(v___y_6023_, v___x_6026_);
if (v___x_6027_ == 0)
{
lean_object* v_s_6028_; 
v_s_6028_ = lean_ctor_get(v_scope_6019_, 0);
lean_inc_ref(v_s_6028_);
lean_dec_ref(v_scope_6019_);
v___y_6007_ = v___y_6023_;
v___y_6008_ = v___y_6025_;
v___y_6009_ = v_s_6028_;
goto v___jp_6006_;
}
else
{
lean_dec_ref(v_scope_6019_);
if (v___y_6024_ == 0)
{
lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6029_ = lean_box(0);
v___x_6030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
return v___x_6030_;
}
else
{
goto v___jp_6003_;
}
}
}
v___jp_6031_:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; uint8_t v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; 
v___x_6039_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_6040_ = lean_string_append(v___y_6038_, v___x_6039_);
lean_inc(v___y_6037_);
lean_inc(v___y_6032_);
lean_inc_ref(v___y_6036_);
v___x_6041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6041_, 0, v___y_6036_);
lean_ctor_set(v___x_6041_, 1, v___y_6032_);
lean_ctor_set(v___x_6041_, 2, v___y_6037_);
v___x_6042_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_6041_, v___y_6037_);
lean_dec_ref_known(v___x_6041_, 3);
v___x_6043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6043_, 0, v___y_6036_);
lean_ctor_set(v___x_6043_, 1, v___y_6032_);
lean_ctor_set(v___x_6043_, 2, v___x_6042_);
v___x_6044_ = l_String_Slice_toString(v___x_6043_);
lean_dec_ref_known(v___x_6043_, 3);
v___x_6045_ = lean_string_append(v___x_6040_, v___x_6044_);
lean_dec_ref(v___x_6044_);
v___x_6046_ = 2;
v___x_6047_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6047_, 0, v___x_6045_);
lean_ctor_set_uint8(v___x_6047_, sizeof(void*)*1, v___x_6046_);
lean_inc_ref(v___y_6034_);
v___x_6048_ = lean_apply_2(v___y_6034_, v___x_6047_, lean_box(0));
v___y_6023_ = v___y_6033_;
v___y_6024_ = v___y_6035_;
v___y_6025_ = v___y_6034_;
goto v___jp_6022_;
}
v___jp_6049_:
{
lean_object* v___x_6055_; uint8_t v___x_6056_; 
v___x_6055_ = lean_string_utf8_byte_size(v___y_6052_);
v___x_6056_ = lean_nat_dec_eq(v___x_6055_, v___y_6050_);
if (v___x_6056_ == 0)
{
lean_object* v_s_6057_; 
v_s_6057_ = lean_ctor_get(v_scope_6019_, 0);
lean_inc_ref(v_s_6057_);
v___y_6032_ = v___y_6050_;
v___y_6033_ = v___y_6051_;
v___y_6034_ = v___y_6054_;
v___y_6035_ = v_didError_6053_;
v___y_6036_ = v___y_6052_;
v___y_6037_ = v___x_6055_;
v___y_6038_ = v_s_6057_;
goto v___jp_6031_;
}
else
{
lean_dec_ref(v___y_6052_);
lean_dec(v___y_6050_);
v___y_6023_ = v___y_6051_;
v___y_6024_ = v_didError_6053_;
v___y_6025_ = v___y_6054_;
goto v___jp_6022_;
}
}
v___jp_6058_:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; uint8_t v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6065_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_6066_ = lean_string_append(v___y_6064_, v___x_6065_);
v___x_6067_ = lean_string_append(v___x_6066_, v___y_6063_);
v___x_6068_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_6069_ = lean_string_append(v___x_6067_, v___x_6068_);
v___x_6070_ = 3;
v___x_6071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6071_, 0, v___x_6069_);
lean_ctor_set_uint8(v___x_6071_, sizeof(void*)*1, v___x_6070_);
lean_inc_ref(v___y_6001_);
v___x_6072_ = lean_apply_2(v___y_6001_, v___x_6071_, lean_box(0));
v___y_6050_ = v___y_6059_;
v___y_6051_ = v___y_6061_;
v___y_6052_ = v___y_6062_;
v_didError_6053_ = v___y_6060_;
v___y_6054_ = v___y_6001_;
goto v___jp_6049_;
}
v___jp_6073_:
{
lean_object* v_s_6079_; 
v_s_6079_ = lean_ctor_get(v_scope_6019_, 0);
lean_inc_ref(v_s_6079_);
v___y_6059_ = v___y_6074_;
v___y_6060_ = v___y_6075_;
v___y_6061_ = v___y_6076_;
v___y_6062_ = v___y_6077_;
v___y_6063_ = v___y_6078_;
v___y_6064_ = v_s_6079_;
goto v___jp_6058_;
}
v___jp_6080_:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; uint8_t v___x_6087_; uint8_t v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6083_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_6084_ = lean_box(0);
v___x_6085_ = lean_unsigned_to_nat(0u);
v___x_6086_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_6087_ = 1;
v___x_6088_ = 0;
v___x_6089_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_6089_, 0, v___x_6083_);
lean_ctor_set(v___x_6089_, 1, v_a_6082_);
lean_ctor_set(v___x_6089_, 2, v___y_6081_);
lean_ctor_set(v___x_6089_, 3, v___x_6084_);
lean_ctor_set(v___x_6089_, 4, v___x_6086_);
lean_ctor_set_uint8(v___x_6089_, sizeof(void*)*5, v___x_6087_);
lean_ctor_set_uint8(v___x_6089_, sizeof(void*)*5 + 1, v___x_6088_);
v___x_6090_ = lean_io_process_spawn(v___x_6089_);
if (lean_obj_tag(v___x_6090_) == 0)
{
lean_object* v_a_6091_; lean_object* v_stdout_6092_; lean_object* v_stderr_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; 
v_a_6091_ = lean_ctor_get(v___x_6090_, 0);
lean_inc(v_a_6091_);
lean_dec_ref_known(v___x_6090_, 1);
v_stdout_6092_ = lean_ctor_get(v_a_6091_, 1);
lean_inc_n(v_stdout_6092_, 2);
v_stderr_6093_ = lean_ctor_get(v_a_6091_, 2);
v___x_6094_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_6095_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_5998_, v_stderr_6093_, v_stdout_6092_, v___x_6094_, v___y_6001_);
if (lean_obj_tag(v___x_6095_) == 0)
{
lean_object* v_a_6096_; lean_object* v___x_6097_; 
v_a_6096_ = lean_ctor_get(v___x_6095_, 0);
lean_inc(v_a_6096_);
lean_dec_ref_known(v___x_6095_, 1);
v___x_6097_ = lean_io_process_child_wait(v___x_6083_, v_a_6091_);
lean_dec(v_a_6091_);
if (lean_obj_tag(v___x_6097_) == 0)
{
lean_object* v_a_6098_; lean_object* v___x_6099_; 
v_a_6098_ = lean_ctor_get(v___x_6097_, 0);
lean_inc(v_a_6098_);
lean_dec_ref_known(v___x_6097_, 1);
v___x_6099_ = l_IO_FS_Handle_readToEnd(v_stdout_6092_);
lean_dec(v_stdout_6092_);
if (lean_obj_tag(v___x_6099_) == 0)
{
lean_object* v_a_6100_; uint8_t v_didError_6101_; lean_object* v_numSuccesses_6102_; lean_object* v___x_6103_; uint8_t v___x_6104_; 
v_a_6100_ = lean_ctor_get(v___x_6099_, 0);
lean_inc(v_a_6100_);
lean_dec_ref_known(v___x_6099_, 1);
v_didError_6101_ = lean_ctor_get_uint8(v_a_6096_, sizeof(void*)*1);
v_numSuccesses_6102_ = lean_ctor_get(v_a_6096_, 0);
lean_inc(v_numSuccesses_6102_);
lean_dec(v_a_6096_);
v___x_6103_ = lean_array_get_size(v_infos_6020_);
lean_dec_ref(v_infos_6020_);
v___x_6104_ = lean_nat_dec_lt(v_numSuccesses_6102_, v___x_6103_);
lean_dec(v_numSuccesses_6102_);
if (v___x_6104_ == 0)
{
uint32_t v___x_6105_; 
v___x_6105_ = lean_unbox_uint32(v_a_6098_);
lean_dec(v_a_6098_);
v___y_6050_ = v___x_6085_;
v___y_6051_ = v___x_6105_;
v___y_6052_ = v_a_6100_;
v_didError_6053_ = v_didError_6101_;
v___y_6054_ = v___y_6001_;
goto v___jp_6049_;
}
else
{
if (v_kind_6018_ == 0)
{
lean_object* v___x_6106_; uint32_t v___x_6107_; 
v___x_6106_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_6107_ = lean_unbox_uint32(v_a_6098_);
lean_dec(v_a_6098_);
v___y_6074_ = v___x_6085_;
v___y_6075_ = v___x_6087_;
v___y_6076_ = v___x_6107_;
v___y_6077_ = v_a_6100_;
v___y_6078_ = v___x_6106_;
goto v___jp_6073_;
}
else
{
lean_object* v___x_6108_; uint32_t v___x_6109_; 
v___x_6108_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_6109_ = lean_unbox_uint32(v_a_6098_);
lean_dec(v_a_6098_);
v___y_6074_ = v___x_6085_;
v___y_6075_ = v___x_6087_;
v___y_6076_ = v___x_6109_;
v___y_6077_ = v_a_6100_;
v___y_6078_ = v___x_6108_;
goto v___jp_6073_;
}
}
}
else
{
lean_object* v_a_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6122_; 
lean_dec(v_a_6098_);
lean_dec(v_a_6096_);
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
v_a_6110_ = lean_ctor_get(v___x_6099_, 0);
v_isSharedCheck_6122_ = !lean_is_exclusive(v___x_6099_);
if (v_isSharedCheck_6122_ == 0)
{
v___x_6112_ = v___x_6099_;
v_isShared_6113_ = v_isSharedCheck_6122_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_a_6110_);
lean_dec(v___x_6099_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6122_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6114_; uint8_t v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6120_; 
v___x_6114_ = lean_io_error_to_string(v_a_6110_);
v___x_6115_ = 3;
v___x_6116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set_uint8(v___x_6116_, sizeof(void*)*1, v___x_6115_);
lean_inc_ref(v___y_6001_);
v___x_6117_ = lean_apply_2(v___y_6001_, v___x_6116_, lean_box(0));
v___x_6118_ = lean_box(0);
if (v_isShared_6113_ == 0)
{
lean_ctor_set(v___x_6112_, 0, v___x_6118_);
v___x_6120_ = v___x_6112_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6118_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
}
else
{
lean_object* v_a_6123_; lean_object* v___x_6125_; uint8_t v_isShared_6126_; uint8_t v_isSharedCheck_6135_; 
lean_dec(v_a_6096_);
lean_dec(v_stdout_6092_);
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
v_a_6123_ = lean_ctor_get(v___x_6097_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v___x_6097_);
if (v_isSharedCheck_6135_ == 0)
{
v___x_6125_ = v___x_6097_;
v_isShared_6126_ = v_isSharedCheck_6135_;
goto v_resetjp_6124_;
}
else
{
lean_inc(v_a_6123_);
lean_dec(v___x_6097_);
v___x_6125_ = lean_box(0);
v_isShared_6126_ = v_isSharedCheck_6135_;
goto v_resetjp_6124_;
}
v_resetjp_6124_:
{
lean_object* v___x_6127_; uint8_t v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6133_; 
v___x_6127_ = lean_io_error_to_string(v_a_6123_);
v___x_6128_ = 3;
v___x_6129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6129_, 0, v___x_6127_);
lean_ctor_set_uint8(v___x_6129_, sizeof(void*)*1, v___x_6128_);
lean_inc_ref(v___y_6001_);
v___x_6130_ = lean_apply_2(v___y_6001_, v___x_6129_, lean_box(0));
v___x_6131_ = lean_box(0);
if (v_isShared_6126_ == 0)
{
lean_ctor_set(v___x_6125_, 0, v___x_6131_);
v___x_6133_ = v___x_6125_;
goto v_reusejp_6132_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v___x_6131_);
v___x_6133_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6132_;
}
v_reusejp_6132_:
{
return v___x_6133_;
}
}
}
}
else
{
lean_object* v_a_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6143_; 
lean_dec(v_stdout_6092_);
lean_dec(v_a_6091_);
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
v_a_6136_ = lean_ctor_get(v___x_6095_, 0);
v_isSharedCheck_6143_ = !lean_is_exclusive(v___x_6095_);
if (v_isSharedCheck_6143_ == 0)
{
v___x_6138_ = v___x_6095_;
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_a_6136_);
lean_dec(v___x_6095_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
lean_object* v___x_6141_; 
if (v_isShared_6139_ == 0)
{
v___x_6141_ = v___x_6138_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6142_; 
v_reuseFailAlloc_6142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
v___x_6141_ = v_reuseFailAlloc_6142_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
return v___x_6141_;
}
}
}
}
else
{
lean_object* v_a_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6156_; 
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
lean_dec_ref(v_cfg_5998_);
v_a_6144_ = lean_ctor_get(v___x_6090_, 0);
v_isSharedCheck_6156_ = !lean_is_exclusive(v___x_6090_);
if (v_isSharedCheck_6156_ == 0)
{
v___x_6146_ = v___x_6090_;
v_isShared_6147_ = v_isSharedCheck_6156_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_a_6144_);
lean_dec(v___x_6090_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6156_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
lean_object* v___x_6148_; uint8_t v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6154_; 
v___x_6148_ = lean_io_error_to_string(v_a_6144_);
v___x_6149_ = 3;
v___x_6150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set_uint8(v___x_6150_, sizeof(void*)*1, v___x_6149_);
lean_inc_ref(v___y_6001_);
v___x_6151_ = lean_apply_2(v___y_6001_, v___x_6150_, lean_box(0));
v___x_6152_ = lean_box(0);
if (v_isShared_6147_ == 0)
{
lean_ctor_set(v___x_6146_, 0, v___x_6152_);
v___x_6154_ = v___x_6146_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6152_);
v___x_6154_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
return v___x_6154_;
}
}
}
}
v___jp_6157_:
{
lean_object* v___x_6162_; uint8_t v___x_6163_; 
v___x_6162_ = lean_array_get_size(v___y_6160_);
v___x_6163_ = lean_nat_dec_lt(v___y_6159_, v___x_6162_);
if (v___x_6163_ == 0)
{
v___y_6081_ = v___y_6158_;
v_a_6082_ = v_val_6161_;
goto v___jp_6080_;
}
else
{
lean_object* v___x_6164_; size_t v___x_6165_; size_t v___x_6166_; lean_object* v___x_6167_; 
v___x_6164_ = lean_box(0);
v___x_6165_ = ((size_t)0ULL);
v___x_6166_ = lean_usize_of_nat(v___x_6162_);
v___x_6167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_6160_, v___x_6165_, v___x_6166_, v___x_6164_, v___y_6001_);
if (lean_obj_tag(v___x_6167_) == 0)
{
lean_dec_ref_known(v___x_6167_, 1);
v___y_6081_ = v___y_6158_;
v_a_6082_ = v_val_6161_;
goto v___jp_6080_;
}
else
{
lean_dec_ref(v_val_6161_);
lean_dec_ref(v___y_6158_);
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
lean_dec_ref(v_cfg_5998_);
return v___x_6167_;
}
}
}
v___jp_6168_:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6170_ = lean_unsigned_to_nat(0u);
v___x_6171_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_6172_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31));
v___x_6173_ = lean_io_getenv(v___x_6172_);
if (lean_obj_tag(v___x_6173_) == 0)
{
lean_object* v___x_6174_; 
v___x_6174_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32));
v___y_6158_ = v_a_6169_;
v___y_6159_ = v___x_6170_;
v___y_6160_ = v___x_6171_;
v_val_6161_ = v___x_6174_;
goto v___jp_6157_;
}
else
{
lean_object* v_val_6175_; 
v_val_6175_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_val_6175_);
lean_dec_ref_known(v___x_6173_, 1);
v___y_6158_ = v_a_6169_;
v___y_6159_ = v___x_6170_;
v___y_6160_ = v___x_6171_;
v_val_6161_ = v_val_6175_;
goto v___jp_6157_;
}
}
v___jp_6176_:
{
lean_object* v___x_6177_; 
v___x_6177_ = lean_io_prim_handle_flush(v_h_5999_);
if (lean_obj_tag(v___x_6177_) == 0)
{
lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
lean_dec_ref_known(v___x_6177_, 1);
v___x_6178_ = lean_unsigned_to_nat(11u);
v___x_6179_ = lean_mk_empty_array_with_capacity(v___x_6178_);
lean_dec_ref(v___x_6179_);
v___x_6180_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_6181_ = lean_array_push(v___x_6180_, v_path_6000_);
v_a_6169_ = v___x_6181_;
goto v___jp_6168_;
}
else
{
lean_object* v_a_6182_; lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6194_; 
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
lean_dec_ref(v_path_6000_);
lean_dec_ref(v_cfg_5998_);
v_a_6182_ = lean_ctor_get(v___x_6177_, 0);
v_isSharedCheck_6194_ = !lean_is_exclusive(v___x_6177_);
if (v_isSharedCheck_6194_ == 0)
{
v___x_6184_ = v___x_6177_;
v_isShared_6185_ = v_isSharedCheck_6194_;
goto v_resetjp_6183_;
}
else
{
lean_inc(v_a_6182_);
lean_dec(v___x_6177_);
v___x_6184_ = lean_box(0);
v_isShared_6185_ = v_isSharedCheck_6194_;
goto v_resetjp_6183_;
}
v_resetjp_6183_:
{
lean_object* v___x_6186_; uint8_t v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6192_; 
v___x_6186_ = lean_io_error_to_string(v_a_6182_);
v___x_6187_ = 3;
v___x_6188_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*1, v___x_6187_);
lean_inc_ref(v___y_6001_);
v___x_6189_ = lean_apply_2(v___y_6001_, v___x_6188_, lean_box(0));
v___x_6190_ = lean_box(0);
if (v_isShared_6185_ == 0)
{
lean_ctor_set(v___x_6184_, 0, v___x_6190_);
v___x_6192_ = v___x_6184_;
goto v_reusejp_6191_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6190_);
v___x_6192_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6191_;
}
v_reusejp_6191_:
{
return v___x_6192_;
}
}
}
}
v___jp_6195_:
{
lean_object* v___x_6196_; 
v___x_6196_ = lean_io_prim_handle_flush(v_h_5999_);
if (lean_obj_tag(v___x_6196_) == 0)
{
lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
lean_dec_ref_known(v___x_6196_, 1);
v___x_6197_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_6198_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_6199_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_6200_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_6201_ = lean_unsigned_to_nat(17u);
v___x_6202_ = lean_mk_empty_array_with_capacity(v___x_6201_);
lean_dec_ref(v___x_6202_);
v___x_6203_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_6021_);
v___x_6204_ = lean_array_push(v___x_6203_, v_key_6021_);
v___x_6205_ = lean_array_push(v___x_6204_, v___x_6197_);
v___x_6206_ = lean_array_push(v___x_6205_, v___x_6198_);
v___x_6207_ = lean_array_push(v___x_6206_, v___x_6199_);
v___x_6208_ = lean_array_push(v___x_6207_, v___x_6200_);
v___x_6209_ = lean_array_push(v___x_6208_, v_path_6000_);
v_a_6169_ = v___x_6209_;
goto v___jp_6168_;
}
else
{
lean_object* v_a_6210_; lean_object* v___x_6212_; uint8_t v_isShared_6213_; uint8_t v_isSharedCheck_6222_; 
lean_dec_ref(v_infos_6020_);
lean_dec_ref(v_scope_6019_);
lean_dec_ref(v_path_6000_);
lean_dec_ref(v_cfg_5998_);
v_a_6210_ = lean_ctor_get(v___x_6196_, 0);
v_isSharedCheck_6222_ = !lean_is_exclusive(v___x_6196_);
if (v_isSharedCheck_6222_ == 0)
{
v___x_6212_ = v___x_6196_;
v_isShared_6213_ = v_isSharedCheck_6222_;
goto v_resetjp_6211_;
}
else
{
lean_inc(v_a_6210_);
lean_dec(v___x_6196_);
v___x_6212_ = lean_box(0);
v_isShared_6213_ = v_isSharedCheck_6222_;
goto v_resetjp_6211_;
}
v_resetjp_6211_:
{
lean_object* v___x_6214_; uint8_t v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6220_; 
v___x_6214_ = lean_io_error_to_string(v_a_6210_);
v___x_6215_ = 3;
v___x_6216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6216_, 0, v___x_6214_);
lean_ctor_set_uint8(v___x_6216_, sizeof(void*)*1, v___x_6215_);
lean_inc_ref(v___y_6001_);
v___x_6217_ = lean_apply_2(v___y_6001_, v___x_6216_, lean_box(0));
v___x_6218_ = lean_box(0);
if (v_isShared_6213_ == 0)
{
lean_ctor_set(v___x_6212_, 0, v___x_6218_);
v___x_6220_ = v___x_6212_;
goto v_reusejp_6219_;
}
else
{
lean_object* v_reuseFailAlloc_6221_; 
v_reuseFailAlloc_6221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6221_, 0, v___x_6218_);
v___x_6220_ = v_reuseFailAlloc_6221_;
goto v_reusejp_6219_;
}
v_reusejp_6219_:
{
return v___x_6220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object* v_cfg_6237_, lean_object* v_h_6238_, lean_object* v_path_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_){
_start:
{
lean_object* v_res_6242_; 
v_res_6242_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(v_cfg_6237_, v_h_6238_, v_path_6239_, v___y_6240_);
lean_dec_ref(v___y_6240_);
lean_dec(v_h_6238_);
return v_res_6242_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object* v_a_6243_, lean_object* v_cfg_6244_){
_start:
{
lean_object* v___f_6246_; lean_object* v___x_6247_; 
v___f_6246_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6246_, 0, v_cfg_6244_);
v___x_6247_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_6246_, v_a_6243_);
return v___x_6247_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object* v_a_6248_, lean_object* v_cfg_6249_, lean_object* v_a_6250_){
_start:
{
lean_object* v_res_6251_; 
v_res_6251_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6248_, v_cfg_6249_);
lean_dec_ref(v_a_6248_);
return v_res_6251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(lean_object* v_url_6252_, lean_object* v_infos_6253_, lean_object* v_h_6254_, lean_object* v_path_6255_, lean_object* v___y_6256_){
_start:
{
uint32_t v___y_6259_; lean_object* v___y_6260_; lean_object* v___y_6271_; uint8_t v___y_6272_; uint32_t v___y_6273_; lean_object* v___y_6274_; lean_object* v_msg_6275_; lean_object* v___y_6276_; lean_object* v___y_6290_; lean_object* v___y_6291_; uint8_t v___y_6292_; uint32_t v___y_6293_; lean_object* v___y_6294_; lean_object* v_msg_6295_; lean_object* v___y_6296_; lean_object* v___y_6307_; lean_object* v___y_6308_; uint8_t v___y_6309_; lean_object* v___y_6310_; uint32_t v___y_6311_; lean_object* v___y_6312_; lean_object* v_msg_6313_; lean_object* v___y_6326_; lean_object* v___y_6327_; uint32_t v___y_6328_; lean_object* v___y_6329_; lean_object* v_a_6330_; lean_object* v___y_6358_; lean_object* v___y_6359_; uint8_t v___y_6360_; uint32_t v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6381_; lean_object* v_a_6382_; size_t v_sz_6464_; size_t v___x_6465_; lean_object* v___y_6467_; lean_object* v___y_6468_; lean_object* v___y_6469_; lean_object* v_val_6470_; lean_object* v___x_6484_; lean_object* v_body_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; 
v_sz_6464_ = lean_array_size(v_infos_6253_);
v___x_6465_ = ((size_t)0ULL);
lean_inc_ref(v_infos_6253_);
v___x_6484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_6464_, v___x_6465_, v_infos_6253_);
v_body_6485_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_6485_, 0, v___x_6484_);
v___x_6486_ = l_Lean_Json_compress(v_body_6485_);
v___x_6487_ = lean_io_prim_handle_put_str(v_h_6254_, v___x_6486_);
lean_dec_ref(v___x_6486_);
if (lean_obj_tag(v___x_6487_) == 0)
{
lean_object* v___x_6488_; 
lean_dec_ref_known(v___x_6487_, 1);
v___x_6488_ = lean_io_prim_handle_flush(v_h_6254_);
if (lean_obj_tag(v___x_6488_) == 0)
{
lean_object* v___y_6490_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; uint8_t v___x_6518_; 
lean_dec_ref_known(v___x_6488_, 1);
v___x_6497_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_6498_ = lean_string_append(v___x_6497_, v_path_6255_);
v___x_6499_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_6500_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_6501_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_6502_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_6503_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_6504_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_6505_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_6506_ = lean_unsigned_to_nat(12u);
v___x_6507_ = lean_mk_empty_array_with_capacity(v___x_6506_);
lean_dec_ref(v___x_6507_);
v___x_6508_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_6509_ = lean_array_push(v___x_6508_, v___x_6498_);
v___x_6510_ = lean_array_push(v___x_6509_, v___x_6499_);
v___x_6511_ = lean_array_push(v___x_6510_, v___x_6500_);
v___x_6512_ = lean_array_push(v___x_6511_, v___x_6501_);
v___x_6513_ = lean_array_push(v___x_6512_, v___x_6502_);
v___x_6514_ = lean_array_push(v___x_6513_, v___x_6503_);
v___x_6515_ = lean_array_push(v___x_6514_, v___x_6504_);
v___x_6516_ = lean_array_push(v___x_6515_, v___x_6505_);
v___x_6517_ = l_Lake_Reservoir_lakeHeaders;
v___x_6518_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_6518_ == 0)
{
v___y_6490_ = v___x_6516_;
goto v___jp_6489_;
}
else
{
size_t v___x_6519_; lean_object* v___x_6520_; 
v___x_6519_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
v___x_6520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_6517_, v___x_6465_, v___x_6519_, v___x_6516_);
v___y_6490_ = v___x_6520_;
goto v___jp_6489_;
}
v___jp_6489_:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6491_ = lean_unsigned_to_nat(0u);
v___x_6492_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_6493_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__31));
v___x_6494_ = lean_io_getenv(v___x_6493_);
if (lean_obj_tag(v___x_6494_) == 0)
{
lean_object* v___x_6495_; 
v___x_6495_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__32));
v___y_6467_ = v___y_6490_;
v___y_6468_ = v___x_6491_;
v___y_6469_ = v___x_6492_;
v_val_6470_ = v___x_6495_;
goto v___jp_6466_;
}
else
{
lean_object* v_val_6496_; 
v_val_6496_ = lean_ctor_get(v___x_6494_, 0);
lean_inc(v_val_6496_);
lean_dec_ref_known(v___x_6494_, 1);
v___y_6467_ = v___y_6490_;
v___y_6468_ = v___x_6491_;
v___y_6469_ = v___x_6492_;
v_val_6470_ = v_val_6496_;
goto v___jp_6466_;
}
}
}
else
{
lean_object* v_a_6521_; lean_object* v___x_6523_; uint8_t v_isShared_6524_; uint8_t v_isSharedCheck_6533_; 
lean_dec_ref(v_infos_6253_);
lean_dec_ref(v_url_6252_);
v_a_6521_ = lean_ctor_get(v___x_6488_, 0);
v_isSharedCheck_6533_ = !lean_is_exclusive(v___x_6488_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6523_ = v___x_6488_;
v_isShared_6524_ = v_isSharedCheck_6533_;
goto v_resetjp_6522_;
}
else
{
lean_inc(v_a_6521_);
lean_dec(v___x_6488_);
v___x_6523_ = lean_box(0);
v_isShared_6524_ = v_isSharedCheck_6533_;
goto v_resetjp_6522_;
}
v_resetjp_6522_:
{
lean_object* v___x_6525_; uint8_t v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6531_; 
v___x_6525_ = lean_io_error_to_string(v_a_6521_);
v___x_6526_ = 3;
v___x_6527_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6527_, 0, v___x_6525_);
lean_ctor_set_uint8(v___x_6527_, sizeof(void*)*1, v___x_6526_);
lean_inc_ref(v___y_6256_);
v___x_6528_ = lean_apply_2(v___y_6256_, v___x_6527_, lean_box(0));
v___x_6529_ = lean_box(0);
if (v_isShared_6524_ == 0)
{
lean_ctor_set(v___x_6523_, 0, v___x_6529_);
v___x_6531_ = v___x_6523_;
goto v_reusejp_6530_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v___x_6529_);
v___x_6531_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6530_;
}
v_reusejp_6530_:
{
return v___x_6531_;
}
}
}
}
else
{
lean_object* v_a_6534_; lean_object* v___x_6536_; uint8_t v_isShared_6537_; uint8_t v_isSharedCheck_6546_; 
lean_dec_ref(v_infos_6253_);
lean_dec_ref(v_url_6252_);
v_a_6534_ = lean_ctor_get(v___x_6487_, 0);
v_isSharedCheck_6546_ = !lean_is_exclusive(v___x_6487_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6536_ = v___x_6487_;
v_isShared_6537_ = v_isSharedCheck_6546_;
goto v_resetjp_6535_;
}
else
{
lean_inc(v_a_6534_);
lean_dec(v___x_6487_);
v___x_6536_ = lean_box(0);
v_isShared_6537_ = v_isSharedCheck_6546_;
goto v_resetjp_6535_;
}
v_resetjp_6535_:
{
lean_object* v___x_6538_; uint8_t v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6544_; 
v___x_6538_ = lean_io_error_to_string(v_a_6534_);
v___x_6539_ = 3;
v___x_6540_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6540_, 0, v___x_6538_);
lean_ctor_set_uint8(v___x_6540_, sizeof(void*)*1, v___x_6539_);
lean_inc_ref(v___y_6256_);
v___x_6541_ = lean_apply_2(v___y_6256_, v___x_6540_, lean_box(0));
v___x_6542_ = lean_box(0);
if (v_isShared_6537_ == 0)
{
lean_ctor_set(v___x_6536_, 0, v___x_6542_);
v___x_6544_ = v___x_6536_;
goto v_reusejp_6543_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v___x_6542_);
v___x_6544_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6543_;
}
v_reusejp_6543_:
{
return v___x_6544_;
}
}
}
v___jp_6258_:
{
lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; uint8_t v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; 
v___x_6261_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_6262_ = lean_uint32_to_nat(v___y_6259_);
v___x_6263_ = l_Nat_reprFast(v___x_6262_);
v___x_6264_ = lean_string_append(v___x_6261_, v___x_6263_);
lean_dec_ref(v___x_6263_);
v___x_6265_ = 3;
v___x_6266_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6266_, 0, v___x_6264_);
lean_ctor_set_uint8(v___x_6266_, sizeof(void*)*1, v___x_6265_);
lean_inc_ref(v___y_6260_);
v___x_6267_ = lean_apply_2(v___y_6260_, v___x_6266_, lean_box(0));
v___x_6268_ = lean_box(0);
v___x_6269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6269_, 0, v___x_6268_);
return v___x_6269_;
}
v___jp_6270_:
{
uint8_t v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; 
v___x_6277_ = 3;
v___x_6278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6278_, 0, v_msg_6275_);
lean_ctor_set_uint8(v___x_6278_, sizeof(void*)*1, v___x_6277_);
lean_inc_ref_n(v___y_6276_, 2);
v___x_6279_ = lean_apply_2(v___y_6276_, v___x_6278_, lean_box(0));
v___x_6280_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_6281_ = lean_string_utf8_byte_size(v___y_6271_);
lean_inc(v___y_6274_);
lean_inc_ref(v___y_6271_);
v___x_6282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6282_, 0, v___y_6271_);
lean_ctor_set(v___x_6282_, 1, v___y_6274_);
lean_ctor_set(v___x_6282_, 2, v___x_6281_);
v___x_6283_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_6282_, v___x_6281_);
lean_dec_ref_known(v___x_6282_, 3);
v___x_6284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6284_, 0, v___y_6271_);
lean_ctor_set(v___x_6284_, 1, v___y_6274_);
lean_ctor_set(v___x_6284_, 2, v___x_6283_);
v___x_6285_ = l_String_Slice_toString(v___x_6284_);
lean_dec_ref_known(v___x_6284_, 3);
v___x_6286_ = lean_string_append(v___x_6280_, v___x_6285_);
lean_dec_ref(v___x_6285_);
v___x_6287_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6287_, 0, v___x_6286_);
lean_ctor_set_uint8(v___x_6287_, sizeof(void*)*1, v___y_6272_);
v___x_6288_ = lean_apply_2(v___y_6276_, v___x_6287_, lean_box(0));
v___y_6259_ = v___y_6273_;
v___y_6260_ = v___y_6276_;
goto v___jp_6258_;
}
v___jp_6289_:
{
lean_object* v___x_6297_; uint8_t v___x_6298_; 
v___x_6297_ = lean_string_utf8_byte_size(v___y_6290_);
v___x_6298_ = lean_nat_dec_eq(v___x_6297_, v___y_6294_);
if (v___x_6298_ == 0)
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; 
v___x_6299_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_6300_ = lean_string_append(v_msg_6295_, v___x_6299_);
lean_inc_n(v___y_6294_, 2);
lean_inc_ref(v___y_6290_);
v___x_6301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6301_, 0, v___y_6290_);
lean_ctor_set(v___x_6301_, 1, v___y_6294_);
lean_ctor_set(v___x_6301_, 2, v___x_6297_);
v___x_6302_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_6301_, v___x_6297_);
lean_dec_ref_known(v___x_6301_, 3);
v___x_6303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6303_, 0, v___y_6290_);
lean_ctor_set(v___x_6303_, 1, v___y_6294_);
lean_ctor_set(v___x_6303_, 2, v___x_6302_);
v___x_6304_ = l_String_Slice_toString(v___x_6303_);
lean_dec_ref_known(v___x_6303_, 3);
v___x_6305_ = lean_string_append(v___x_6300_, v___x_6304_);
lean_dec_ref(v___x_6304_);
v___y_6271_ = v___y_6291_;
v___y_6272_ = v___y_6292_;
v___y_6273_ = v___y_6293_;
v___y_6274_ = v___y_6294_;
v_msg_6275_ = v___x_6305_;
v___y_6276_ = v___y_6296_;
goto v___jp_6270_;
}
else
{
lean_dec_ref(v___y_6290_);
v___y_6271_ = v___y_6291_;
v___y_6272_ = v___y_6292_;
v___y_6273_ = v___y_6293_;
v___y_6274_ = v___y_6294_;
v_msg_6275_ = v_msg_6295_;
v___y_6276_ = v___y_6296_;
goto v___jp_6270_;
}
}
v___jp_6306_:
{
lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6314_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
v___x_6315_ = lean_string_append(v_msg_6313_, v___x_6314_);
v___x_6316_ = lean_string_append(v___x_6315_, v_url_6252_);
lean_dec_ref(v_url_6252_);
v___x_6317_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_6318_ = l_Lake_JsonObject_getJson_x3f(v___y_6310_, v___x_6317_);
lean_dec(v___y_6310_);
if (lean_obj_tag(v___x_6318_) == 0)
{
v___y_6290_ = v___y_6307_;
v___y_6291_ = v___y_6308_;
v___y_6292_ = v___y_6309_;
v___y_6293_ = v___y_6311_;
v___y_6294_ = v___y_6312_;
v_msg_6295_ = v___x_6316_;
v___y_6296_ = v___y_6256_;
goto v___jp_6289_;
}
else
{
lean_object* v_val_6319_; lean_object* v___x_6320_; 
v_val_6319_ = lean_ctor_get(v___x_6318_, 0);
lean_inc(v_val_6319_);
lean_dec_ref_known(v___x_6318_, 1);
v___x_6320_ = l_Lean_Json_getStr_x3f(v_val_6319_);
if (lean_obj_tag(v___x_6320_) == 0)
{
lean_dec_ref_known(v___x_6320_, 1);
v___y_6290_ = v___y_6307_;
v___y_6291_ = v___y_6308_;
v___y_6292_ = v___y_6309_;
v___y_6293_ = v___y_6311_;
v___y_6294_ = v___y_6312_;
v_msg_6295_ = v___x_6316_;
v___y_6296_ = v___y_6256_;
goto v___jp_6289_;
}
else
{
lean_object* v_a_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
lean_inc(v_a_6321_);
lean_dec_ref_known(v___x_6320_, 1);
v___x_6322_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_6323_ = lean_string_append(v___x_6316_, v___x_6322_);
v___x_6324_ = lean_string_append(v___x_6323_, v_a_6321_);
lean_dec(v_a_6321_);
v___y_6290_ = v___y_6307_;
v___y_6291_ = v___y_6308_;
v___y_6292_ = v___y_6309_;
v___y_6293_ = v___y_6311_;
v___y_6294_ = v___y_6312_;
v_msg_6295_ = v___x_6324_;
v___y_6296_ = v___y_6256_;
goto v___jp_6289_;
}
}
}
v___jp_6325_:
{
lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; uint8_t v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; uint8_t v___x_6347_; 
v___x_6331_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_6332_ = lean_string_append(v___x_6331_, v_url_6252_);
lean_dec_ref(v_url_6252_);
v___x_6333_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_6334_ = lean_string_append(v___x_6332_, v___x_6333_);
v___x_6335_ = lean_string_append(v___x_6334_, v_a_6330_);
lean_dec_ref(v_a_6330_);
v___x_6336_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_6337_ = lean_string_append(v___x_6335_, v___x_6336_);
v___x_6338_ = lean_string_utf8_byte_size(v___y_6327_);
lean_inc(v___y_6329_);
v___x_6339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6339_, 0, v___y_6327_);
lean_ctor_set(v___x_6339_, 1, v___y_6329_);
lean_ctor_set(v___x_6339_, 2, v___x_6338_);
v___x_6340_ = l_String_Slice_trimAscii(v___x_6339_);
v___x_6341_ = l_String_Slice_toString(v___x_6340_);
lean_dec_ref(v___x_6340_);
v___x_6342_ = lean_string_append(v___x_6337_, v___x_6341_);
lean_dec_ref(v___x_6341_);
v___x_6343_ = 3;
v___x_6344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6344_, 0, v___x_6342_);
lean_ctor_set_uint8(v___x_6344_, sizeof(void*)*1, v___x_6343_);
lean_inc_ref(v___y_6256_);
v___x_6345_ = lean_apply_2(v___y_6256_, v___x_6344_, lean_box(0));
v___x_6346_ = lean_string_utf8_byte_size(v___y_6326_);
v___x_6347_ = lean_nat_dec_eq(v___x_6346_, v___y_6329_);
if (v___x_6347_ == 0)
{
lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; uint8_t v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6348_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
lean_inc(v___y_6329_);
lean_inc_ref(v___y_6326_);
v___x_6349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6349_, 0, v___y_6326_);
lean_ctor_set(v___x_6349_, 1, v___y_6329_);
lean_ctor_set(v___x_6349_, 2, v___x_6346_);
v___x_6350_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_6349_, v___x_6346_);
lean_dec_ref_known(v___x_6349_, 3);
v___x_6351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6351_, 0, v___y_6326_);
lean_ctor_set(v___x_6351_, 1, v___y_6329_);
lean_ctor_set(v___x_6351_, 2, v___x_6350_);
v___x_6352_ = l_String_Slice_toString(v___x_6351_);
lean_dec_ref_known(v___x_6351_, 3);
v___x_6353_ = lean_string_append(v___x_6348_, v___x_6352_);
lean_dec_ref(v___x_6352_);
v___x_6354_ = 2;
v___x_6355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6355_, 0, v___x_6353_);
lean_ctor_set_uint8(v___x_6355_, sizeof(void*)*1, v___x_6354_);
lean_inc_ref(v___y_6256_);
v___x_6356_ = lean_apply_2(v___y_6256_, v___x_6355_, lean_box(0));
v___y_6259_ = v___y_6328_;
v___y_6260_ = v___y_6256_;
goto v___jp_6258_;
}
else
{
lean_dec(v___y_6329_);
lean_dec_ref(v___y_6326_);
v___y_6259_ = v___y_6328_;
v___y_6260_ = v___y_6256_;
goto v___jp_6258_;
}
}
v___jp_6357_:
{
lean_object* v___x_6363_; 
lean_inc_ref(v___y_6359_);
v___x_6363_ = l_Lean_Json_parse(v___y_6359_);
if (lean_obj_tag(v___x_6363_) == 0)
{
lean_object* v_a_6364_; 
v_a_6364_ = lean_ctor_get(v___x_6363_, 0);
lean_inc(v_a_6364_);
lean_dec_ref_known(v___x_6363_, 1);
v___y_6326_ = v___y_6358_;
v___y_6327_ = v___y_6359_;
v___y_6328_ = v___y_6361_;
v___y_6329_ = v___y_6362_;
v_a_6330_ = v_a_6364_;
goto v___jp_6325_;
}
else
{
lean_object* v_a_6365_; lean_object* v___x_6366_; 
v_a_6365_ = lean_ctor_get(v___x_6363_, 0);
lean_inc(v_a_6365_);
lean_dec_ref_known(v___x_6363_, 1);
v___x_6366_ = l_Lean_Json_getObj_x3f(v_a_6365_);
if (lean_obj_tag(v___x_6366_) == 0)
{
lean_object* v_a_6367_; 
v_a_6367_ = lean_ctor_get(v___x_6366_, 0);
lean_inc(v_a_6367_);
lean_dec_ref_known(v___x_6366_, 1);
v___y_6326_ = v___y_6358_;
v___y_6327_ = v___y_6359_;
v___y_6328_ = v___y_6361_;
v___y_6329_ = v___y_6362_;
v_a_6330_ = v_a_6367_;
goto v___jp_6325_;
}
else
{
lean_object* v_a_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; 
v_a_6368_ = lean_ctor_get(v___x_6366_, 0);
lean_inc(v_a_6368_);
lean_dec_ref_known(v___x_6366_, 1);
v___x_6369_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_6370_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_6371_ = l_Lake_JsonObject_getJson_x3f(v_a_6368_, v___x_6370_);
if (lean_obj_tag(v___x_6371_) == 0)
{
v___y_6307_ = v___y_6358_;
v___y_6308_ = v___y_6359_;
v___y_6309_ = v___y_6360_;
v___y_6310_ = v_a_6368_;
v___y_6311_ = v___y_6361_;
v___y_6312_ = v___y_6362_;
v_msg_6313_ = v___x_6369_;
goto v___jp_6306_;
}
else
{
lean_object* v_val_6372_; lean_object* v___x_6373_; 
v_val_6372_ = lean_ctor_get(v___x_6371_, 0);
lean_inc(v_val_6372_);
lean_dec_ref_known(v___x_6371_, 1);
v___x_6373_ = l_Lean_Json_getNat_x3f(v_val_6372_);
if (lean_obj_tag(v___x_6373_) == 0)
{
lean_dec_ref_known(v___x_6373_, 1);
v___y_6307_ = v___y_6358_;
v___y_6308_ = v___y_6359_;
v___y_6309_ = v___y_6360_;
v___y_6310_ = v_a_6368_;
v___y_6311_ = v___y_6361_;
v___y_6312_ = v___y_6362_;
v_msg_6313_ = v___x_6369_;
goto v___jp_6306_;
}
else
{
lean_object* v_a_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; 
v_a_6374_ = lean_ctor_get(v___x_6373_, 0);
lean_inc(v_a_6374_);
lean_dec_ref_known(v___x_6373_, 1);
v___x_6375_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_6376_ = l_Nat_reprFast(v_a_6374_);
v___x_6377_ = lean_string_append(v___x_6375_, v___x_6376_);
lean_dec_ref(v___x_6376_);
v___x_6378_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_6379_ = lean_string_append(v___x_6377_, v___x_6378_);
v___y_6307_ = v___y_6358_;
v___y_6308_ = v___y_6359_;
v___y_6309_ = v___y_6360_;
v___y_6310_ = v_a_6368_;
v___y_6311_ = v___y_6361_;
v___y_6312_ = v___y_6362_;
v_msg_6313_ = v___x_6379_;
goto v___jp_6306_;
}
}
}
}
}
v___jp_6380_:
{
lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; uint8_t v___x_6388_; uint8_t v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; uint8_t v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6383_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
lean_inc_ref(v_url_6252_);
v___x_6384_ = lean_array_push(v___y_6381_, v_url_6252_);
v___x_6385_ = lean_box(0);
v___x_6386_ = lean_unsigned_to_nat(0u);
v___x_6387_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_6388_ = 1;
v___x_6389_ = 0;
v___x_6390_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_6390_, 0, v___x_6383_);
lean_ctor_set(v___x_6390_, 1, v_a_6382_);
lean_ctor_set(v___x_6390_, 2, v___x_6384_);
lean_ctor_set(v___x_6390_, 3, v___x_6385_);
lean_ctor_set(v___x_6390_, 4, v___x_6387_);
lean_ctor_set_uint8(v___x_6390_, sizeof(void*)*5, v___x_6388_);
lean_ctor_set_uint8(v___x_6390_, sizeof(void*)*5 + 1, v___x_6389_);
lean_inc_ref(v___x_6390_);
v___x_6391_ = l_Lake_mkCmdLog(v___x_6390_);
v___x_6392_ = 0;
v___x_6393_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6393_, 0, v___x_6391_);
lean_ctor_set_uint8(v___x_6393_, sizeof(void*)*1, v___x_6392_);
lean_inc_ref(v___y_6256_);
v___x_6394_ = lean_apply_2(v___y_6256_, v___x_6393_, lean_box(0));
v___x_6395_ = l_IO_Process_output(v___x_6390_, v___x_6385_);
if (lean_obj_tag(v___x_6395_) == 0)
{
lean_object* v_a_6396_; lean_object* v___x_6398_; uint8_t v_isShared_6399_; uint8_t v_isSharedCheck_6450_; 
v_a_6396_ = lean_ctor_get(v___x_6395_, 0);
v_isSharedCheck_6450_ = !lean_is_exclusive(v___x_6395_);
if (v_isSharedCheck_6450_ == 0)
{
v___x_6398_ = v___x_6395_;
v_isShared_6399_ = v_isSharedCheck_6450_;
goto v_resetjp_6397_;
}
else
{
lean_inc(v_a_6396_);
lean_dec(v___x_6395_);
v___x_6398_ = lean_box(0);
v_isShared_6399_ = v_isSharedCheck_6450_;
goto v_resetjp_6397_;
}
v_resetjp_6397_:
{
uint32_t v_exitCode_6400_; lean_object* v_stdout_6401_; lean_object* v_stderr_6402_; lean_object* v___x_6403_; 
v_exitCode_6400_ = lean_ctor_get_uint32(v_a_6396_, sizeof(void*)*2);
v_stdout_6401_ = lean_ctor_get(v_a_6396_, 0);
lean_inc_ref_n(v_stdout_6401_, 2);
v_stderr_6402_ = lean_ctor_get(v_a_6396_, 1);
lean_inc_ref(v_stderr_6402_);
lean_dec(v_a_6396_);
v___x_6403_ = l_Lean_Json_parse(v_stdout_6401_);
if (lean_obj_tag(v___x_6403_) == 0)
{
lean_dec_ref_known(v___x_6403_, 1);
lean_del_object(v___x_6398_);
lean_dec_ref(v_infos_6253_);
v___y_6358_ = v_stdout_6401_;
v___y_6359_ = v_stderr_6402_;
v___y_6360_ = v___x_6392_;
v___y_6361_ = v_exitCode_6400_;
v___y_6362_ = v___x_6386_;
goto v___jp_6357_;
}
else
{
lean_object* v_a_6404_; lean_object* v___x_6405_; 
v_a_6404_ = lean_ctor_get(v___x_6403_, 0);
lean_inc(v_a_6404_);
lean_dec_ref_known(v___x_6403_, 1);
v___x_6405_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_6404_);
if (lean_obj_tag(v___x_6405_) == 0)
{
lean_dec_ref_known(v___x_6405_, 1);
lean_del_object(v___x_6398_);
lean_dec_ref(v_infos_6253_);
v___y_6358_ = v_stdout_6401_;
v___y_6359_ = v_stderr_6402_;
v___y_6360_ = v___x_6392_;
v___y_6361_ = v_exitCode_6400_;
v___y_6362_ = v___x_6386_;
goto v___jp_6357_;
}
else
{
lean_object* v_a_6406_; 
lean_dec_ref(v_stderr_6402_);
lean_dec_ref(v_stdout_6401_);
v_a_6406_ = lean_ctor_get(v___x_6405_, 0);
lean_inc(v_a_6406_);
lean_dec_ref_known(v___x_6405_, 1);
if (lean_obj_tag(v_a_6406_) == 0)
{
lean_object* v_a_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; uint8_t v___x_6410_; 
v_a_6407_ = lean_ctor_get(v_a_6406_, 0);
lean_inc(v_a_6407_);
lean_dec_ref_known(v_a_6406_, 1);
v___x_6408_ = lean_array_get_size(v_infos_6253_);
v___x_6409_ = lean_array_get_size(v_a_6407_);
v___x_6410_ = lean_nat_dec_eq(v___x_6408_, v___x_6409_);
if (v___x_6410_ == 0)
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; uint8_t v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6426_; 
lean_dec(v_a_6407_);
lean_dec_ref(v_infos_6253_);
v___x_6411_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_6412_ = lean_string_append(v___x_6411_, v_url_6252_);
lean_dec_ref(v_url_6252_);
v___x_6413_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_6414_ = lean_string_append(v___x_6412_, v___x_6413_);
v___x_6415_ = l_Nat_reprFast(v___x_6408_);
v___x_6416_ = lean_string_append(v___x_6414_, v___x_6415_);
lean_dec_ref(v___x_6415_);
v___x_6417_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_6418_ = lean_string_append(v___x_6416_, v___x_6417_);
v___x_6419_ = l_Nat_reprFast(v___x_6409_);
v___x_6420_ = lean_string_append(v___x_6418_, v___x_6419_);
lean_dec_ref(v___x_6419_);
v___x_6421_ = 3;
v___x_6422_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6422_, 0, v___x_6420_);
lean_ctor_set_uint8(v___x_6422_, sizeof(void*)*1, v___x_6421_);
lean_inc_ref(v___y_6256_);
v___x_6423_ = lean_apply_2(v___y_6256_, v___x_6422_, lean_box(0));
v___x_6424_ = lean_box(0);
if (v_isShared_6399_ == 0)
{
lean_ctor_set_tag(v___x_6398_, 1);
lean_ctor_set(v___x_6398_, 0, v___x_6424_);
v___x_6426_ = v___x_6398_;
goto v_reusejp_6425_;
}
else
{
lean_object* v_reuseFailAlloc_6427_; 
v_reuseFailAlloc_6427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6427_, 0, v___x_6424_);
v___x_6426_ = v_reuseFailAlloc_6427_;
goto v_reusejp_6425_;
}
v_reusejp_6425_:
{
return v___x_6426_;
}
}
else
{
lean_object* v___x_6428_; lean_object* v___x_6430_; 
lean_dec_ref(v_url_6252_);
v___x_6428_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_6407_, v___x_6408_, v___x_6408_, v_infos_6253_);
lean_dec(v_a_6407_);
if (v_isShared_6399_ == 0)
{
lean_ctor_set(v___x_6398_, 0, v___x_6428_);
v___x_6430_ = v___x_6398_;
goto v_reusejp_6429_;
}
else
{
lean_object* v_reuseFailAlloc_6431_; 
v_reuseFailAlloc_6431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6431_, 0, v___x_6428_);
v___x_6430_ = v_reuseFailAlloc_6431_;
goto v_reusejp_6429_;
}
v_reusejp_6429_:
{
return v___x_6430_;
}
}
}
else
{
lean_object* v_status_6432_; lean_object* v_message_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; uint8_t v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6448_; 
lean_dec_ref(v_infos_6253_);
v_status_6432_ = lean_ctor_get(v_a_6406_, 0);
lean_inc(v_status_6432_);
v_message_6433_ = lean_ctor_get(v_a_6406_, 1);
lean_inc_ref(v_message_6433_);
lean_dec_ref_known(v_a_6406_, 2);
v___x_6434_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_6435_ = l_Nat_reprFast(v_status_6432_);
v___x_6436_ = lean_string_append(v___x_6434_, v___x_6435_);
lean_dec_ref(v___x_6435_);
v___x_6437_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_6438_ = lean_string_append(v___x_6436_, v___x_6437_);
v___x_6439_ = lean_string_append(v___x_6438_, v_url_6252_);
lean_dec_ref(v_url_6252_);
v___x_6440_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_6441_ = lean_string_append(v___x_6439_, v___x_6440_);
v___x_6442_ = lean_string_append(v___x_6441_, v_message_6433_);
lean_dec_ref(v_message_6433_);
v___x_6443_ = 3;
v___x_6444_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6444_, 0, v___x_6442_);
lean_ctor_set_uint8(v___x_6444_, sizeof(void*)*1, v___x_6443_);
lean_inc_ref(v___y_6256_);
v___x_6445_ = lean_apply_2(v___y_6256_, v___x_6444_, lean_box(0));
v___x_6446_ = lean_box(0);
if (v_isShared_6399_ == 0)
{
lean_ctor_set_tag(v___x_6398_, 1);
lean_ctor_set(v___x_6398_, 0, v___x_6446_);
v___x_6448_ = v___x_6398_;
goto v_reusejp_6447_;
}
else
{
lean_object* v_reuseFailAlloc_6449_; 
v_reuseFailAlloc_6449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6449_, 0, v___x_6446_);
v___x_6448_ = v_reuseFailAlloc_6449_;
goto v_reusejp_6447_;
}
v_reusejp_6447_:
{
return v___x_6448_;
}
}
}
}
}
}
else
{
lean_object* v_a_6451_; lean_object* v___x_6453_; uint8_t v_isShared_6454_; uint8_t v_isSharedCheck_6463_; 
lean_dec_ref(v_infos_6253_);
lean_dec_ref(v_url_6252_);
v_a_6451_ = lean_ctor_get(v___x_6395_, 0);
v_isSharedCheck_6463_ = !lean_is_exclusive(v___x_6395_);
if (v_isSharedCheck_6463_ == 0)
{
v___x_6453_ = v___x_6395_;
v_isShared_6454_ = v_isSharedCheck_6463_;
goto v_resetjp_6452_;
}
else
{
lean_inc(v_a_6451_);
lean_dec(v___x_6395_);
v___x_6453_ = lean_box(0);
v_isShared_6454_ = v_isSharedCheck_6463_;
goto v_resetjp_6452_;
}
v_resetjp_6452_:
{
lean_object* v___x_6455_; uint8_t v___x_6456_; lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6461_; 
v___x_6455_ = lean_io_error_to_string(v_a_6451_);
v___x_6456_ = 3;
v___x_6457_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6457_, 0, v___x_6455_);
lean_ctor_set_uint8(v___x_6457_, sizeof(void*)*1, v___x_6456_);
lean_inc_ref(v___y_6256_);
v___x_6458_ = lean_apply_2(v___y_6256_, v___x_6457_, lean_box(0));
v___x_6459_ = lean_box(0);
if (v_isShared_6454_ == 0)
{
lean_ctor_set(v___x_6453_, 0, v___x_6459_);
v___x_6461_ = v___x_6453_;
goto v_reusejp_6460_;
}
else
{
lean_object* v_reuseFailAlloc_6462_; 
v_reuseFailAlloc_6462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6459_);
v___x_6461_ = v_reuseFailAlloc_6462_;
goto v_reusejp_6460_;
}
v_reusejp_6460_:
{
return v___x_6461_;
}
}
}
}
v___jp_6466_:
{
lean_object* v___x_6471_; uint8_t v___x_6472_; 
v___x_6471_ = lean_array_get_size(v___y_6469_);
v___x_6472_ = lean_nat_dec_lt(v___y_6468_, v___x_6471_);
if (v___x_6472_ == 0)
{
v___y_6381_ = v___y_6467_;
v_a_6382_ = v_val_6470_;
goto v___jp_6380_;
}
else
{
lean_object* v___x_6473_; size_t v___x_6474_; lean_object* v___x_6475_; 
v___x_6473_ = lean_box(0);
v___x_6474_ = lean_usize_of_nat(v___x_6471_);
v___x_6475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_6469_, v___x_6465_, v___x_6474_, v___x_6473_, v___y_6256_);
if (lean_obj_tag(v___x_6475_) == 0)
{
lean_dec_ref_known(v___x_6475_, 1);
v___y_6381_ = v___y_6467_;
v_a_6382_ = v_val_6470_;
goto v___jp_6380_;
}
else
{
lean_object* v_a_6476_; lean_object* v___x_6478_; uint8_t v_isShared_6479_; uint8_t v_isSharedCheck_6483_; 
lean_dec_ref(v_val_6470_);
lean_dec_ref(v___y_6467_);
lean_dec_ref(v_infos_6253_);
lean_dec_ref(v_url_6252_);
v_a_6476_ = lean_ctor_get(v___x_6475_, 0);
v_isSharedCheck_6483_ = !lean_is_exclusive(v___x_6475_);
if (v_isSharedCheck_6483_ == 0)
{
v___x_6478_ = v___x_6475_;
v_isShared_6479_ = v_isSharedCheck_6483_;
goto v_resetjp_6477_;
}
else
{
lean_inc(v_a_6476_);
lean_dec(v___x_6475_);
v___x_6478_ = lean_box(0);
v_isShared_6479_ = v_isSharedCheck_6483_;
goto v_resetjp_6477_;
}
v_resetjp_6477_:
{
lean_object* v___x_6481_; 
if (v_isShared_6479_ == 0)
{
v___x_6481_ = v___x_6478_;
goto v_reusejp_6480_;
}
else
{
lean_object* v_reuseFailAlloc_6482_; 
v_reuseFailAlloc_6482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6482_, 0, v_a_6476_);
v___x_6481_ = v_reuseFailAlloc_6482_;
goto v_reusejp_6480_;
}
v_reusejp_6480_:
{
return v___x_6481_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed(lean_object* v_url_6547_, lean_object* v_infos_6548_, lean_object* v_h_6549_, lean_object* v_path_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_){
_start:
{
lean_object* v_res_6553_; 
v_res_6553_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(v_url_6547_, v_infos_6548_, v_h_6549_, v_path_6550_, v___y_6551_);
lean_dec_ref(v___y_6551_);
lean_dec_ref(v_path_6550_);
lean_dec(v_h_6549_);
return v_res_6553_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object* v_a_6554_, lean_object* v_url_6555_, lean_object* v_infos_6556_){
_start:
{
lean_object* v___f_6558_; lean_object* v___x_6559_; 
v___f_6558_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_6558_, 0, v_url_6555_);
lean_closure_set(v___f_6558_, 1, v_infos_6556_);
v___x_6559_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_6558_, v_a_6554_);
return v___x_6559_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object* v_a_6560_, lean_object* v_url_6561_, lean_object* v_infos_6562_, lean_object* v_a_6563_){
_start:
{
lean_object* v_res_6564_; 
v_res_6564_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6560_, v_url_6561_, v_infos_6562_);
lean_dec_ref(v_a_6560_);
return v_res_6564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(lean_object* v_service_6565_, lean_object* v_scope_6566_, lean_object* v_cache_6567_, uint8_t v_force_6568_, lean_object* v_as_6569_, size_t v_i_6570_, size_t v_stop_6571_, lean_object* v_b_6572_, lean_object* v___y_6573_){
_start:
{
lean_object* v_a_6576_; lean_object* v___y_6581_; lean_object* v___y_6592_; lean_object* v___y_6603_; uint8_t v___x_6613_; 
v___x_6613_ = lean_usize_dec_eq(v_i_6570_, v_stop_6571_);
if (v___x_6613_ == 0)
{
lean_object* v___x_6614_; uint64_t v_hash_6615_; lean_object* v_ext_6616_; lean_object* v_url_6617_; lean_object* v___y_6619_; uint8_t v_a_6620_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___y_6696_; lean_object* v___x_6763_; lean_object* v___x_6764_; uint8_t v___x_6765_; 
v___x_6614_ = lean_array_uget_borrowed(v_as_6569_, v_i_6570_);
v_hash_6615_ = lean_ctor_get_uint64(v___x_6614_, sizeof(void*)*1);
v_ext_6616_ = lean_ctor_get(v___x_6614_, 0);
lean_inc_ref(v_scope_6566_);
lean_inc_ref(v_service_6565_);
v_url_6617_ = l_Lake_CacheService_artifactUrl(v_hash_6615_, v_service_6565_, v_scope_6566_);
v___x_6693_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
lean_inc_ref(v_cache_6567_);
v___x_6694_ = l_System_FilePath_join(v_cache_6567_, v___x_6693_);
v___x_6763_ = lean_string_utf8_byte_size(v_ext_6616_);
v___x_6764_ = lean_unsigned_to_nat(0u);
v___x_6765_ = lean_nat_dec_eq(v___x_6763_, v___x_6764_);
if (v___x_6765_ == 0)
{
lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; 
v___x_6766_ = l_Lake_lowerHexUInt64(v_hash_6615_);
v___x_6767_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_6768_ = lean_string_append(v___x_6766_, v___x_6767_);
v___x_6769_ = lean_string_append(v___x_6768_, v_ext_6616_);
v___y_6696_ = v___x_6769_;
goto v___jp_6695_;
}
else
{
lean_object* v___x_6770_; 
v___x_6770_ = l_Lake_lowerHexUInt64(v_hash_6615_);
v___y_6696_ = v___x_6770_;
goto v___jp_6695_;
}
v___jp_6618_:
{
if (v_a_6620_ == 0)
{
lean_object* v_infos_6621_; lean_object* v_indices_6622_; lean_object* v___x_6623_; 
v_infos_6621_ = lean_ctor_get(v_b_6572_, 0);
v_indices_6622_ = lean_ctor_get(v_b_6572_, 1);
v___x_6623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_indices_6622_, v_hash_6615_);
if (lean_obj_tag(v___x_6623_) == 1)
{
lean_object* v_val_6624_; lean_object* v___x_6625_; uint8_t v___x_6626_; 
lean_dec_ref(v_url_6617_);
v_val_6624_ = lean_ctor_get(v___x_6623_, 0);
lean_inc(v_val_6624_);
lean_dec_ref_known(v___x_6623_, 1);
v___x_6625_ = lean_array_get_size(v_infos_6621_);
v___x_6626_ = lean_nat_dec_lt(v_val_6624_, v___x_6625_);
if (v___x_6626_ == 0)
{
lean_dec(v_val_6624_);
lean_dec_ref(v___y_6619_);
lean_inc_ref(v_infos_6621_);
v___y_6592_ = v_infos_6621_;
goto v___jp_6591_;
}
else
{
lean_object* v_v_6627_; lean_object* v_url_6628_; uint64_t v_hash_6629_; lean_object* v_path_6630_; lean_object* v_extraPaths_6631_; lean_object* v___x_6633_; uint8_t v_isShared_6634_; uint8_t v_isSharedCheck_6642_; 
v_v_6627_ = lean_array_fget(v_infos_6621_, v_val_6624_);
v_url_6628_ = lean_ctor_get(v_v_6627_, 0);
v_hash_6629_ = lean_ctor_get_uint64(v_v_6627_, sizeof(void*)*3);
v_path_6630_ = lean_ctor_get(v_v_6627_, 1);
v_extraPaths_6631_ = lean_ctor_get(v_v_6627_, 2);
v_isSharedCheck_6642_ = !lean_is_exclusive(v_v_6627_);
if (v_isSharedCheck_6642_ == 0)
{
v___x_6633_ = v_v_6627_;
v_isShared_6634_ = v_isSharedCheck_6642_;
goto v_resetjp_6632_;
}
else
{
lean_inc(v_extraPaths_6631_);
lean_inc(v_path_6630_);
lean_inc(v_url_6628_);
lean_dec(v_v_6627_);
v___x_6633_ = lean_box(0);
v_isShared_6634_ = v_isSharedCheck_6642_;
goto v_resetjp_6632_;
}
v_resetjp_6632_:
{
lean_object* v___x_6635_; lean_object* v_xs_x27_6636_; lean_object* v___x_6637_; lean_object* v___x_6639_; 
v___x_6635_ = lean_box(0);
lean_inc_ref(v_infos_6621_);
v_xs_x27_6636_ = lean_array_fset(v_infos_6621_, v_val_6624_, v___x_6635_);
v___x_6637_ = lean_array_push(v_extraPaths_6631_, v___y_6619_);
if (v_isShared_6634_ == 0)
{
lean_ctor_set(v___x_6633_, 2, v___x_6637_);
v___x_6639_ = v___x_6633_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6641_; 
v_reuseFailAlloc_6641_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_6641_, 0, v_url_6628_);
lean_ctor_set(v_reuseFailAlloc_6641_, 1, v_path_6630_);
lean_ctor_set(v_reuseFailAlloc_6641_, 2, v___x_6637_);
lean_ctor_set_uint64(v_reuseFailAlloc_6641_, sizeof(void*)*3, v_hash_6629_);
v___x_6639_ = v_reuseFailAlloc_6641_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
lean_object* v___x_6640_; 
v___x_6640_ = lean_array_fset(v_xs_x27_6636_, v_val_6624_, v___x_6639_);
lean_dec(v_val_6624_);
v___y_6592_ = v___x_6640_;
goto v___jp_6591_;
}
}
}
}
else
{
lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6654_; 
lean_inc_ref(v_indices_6622_);
lean_inc_ref(v_infos_6621_);
lean_dec(v___x_6623_);
v_isSharedCheck_6654_ = !lean_is_exclusive(v_b_6572_);
if (v_isSharedCheck_6654_ == 0)
{
lean_object* v_unused_6655_; lean_object* v_unused_6656_; 
v_unused_6655_ = lean_ctor_get(v_b_6572_, 1);
lean_dec(v_unused_6655_);
v_unused_6656_ = lean_ctor_get(v_b_6572_, 0);
lean_dec(v_unused_6656_);
v___x_6644_ = v_b_6572_;
v_isShared_6645_ = v_isSharedCheck_6654_;
goto v_resetjp_6643_;
}
else
{
lean_dec(v_b_6572_);
v___x_6644_ = lean_box(0);
v_isShared_6645_ = v_isSharedCheck_6654_;
goto v_resetjp_6643_;
}
v_resetjp_6643_:
{
lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6652_; 
v___x_6646_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_6647_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6647_, 0, v_url_6617_);
lean_ctor_set(v___x_6647_, 1, v___y_6619_);
lean_ctor_set(v___x_6647_, 2, v___x_6646_);
lean_ctor_set_uint64(v___x_6647_, sizeof(void*)*3, v_hash_6615_);
lean_inc_ref(v_infos_6621_);
v___x_6648_ = lean_array_push(v_infos_6621_, v___x_6647_);
v___x_6649_ = lean_array_get_size(v_infos_6621_);
lean_dec_ref(v_infos_6621_);
v___x_6650_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6622_, v_hash_6615_, v___x_6649_);
if (v_isShared_6645_ == 0)
{
lean_ctor_set(v___x_6644_, 1, v___x_6650_);
lean_ctor_set(v___x_6644_, 0, v___x_6648_);
v___x_6652_ = v___x_6644_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v___x_6648_);
lean_ctor_set(v_reuseFailAlloc_6653_, 1, v___x_6650_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
v_a_6576_ = v___x_6652_;
goto v___jp_6575_;
}
}
}
}
else
{
lean_object* v_infos_6657_; lean_object* v_indices_6658_; lean_object* v___x_6659_; 
v_infos_6657_ = lean_ctor_get(v_b_6572_, 0);
v_indices_6658_ = lean_ctor_get(v_b_6572_, 1);
v___x_6659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_indices_6658_, v_hash_6615_);
if (lean_obj_tag(v___x_6659_) == 1)
{
lean_object* v_val_6660_; lean_object* v___x_6661_; uint8_t v___x_6662_; 
lean_dec_ref(v_url_6617_);
v_val_6660_ = lean_ctor_get(v___x_6659_, 0);
lean_inc(v_val_6660_);
lean_dec_ref_known(v___x_6659_, 1);
v___x_6661_ = lean_array_get_size(v_infos_6657_);
v___x_6662_ = lean_nat_dec_lt(v_val_6660_, v___x_6661_);
if (v___x_6662_ == 0)
{
lean_dec(v_val_6660_);
lean_dec_ref(v___y_6619_);
lean_inc_ref(v_infos_6657_);
v___y_6581_ = v_infos_6657_;
goto v___jp_6580_;
}
else
{
lean_object* v_v_6663_; lean_object* v_url_6664_; uint64_t v_hash_6665_; lean_object* v_path_6666_; lean_object* v_extraPaths_6667_; lean_object* v___x_6669_; uint8_t v_isShared_6670_; uint8_t v_isSharedCheck_6678_; 
v_v_6663_ = lean_array_fget(v_infos_6657_, v_val_6660_);
v_url_6664_ = lean_ctor_get(v_v_6663_, 0);
v_hash_6665_ = lean_ctor_get_uint64(v_v_6663_, sizeof(void*)*3);
v_path_6666_ = lean_ctor_get(v_v_6663_, 1);
v_extraPaths_6667_ = lean_ctor_get(v_v_6663_, 2);
v_isSharedCheck_6678_ = !lean_is_exclusive(v_v_6663_);
if (v_isSharedCheck_6678_ == 0)
{
v___x_6669_ = v_v_6663_;
v_isShared_6670_ = v_isSharedCheck_6678_;
goto v_resetjp_6668_;
}
else
{
lean_inc(v_extraPaths_6667_);
lean_inc(v_path_6666_);
lean_inc(v_url_6664_);
lean_dec(v_v_6663_);
v___x_6669_ = lean_box(0);
v_isShared_6670_ = v_isSharedCheck_6678_;
goto v_resetjp_6668_;
}
v_resetjp_6668_:
{
lean_object* v___x_6671_; lean_object* v_xs_x27_6672_; lean_object* v___x_6673_; lean_object* v___x_6675_; 
v___x_6671_ = lean_box(0);
lean_inc_ref(v_infos_6657_);
v_xs_x27_6672_ = lean_array_fset(v_infos_6657_, v_val_6660_, v___x_6671_);
v___x_6673_ = lean_array_push(v_extraPaths_6667_, v_path_6666_);
if (v_isShared_6670_ == 0)
{
lean_ctor_set(v___x_6669_, 2, v___x_6673_);
lean_ctor_set(v___x_6669_, 1, v___y_6619_);
v___x_6675_ = v___x_6669_;
goto v_reusejp_6674_;
}
else
{
lean_object* v_reuseFailAlloc_6677_; 
v_reuseFailAlloc_6677_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_6677_, 0, v_url_6664_);
lean_ctor_set(v_reuseFailAlloc_6677_, 1, v___y_6619_);
lean_ctor_set(v_reuseFailAlloc_6677_, 2, v___x_6673_);
lean_ctor_set_uint64(v_reuseFailAlloc_6677_, sizeof(void*)*3, v_hash_6665_);
v___x_6675_ = v_reuseFailAlloc_6677_;
goto v_reusejp_6674_;
}
v_reusejp_6674_:
{
lean_object* v___x_6676_; 
v___x_6676_ = lean_array_fset(v_xs_x27_6672_, v_val_6660_, v___x_6675_);
lean_dec(v_val_6660_);
v___y_6581_ = v___x_6676_;
goto v___jp_6580_;
}
}
}
}
else
{
lean_object* v___x_6680_; uint8_t v_isShared_6681_; uint8_t v_isSharedCheck_6690_; 
lean_inc_ref(v_indices_6658_);
lean_inc_ref(v_infos_6657_);
lean_dec(v___x_6659_);
v_isSharedCheck_6690_ = !lean_is_exclusive(v_b_6572_);
if (v_isSharedCheck_6690_ == 0)
{
lean_object* v_unused_6691_; lean_object* v_unused_6692_; 
v_unused_6691_ = lean_ctor_get(v_b_6572_, 1);
lean_dec(v_unused_6691_);
v_unused_6692_ = lean_ctor_get(v_b_6572_, 0);
lean_dec(v_unused_6692_);
v___x_6680_ = v_b_6572_;
v_isShared_6681_ = v_isSharedCheck_6690_;
goto v_resetjp_6679_;
}
else
{
lean_dec(v_b_6572_);
v___x_6680_ = lean_box(0);
v_isShared_6681_ = v_isSharedCheck_6690_;
goto v_resetjp_6679_;
}
v_resetjp_6679_:
{
lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6688_; 
v___x_6682_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_6683_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6683_, 0, v_url_6617_);
lean_ctor_set(v___x_6683_, 1, v___y_6619_);
lean_ctor_set(v___x_6683_, 2, v___x_6682_);
lean_ctor_set_uint64(v___x_6683_, sizeof(void*)*3, v_hash_6615_);
lean_inc_ref(v_infos_6657_);
v___x_6684_ = lean_array_push(v_infos_6657_, v___x_6683_);
v___x_6685_ = lean_array_get_size(v_infos_6657_);
lean_dec_ref(v_infos_6657_);
v___x_6686_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6658_, v_hash_6615_, v___x_6685_);
if (v_isShared_6681_ == 0)
{
lean_ctor_set(v___x_6680_, 1, v___x_6686_);
lean_ctor_set(v___x_6680_, 0, v___x_6684_);
v___x_6688_ = v___x_6680_;
goto v_reusejp_6687_;
}
else
{
lean_object* v_reuseFailAlloc_6689_; 
v_reuseFailAlloc_6689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6689_, 0, v___x_6684_);
lean_ctor_set(v_reuseFailAlloc_6689_, 1, v___x_6686_);
v___x_6688_ = v_reuseFailAlloc_6689_;
goto v_reusejp_6687_;
}
v_reusejp_6687_:
{
v_a_6576_ = v___x_6688_;
goto v___jp_6575_;
}
}
}
}
}
v___jp_6695_:
{
lean_object* v_path_6697_; 
v_path_6697_ = l_System_FilePath_join(v___x_6694_, v___y_6696_);
if (v_force_6568_ == 0)
{
lean_object* v___x_6698_; uint8_t v___x_6699_; uint8_t v___x_6700_; 
v___x_6698_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_6699_ = l_System_FilePath_pathExists(v_path_6697_);
v___x_6700_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_6700_ == 0)
{
v___y_6619_ = v_path_6697_;
v_a_6620_ = v___x_6699_;
goto v___jp_6618_;
}
else
{
lean_object* v___x_6701_; size_t v___x_6702_; size_t v___x_6703_; lean_object* v___x_6704_; 
v___x_6701_ = lean_box(0);
v___x_6702_ = ((size_t)0ULL);
v___x_6703_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_6704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6698_, v___x_6702_, v___x_6703_, v___x_6701_, v___y_6573_);
if (lean_obj_tag(v___x_6704_) == 0)
{
lean_dec_ref_known(v___x_6704_, 1);
v___y_6619_ = v_path_6697_;
v_a_6620_ = v___x_6699_;
goto v___jp_6618_;
}
else
{
lean_object* v_a_6705_; lean_object* v___x_6707_; uint8_t v_isShared_6708_; uint8_t v_isSharedCheck_6712_; 
lean_dec_ref(v_path_6697_);
lean_dec_ref(v_url_6617_);
lean_dec_ref(v_b_6572_);
lean_dec_ref(v_cache_6567_);
lean_dec_ref(v_scope_6566_);
lean_dec_ref(v_service_6565_);
v_a_6705_ = lean_ctor_get(v___x_6704_, 0);
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6704_);
if (v_isSharedCheck_6712_ == 0)
{
v___x_6707_ = v___x_6704_;
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
else
{
lean_inc(v_a_6705_);
lean_dec(v___x_6704_);
v___x_6707_ = lean_box(0);
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
v_resetjp_6706_:
{
lean_object* v___x_6710_; 
if (v_isShared_6708_ == 0)
{
v___x_6710_ = v___x_6707_;
goto v_reusejp_6709_;
}
else
{
lean_object* v_reuseFailAlloc_6711_; 
v_reuseFailAlloc_6711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6711_, 0, v_a_6705_);
v___x_6710_ = v_reuseFailAlloc_6711_;
goto v_reusejp_6709_;
}
v_reusejp_6709_:
{
return v___x_6710_;
}
}
}
}
}
else
{
lean_object* v___x_6713_; 
v___x_6713_ = l_Lake_removeFileIfExists(v_path_6697_);
if (lean_obj_tag(v___x_6713_) == 0)
{
lean_object* v_infos_6714_; lean_object* v_indices_6715_; lean_object* v___x_6716_; 
lean_dec_ref_known(v___x_6713_, 1);
v_infos_6714_ = lean_ctor_get(v_b_6572_, 0);
v_indices_6715_ = lean_ctor_get(v_b_6572_, 1);
v___x_6716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_indices_6715_, v_hash_6615_);
if (lean_obj_tag(v___x_6716_) == 1)
{
lean_object* v_val_6717_; lean_object* v___x_6718_; uint8_t v___x_6719_; 
lean_dec_ref(v_url_6617_);
v_val_6717_ = lean_ctor_get(v___x_6716_, 0);
lean_inc(v_val_6717_);
lean_dec_ref_known(v___x_6716_, 1);
v___x_6718_ = lean_array_get_size(v_infos_6714_);
v___x_6719_ = lean_nat_dec_lt(v_val_6717_, v___x_6718_);
if (v___x_6719_ == 0)
{
lean_dec(v_val_6717_);
lean_dec_ref(v_path_6697_);
lean_inc_ref(v_infos_6714_);
v___y_6603_ = v_infos_6714_;
goto v___jp_6602_;
}
else
{
lean_object* v_v_6720_; lean_object* v_url_6721_; uint64_t v_hash_6722_; lean_object* v_path_6723_; lean_object* v_extraPaths_6724_; lean_object* v___x_6726_; uint8_t v_isShared_6727_; uint8_t v_isSharedCheck_6735_; 
v_v_6720_ = lean_array_fget(v_infos_6714_, v_val_6717_);
v_url_6721_ = lean_ctor_get(v_v_6720_, 0);
v_hash_6722_ = lean_ctor_get_uint64(v_v_6720_, sizeof(void*)*3);
v_path_6723_ = lean_ctor_get(v_v_6720_, 1);
v_extraPaths_6724_ = lean_ctor_get(v_v_6720_, 2);
v_isSharedCheck_6735_ = !lean_is_exclusive(v_v_6720_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6726_ = v_v_6720_;
v_isShared_6727_ = v_isSharedCheck_6735_;
goto v_resetjp_6725_;
}
else
{
lean_inc(v_extraPaths_6724_);
lean_inc(v_path_6723_);
lean_inc(v_url_6721_);
lean_dec(v_v_6720_);
v___x_6726_ = lean_box(0);
v_isShared_6727_ = v_isSharedCheck_6735_;
goto v_resetjp_6725_;
}
v_resetjp_6725_:
{
lean_object* v___x_6728_; lean_object* v_xs_x27_6729_; lean_object* v___x_6730_; lean_object* v___x_6732_; 
v___x_6728_ = lean_box(0);
lean_inc_ref(v_infos_6714_);
v_xs_x27_6729_ = lean_array_fset(v_infos_6714_, v_val_6717_, v___x_6728_);
v___x_6730_ = lean_array_push(v_extraPaths_6724_, v_path_6697_);
if (v_isShared_6727_ == 0)
{
lean_ctor_set(v___x_6726_, 2, v___x_6730_);
v___x_6732_ = v___x_6726_;
goto v_reusejp_6731_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_url_6721_);
lean_ctor_set(v_reuseFailAlloc_6734_, 1, v_path_6723_);
lean_ctor_set(v_reuseFailAlloc_6734_, 2, v___x_6730_);
lean_ctor_set_uint64(v_reuseFailAlloc_6734_, sizeof(void*)*3, v_hash_6722_);
v___x_6732_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6731_;
}
v_reusejp_6731_:
{
lean_object* v___x_6733_; 
v___x_6733_ = lean_array_fset(v_xs_x27_6729_, v_val_6717_, v___x_6732_);
lean_dec(v_val_6717_);
v___y_6603_ = v___x_6733_;
goto v___jp_6602_;
}
}
}
}
else
{
lean_object* v___x_6737_; uint8_t v_isShared_6738_; uint8_t v_isSharedCheck_6747_; 
lean_inc_ref(v_indices_6715_);
lean_inc_ref(v_infos_6714_);
lean_dec(v___x_6716_);
v_isSharedCheck_6747_ = !lean_is_exclusive(v_b_6572_);
if (v_isSharedCheck_6747_ == 0)
{
lean_object* v_unused_6748_; lean_object* v_unused_6749_; 
v_unused_6748_ = lean_ctor_get(v_b_6572_, 1);
lean_dec(v_unused_6748_);
v_unused_6749_ = lean_ctor_get(v_b_6572_, 0);
lean_dec(v_unused_6749_);
v___x_6737_ = v_b_6572_;
v_isShared_6738_ = v_isSharedCheck_6747_;
goto v_resetjp_6736_;
}
else
{
lean_dec(v_b_6572_);
v___x_6737_ = lean_box(0);
v_isShared_6738_ = v_isSharedCheck_6747_;
goto v_resetjp_6736_;
}
v_resetjp_6736_:
{
lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v___x_6743_; lean_object* v___x_6745_; 
v___x_6739_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
v___x_6740_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6740_, 0, v_url_6617_);
lean_ctor_set(v___x_6740_, 1, v_path_6697_);
lean_ctor_set(v___x_6740_, 2, v___x_6739_);
lean_ctor_set_uint64(v___x_6740_, sizeof(void*)*3, v_hash_6615_);
lean_inc_ref(v_infos_6714_);
v___x_6741_ = lean_array_push(v_infos_6714_, v___x_6740_);
v___x_6742_ = lean_array_get_size(v_infos_6714_);
lean_dec_ref(v_infos_6714_);
v___x_6743_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_6715_, v_hash_6615_, v___x_6742_);
if (v_isShared_6738_ == 0)
{
lean_ctor_set(v___x_6737_, 1, v___x_6743_);
lean_ctor_set(v___x_6737_, 0, v___x_6741_);
v___x_6745_ = v___x_6737_;
goto v_reusejp_6744_;
}
else
{
lean_object* v_reuseFailAlloc_6746_; 
v_reuseFailAlloc_6746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6746_, 0, v___x_6741_);
lean_ctor_set(v_reuseFailAlloc_6746_, 1, v___x_6743_);
v___x_6745_ = v_reuseFailAlloc_6746_;
goto v_reusejp_6744_;
}
v_reusejp_6744_:
{
v_a_6576_ = v___x_6745_;
goto v___jp_6575_;
}
}
}
}
else
{
lean_object* v_a_6750_; lean_object* v___x_6752_; uint8_t v_isShared_6753_; uint8_t v_isSharedCheck_6762_; 
lean_dec_ref(v_path_6697_);
lean_dec_ref(v_url_6617_);
lean_dec_ref(v_b_6572_);
lean_dec_ref(v_cache_6567_);
lean_dec_ref(v_scope_6566_);
lean_dec_ref(v_service_6565_);
v_a_6750_ = lean_ctor_get(v___x_6713_, 0);
v_isSharedCheck_6762_ = !lean_is_exclusive(v___x_6713_);
if (v_isSharedCheck_6762_ == 0)
{
v___x_6752_ = v___x_6713_;
v_isShared_6753_ = v_isSharedCheck_6762_;
goto v_resetjp_6751_;
}
else
{
lean_inc(v_a_6750_);
lean_dec(v___x_6713_);
v___x_6752_ = lean_box(0);
v_isShared_6753_ = v_isSharedCheck_6762_;
goto v_resetjp_6751_;
}
v_resetjp_6751_:
{
lean_object* v___x_6754_; uint8_t v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6760_; 
v___x_6754_ = lean_io_error_to_string(v_a_6750_);
v___x_6755_ = 3;
v___x_6756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6756_, 0, v___x_6754_);
lean_ctor_set_uint8(v___x_6756_, sizeof(void*)*1, v___x_6755_);
lean_inc_ref(v___y_6573_);
v___x_6757_ = lean_apply_2(v___y_6573_, v___x_6756_, lean_box(0));
v___x_6758_ = lean_box(0);
if (v_isShared_6753_ == 0)
{
lean_ctor_set(v___x_6752_, 0, v___x_6758_);
v___x_6760_ = v___x_6752_;
goto v_reusejp_6759_;
}
else
{
lean_object* v_reuseFailAlloc_6761_; 
v_reuseFailAlloc_6761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6761_, 0, v___x_6758_);
v___x_6760_ = v_reuseFailAlloc_6761_;
goto v_reusejp_6759_;
}
v_reusejp_6759_:
{
return v___x_6760_;
}
}
}
}
}
}
else
{
lean_object* v___x_6771_; 
lean_dec_ref(v_cache_6567_);
lean_dec_ref(v_scope_6566_);
lean_dec_ref(v_service_6565_);
v___x_6771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6771_, 0, v_b_6572_);
return v___x_6771_;
}
v___jp_6575_:
{
size_t v___x_6577_; size_t v___x_6578_; 
v___x_6577_ = ((size_t)1ULL);
v___x_6578_ = lean_usize_add(v_i_6570_, v___x_6577_);
v_i_6570_ = v___x_6578_;
v_b_6572_ = v_a_6576_;
goto _start;
}
v___jp_6580_:
{
lean_object* v_indices_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6589_; 
v_indices_6582_ = lean_ctor_get(v_b_6572_, 1);
v_isSharedCheck_6589_ = !lean_is_exclusive(v_b_6572_);
if (v_isSharedCheck_6589_ == 0)
{
lean_object* v_unused_6590_; 
v_unused_6590_ = lean_ctor_get(v_b_6572_, 0);
lean_dec(v_unused_6590_);
v___x_6584_ = v_b_6572_;
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_indices_6582_);
lean_dec(v_b_6572_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
lean_object* v___x_6587_; 
if (v_isShared_6585_ == 0)
{
lean_ctor_set(v___x_6584_, 0, v___y_6581_);
v___x_6587_ = v___x_6584_;
goto v_reusejp_6586_;
}
else
{
lean_object* v_reuseFailAlloc_6588_; 
v_reuseFailAlloc_6588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6588_, 0, v___y_6581_);
lean_ctor_set(v_reuseFailAlloc_6588_, 1, v_indices_6582_);
v___x_6587_ = v_reuseFailAlloc_6588_;
goto v_reusejp_6586_;
}
v_reusejp_6586_:
{
v_a_6576_ = v___x_6587_;
goto v___jp_6575_;
}
}
}
v___jp_6591_:
{
lean_object* v_indices_6593_; lean_object* v___x_6595_; uint8_t v_isShared_6596_; uint8_t v_isSharedCheck_6600_; 
v_indices_6593_ = lean_ctor_get(v_b_6572_, 1);
v_isSharedCheck_6600_ = !lean_is_exclusive(v_b_6572_);
if (v_isSharedCheck_6600_ == 0)
{
lean_object* v_unused_6601_; 
v_unused_6601_ = lean_ctor_get(v_b_6572_, 0);
lean_dec(v_unused_6601_);
v___x_6595_ = v_b_6572_;
v_isShared_6596_ = v_isSharedCheck_6600_;
goto v_resetjp_6594_;
}
else
{
lean_inc(v_indices_6593_);
lean_dec(v_b_6572_);
v___x_6595_ = lean_box(0);
v_isShared_6596_ = v_isSharedCheck_6600_;
goto v_resetjp_6594_;
}
v_resetjp_6594_:
{
lean_object* v___x_6598_; 
if (v_isShared_6596_ == 0)
{
lean_ctor_set(v___x_6595_, 0, v___y_6592_);
v___x_6598_ = v___x_6595_;
goto v_reusejp_6597_;
}
else
{
lean_object* v_reuseFailAlloc_6599_; 
v_reuseFailAlloc_6599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6599_, 0, v___y_6592_);
lean_ctor_set(v_reuseFailAlloc_6599_, 1, v_indices_6593_);
v___x_6598_ = v_reuseFailAlloc_6599_;
goto v_reusejp_6597_;
}
v_reusejp_6597_:
{
v_a_6576_ = v___x_6598_;
goto v___jp_6575_;
}
}
}
v___jp_6602_:
{
lean_object* v_indices_6604_; lean_object* v___x_6606_; uint8_t v_isShared_6607_; uint8_t v_isSharedCheck_6611_; 
v_indices_6604_ = lean_ctor_get(v_b_6572_, 1);
v_isSharedCheck_6611_ = !lean_is_exclusive(v_b_6572_);
if (v_isSharedCheck_6611_ == 0)
{
lean_object* v_unused_6612_; 
v_unused_6612_ = lean_ctor_get(v_b_6572_, 0);
lean_dec(v_unused_6612_);
v___x_6606_ = v_b_6572_;
v_isShared_6607_ = v_isSharedCheck_6611_;
goto v_resetjp_6605_;
}
else
{
lean_inc(v_indices_6604_);
lean_dec(v_b_6572_);
v___x_6606_ = lean_box(0);
v_isShared_6607_ = v_isSharedCheck_6611_;
goto v_resetjp_6605_;
}
v_resetjp_6605_:
{
lean_object* v___x_6609_; 
if (v_isShared_6607_ == 0)
{
lean_ctor_set(v___x_6606_, 0, v___y_6603_);
v___x_6609_ = v___x_6606_;
goto v_reusejp_6608_;
}
else
{
lean_object* v_reuseFailAlloc_6610_; 
v_reuseFailAlloc_6610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6610_, 0, v___y_6603_);
lean_ctor_set(v_reuseFailAlloc_6610_, 1, v_indices_6604_);
v___x_6609_ = v_reuseFailAlloc_6610_;
goto v_reusejp_6608_;
}
v_reusejp_6608_:
{
v_a_6576_ = v___x_6609_;
goto v___jp_6575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3___boxed(lean_object* v_service_6772_, lean_object* v_scope_6773_, lean_object* v_cache_6774_, lean_object* v_force_6775_, lean_object* v_as_6776_, lean_object* v_i_6777_, lean_object* v_stop_6778_, lean_object* v_b_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_){
_start:
{
uint8_t v_force_boxed_6782_; size_t v_i_boxed_6783_; size_t v_stop_boxed_6784_; lean_object* v_res_6785_; 
v_force_boxed_6782_ = lean_unbox(v_force_6775_);
v_i_boxed_6783_ = lean_unbox_usize(v_i_6777_);
lean_dec(v_i_6777_);
v_stop_boxed_6784_ = lean_unbox_usize(v_stop_6778_);
lean_dec(v_stop_6778_);
v_res_6785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6772_, v_scope_6773_, v_cache_6774_, v_force_boxed_6782_, v_as_6776_, v_i_boxed_6783_, v_stop_boxed_6784_, v_b_6779_, v___y_6780_);
lean_dec_ref(v___y_6780_);
lean_dec_ref(v_as_6776_);
return v_res_6785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object* v_as_6787_, size_t v_i_6788_, size_t v_stop_6789_, lean_object* v_b_6790_, lean_object* v___y_6791_){
_start:
{
lean_object* v_a_6794_; uint8_t v___x_6798_; 
v___x_6798_ = lean_usize_dec_eq(v_i_6788_, v_stop_6789_);
if (v___x_6798_ == 0)
{
lean_object* v___x_6799_; lean_object* v_a_6803_; uint8_t v_a_6820_; lean_object* v_path_6821_; lean_object* v_extraPaths_6822_; lean_object* v___x_6823_; lean_object* v___x_6824_; uint8_t v___x_6825_; 
v___x_6799_ = lean_array_uget_borrowed(v_as_6787_, v_i_6788_);
v_path_6821_ = lean_ctor_get(v___x_6799_, 1);
v_extraPaths_6822_ = lean_ctor_get(v___x_6799_, 2);
v___x_6823_ = lean_array_get_size(v_extraPaths_6822_);
v___x_6824_ = lean_unsigned_to_nat(0u);
v___x_6825_ = lean_nat_dec_eq(v___x_6823_, v___x_6824_);
if (v___x_6825_ == 0)
{
lean_object* v___x_6826_; lean_object* v_val_6828_; lean_object* v___x_6842_; 
v___x_6826_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_6842_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_createExtraPaths(v_path_6821_, v_extraPaths_6822_);
if (lean_obj_tag(v___x_6842_) == 0)
{
lean_object* v_a_6843_; lean_object* v___x_6845_; uint8_t v_isShared_6846_; uint8_t v_isSharedCheck_6850_; 
v_a_6843_ = lean_ctor_get(v___x_6842_, 0);
v_isSharedCheck_6850_ = !lean_is_exclusive(v___x_6842_);
if (v_isSharedCheck_6850_ == 0)
{
v___x_6845_ = v___x_6842_;
v_isShared_6846_ = v_isSharedCheck_6850_;
goto v_resetjp_6844_;
}
else
{
lean_inc(v_a_6843_);
lean_dec(v___x_6842_);
v___x_6845_ = lean_box(0);
v_isShared_6846_ = v_isSharedCheck_6850_;
goto v_resetjp_6844_;
}
v_resetjp_6844_:
{
lean_object* v___x_6848_; 
if (v_isShared_6846_ == 0)
{
lean_ctor_set_tag(v___x_6845_, 1);
v___x_6848_ = v___x_6845_;
goto v_reusejp_6847_;
}
else
{
lean_object* v_reuseFailAlloc_6849_; 
v_reuseFailAlloc_6849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6849_, 0, v_a_6843_);
v___x_6848_ = v_reuseFailAlloc_6849_;
goto v_reusejp_6847_;
}
v_reusejp_6847_:
{
v_val_6828_ = v___x_6848_;
goto v___jp_6827_;
}
}
}
else
{
lean_object* v_a_6851_; lean_object* v___x_6853_; uint8_t v_isShared_6854_; uint8_t v_isSharedCheck_6858_; 
v_a_6851_ = lean_ctor_get(v___x_6842_, 0);
v_isSharedCheck_6858_ = !lean_is_exclusive(v___x_6842_);
if (v_isSharedCheck_6858_ == 0)
{
v___x_6853_ = v___x_6842_;
v_isShared_6854_ = v_isSharedCheck_6858_;
goto v_resetjp_6852_;
}
else
{
lean_inc(v_a_6851_);
lean_dec(v___x_6842_);
v___x_6853_ = lean_box(0);
v_isShared_6854_ = v_isSharedCheck_6858_;
goto v_resetjp_6852_;
}
v_resetjp_6852_:
{
lean_object* v___x_6856_; 
if (v_isShared_6854_ == 0)
{
lean_ctor_set_tag(v___x_6853_, 0);
v___x_6856_ = v___x_6853_;
goto v_reusejp_6855_;
}
else
{
lean_object* v_reuseFailAlloc_6857_; 
v_reuseFailAlloc_6857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6857_, 0, v_a_6851_);
v___x_6856_ = v_reuseFailAlloc_6857_;
goto v_reusejp_6855_;
}
v_reusejp_6855_:
{
v_val_6828_ = v___x_6856_;
goto v___jp_6827_;
}
}
}
v___jp_6827_:
{
uint8_t v___x_6829_; 
v___x_6829_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_6829_ == 0)
{
v_a_6803_ = v_val_6828_;
goto v___jp_6802_;
}
else
{
lean_object* v___x_6830_; size_t v___x_6831_; size_t v___x_6832_; lean_object* v___x_6833_; 
v___x_6830_ = lean_box(0);
v___x_6831_ = ((size_t)0ULL);
v___x_6832_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_6833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6826_, v___x_6831_, v___x_6832_, v___x_6830_, v___y_6791_);
if (lean_obj_tag(v___x_6833_) == 0)
{
lean_dec_ref_known(v___x_6833_, 1);
v_a_6803_ = v_val_6828_;
goto v___jp_6802_;
}
else
{
lean_object* v_a_6834_; lean_object* v___x_6836_; uint8_t v_isShared_6837_; uint8_t v_isSharedCheck_6841_; 
lean_dec_ref(v_val_6828_);
lean_dec_ref(v_b_6790_);
v_a_6834_ = lean_ctor_get(v___x_6833_, 0);
v_isSharedCheck_6841_ = !lean_is_exclusive(v___x_6833_);
if (v_isSharedCheck_6841_ == 0)
{
v___x_6836_ = v___x_6833_;
v_isShared_6837_ = v_isSharedCheck_6841_;
goto v_resetjp_6835_;
}
else
{
lean_inc(v_a_6834_);
lean_dec(v___x_6833_);
v___x_6836_ = lean_box(0);
v_isShared_6837_ = v_isSharedCheck_6841_;
goto v_resetjp_6835_;
}
v_resetjp_6835_:
{
lean_object* v___x_6839_; 
if (v_isShared_6837_ == 0)
{
v___x_6839_ = v___x_6836_;
goto v_reusejp_6838_;
}
else
{
lean_object* v_reuseFailAlloc_6840_; 
v_reuseFailAlloc_6840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6840_, 0, v_a_6834_);
v___x_6839_ = v_reuseFailAlloc_6840_;
goto v_reusejp_6838_;
}
v_reusejp_6838_:
{
return v___x_6839_;
}
}
}
}
}
}
else
{
lean_object* v___x_6859_; uint8_t v___x_6860_; uint8_t v___x_6861_; 
v___x_6859_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_6860_ = l_System_FilePath_pathExists(v_path_6821_);
v___x_6861_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_6861_ == 0)
{
v_a_6820_ = v___x_6860_;
goto v___jp_6819_;
}
else
{
lean_object* v___x_6862_; size_t v___x_6863_; size_t v___x_6864_; lean_object* v___x_6865_; 
v___x_6862_ = lean_box(0);
v___x_6863_ = ((size_t)0ULL);
v___x_6864_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_6865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6859_, v___x_6863_, v___x_6864_, v___x_6862_, v___y_6791_);
if (lean_obj_tag(v___x_6865_) == 0)
{
lean_dec_ref_known(v___x_6865_, 1);
v_a_6820_ = v___x_6860_;
goto v___jp_6819_;
}
else
{
lean_object* v_a_6866_; lean_object* v___x_6868_; uint8_t v_isShared_6869_; uint8_t v_isSharedCheck_6873_; 
lean_dec_ref(v_b_6790_);
v_a_6866_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6873_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6873_ == 0)
{
v___x_6868_ = v___x_6865_;
v_isShared_6869_ = v_isSharedCheck_6873_;
goto v_resetjp_6867_;
}
else
{
lean_inc(v_a_6866_);
lean_dec(v___x_6865_);
v___x_6868_ = lean_box(0);
v_isShared_6869_ = v_isSharedCheck_6873_;
goto v_resetjp_6867_;
}
v_resetjp_6867_:
{
lean_object* v___x_6871_; 
if (v_isShared_6869_ == 0)
{
v___x_6871_ = v___x_6868_;
goto v_reusejp_6870_;
}
else
{
lean_object* v_reuseFailAlloc_6872_; 
v_reuseFailAlloc_6872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6872_, 0, v_a_6866_);
v___x_6871_ = v_reuseFailAlloc_6872_;
goto v_reusejp_6870_;
}
v_reusejp_6870_:
{
return v___x_6871_;
}
}
}
}
}
v___jp_6800_:
{
lean_object* v___x_6801_; 
lean_inc(v___x_6799_);
v___x_6801_ = lean_array_push(v_b_6790_, v___x_6799_);
v_a_6794_ = v___x_6801_;
goto v___jp_6793_;
}
v___jp_6802_:
{
if (lean_obj_tag(v_a_6803_) == 0)
{
lean_object* v_a_6804_; lean_object* v___x_6806_; uint8_t v_isShared_6807_; uint8_t v_isSharedCheck_6818_; 
v_a_6804_ = lean_ctor_get(v_a_6803_, 0);
v_isSharedCheck_6818_ = !lean_is_exclusive(v_a_6803_);
if (v_isSharedCheck_6818_ == 0)
{
v___x_6806_ = v_a_6803_;
v_isShared_6807_ = v_isSharedCheck_6818_;
goto v_resetjp_6805_;
}
else
{
lean_inc(v_a_6804_);
lean_dec(v_a_6803_);
v___x_6806_ = lean_box(0);
v_isShared_6807_ = v_isSharedCheck_6818_;
goto v_resetjp_6805_;
}
v_resetjp_6805_:
{
if (lean_obj_tag(v_a_6804_) == 11)
{
lean_dec_ref_known(v_a_6804_, 2);
lean_del_object(v___x_6806_);
goto v___jp_6800_;
}
else
{
lean_object* v___x_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; uint8_t v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6816_; 
lean_dec_ref(v_b_6790_);
v___x_6808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___closed__0));
v___x_6809_ = lean_io_error_to_string(v_a_6804_);
v___x_6810_ = lean_string_append(v___x_6808_, v___x_6809_);
lean_dec_ref(v___x_6809_);
v___x_6811_ = 3;
v___x_6812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6812_, 0, v___x_6810_);
lean_ctor_set_uint8(v___x_6812_, sizeof(void*)*1, v___x_6811_);
lean_inc_ref(v___y_6791_);
v___x_6813_ = lean_apply_2(v___y_6791_, v___x_6812_, lean_box(0));
v___x_6814_ = lean_box(0);
if (v_isShared_6807_ == 0)
{
lean_ctor_set_tag(v___x_6806_, 1);
lean_ctor_set(v___x_6806_, 0, v___x_6814_);
v___x_6816_ = v___x_6806_;
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
}
else
{
lean_dec_ref_known(v_a_6803_, 1);
v_a_6794_ = v_b_6790_;
goto v___jp_6793_;
}
}
v___jp_6819_:
{
if (v_a_6820_ == 0)
{
goto v___jp_6800_;
}
else
{
v_a_6794_ = v_b_6790_;
goto v___jp_6793_;
}
}
}
else
{
lean_object* v___x_6874_; 
v___x_6874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6874_, 0, v_b_6790_);
return v___x_6874_;
}
v___jp_6793_:
{
size_t v___x_6795_; size_t v___x_6796_; 
v___x_6795_ = ((size_t)1ULL);
v___x_6796_ = lean_usize_add(v_i_6788_, v___x_6795_);
v_i_6788_ = v___x_6796_;
v_b_6790_ = v_a_6794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_as_6875_, lean_object* v_i_6876_, lean_object* v_stop_6877_, lean_object* v_b_6878_, lean_object* v___y_6879_, lean_object* v___y_6880_){
_start:
{
size_t v_i_boxed_6881_; size_t v_stop_boxed_6882_; lean_object* v_res_6883_; 
v_i_boxed_6881_ = lean_unbox_usize(v_i_6876_);
lean_dec(v_i_6876_);
v_stop_boxed_6882_ = lean_unbox_usize(v_stop_6877_);
lean_dec(v_stop_6877_);
v_res_6883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_as_6875_, v_i_boxed_6881_, v_stop_boxed_6882_, v_b_6878_, v___y_6879_);
lean_dec_ref(v___y_6879_);
lean_dec_ref(v_as_6875_);
return v_res_6883_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_6888_, lean_object* v_cache_6889_, lean_object* v_service_6890_, lean_object* v_scope_6891_, uint8_t v_force_6892_, lean_object* v_a_6893_){
_start:
{
lean_object* v_a_6896_; lean_object* v_a_6918_; lean_object* v___x_6936_; lean_object* v___x_6937_; uint8_t v___x_6938_; 
v___x_6936_ = lean_array_get_size(v_descrs_6888_);
v___x_6937_ = lean_unsigned_to_nat(0u);
v___x_6938_ = lean_nat_dec_eq(v___x_6936_, v___x_6937_);
if (v___x_6938_ == 0)
{
lean_object* v___x_6939_; lean_object* v_infos_6941_; uint8_t v___x_6956_; 
v___x_6939_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_6956_ = lean_nat_dec_lt(v___x_6937_, v___x_6936_);
if (v___x_6956_ == 0)
{
v_infos_6941_ = v___x_6939_;
goto v___jp_6940_;
}
else
{
lean_object* v___x_6957_; size_t v___x_6958_; size_t v___x_6959_; lean_object* v___x_6960_; 
v___x_6957_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
v___x_6958_ = ((size_t)0ULL);
v___x_6959_ = lean_usize_of_nat(v___x_6936_);
lean_inc_ref(v_cache_6889_);
lean_inc_ref(v_scope_6891_);
lean_inc_ref(v_service_6890_);
v___x_6960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6890_, v_scope_6891_, v_cache_6889_, v_force_6892_, v_descrs_6888_, v___x_6958_, v___x_6959_, v___x_6957_, v_a_6893_);
if (lean_obj_tag(v___x_6960_) == 0)
{
lean_object* v_a_6961_; lean_object* v_infos_6962_; 
v_a_6961_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_a_6961_);
lean_dec_ref_known(v___x_6960_, 1);
v_infos_6962_ = lean_ctor_get(v_a_6961_, 0);
lean_inc_ref(v_infos_6962_);
lean_dec(v_a_6961_);
v_infos_6941_ = v_infos_6962_;
goto v___jp_6940_;
}
else
{
lean_object* v_a_6963_; lean_object* v___x_6965_; uint8_t v_isShared_6966_; uint8_t v_isSharedCheck_6970_; 
lean_dec_ref(v_scope_6891_);
lean_dec_ref(v_service_6890_);
lean_dec_ref(v_cache_6889_);
v_a_6963_ = lean_ctor_get(v___x_6960_, 0);
v_isSharedCheck_6970_ = !lean_is_exclusive(v___x_6960_);
if (v_isSharedCheck_6970_ == 0)
{
v___x_6965_ = v___x_6960_;
v_isShared_6966_ = v_isSharedCheck_6970_;
goto v_resetjp_6964_;
}
else
{
lean_inc(v_a_6963_);
lean_dec(v___x_6960_);
v___x_6965_ = lean_box(0);
v_isShared_6966_ = v_isSharedCheck_6970_;
goto v_resetjp_6964_;
}
v_resetjp_6964_:
{
lean_object* v___x_6968_; 
if (v_isShared_6966_ == 0)
{
v___x_6968_ = v___x_6965_;
goto v_reusejp_6967_;
}
else
{
lean_object* v_reuseFailAlloc_6969_; 
v_reuseFailAlloc_6969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6969_, 0, v_a_6963_);
v___x_6968_ = v_reuseFailAlloc_6969_;
goto v_reusejp_6967_;
}
v_reusejp_6967_:
{
return v___x_6968_;
}
}
}
}
v___jp_6940_:
{
lean_object* v___x_6942_; uint8_t v___x_6943_; 
v___x_6942_ = lean_array_get_size(v_infos_6941_);
v___x_6943_ = lean_nat_dec_lt(v___x_6937_, v___x_6942_);
if (v___x_6943_ == 0)
{
lean_dec_ref(v_infos_6941_);
v_a_6918_ = v___x_6939_;
goto v___jp_6917_;
}
else
{
size_t v___x_6944_; size_t v___x_6945_; lean_object* v___x_6946_; 
v___x_6944_ = ((size_t)0ULL);
v___x_6945_ = lean_usize_of_nat(v___x_6942_);
v___x_6946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_6941_, v___x_6944_, v___x_6945_, v___x_6939_, v_a_6893_);
lean_dec_ref(v_infos_6941_);
if (lean_obj_tag(v___x_6946_) == 0)
{
lean_object* v_a_6947_; 
v_a_6947_ = lean_ctor_get(v___x_6946_, 0);
lean_inc(v_a_6947_);
lean_dec_ref_known(v___x_6946_, 1);
v_a_6918_ = v_a_6947_;
goto v___jp_6917_;
}
else
{
lean_object* v_a_6948_; lean_object* v___x_6950_; uint8_t v_isShared_6951_; uint8_t v_isSharedCheck_6955_; 
lean_dec_ref(v_scope_6891_);
lean_dec_ref(v_service_6890_);
lean_dec_ref(v_cache_6889_);
v_a_6948_ = lean_ctor_get(v___x_6946_, 0);
v_isSharedCheck_6955_ = !lean_is_exclusive(v___x_6946_);
if (v_isSharedCheck_6955_ == 0)
{
v___x_6950_ = v___x_6946_;
v_isShared_6951_ = v_isSharedCheck_6955_;
goto v_resetjp_6949_;
}
else
{
lean_inc(v_a_6948_);
lean_dec(v___x_6946_);
v___x_6950_ = lean_box(0);
v_isShared_6951_ = v_isSharedCheck_6955_;
goto v_resetjp_6949_;
}
v_resetjp_6949_:
{
lean_object* v___x_6953_; 
if (v_isShared_6951_ == 0)
{
v___x_6953_ = v___x_6950_;
goto v_reusejp_6952_;
}
else
{
lean_object* v_reuseFailAlloc_6954_; 
v_reuseFailAlloc_6954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6954_, 0, v_a_6948_);
v___x_6953_ = v_reuseFailAlloc_6954_;
goto v_reusejp_6952_;
}
v_reusejp_6952_:
{
return v___x_6953_;
}
}
}
}
}
}
else
{
lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; 
lean_dec_ref(v_scope_6891_);
lean_dec_ref(v_service_6890_);
lean_dec_ref(v_cache_6889_);
v___x_6971_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__1));
lean_inc_ref(v_a_6893_);
v___x_6972_ = lean_apply_2(v_a_6893_, v___x_6971_, lean_box(0));
v___x_6973_ = lean_box(0);
v___x_6974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6974_, 0, v___x_6973_);
return v___x_6974_;
}
v___jp_6895_:
{
lean_object* v___x_6897_; lean_object* v___x_6898_; lean_object* v___x_6899_; 
v___x_6897_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6898_ = l_System_FilePath_join(v_cache_6889_, v___x_6897_);
v___x_6899_ = l_IO_FS_createDirAll(v___x_6898_);
if (lean_obj_tag(v___x_6899_) == 0)
{
uint8_t v___x_6900_; lean_object* v___x_6901_; lean_object* v___x_6902_; lean_object* v___x_6903_; 
lean_dec_ref_known(v___x_6899_, 1);
v___x_6900_ = 0;
v___x_6901_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6902_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6902_, 0, v_scope_6891_);
lean_ctor_set(v___x_6902_, 1, v_a_6896_);
lean_ctor_set(v___x_6902_, 2, v___x_6901_);
lean_ctor_set_uint8(v___x_6902_, sizeof(void*)*3, v___x_6900_);
v___x_6903_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6893_, v___x_6902_);
return v___x_6903_;
}
else
{
lean_object* v_a_6904_; lean_object* v___x_6906_; uint8_t v_isShared_6907_; uint8_t v_isSharedCheck_6916_; 
lean_dec_ref(v_a_6896_);
lean_dec_ref(v_scope_6891_);
v_a_6904_ = lean_ctor_get(v___x_6899_, 0);
v_isSharedCheck_6916_ = !lean_is_exclusive(v___x_6899_);
if (v_isSharedCheck_6916_ == 0)
{
v___x_6906_ = v___x_6899_;
v_isShared_6907_ = v_isSharedCheck_6916_;
goto v_resetjp_6905_;
}
else
{
lean_inc(v_a_6904_);
lean_dec(v___x_6899_);
v___x_6906_ = lean_box(0);
v_isShared_6907_ = v_isSharedCheck_6916_;
goto v_resetjp_6905_;
}
v_resetjp_6905_:
{
lean_object* v___x_6908_; uint8_t v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v___x_6914_; 
v___x_6908_ = lean_io_error_to_string(v_a_6904_);
v___x_6909_ = 3;
v___x_6910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6910_, 0, v___x_6908_);
lean_ctor_set_uint8(v___x_6910_, sizeof(void*)*1, v___x_6909_);
lean_inc_ref(v_a_6893_);
v___x_6911_ = lean_apply_2(v_a_6893_, v___x_6910_, lean_box(0));
v___x_6912_ = lean_box(0);
if (v_isShared_6907_ == 0)
{
lean_ctor_set(v___x_6906_, 0, v___x_6912_);
v___x_6914_ = v___x_6906_;
goto v_reusejp_6913_;
}
else
{
lean_object* v_reuseFailAlloc_6915_; 
v_reuseFailAlloc_6915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
v___x_6914_ = v_reuseFailAlloc_6915_;
goto v_reusejp_6913_;
}
v_reusejp_6913_:
{
return v___x_6914_;
}
}
}
}
v___jp_6917_:
{
lean_object* v___x_6919_; lean_object* v___x_6920_; uint8_t v___x_6921_; 
v___x_6919_ = lean_array_get_size(v_a_6918_);
v___x_6920_ = lean_unsigned_to_nat(0u);
v___x_6921_ = lean_nat_dec_eq(v___x_6919_, v___x_6920_);
if (v___x_6921_ == 0)
{
uint8_t v_isReservoir_6922_; 
v_isReservoir_6922_ = lean_ctor_get_uint8(v_service_6890_, sizeof(void*)*5);
if (v_isReservoir_6922_ == 0)
{
lean_dec_ref(v_service_6890_);
v_a_6896_ = v_a_6918_;
goto v___jp_6895_;
}
else
{
lean_object* v___x_6923_; lean_object* v___x_6924_; 
lean_inc_ref(v_scope_6891_);
v___x_6923_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6890_, v_scope_6891_);
v___x_6924_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6893_, v___x_6923_, v_a_6918_);
if (lean_obj_tag(v___x_6924_) == 0)
{
lean_object* v_a_6925_; 
v_a_6925_ = lean_ctor_get(v___x_6924_, 0);
lean_inc(v_a_6925_);
lean_dec_ref_known(v___x_6924_, 1);
v_a_6896_ = v_a_6925_;
goto v___jp_6895_;
}
else
{
lean_object* v_a_6926_; lean_object* v___x_6928_; uint8_t v_isShared_6929_; uint8_t v_isSharedCheck_6933_; 
lean_dec_ref(v_scope_6891_);
lean_dec_ref(v_cache_6889_);
v_a_6926_ = lean_ctor_get(v___x_6924_, 0);
v_isSharedCheck_6933_ = !lean_is_exclusive(v___x_6924_);
if (v_isSharedCheck_6933_ == 0)
{
v___x_6928_ = v___x_6924_;
v_isShared_6929_ = v_isSharedCheck_6933_;
goto v_resetjp_6927_;
}
else
{
lean_inc(v_a_6926_);
lean_dec(v___x_6924_);
v___x_6928_ = lean_box(0);
v_isShared_6929_ = v_isSharedCheck_6933_;
goto v_resetjp_6927_;
}
v_resetjp_6927_:
{
lean_object* v___x_6931_; 
if (v_isShared_6929_ == 0)
{
v___x_6931_ = v___x_6928_;
goto v_reusejp_6930_;
}
else
{
lean_object* v_reuseFailAlloc_6932_; 
v_reuseFailAlloc_6932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6932_, 0, v_a_6926_);
v___x_6931_ = v_reuseFailAlloc_6932_;
goto v_reusejp_6930_;
}
v_reusejp_6930_:
{
return v___x_6931_;
}
}
}
}
}
else
{
lean_object* v___x_6934_; lean_object* v___x_6935_; 
lean_dec_ref(v_a_6918_);
lean_dec_ref(v_scope_6891_);
lean_dec_ref(v_service_6890_);
lean_dec_ref(v_cache_6889_);
v___x_6934_ = lean_box(0);
v___x_6935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6935_, 0, v___x_6934_);
return v___x_6935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_6975_, lean_object* v_cache_6976_, lean_object* v_service_6977_, lean_object* v_scope_6978_, lean_object* v_force_6979_, lean_object* v_a_6980_, lean_object* v_a_6981_){
_start:
{
uint8_t v_force_boxed_6982_; lean_object* v_res_6983_; 
v_force_boxed_6982_ = lean_unbox(v_force_6979_);
v_res_6983_ = l_Lake_CacheService_downloadArtifacts(v_descrs_6975_, v_cache_6976_, v_service_6977_, v_scope_6978_, v_force_boxed_6982_, v_a_6980_);
lean_dec_ref(v_a_6980_);
lean_dec_ref(v_descrs_6975_);
return v_res_6983_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_6984_, lean_object* v_descrs_6985_, lean_object* v_cache_6986_, lean_object* v_service_6987_, lean_object* v_scope_6988_, uint8_t v_force_6989_){
_start:
{
lean_object* v_a_6992_; lean_object* v_a_7014_; lean_object* v___x_7032_; lean_object* v___x_7033_; uint8_t v___x_7034_; 
v___x_7032_ = lean_array_get_size(v_descrs_6985_);
v___x_7033_ = lean_unsigned_to_nat(0u);
v___x_7034_ = lean_nat_dec_eq(v___x_7032_, v___x_7033_);
if (v___x_7034_ == 0)
{
lean_object* v___x_7035_; lean_object* v_infos_7037_; uint8_t v___x_7052_; 
v___x_7035_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__0));
v___x_7052_ = lean_nat_dec_lt(v___x_7033_, v___x_7032_);
if (v___x_7052_ == 0)
{
v_infos_7037_ = v___x_7035_;
goto v___jp_7036_;
}
else
{
lean_object* v___x_7053_; size_t v___x_7054_; size_t v___x_7055_; lean_object* v___x_7056_; 
v___x_7053_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
v___x_7054_ = ((size_t)0ULL);
v___x_7055_ = lean_usize_of_nat(v___x_7032_);
lean_inc_ref(v_cache_6986_);
lean_inc_ref(v_scope_6988_);
lean_inc_ref(v_service_6987_);
v___x_7056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__3(v_service_6987_, v_scope_6988_, v_cache_6986_, v_force_6989_, v_descrs_6985_, v___x_7054_, v___x_7055_, v___x_7053_, v_a_6984_);
if (lean_obj_tag(v___x_7056_) == 0)
{
lean_object* v_a_7057_; lean_object* v_infos_7058_; 
v_a_7057_ = lean_ctor_get(v___x_7056_, 0);
lean_inc(v_a_7057_);
lean_dec_ref_known(v___x_7056_, 1);
v_infos_7058_ = lean_ctor_get(v_a_7057_, 0);
lean_inc_ref(v_infos_7058_);
lean_dec(v_a_7057_);
v_infos_7037_ = v_infos_7058_;
goto v___jp_7036_;
}
else
{
lean_object* v_a_7059_; lean_object* v___x_7061_; uint8_t v_isShared_7062_; uint8_t v_isSharedCheck_7066_; 
lean_dec_ref(v_scope_6988_);
lean_dec_ref(v_service_6987_);
lean_dec_ref(v_cache_6986_);
v_a_7059_ = lean_ctor_get(v___x_7056_, 0);
v_isSharedCheck_7066_ = !lean_is_exclusive(v___x_7056_);
if (v_isSharedCheck_7066_ == 0)
{
v___x_7061_ = v___x_7056_;
v_isShared_7062_ = v_isSharedCheck_7066_;
goto v_resetjp_7060_;
}
else
{
lean_inc(v_a_7059_);
lean_dec(v___x_7056_);
v___x_7061_ = lean_box(0);
v_isShared_7062_ = v_isSharedCheck_7066_;
goto v_resetjp_7060_;
}
v_resetjp_7060_:
{
lean_object* v___x_7064_; 
if (v_isShared_7062_ == 0)
{
v___x_7064_ = v___x_7061_;
goto v_reusejp_7063_;
}
else
{
lean_object* v_reuseFailAlloc_7065_; 
v_reuseFailAlloc_7065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7065_, 0, v_a_7059_);
v___x_7064_ = v_reuseFailAlloc_7065_;
goto v_reusejp_7063_;
}
v_reusejp_7063_:
{
return v___x_7064_;
}
}
}
}
v___jp_7036_:
{
lean_object* v___x_7038_; uint8_t v___x_7039_; 
v___x_7038_ = lean_array_get_size(v_infos_7037_);
v___x_7039_ = lean_nat_dec_lt(v___x_7033_, v___x_7038_);
if (v___x_7039_ == 0)
{
lean_dec_ref(v_infos_7037_);
v_a_7014_ = v___x_7035_;
goto v___jp_7013_;
}
else
{
size_t v___x_7040_; size_t v___x_7041_; lean_object* v___x_7042_; 
v___x_7040_ = ((size_t)0ULL);
v___x_7041_ = lean_usize_of_nat(v___x_7038_);
v___x_7042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_infos_7037_, v___x_7040_, v___x_7041_, v___x_7035_, v_a_6984_);
lean_dec_ref(v_infos_7037_);
if (lean_obj_tag(v___x_7042_) == 0)
{
lean_object* v_a_7043_; 
v_a_7043_ = lean_ctor_get(v___x_7042_, 0);
lean_inc(v_a_7043_);
lean_dec_ref_known(v___x_7042_, 1);
v_a_7014_ = v_a_7043_;
goto v___jp_7013_;
}
else
{
lean_object* v_a_7044_; lean_object* v___x_7046_; uint8_t v_isShared_7047_; uint8_t v_isSharedCheck_7051_; 
lean_dec_ref(v_scope_6988_);
lean_dec_ref(v_service_6987_);
lean_dec_ref(v_cache_6986_);
v_a_7044_ = lean_ctor_get(v___x_7042_, 0);
v_isSharedCheck_7051_ = !lean_is_exclusive(v___x_7042_);
if (v_isSharedCheck_7051_ == 0)
{
v___x_7046_ = v___x_7042_;
v_isShared_7047_ = v_isSharedCheck_7051_;
goto v_resetjp_7045_;
}
else
{
lean_inc(v_a_7044_);
lean_dec(v___x_7042_);
v___x_7046_ = lean_box(0);
v_isShared_7047_ = v_isSharedCheck_7051_;
goto v_resetjp_7045_;
}
v_resetjp_7045_:
{
lean_object* v___x_7049_; 
if (v_isShared_7047_ == 0)
{
v___x_7049_ = v___x_7046_;
goto v_reusejp_7048_;
}
else
{
lean_object* v_reuseFailAlloc_7050_; 
v_reuseFailAlloc_7050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7050_, 0, v_a_7044_);
v___x_7049_ = v_reuseFailAlloc_7050_;
goto v_reusejp_7048_;
}
v_reusejp_7048_:
{
return v___x_7049_;
}
}
}
}
}
}
else
{
lean_object* v___x_7067_; lean_object* v___x_7068_; lean_object* v___x_7069_; lean_object* v___x_7070_; 
lean_dec_ref(v_scope_6988_);
lean_dec_ref(v_service_6987_);
lean_dec_ref(v_cache_6986_);
v___x_7067_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__1));
lean_inc_ref(v_a_6984_);
v___x_7068_ = lean_apply_2(v_a_6984_, v___x_7067_, lean_box(0));
v___x_7069_ = lean_box(0);
v___x_7070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7070_, 0, v___x_7069_);
return v___x_7070_;
}
v___jp_6991_:
{
lean_object* v___x_6993_; lean_object* v___x_6994_; lean_object* v___x_6995_; 
v___x_6993_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6994_ = l_System_FilePath_join(v_cache_6986_, v___x_6993_);
v___x_6995_ = l_IO_FS_createDirAll(v___x_6994_);
if (lean_obj_tag(v___x_6995_) == 0)
{
uint8_t v___x_6996_; lean_object* v___x_6997_; lean_object* v___x_6998_; lean_object* v___x_6999_; 
lean_dec_ref_known(v___x_6995_, 1);
v___x_6996_ = 0;
v___x_6997_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6998_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6998_, 0, v_scope_6988_);
lean_ctor_set(v___x_6998_, 1, v_a_6992_);
lean_ctor_set(v___x_6998_, 2, v___x_6997_);
lean_ctor_set_uint8(v___x_6998_, sizeof(void*)*3, v___x_6996_);
v___x_6999_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6984_, v___x_6998_);
return v___x_6999_;
}
else
{
lean_object* v_a_7000_; lean_object* v___x_7002_; uint8_t v_isShared_7003_; uint8_t v_isSharedCheck_7012_; 
lean_dec_ref(v_a_6992_);
lean_dec_ref(v_scope_6988_);
v_a_7000_ = lean_ctor_get(v___x_6995_, 0);
v_isSharedCheck_7012_ = !lean_is_exclusive(v___x_6995_);
if (v_isSharedCheck_7012_ == 0)
{
v___x_7002_ = v___x_6995_;
v_isShared_7003_ = v_isSharedCheck_7012_;
goto v_resetjp_7001_;
}
else
{
lean_inc(v_a_7000_);
lean_dec(v___x_6995_);
v___x_7002_ = lean_box(0);
v_isShared_7003_ = v_isSharedCheck_7012_;
goto v_resetjp_7001_;
}
v_resetjp_7001_:
{
lean_object* v___x_7004_; uint8_t v___x_7005_; lean_object* v___x_7006_; lean_object* v___x_7007_; lean_object* v___x_7008_; lean_object* v___x_7010_; 
v___x_7004_ = lean_io_error_to_string(v_a_7000_);
v___x_7005_ = 3;
v___x_7006_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7006_, 0, v___x_7004_);
lean_ctor_set_uint8(v___x_7006_, sizeof(void*)*1, v___x_7005_);
lean_inc_ref(v_a_6984_);
v___x_7007_ = lean_apply_2(v_a_6984_, v___x_7006_, lean_box(0));
v___x_7008_ = lean_box(0);
if (v_isShared_7003_ == 0)
{
lean_ctor_set(v___x_7002_, 0, v___x_7008_);
v___x_7010_ = v___x_7002_;
goto v_reusejp_7009_;
}
else
{
lean_object* v_reuseFailAlloc_7011_; 
v_reuseFailAlloc_7011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7011_, 0, v___x_7008_);
v___x_7010_ = v_reuseFailAlloc_7011_;
goto v_reusejp_7009_;
}
v_reusejp_7009_:
{
return v___x_7010_;
}
}
}
}
v___jp_7013_:
{
lean_object* v___x_7015_; lean_object* v___x_7016_; uint8_t v___x_7017_; 
v___x_7015_ = lean_array_get_size(v_a_7014_);
v___x_7016_ = lean_unsigned_to_nat(0u);
v___x_7017_ = lean_nat_dec_eq(v___x_7015_, v___x_7016_);
if (v___x_7017_ == 0)
{
uint8_t v_isReservoir_7018_; 
v_isReservoir_7018_ = lean_ctor_get_uint8(v_service_6987_, sizeof(void*)*5);
if (v_isReservoir_7018_ == 0)
{
lean_dec_ref(v_service_6987_);
v_a_6992_ = v_a_7014_;
goto v___jp_6991_;
}
else
{
lean_object* v___x_7019_; lean_object* v___x_7020_; 
lean_inc_ref(v_scope_6988_);
v___x_7019_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6987_, v_scope_6988_);
v___x_7020_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6984_, v___x_7019_, v_a_7014_);
if (lean_obj_tag(v___x_7020_) == 0)
{
lean_object* v_a_7021_; 
v_a_7021_ = lean_ctor_get(v___x_7020_, 0);
lean_inc(v_a_7021_);
lean_dec_ref_known(v___x_7020_, 1);
v_a_6992_ = v_a_7021_;
goto v___jp_6991_;
}
else
{
lean_object* v_a_7022_; lean_object* v___x_7024_; uint8_t v_isShared_7025_; uint8_t v_isSharedCheck_7029_; 
lean_dec_ref(v_scope_6988_);
lean_dec_ref(v_cache_6986_);
v_a_7022_ = lean_ctor_get(v___x_7020_, 0);
v_isSharedCheck_7029_ = !lean_is_exclusive(v___x_7020_);
if (v_isSharedCheck_7029_ == 0)
{
v___x_7024_ = v___x_7020_;
v_isShared_7025_ = v_isSharedCheck_7029_;
goto v_resetjp_7023_;
}
else
{
lean_inc(v_a_7022_);
lean_dec(v___x_7020_);
v___x_7024_ = lean_box(0);
v_isShared_7025_ = v_isSharedCheck_7029_;
goto v_resetjp_7023_;
}
v_resetjp_7023_:
{
lean_object* v___x_7027_; 
if (v_isShared_7025_ == 0)
{
v___x_7027_ = v___x_7024_;
goto v_reusejp_7026_;
}
else
{
lean_object* v_reuseFailAlloc_7028_; 
v_reuseFailAlloc_7028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7028_, 0, v_a_7022_);
v___x_7027_ = v_reuseFailAlloc_7028_;
goto v_reusejp_7026_;
}
v_reusejp_7026_:
{
return v___x_7027_;
}
}
}
}
}
else
{
lean_object* v___x_7030_; lean_object* v___x_7031_; 
lean_dec_ref(v_a_7014_);
lean_dec_ref(v_scope_6988_);
lean_dec_ref(v_service_6987_);
lean_dec_ref(v_cache_6986_);
v___x_7030_ = lean_box(0);
v___x_7031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7031_, 0, v___x_7030_);
return v___x_7031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_7071_, lean_object* v_descrs_7072_, lean_object* v_cache_7073_, lean_object* v_service_7074_, lean_object* v_scope_7075_, lean_object* v_force_7076_, lean_object* v_a_7077_){
_start:
{
uint8_t v_force_boxed_7078_; lean_object* v_res_7079_; 
v_force_boxed_7078_ = lean_unbox(v_force_7076_);
v_res_7079_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_7071_, v_descrs_7072_, v_cache_7073_, v_service_7074_, v_scope_7075_, v_force_boxed_7078_);
lean_dec_ref(v_descrs_7072_);
lean_dec_ref(v_a_7071_);
return v_res_7079_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_7080_, lean_object* v_cache_7081_, lean_object* v_service_7082_, lean_object* v_localScope_7083_, lean_object* v_remoteScope_7084_, uint8_t v_force_7085_, lean_object* v_a_7086_){
_start:
{
lean_object* v_name_x3f_7088_; lean_object* v___x_7089_; uint8_t v___x_7090_; lean_object* v___x_7091_; 
v_name_x3f_7088_ = lean_ctor_get(v_service_7082_, 0);
lean_inc_ref(v_remoteScope_7084_);
v___x_7089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7089_, 0, v_remoteScope_7084_);
v___x_7090_ = 1;
lean_inc(v_name_x3f_7088_);
lean_inc_ref(v_cache_7081_);
v___x_7091_ = l_Lake_Cache_writeMap(v_cache_7081_, v_localScope_7083_, v_map_7080_, v_name_x3f_7088_, v___x_7089_, v___x_7090_);
if (lean_obj_tag(v___x_7091_) == 0)
{
lean_object* v___x_7093_; uint8_t v_isShared_7094_; uint8_t v_isSharedCheck_7127_; 
v_isSharedCheck_7127_ = !lean_is_exclusive(v___x_7091_);
if (v_isSharedCheck_7127_ == 0)
{
lean_object* v_unused_7128_; 
v_unused_7128_ = lean_ctor_get(v___x_7091_, 0);
lean_dec(v_unused_7128_);
v___x_7093_ = v___x_7091_;
v_isShared_7094_ = v_isSharedCheck_7127_;
goto v_resetjp_7092_;
}
else
{
lean_dec(v___x_7091_);
v___x_7093_ = lean_box(0);
v_isShared_7094_ = v_isSharedCheck_7127_;
goto v_resetjp_7092_;
}
v_resetjp_7092_:
{
lean_object* v___x_7095_; lean_object* v___x_7096_; lean_object* v___x_7097_; 
v___x_7095_ = lean_unsigned_to_nat(0u);
v___x_7096_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_7097_ = l_Lake_CacheMap_collectOutputDescrs(v_map_7080_, v___x_7096_);
if (lean_obj_tag(v___x_7097_) == 0)
{
lean_object* v_a_7098_; lean_object* v_a_7099_; lean_object* v___x_7100_; uint8_t v___x_7101_; 
lean_del_object(v___x_7093_);
v_a_7098_ = lean_ctor_get(v___x_7097_, 0);
lean_inc(v_a_7098_);
v_a_7099_ = lean_ctor_get(v___x_7097_, 1);
lean_inc(v_a_7099_);
lean_dec_ref_known(v___x_7097_, 2);
v___x_7100_ = lean_array_get_size(v_a_7099_);
v___x_7101_ = lean_nat_dec_lt(v___x_7095_, v___x_7100_);
if (v___x_7101_ == 0)
{
lean_object* v___x_7102_; 
lean_dec(v_a_7099_);
v___x_7102_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_7086_, v_a_7098_, v_cache_7081_, v_service_7082_, v_remoteScope_7084_, v_force_7085_);
lean_dec(v_a_7098_);
return v___x_7102_;
}
else
{
lean_object* v___x_7103_; size_t v___x_7104_; size_t v___x_7105_; lean_object* v___x_7106_; 
v___x_7103_ = lean_box(0);
v___x_7104_ = ((size_t)0ULL);
v___x_7105_ = lean_usize_of_nat(v___x_7100_);
v___x_7106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7099_, v___x_7104_, v___x_7105_, v___x_7103_, v_a_7086_);
lean_dec(v_a_7099_);
if (lean_obj_tag(v___x_7106_) == 0)
{
lean_object* v___x_7107_; 
lean_dec_ref_known(v___x_7106_, 1);
v___x_7107_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_7086_, v_a_7098_, v_cache_7081_, v_service_7082_, v_remoteScope_7084_, v_force_7085_);
lean_dec(v_a_7098_);
return v___x_7107_;
}
else
{
lean_dec(v_a_7098_);
lean_dec_ref(v_remoteScope_7084_);
lean_dec_ref(v_service_7082_);
lean_dec_ref(v_cache_7081_);
return v___x_7106_;
}
}
}
else
{
lean_object* v_a_7108_; lean_object* v___x_7109_; uint8_t v___x_7110_; 
lean_dec_ref(v_remoteScope_7084_);
lean_dec_ref(v_service_7082_);
lean_dec_ref(v_cache_7081_);
v_a_7108_ = lean_ctor_get(v___x_7097_, 1);
lean_inc(v_a_7108_);
lean_dec_ref_known(v___x_7097_, 2);
v___x_7109_ = lean_array_get_size(v_a_7108_);
v___x_7110_ = lean_nat_dec_lt(v___x_7095_, v___x_7109_);
if (v___x_7110_ == 0)
{
lean_object* v___x_7111_; lean_object* v___x_7113_; 
lean_dec(v_a_7108_);
v___x_7111_ = lean_box(0);
if (v_isShared_7094_ == 0)
{
lean_ctor_set_tag(v___x_7093_, 1);
lean_ctor_set(v___x_7093_, 0, v___x_7111_);
v___x_7113_ = v___x_7093_;
goto v_reusejp_7112_;
}
else
{
lean_object* v_reuseFailAlloc_7114_; 
v_reuseFailAlloc_7114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7114_, 0, v___x_7111_);
v___x_7113_ = v_reuseFailAlloc_7114_;
goto v_reusejp_7112_;
}
v_reusejp_7112_:
{
return v___x_7113_;
}
}
else
{
lean_object* v___x_7115_; size_t v___x_7116_; size_t v___x_7117_; lean_object* v___x_7118_; 
lean_del_object(v___x_7093_);
v___x_7115_ = lean_box(0);
v___x_7116_ = ((size_t)0ULL);
v___x_7117_ = lean_usize_of_nat(v___x_7109_);
v___x_7118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7108_, v___x_7116_, v___x_7117_, v___x_7115_, v_a_7086_);
lean_dec(v_a_7108_);
if (lean_obj_tag(v___x_7118_) == 0)
{
lean_object* v___x_7120_; uint8_t v_isShared_7121_; uint8_t v_isSharedCheck_7125_; 
v_isSharedCheck_7125_ = !lean_is_exclusive(v___x_7118_);
if (v_isSharedCheck_7125_ == 0)
{
lean_object* v_unused_7126_; 
v_unused_7126_ = lean_ctor_get(v___x_7118_, 0);
lean_dec(v_unused_7126_);
v___x_7120_ = v___x_7118_;
v_isShared_7121_ = v_isSharedCheck_7125_;
goto v_resetjp_7119_;
}
else
{
lean_dec(v___x_7118_);
v___x_7120_ = lean_box(0);
v_isShared_7121_ = v_isSharedCheck_7125_;
goto v_resetjp_7119_;
}
v_resetjp_7119_:
{
lean_object* v___x_7123_; 
if (v_isShared_7121_ == 0)
{
lean_ctor_set_tag(v___x_7120_, 1);
lean_ctor_set(v___x_7120_, 0, v___x_7115_);
v___x_7123_ = v___x_7120_;
goto v_reusejp_7122_;
}
else
{
lean_object* v_reuseFailAlloc_7124_; 
v_reuseFailAlloc_7124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7124_, 0, v___x_7115_);
v___x_7123_ = v_reuseFailAlloc_7124_;
goto v_reusejp_7122_;
}
v_reusejp_7122_:
{
return v___x_7123_;
}
}
}
else
{
return v___x_7118_;
}
}
}
}
}
else
{
lean_object* v_a_7129_; lean_object* v___x_7131_; uint8_t v_isShared_7132_; uint8_t v_isSharedCheck_7141_; 
lean_dec_ref(v_remoteScope_7084_);
lean_dec_ref(v_service_7082_);
lean_dec_ref(v_cache_7081_);
lean_dec_ref(v_map_7080_);
v_a_7129_ = lean_ctor_get(v___x_7091_, 0);
v_isSharedCheck_7141_ = !lean_is_exclusive(v___x_7091_);
if (v_isSharedCheck_7141_ == 0)
{
v___x_7131_ = v___x_7091_;
v_isShared_7132_ = v_isSharedCheck_7141_;
goto v_resetjp_7130_;
}
else
{
lean_inc(v_a_7129_);
lean_dec(v___x_7091_);
v___x_7131_ = lean_box(0);
v_isShared_7132_ = v_isSharedCheck_7141_;
goto v_resetjp_7130_;
}
v_resetjp_7130_:
{
lean_object* v___x_7133_; uint8_t v___x_7134_; lean_object* v___x_7135_; lean_object* v___x_7136_; lean_object* v___x_7137_; lean_object* v___x_7139_; 
v___x_7133_ = lean_io_error_to_string(v_a_7129_);
v___x_7134_ = 3;
v___x_7135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7135_, 0, v___x_7133_);
lean_ctor_set_uint8(v___x_7135_, sizeof(void*)*1, v___x_7134_);
lean_inc_ref(v_a_7086_);
v___x_7136_ = lean_apply_2(v_a_7086_, v___x_7135_, lean_box(0));
v___x_7137_ = lean_box(0);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 0, v___x_7137_);
v___x_7139_ = v___x_7131_;
goto v_reusejp_7138_;
}
else
{
lean_object* v_reuseFailAlloc_7140_; 
v_reuseFailAlloc_7140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7140_, 0, v___x_7137_);
v___x_7139_ = v_reuseFailAlloc_7140_;
goto v_reusejp_7138_;
}
v_reusejp_7138_:
{
return v___x_7139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_7142_, lean_object* v_cache_7143_, lean_object* v_service_7144_, lean_object* v_localScope_7145_, lean_object* v_remoteScope_7146_, lean_object* v_force_7147_, lean_object* v_a_7148_, lean_object* v_a_7149_){
_start:
{
uint8_t v_force_boxed_7150_; lean_object* v_res_7151_; 
v_force_boxed_7150_ = lean_unbox(v_force_7147_);
v_res_7151_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_7142_, v_cache_7143_, v_service_7144_, v_localScope_7145_, v_remoteScope_7146_, v_force_boxed_7150_, v_a_7148_);
lean_dec_ref(v_a_7148_);
return v_res_7151_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* v_m_7152_, uint64_t v_a_7153_){
_start:
{
lean_object* v_buckets_7154_; lean_object* v___x_7155_; uint64_t v___x_7156_; uint64_t v___x_7157_; uint64_t v_fold_7158_; uint64_t v___x_7159_; uint64_t v___x_7160_; uint64_t v___x_7161_; size_t v___x_7162_; size_t v___x_7163_; size_t v___x_7164_; size_t v___x_7165_; size_t v___x_7166_; lean_object* v___x_7167_; uint8_t v___x_7168_; 
v_buckets_7154_ = lean_ctor_get(v_m_7152_, 1);
v___x_7155_ = lean_array_get_size(v_buckets_7154_);
v___x_7156_ = 32ULL;
v___x_7157_ = lean_uint64_shift_right(v_a_7153_, v___x_7156_);
v_fold_7158_ = lean_uint64_xor(v_a_7153_, v___x_7157_);
v___x_7159_ = 16ULL;
v___x_7160_ = lean_uint64_shift_right(v_fold_7158_, v___x_7159_);
v___x_7161_ = lean_uint64_xor(v_fold_7158_, v___x_7160_);
v___x_7162_ = lean_uint64_to_usize(v___x_7161_);
v___x_7163_ = lean_usize_of_nat(v___x_7155_);
v___x_7164_ = ((size_t)1ULL);
v___x_7165_ = lean_usize_sub(v___x_7163_, v___x_7164_);
v___x_7166_ = lean_usize_land(v___x_7162_, v___x_7165_);
v___x_7167_ = lean_array_uget_borrowed(v_buckets_7154_, v___x_7166_);
v___x_7168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_7153_, v___x_7167_);
return v___x_7168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* v_m_7169_, lean_object* v_a_7170_){
_start:
{
uint64_t v_a_boxed_7171_; uint8_t v_res_7172_; lean_object* v_r_7173_; 
v_a_boxed_7171_ = lean_unbox_uint64(v_a_7170_);
lean_dec_ref(v_a_7170_);
v_res_7172_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_m_7169_, v_a_boxed_7171_);
lean_dec_ref(v_m_7169_);
v_r_7173_ = lean_box(v_res_7172_);
return v_r_7173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(lean_object* v_descrs_7174_, lean_object* v_service_7175_, lean_object* v_scope_7176_, lean_object* v_paths_7177_, lean_object* v_n_7178_, lean_object* v_i_7179_, lean_object* v_a_7180_){
_start:
{
lean_object* v_zero_7182_; uint8_t v_isZero_7183_; 
v_zero_7182_ = lean_unsigned_to_nat(0u);
v_isZero_7183_ = lean_nat_dec_eq(v_i_7179_, v_zero_7182_);
if (v_isZero_7183_ == 1)
{
lean_object* v___x_7184_; 
lean_dec(v_i_7179_);
lean_dec_ref(v_scope_7176_);
lean_dec_ref(v_service_7175_);
v___x_7184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7184_, 0, v_a_7180_);
return v___x_7184_;
}
else
{
lean_object* v_one_7185_; lean_object* v_n_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7189_; uint64_t v_hash_7190_; lean_object* v_infos_7191_; lean_object* v_indices_7192_; lean_object* v_url_7193_; uint8_t v___x_7194_; 
v_one_7185_ = lean_unsigned_to_nat(1u);
v_n_7186_ = lean_nat_sub(v_i_7179_, v_one_7185_);
lean_dec(v_i_7179_);
v___x_7187_ = lean_nat_sub(v_n_7178_, v_n_7186_);
v___x_7188_ = lean_nat_sub(v___x_7187_, v_one_7185_);
lean_dec(v___x_7187_);
v___x_7189_ = lean_array_fget_borrowed(v_descrs_7174_, v___x_7188_);
v_hash_7190_ = lean_ctor_get_uint64(v___x_7189_, sizeof(void*)*1);
v_infos_7191_ = lean_ctor_get(v_a_7180_, 0);
v_indices_7192_ = lean_ctor_get(v_a_7180_, 1);
lean_inc_ref(v_scope_7176_);
lean_inc_ref(v_service_7175_);
v_url_7193_ = l_Lake_CacheService_artifactUrl(v_hash_7190_, v_service_7175_, v_scope_7176_);
v___x_7194_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_indices_7192_, v_hash_7190_);
if (v___x_7194_ == 0)
{
lean_object* v___x_7196_; uint8_t v_isShared_7197_; uint8_t v_isSharedCheck_7208_; 
lean_inc_ref(v_indices_7192_);
lean_inc_ref(v_infos_7191_);
v_isSharedCheck_7208_ = !lean_is_exclusive(v_a_7180_);
if (v_isSharedCheck_7208_ == 0)
{
lean_object* v_unused_7209_; lean_object* v_unused_7210_; 
v_unused_7209_ = lean_ctor_get(v_a_7180_, 1);
lean_dec(v_unused_7209_);
v_unused_7210_ = lean_ctor_get(v_a_7180_, 0);
lean_dec(v_unused_7210_);
v___x_7196_ = v_a_7180_;
v_isShared_7197_ = v_isSharedCheck_7208_;
goto v_resetjp_7195_;
}
else
{
lean_dec(v_a_7180_);
v___x_7196_ = lean_box(0);
v_isShared_7197_ = v_isSharedCheck_7208_;
goto v_resetjp_7195_;
}
v_resetjp_7195_:
{
lean_object* v___x_7198_; lean_object* v___x_7199_; lean_object* v___x_7200_; lean_object* v___x_7201_; lean_object* v___x_7202_; lean_object* v___x_7203_; lean_object* v___x_7205_; 
v___x_7198_ = lean_array_fget_borrowed(v_paths_7177_, v___x_7188_);
lean_dec(v___x_7188_);
v___x_7199_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc(v___x_7198_);
v___x_7200_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7200_, 0, v_url_7193_);
lean_ctor_set(v___x_7200_, 1, v___x_7198_);
lean_ctor_set(v___x_7200_, 2, v___x_7199_);
lean_ctor_set_uint64(v___x_7200_, sizeof(void*)*3, v_hash_7190_);
lean_inc_ref(v_infos_7191_);
v___x_7201_ = lean_array_push(v_infos_7191_, v___x_7200_);
v___x_7202_ = lean_array_get_size(v_infos_7191_);
lean_dec_ref(v_infos_7191_);
v___x_7203_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_indices_7192_, v_hash_7190_, v___x_7202_);
if (v_isShared_7197_ == 0)
{
lean_ctor_set(v___x_7196_, 1, v___x_7203_);
lean_ctor_set(v___x_7196_, 0, v___x_7201_);
v___x_7205_ = v___x_7196_;
goto v_reusejp_7204_;
}
else
{
lean_object* v_reuseFailAlloc_7207_; 
v_reuseFailAlloc_7207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7207_, 0, v___x_7201_);
lean_ctor_set(v_reuseFailAlloc_7207_, 1, v___x_7203_);
v___x_7205_ = v_reuseFailAlloc_7207_;
goto v_reusejp_7204_;
}
v_reusejp_7204_:
{
v_i_7179_ = v_n_7186_;
v_a_7180_ = v___x_7205_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_url_7193_);
lean_dec(v___x_7188_);
v_i_7179_ = v_n_7186_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg___boxed(lean_object* v_descrs_7212_, lean_object* v_service_7213_, lean_object* v_scope_7214_, lean_object* v_paths_7215_, lean_object* v_n_7216_, lean_object* v_i_7217_, lean_object* v_a_7218_, lean_object* v___y_7219_){
_start:
{
lean_object* v_res_7220_; 
v_res_7220_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_7212_, v_service_7213_, v_scope_7214_, v_paths_7215_, v_n_7216_, v_i_7217_, v_a_7218_);
lean_dec(v_n_7216_);
lean_dec_ref(v_paths_7215_);
lean_dec_ref(v_descrs_7212_);
return v_res_7220_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_7225_, lean_object* v_descrs_7226_, lean_object* v_paths_7227_, lean_object* v_service_7228_, lean_object* v_scope_7229_, lean_object* v_a_7230_){
_start:
{
lean_object* v___x_7232_; uint8_t v___x_7233_; 
v___x_7232_ = lean_unsigned_to_nat(0u);
v___x_7233_ = lean_nat_dec_eq(v_n_7225_, v___x_7232_);
if (v___x_7233_ == 0)
{
lean_object* v___x_7234_; lean_object* v___x_7235_; lean_object* v_a_7236_; lean_object* v_infos_7237_; lean_object* v_key_7238_; uint8_t v___x_7239_; lean_object* v___x_7240_; lean_object* v___x_7241_; 
v___x_7234_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1, &l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_TransferDict_empty___closed__1);
lean_inc(v_n_7225_);
lean_inc_ref(v_scope_7229_);
lean_inc_ref(v_service_7228_);
v___x_7235_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_7226_, v_service_7228_, v_scope_7229_, v_paths_7227_, v_n_7225_, v_n_7225_, v___x_7234_);
lean_dec(v_n_7225_);
v_a_7236_ = lean_ctor_get(v___x_7235_, 0);
lean_inc(v_a_7236_);
lean_dec_ref(v___x_7235_);
v_infos_7237_ = lean_ctor_get(v_a_7236_, 0);
lean_inc_ref(v_infos_7237_);
lean_dec(v_a_7236_);
v_key_7238_ = lean_ctor_get(v_service_7228_, 1);
lean_inc_ref(v_key_7238_);
lean_dec_ref(v_service_7228_);
v___x_7239_ = 1;
v___x_7240_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7240_, 0, v_scope_7229_);
lean_ctor_set(v___x_7240_, 1, v_infos_7237_);
lean_ctor_set(v___x_7240_, 2, v_key_7238_);
lean_ctor_set_uint8(v___x_7240_, sizeof(void*)*3, v___x_7239_);
v___x_7241_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_7230_, v___x_7240_);
return v___x_7241_;
}
else
{
lean_object* v___x_7242_; lean_object* v___x_7243_; lean_object* v___x_7244_; lean_object* v___x_7245_; 
lean_dec_ref(v_scope_7229_);
lean_dec_ref(v_service_7228_);
lean_dec(v_n_7225_);
v___x_7242_ = ((lean_object*)(l_Lake_CacheService_uploadArtifacts___closed__1));
lean_inc_ref(v_a_7230_);
v___x_7243_ = lean_apply_2(v_a_7230_, v___x_7242_, lean_box(0));
v___x_7244_ = lean_box(0);
v___x_7245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7245_, 0, v___x_7244_);
return v___x_7245_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_7246_, lean_object* v_descrs_7247_, lean_object* v_paths_7248_, lean_object* v_service_7249_, lean_object* v_scope_7250_, lean_object* v_a_7251_, lean_object* v_a_7252_){
_start:
{
lean_object* v_res_7253_; 
v_res_7253_ = l_Lake_CacheService_uploadArtifacts(v_n_7246_, v_descrs_7247_, v_paths_7248_, v_service_7249_, v_scope_7250_, v_a_7251_);
lean_dec_ref(v_a_7251_);
lean_dec_ref(v_paths_7248_);
lean_dec_ref(v_descrs_7247_);
return v_res_7253_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object* v_00_u03b2_7254_, lean_object* v_m_7255_, uint64_t v_a_7256_){
_start:
{
uint8_t v___x_7257_; 
v___x_7257_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_m_7255_, v_a_7256_);
return v___x_7257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* v_00_u03b2_7258_, lean_object* v_m_7259_, lean_object* v_a_7260_){
_start:
{
uint64_t v_a_boxed_7261_; uint8_t v_res_7262_; lean_object* v_r_7263_; 
v_a_boxed_7261_ = lean_unbox_uint64(v_a_7260_);
lean_dec_ref(v_a_7260_);
v_res_7262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_CacheService_uploadArtifacts_spec__0(v_00_u03b2_7258_, v_m_7259_, v_a_boxed_7261_);
lean_dec_ref(v_m_7259_);
v_r_7263_ = lean_box(v_res_7262_);
return v_r_7263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(lean_object* v_descrs_7264_, lean_object* v_service_7265_, lean_object* v_scope_7266_, lean_object* v_paths_7267_, lean_object* v_n_7268_, lean_object* v_i_7269_, lean_object* v_a_7270_, lean_object* v_a_7271_, lean_object* v___y_7272_){
_start:
{
lean_object* v___x_7274_; 
v___x_7274_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___redArg(v_descrs_7264_, v_service_7265_, v_scope_7266_, v_paths_7267_, v_n_7268_, v_i_7269_, v_a_7271_);
return v___x_7274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1___boxed(lean_object* v_descrs_7275_, lean_object* v_service_7276_, lean_object* v_scope_7277_, lean_object* v_paths_7278_, lean_object* v_n_7279_, lean_object* v_i_7280_, lean_object* v_a_7281_, lean_object* v_a_7282_, lean_object* v___y_7283_, lean_object* v___y_7284_){
_start:
{
lean_object* v_res_7285_; 
v_res_7285_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__1(v_descrs_7275_, v_service_7276_, v_scope_7277_, v_paths_7278_, v_n_7279_, v_i_7280_, v_a_7281_, v_a_7282_, v___y_7283_);
lean_dec_ref(v___y_7283_);
lean_dec(v_n_7279_);
lean_dec_ref(v_paths_7278_);
lean_dec_ref(v_descrs_7275_);
return v_res_7285_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_7290_, lean_object* v_service_7291_, lean_object* v_scope_7292_, lean_object* v_platform_7293_, lean_object* v_toolchain_7294_){
_start:
{
lean_object* v_url_7296_; lean_object* v_url_7303_; 
if (lean_obj_tag(v_scope_7292_) == 0)
{
lean_object* v_s_7312_; lean_object* v_revisionEndpoint_7313_; lean_object* v___x_7314_; lean_object* v___x_7315_; lean_object* v___x_7316_; lean_object* v___x_7317_; lean_object* v___x_7318_; lean_object* v___x_7319_; 
v_s_7312_ = lean_ctor_get(v_scope_7292_, 0);
lean_inc_ref(v_s_7312_);
lean_dec_ref_known(v_scope_7292_, 1);
v_revisionEndpoint_7313_ = lean_ctor_get(v_service_7291_, 3);
lean_inc_ref(v_revisionEndpoint_7313_);
lean_dec_ref(v_service_7291_);
v___x_7314_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_7313_, v_s_7312_);
v___x_7315_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_7316_ = lean_string_append(v___x_7315_, v_rev_7290_);
v___x_7317_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_7318_ = lean_string_append(v___x_7316_, v___x_7317_);
v___x_7319_ = lean_string_append(v___x_7314_, v___x_7318_);
lean_dec_ref(v___x_7318_);
return v___x_7319_;
}
else
{
lean_object* v_s_7320_; lean_object* v_revisionEndpoint_7321_; lean_object* v_url_7322_; lean_object* v___x_7323_; lean_object* v___x_7324_; uint8_t v___x_7325_; 
v_s_7320_ = lean_ctor_get(v_scope_7292_, 0);
lean_inc_ref(v_s_7320_);
lean_dec_ref_known(v_scope_7292_, 1);
v_revisionEndpoint_7321_ = lean_ctor_get(v_service_7291_, 3);
lean_inc_ref(v_revisionEndpoint_7321_);
lean_dec_ref(v_service_7291_);
v_url_7322_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_7321_, v_s_7320_);
v___x_7323_ = lean_string_utf8_byte_size(v_platform_7293_);
v___x_7324_ = lean_unsigned_to_nat(0u);
v___x_7325_ = lean_nat_dec_eq(v___x_7323_, v___x_7324_);
if (v___x_7325_ == 0)
{
lean_object* v___x_7326_; lean_object* v___x_7327_; lean_object* v_url_7328_; 
v___x_7326_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_7327_ = lean_string_append(v_url_7322_, v___x_7326_);
v_url_7328_ = l_Lake_uriEncode(v_platform_7293_, v___x_7327_);
v_url_7303_ = v_url_7328_;
goto v___jp_7302_;
}
else
{
v_url_7303_ = v_url_7322_;
goto v___jp_7302_;
}
}
v___jp_7295_:
{
lean_object* v___x_7297_; lean_object* v___x_7298_; lean_object* v___x_7299_; lean_object* v___x_7300_; lean_object* v___x_7301_; 
v___x_7297_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_7298_ = lean_string_append(v_url_7296_, v___x_7297_);
v___x_7299_ = lean_string_append(v___x_7298_, v_rev_7290_);
v___x_7300_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_7301_ = lean_string_append(v___x_7299_, v___x_7300_);
return v___x_7301_;
}
v___jp_7302_:
{
lean_object* v___x_7304_; lean_object* v___x_7305_; uint8_t v___x_7306_; 
v___x_7304_ = lean_string_utf8_byte_size(v_toolchain_7294_);
v___x_7305_ = lean_unsigned_to_nat(0u);
v___x_7306_ = lean_nat_dec_eq(v___x_7304_, v___x_7305_);
if (v___x_7306_ == 0)
{
lean_object* v___x_7307_; lean_object* v___x_7308_; lean_object* v___x_7309_; lean_object* v___x_7310_; lean_object* v_url_7311_; 
v___x_7307_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_7308_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_7294_, v___x_7307_, v___x_7305_);
v___x_7309_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_7310_ = lean_string_append(v_url_7303_, v___x_7309_);
v_url_7311_ = l_Lake_uriEncode(v___x_7308_, v___x_7310_);
lean_dec_ref(v___x_7308_);
v_url_7296_ = v_url_7311_;
goto v___jp_7295_;
}
else
{
v_url_7296_ = v_url_7303_;
goto v___jp_7295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_7329_, lean_object* v_service_7330_, lean_object* v_scope_7331_, lean_object* v_platform_7332_, lean_object* v_toolchain_7333_){
_start:
{
lean_object* v_res_7334_; 
v_res_7334_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7329_, v_service_7330_, v_scope_7331_, v_platform_7332_, v_toolchain_7333_);
lean_dec_ref(v_toolchain_7333_);
lean_dec_ref(v_platform_7332_);
lean_dec_ref(v_rev_7329_);
return v_res_7334_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_7338_, lean_object* v_service_7339_, lean_object* v_scope_7340_, lean_object* v_platform_7341_, lean_object* v_toolchain_7342_){
_start:
{
lean_object* v_url_7344_; lean_object* v___y_7352_; uint8_t v_isReservoir_7362_; 
v_isReservoir_7362_ = lean_ctor_get_uint8(v_service_7339_, sizeof(void*)*5);
if (v_isReservoir_7362_ == 0)
{
lean_object* v___x_7363_; 
v___x_7363_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7338_, v_service_7339_, v_scope_7340_, v_platform_7341_, v_toolchain_7342_);
return v___x_7363_;
}
else
{
if (lean_obj_tag(v_scope_7340_) == 0)
{
lean_object* v_apiEndpoint_7364_; lean_object* v_s_7365_; lean_object* v___x_7366_; lean_object* v___x_7367_; lean_object* v___x_7368_; 
v_apiEndpoint_7364_ = lean_ctor_get(v_service_7339_, 4);
lean_inc_ref(v_apiEndpoint_7364_);
lean_dec_ref(v_service_7339_);
v_s_7365_ = lean_ctor_get(v_scope_7340_, 0);
lean_inc_ref(v_s_7365_);
lean_dec_ref_known(v_scope_7340_, 1);
v___x_7366_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_7367_ = lean_string_append(v_apiEndpoint_7364_, v___x_7366_);
v___x_7368_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_7367_, v_s_7365_);
v___y_7352_ = v___x_7368_;
goto v___jp_7351_;
}
else
{
lean_object* v_apiEndpoint_7369_; lean_object* v_s_7370_; lean_object* v___x_7371_; lean_object* v___x_7372_; lean_object* v___x_7373_; 
v_apiEndpoint_7369_ = lean_ctor_get(v_service_7339_, 4);
lean_inc_ref(v_apiEndpoint_7369_);
lean_dec_ref(v_service_7339_);
v_s_7370_ = lean_ctor_get(v_scope_7340_, 0);
lean_inc_ref(v_s_7370_);
lean_dec_ref_known(v_scope_7340_, 1);
v___x_7371_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_7372_ = lean_string_append(v_apiEndpoint_7369_, v___x_7371_);
v___x_7373_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_7372_, v_s_7370_);
v___y_7352_ = v___x_7373_;
goto v___jp_7351_;
}
}
v___jp_7343_:
{
lean_object* v___x_7345_; lean_object* v___x_7346_; uint8_t v___x_7347_; 
v___x_7345_ = lean_string_utf8_byte_size(v_toolchain_7342_);
v___x_7346_ = lean_unsigned_to_nat(0u);
v___x_7347_ = lean_nat_dec_eq(v___x_7345_, v___x_7346_);
if (v___x_7347_ == 0)
{
lean_object* v___x_7348_; lean_object* v___x_7349_; lean_object* v_url_7350_; 
v___x_7348_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_7349_ = lean_string_append(v_url_7344_, v___x_7348_);
v_url_7350_ = l_Lake_uriEncode(v_toolchain_7342_, v___x_7349_);
return v_url_7350_;
}
else
{
return v_url_7344_;
}
}
v___jp_7351_:
{
lean_object* v___x_7353_; lean_object* v___x_7354_; lean_object* v_url_7355_; lean_object* v___x_7356_; lean_object* v___x_7357_; uint8_t v___x_7358_; 
v___x_7353_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_7354_ = lean_string_append(v___y_7352_, v___x_7353_);
v_url_7355_ = lean_string_append(v___x_7354_, v_rev_7338_);
v___x_7356_ = lean_string_utf8_byte_size(v_platform_7341_);
v___x_7357_ = lean_unsigned_to_nat(0u);
v___x_7358_ = lean_nat_dec_eq(v___x_7356_, v___x_7357_);
if (v___x_7358_ == 0)
{
lean_object* v___x_7359_; lean_object* v___x_7360_; lean_object* v_url_7361_; 
v___x_7359_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_7360_ = lean_string_append(v_url_7355_, v___x_7359_);
v_url_7361_ = l_Lake_uriEncode(v_platform_7341_, v___x_7360_);
v_url_7344_ = v_url_7361_;
goto v___jp_7343_;
}
else
{
v_url_7344_ = v_url_7355_;
goto v___jp_7343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_7374_, lean_object* v_service_7375_, lean_object* v_scope_7376_, lean_object* v_platform_7377_, lean_object* v_toolchain_7378_){
_start:
{
lean_object* v_res_7379_; 
v_res_7379_ = l_Lake_CacheService_revisionUrl(v_rev_7374_, v_service_7375_, v_scope_7376_, v_platform_7377_, v_toolchain_7378_);
lean_dec_ref(v_toolchain_7378_);
lean_dec_ref(v_platform_7377_);
lean_dec_ref(v_rev_7374_);
return v_res_7379_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_7384_, lean_object* v_cache_7385_, lean_object* v_service_7386_, lean_object* v_localScope_7387_, lean_object* v_remoteScope_7388_, lean_object* v_platform_7389_, lean_object* v_toolchain_7390_, uint8_t v_force_7391_, lean_object* v_a_7392_){
_start:
{
lean_object* v___y_7395_; lean_object* v___y_7396_; lean_object* v_a_7404_; lean_object* v_a_7407_; lean_object* v_a_7411_; lean_object* v___x_7414_; lean_object* v___x_7415_; lean_object* v___x_7416_; lean_object* v___x_7417_; lean_object* v___x_7418_; lean_object* v_path_7419_; lean_object* v_a_7421_; lean_object* v___y_7507_; lean_object* v___y_7508_; uint8_t v_a_7548_; lean_object* v___x_7595_; uint8_t v___x_7596_; uint8_t v___x_7597_; 
v___x_7414_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_7415_ = l_System_FilePath_join(v_cache_7385_, v___x_7414_);
lean_inc_ref(v_localScope_7387_);
v___x_7416_ = l_System_FilePath_join(v___x_7415_, v_localScope_7387_);
v___x_7417_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_7384_);
v___x_7418_ = lean_string_append(v_rev_7384_, v___x_7417_);
v_path_7419_ = l_System_FilePath_join(v___x_7416_, v___x_7418_);
v___x_7595_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_7596_ = l_System_FilePath_pathExists(v_path_7419_);
v___x_7597_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__29);
if (v___x_7597_ == 0)
{
v_a_7548_ = v___x_7596_;
goto v___jp_7547_;
}
else
{
lean_object* v___x_7598_; size_t v___x_7599_; size_t v___x_7600_; lean_object* v___x_7601_; 
v___x_7598_ = lean_box(0);
v___x_7599_ = ((size_t)0ULL);
v___x_7600_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__30);
v___x_7601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_7595_, v___x_7599_, v___x_7600_, v___x_7598_, v_a_7392_);
if (lean_obj_tag(v___x_7601_) == 0)
{
lean_dec_ref_known(v___x_7601_, 1);
v_a_7548_ = v___x_7596_;
goto v___jp_7547_;
}
else
{
lean_object* v_a_7602_; lean_object* v___x_7604_; uint8_t v_isShared_7605_; uint8_t v_isSharedCheck_7609_; 
lean_dec_ref(v_path_7419_);
lean_dec_ref(v_remoteScope_7388_);
lean_dec_ref(v_localScope_7387_);
lean_dec_ref(v_service_7386_);
lean_dec_ref(v_rev_7384_);
v_a_7602_ = lean_ctor_get(v___x_7601_, 0);
v_isSharedCheck_7609_ = !lean_is_exclusive(v___x_7601_);
if (v_isSharedCheck_7609_ == 0)
{
v___x_7604_ = v___x_7601_;
v_isShared_7605_ = v_isSharedCheck_7609_;
goto v_resetjp_7603_;
}
else
{
lean_inc(v_a_7602_);
lean_dec(v___x_7601_);
v___x_7604_ = lean_box(0);
v_isShared_7605_ = v_isSharedCheck_7609_;
goto v_resetjp_7603_;
}
v_resetjp_7603_:
{
lean_object* v___x_7607_; 
if (v_isShared_7605_ == 0)
{
v___x_7607_ = v___x_7604_;
goto v_reusejp_7606_;
}
else
{
lean_object* v_reuseFailAlloc_7608_; 
v_reuseFailAlloc_7608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7608_, 0, v_a_7602_);
v___x_7607_ = v_reuseFailAlloc_7608_;
goto v_reusejp_7606_;
}
v_reusejp_7606_:
{
return v___x_7607_;
}
}
}
}
v___jp_7394_:
{
lean_object* v___x_7397_; lean_object* v___x_7398_; uint8_t v___x_7399_; lean_object* v___x_7400_; lean_object* v___x_7401_; lean_object* v___x_7402_; 
v___x_7397_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_7398_ = lean_string_append(v___y_7396_, v___x_7397_);
v___x_7399_ = 3;
v___x_7400_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7400_, 0, v___x_7398_);
lean_ctor_set_uint8(v___x_7400_, sizeof(void*)*1, v___x_7399_);
lean_inc_ref(v_a_7392_);
v___x_7401_ = lean_apply_2(v_a_7392_, v___x_7400_, lean_box(0));
v___x_7402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7402_, 0, v___y_7395_);
return v___x_7402_;
}
v___jp_7403_:
{
lean_object* v_s_7405_; 
v_s_7405_ = lean_ctor_get(v_remoteScope_7388_, 0);
lean_inc_ref(v_s_7405_);
lean_dec_ref(v_remoteScope_7388_);
v___y_7395_ = v_a_7404_;
v___y_7396_ = v_s_7405_;
goto v___jp_7394_;
}
v___jp_7406_:
{
lean_object* v___x_7408_; lean_object* v___x_7409_; 
v___x_7408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7408_, 0, v_a_7407_);
v___x_7409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7409_, 0, v___x_7408_);
return v___x_7409_;
}
v___jp_7410_:
{
lean_object* v___x_7412_; lean_object* v___x_7413_; 
v___x_7412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7412_, 0, v_a_7411_);
v___x_7413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7413_, 0, v___x_7412_);
return v___x_7413_;
}
v___jp_7420_:
{
if (lean_obj_tag(v_a_7421_) == 1)
{
lean_object* v_val_7422_; lean_object* v___x_7423_; 
v_val_7422_ = lean_ctor_get(v_a_7421_, 0);
lean_inc(v_val_7422_);
lean_dec_ref_known(v_a_7421_, 1);
lean_inc_ref(v_path_7419_);
v___x_7423_ = l_Lake_createParentDirs(v_path_7419_);
if (lean_obj_tag(v___x_7423_) == 0)
{
lean_object* v___x_7424_; 
lean_dec_ref_known(v___x_7423_, 1);
v___x_7424_ = l_IO_FS_writeFile(v_path_7419_, v_val_7422_);
lean_dec(v_val_7422_);
if (lean_obj_tag(v___x_7424_) == 0)
{
lean_object* v___x_7426_; uint8_t v_isShared_7427_; uint8_t v_isSharedCheck_7476_; 
v_isSharedCheck_7476_ = !lean_is_exclusive(v___x_7424_);
if (v_isSharedCheck_7476_ == 0)
{
lean_object* v_unused_7477_; 
v_unused_7477_ = lean_ctor_get(v___x_7424_, 0);
lean_dec(v_unused_7477_);
v___x_7426_ = v___x_7424_;
v_isShared_7427_ = v_isSharedCheck_7476_;
goto v_resetjp_7425_;
}
else
{
lean_dec(v___x_7424_);
v___x_7426_ = lean_box(0);
v_isShared_7427_ = v_isSharedCheck_7476_;
goto v_resetjp_7425_;
}
v_resetjp_7425_:
{
lean_object* v___x_7428_; lean_object* v___x_7429_; uint8_t v___x_7430_; lean_object* v___x_7431_; lean_object* v___x_7432_; 
v___x_7428_ = lean_string_utf8_byte_size(v_platform_7389_);
v___x_7429_ = lean_unsigned_to_nat(0u);
v___x_7430_ = lean_nat_dec_eq(v___x_7428_, v___x_7429_);
v___x_7431_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_7432_ = l_Lake_CacheMap_load(v_path_7419_, v___x_7430_, v___x_7431_);
if (lean_obj_tag(v___x_7432_) == 0)
{
lean_object* v_a_7433_; lean_object* v_a_7434_; lean_object* v___x_7435_; uint8_t v___x_7436_; 
lean_del_object(v___x_7426_);
v_a_7433_ = lean_ctor_get(v___x_7432_, 0);
lean_inc(v_a_7433_);
v_a_7434_ = lean_ctor_get(v___x_7432_, 1);
lean_inc(v_a_7434_);
lean_dec_ref_known(v___x_7432_, 2);
v___x_7435_ = lean_array_get_size(v_a_7434_);
v___x_7436_ = lean_nat_dec_lt(v___x_7429_, v___x_7435_);
if (v___x_7436_ == 0)
{
lean_dec(v_a_7434_);
v_a_7407_ = v_a_7433_;
goto v___jp_7406_;
}
else
{
lean_object* v___x_7437_; size_t v___x_7438_; size_t v___x_7439_; lean_object* v___x_7440_; 
v___x_7437_ = lean_box(0);
v___x_7438_ = ((size_t)0ULL);
v___x_7439_ = lean_usize_of_nat(v___x_7435_);
v___x_7440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7434_, v___x_7438_, v___x_7439_, v___x_7437_, v_a_7392_);
lean_dec(v_a_7434_);
if (lean_obj_tag(v___x_7440_) == 0)
{
lean_dec_ref_known(v___x_7440_, 1);
v_a_7407_ = v_a_7433_;
goto v___jp_7406_;
}
else
{
lean_object* v_a_7441_; lean_object* v___x_7443_; uint8_t v_isShared_7444_; uint8_t v_isSharedCheck_7448_; 
lean_dec(v_a_7433_);
v_a_7441_ = lean_ctor_get(v___x_7440_, 0);
v_isSharedCheck_7448_ = !lean_is_exclusive(v___x_7440_);
if (v_isSharedCheck_7448_ == 0)
{
v___x_7443_ = v___x_7440_;
v_isShared_7444_ = v_isSharedCheck_7448_;
goto v_resetjp_7442_;
}
else
{
lean_inc(v_a_7441_);
lean_dec(v___x_7440_);
v___x_7443_ = lean_box(0);
v_isShared_7444_ = v_isSharedCheck_7448_;
goto v_resetjp_7442_;
}
v_resetjp_7442_:
{
lean_object* v___x_7446_; 
if (v_isShared_7444_ == 0)
{
v___x_7446_ = v___x_7443_;
goto v_reusejp_7445_;
}
else
{
lean_object* v_reuseFailAlloc_7447_; 
v_reuseFailAlloc_7447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7447_, 0, v_a_7441_);
v___x_7446_ = v_reuseFailAlloc_7447_;
goto v_reusejp_7445_;
}
v_reusejp_7445_:
{
return v___x_7446_;
}
}
}
}
}
else
{
lean_object* v_a_7449_; lean_object* v___x_7450_; uint8_t v___x_7451_; 
v_a_7449_ = lean_ctor_get(v___x_7432_, 1);
lean_inc(v_a_7449_);
lean_dec_ref_known(v___x_7432_, 2);
v___x_7450_ = lean_array_get_size(v_a_7449_);
v___x_7451_ = lean_nat_dec_lt(v___x_7429_, v___x_7450_);
if (v___x_7451_ == 0)
{
lean_object* v___x_7452_; lean_object* v___x_7454_; 
lean_dec(v_a_7449_);
v___x_7452_ = lean_box(0);
if (v_isShared_7427_ == 0)
{
lean_ctor_set_tag(v___x_7426_, 1);
lean_ctor_set(v___x_7426_, 0, v___x_7452_);
v___x_7454_ = v___x_7426_;
goto v_reusejp_7453_;
}
else
{
lean_object* v_reuseFailAlloc_7455_; 
v_reuseFailAlloc_7455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7455_, 0, v___x_7452_);
v___x_7454_ = v_reuseFailAlloc_7455_;
goto v_reusejp_7453_;
}
v_reusejp_7453_:
{
return v___x_7454_;
}
}
else
{
lean_object* v___x_7456_; size_t v___x_7457_; size_t v___x_7458_; lean_object* v___x_7459_; 
lean_del_object(v___x_7426_);
v___x_7456_ = lean_box(0);
v___x_7457_ = ((size_t)0ULL);
v___x_7458_ = lean_usize_of_nat(v___x_7450_);
v___x_7459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7449_, v___x_7457_, v___x_7458_, v___x_7456_, v_a_7392_);
lean_dec(v_a_7449_);
if (lean_obj_tag(v___x_7459_) == 0)
{
lean_object* v___x_7461_; uint8_t v_isShared_7462_; uint8_t v_isSharedCheck_7466_; 
v_isSharedCheck_7466_ = !lean_is_exclusive(v___x_7459_);
if (v_isSharedCheck_7466_ == 0)
{
lean_object* v_unused_7467_; 
v_unused_7467_ = lean_ctor_get(v___x_7459_, 0);
lean_dec(v_unused_7467_);
v___x_7461_ = v___x_7459_;
v_isShared_7462_ = v_isSharedCheck_7466_;
goto v_resetjp_7460_;
}
else
{
lean_dec(v___x_7459_);
v___x_7461_ = lean_box(0);
v_isShared_7462_ = v_isSharedCheck_7466_;
goto v_resetjp_7460_;
}
v_resetjp_7460_:
{
lean_object* v___x_7464_; 
if (v_isShared_7462_ == 0)
{
lean_ctor_set_tag(v___x_7461_, 1);
lean_ctor_set(v___x_7461_, 0, v___x_7456_);
v___x_7464_ = v___x_7461_;
goto v_reusejp_7463_;
}
else
{
lean_object* v_reuseFailAlloc_7465_; 
v_reuseFailAlloc_7465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7465_, 0, v___x_7456_);
v___x_7464_ = v_reuseFailAlloc_7465_;
goto v_reusejp_7463_;
}
v_reusejp_7463_:
{
return v___x_7464_;
}
}
}
else
{
lean_object* v_a_7468_; lean_object* v___x_7470_; uint8_t v_isShared_7471_; uint8_t v_isSharedCheck_7475_; 
v_a_7468_ = lean_ctor_get(v___x_7459_, 0);
v_isSharedCheck_7475_ = !lean_is_exclusive(v___x_7459_);
if (v_isSharedCheck_7475_ == 0)
{
v___x_7470_ = v___x_7459_;
v_isShared_7471_ = v_isSharedCheck_7475_;
goto v_resetjp_7469_;
}
else
{
lean_inc(v_a_7468_);
lean_dec(v___x_7459_);
v___x_7470_ = lean_box(0);
v_isShared_7471_ = v_isSharedCheck_7475_;
goto v_resetjp_7469_;
}
v_resetjp_7469_:
{
lean_object* v___x_7473_; 
if (v_isShared_7471_ == 0)
{
v___x_7473_ = v___x_7470_;
goto v_reusejp_7472_;
}
else
{
lean_object* v_reuseFailAlloc_7474_; 
v_reuseFailAlloc_7474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7474_, 0, v_a_7468_);
v___x_7473_ = v_reuseFailAlloc_7474_;
goto v_reusejp_7472_;
}
v_reusejp_7472_:
{
return v___x_7473_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_7478_; lean_object* v___x_7480_; uint8_t v_isShared_7481_; uint8_t v_isSharedCheck_7490_; 
lean_dec_ref(v_path_7419_);
v_a_7478_ = lean_ctor_get(v___x_7424_, 0);
v_isSharedCheck_7490_ = !lean_is_exclusive(v___x_7424_);
if (v_isSharedCheck_7490_ == 0)
{
v___x_7480_ = v___x_7424_;
v_isShared_7481_ = v_isSharedCheck_7490_;
goto v_resetjp_7479_;
}
else
{
lean_inc(v_a_7478_);
lean_dec(v___x_7424_);
v___x_7480_ = lean_box(0);
v_isShared_7481_ = v_isSharedCheck_7490_;
goto v_resetjp_7479_;
}
v_resetjp_7479_:
{
lean_object* v___x_7482_; uint8_t v___x_7483_; lean_object* v___x_7484_; lean_object* v___x_7485_; lean_object* v___x_7486_; lean_object* v___x_7488_; 
v___x_7482_ = lean_io_error_to_string(v_a_7478_);
v___x_7483_ = 3;
v___x_7484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7484_, 0, v___x_7482_);
lean_ctor_set_uint8(v___x_7484_, sizeof(void*)*1, v___x_7483_);
lean_inc_ref(v_a_7392_);
v___x_7485_ = lean_apply_2(v_a_7392_, v___x_7484_, lean_box(0));
v___x_7486_ = lean_box(0);
if (v_isShared_7481_ == 0)
{
lean_ctor_set(v___x_7480_, 0, v___x_7486_);
v___x_7488_ = v___x_7480_;
goto v_reusejp_7487_;
}
else
{
lean_object* v_reuseFailAlloc_7489_; 
v_reuseFailAlloc_7489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7489_, 0, v___x_7486_);
v___x_7488_ = v_reuseFailAlloc_7489_;
goto v_reusejp_7487_;
}
v_reusejp_7487_:
{
return v___x_7488_;
}
}
}
}
else
{
lean_object* v_a_7491_; lean_object* v___x_7493_; uint8_t v_isShared_7494_; uint8_t v_isSharedCheck_7503_; 
lean_dec(v_val_7422_);
lean_dec_ref(v_path_7419_);
v_a_7491_ = lean_ctor_get(v___x_7423_, 0);
v_isSharedCheck_7503_ = !lean_is_exclusive(v___x_7423_);
if (v_isSharedCheck_7503_ == 0)
{
v___x_7493_ = v___x_7423_;
v_isShared_7494_ = v_isSharedCheck_7503_;
goto v_resetjp_7492_;
}
else
{
lean_inc(v_a_7491_);
lean_dec(v___x_7423_);
v___x_7493_ = lean_box(0);
v_isShared_7494_ = v_isSharedCheck_7503_;
goto v_resetjp_7492_;
}
v_resetjp_7492_:
{
lean_object* v___x_7495_; uint8_t v___x_7496_; lean_object* v___x_7497_; lean_object* v___x_7498_; lean_object* v___x_7499_; lean_object* v___x_7501_; 
v___x_7495_ = lean_io_error_to_string(v_a_7491_);
v___x_7496_ = 3;
v___x_7497_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7497_, 0, v___x_7495_);
lean_ctor_set_uint8(v___x_7497_, sizeof(void*)*1, v___x_7496_);
lean_inc_ref(v_a_7392_);
v___x_7498_ = lean_apply_2(v_a_7392_, v___x_7497_, lean_box(0));
v___x_7499_ = lean_box(0);
if (v_isShared_7494_ == 0)
{
lean_ctor_set(v___x_7493_, 0, v___x_7499_);
v___x_7501_ = v___x_7493_;
goto v_reusejp_7500_;
}
else
{
lean_object* v_reuseFailAlloc_7502_; 
v_reuseFailAlloc_7502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7502_, 0, v___x_7499_);
v___x_7501_ = v_reuseFailAlloc_7502_;
goto v_reusejp_7500_;
}
v_reusejp_7500_:
{
return v___x_7501_;
}
}
}
}
else
{
lean_object* v___x_7504_; lean_object* v___x_7505_; 
lean_dec(v_a_7421_);
lean_dec_ref(v_path_7419_);
v___x_7504_ = lean_box(0);
v___x_7505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7505_, 0, v___x_7504_);
return v___x_7505_;
}
}
v___jp_7506_:
{
lean_object* v___x_7509_; lean_object* v___x_7510_; lean_object* v___x_7511_; 
v___x_7509_ = lean_unsigned_to_nat(0u);
v___x_7510_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_7511_ = l_Lake_getUrl_x3f(v___y_7507_, v___y_7508_, v___x_7510_);
if (lean_obj_tag(v___x_7511_) == 0)
{
lean_object* v_a_7512_; lean_object* v_a_7513_; lean_object* v___x_7514_; uint8_t v___x_7515_; 
v_a_7512_ = lean_ctor_get(v___x_7511_, 0);
lean_inc(v_a_7512_);
v_a_7513_ = lean_ctor_get(v___x_7511_, 1);
lean_inc(v_a_7513_);
lean_dec_ref_known(v___x_7511_, 2);
v___x_7514_ = lean_array_get_size(v_a_7513_);
v___x_7515_ = lean_nat_dec_lt(v___x_7509_, v___x_7514_);
if (v___x_7515_ == 0)
{
lean_dec(v_a_7513_);
lean_dec_ref(v_remoteScope_7388_);
v_a_7421_ = v_a_7512_;
goto v___jp_7420_;
}
else
{
lean_object* v___x_7516_; size_t v___x_7517_; size_t v___x_7518_; lean_object* v___x_7519_; 
v___x_7516_ = lean_box(0);
v___x_7517_ = ((size_t)0ULL);
v___x_7518_ = lean_usize_of_nat(v___x_7514_);
v___x_7519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7513_, v___x_7517_, v___x_7518_, v___x_7516_, v_a_7392_);
lean_dec(v_a_7513_);
if (lean_obj_tag(v___x_7519_) == 0)
{
lean_dec_ref_known(v___x_7519_, 1);
lean_dec_ref(v_remoteScope_7388_);
v_a_7421_ = v_a_7512_;
goto v___jp_7420_;
}
else
{
lean_object* v_a_7520_; 
lean_dec(v_a_7512_);
lean_dec_ref(v_path_7419_);
v_a_7520_ = lean_ctor_get(v___x_7519_, 0);
lean_inc(v_a_7520_);
lean_dec_ref_known(v___x_7519_, 1);
v_a_7404_ = v_a_7520_;
goto v___jp_7403_;
}
}
}
else
{
lean_object* v_a_7521_; lean_object* v___x_7522_; uint8_t v___x_7523_; 
lean_dec_ref(v_path_7419_);
v_a_7521_ = lean_ctor_get(v___x_7511_, 1);
lean_inc(v_a_7521_);
lean_dec_ref_known(v___x_7511_, 2);
v___x_7522_ = lean_array_get_size(v_a_7521_);
v___x_7523_ = lean_nat_dec_lt(v___x_7509_, v___x_7522_);
if (v___x_7523_ == 0)
{
lean_object* v___x_7524_; 
lean_dec(v_a_7521_);
v___x_7524_ = lean_box(0);
v_a_7404_ = v___x_7524_;
goto v___jp_7403_;
}
else
{
lean_object* v___x_7525_; size_t v___x_7526_; size_t v___x_7527_; lean_object* v___x_7528_; 
v___x_7525_ = lean_box(0);
v___x_7526_ = ((size_t)0ULL);
v___x_7527_ = lean_usize_of_nat(v___x_7522_);
v___x_7528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7521_, v___x_7526_, v___x_7527_, v___x_7525_, v_a_7392_);
lean_dec(v_a_7521_);
if (lean_obj_tag(v___x_7528_) == 0)
{
lean_dec_ref_known(v___x_7528_, 1);
v_a_7404_ = v___x_7525_;
goto v___jp_7403_;
}
else
{
lean_object* v_a_7529_; 
v_a_7529_ = lean_ctor_get(v___x_7528_, 0);
lean_inc(v_a_7529_);
lean_dec_ref_known(v___x_7528_, 1);
v_a_7404_ = v_a_7529_;
goto v___jp_7403_;
}
}
}
}
v___jp_7530_:
{
lean_object* v___x_7531_; lean_object* v___x_7532_; lean_object* v___x_7533_; lean_object* v___x_7534_; lean_object* v___x_7535_; lean_object* v___x_7536_; lean_object* v___x_7537_; lean_object* v___x_7538_; lean_object* v___x_7539_; lean_object* v___x_7540_; uint8_t v___x_7541_; lean_object* v___x_7542_; lean_object* v___x_7543_; uint8_t v_isReservoir_7544_; 
lean_inc_ref(v_remoteScope_7388_);
lean_inc_ref(v_service_7386_);
v___x_7531_ = l_Lake_CacheService_revisionUrl(v_rev_7384_, v_service_7386_, v_remoteScope_7388_, v_platform_7389_, v_toolchain_7390_);
v___x_7532_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_7533_ = lean_string_append(v_localScope_7387_, v___x_7532_);
v___x_7534_ = lean_string_append(v___x_7533_, v_rev_7384_);
lean_dec_ref(v_rev_7384_);
v___x_7535_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_7536_ = lean_string_append(v___x_7534_, v___x_7535_);
v___x_7537_ = lean_string_append(v___x_7536_, v_path_7419_);
v___x_7538_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_7539_ = lean_string_append(v___x_7537_, v___x_7538_);
v___x_7540_ = lean_string_append(v___x_7539_, v___x_7531_);
v___x_7541_ = 1;
v___x_7542_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7542_, 0, v___x_7540_);
lean_ctor_set_uint8(v___x_7542_, sizeof(void*)*1, v___x_7541_);
lean_inc_ref(v_a_7392_);
v___x_7543_ = lean_apply_2(v_a_7392_, v___x_7542_, lean_box(0));
v_isReservoir_7544_ = lean_ctor_get_uint8(v_service_7386_, sizeof(void*)*5);
lean_dec_ref(v_service_7386_);
if (v_isReservoir_7544_ == 0)
{
lean_object* v___x_7545_; 
v___x_7545_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_7507_ = v___x_7531_;
v___y_7508_ = v___x_7545_;
goto v___jp_7506_;
}
else
{
lean_object* v___x_7546_; 
v___x_7546_ = l_Lake_Reservoir_lakeHeaders;
v___y_7507_ = v___x_7531_;
v___y_7508_ = v___x_7546_;
goto v___jp_7506_;
}
}
v___jp_7547_:
{
if (v_a_7548_ == 0)
{
goto v___jp_7530_;
}
else
{
if (v_force_7391_ == 0)
{
lean_object* v___x_7549_; lean_object* v___x_7550_; uint8_t v___x_7551_; lean_object* v___x_7552_; lean_object* v___x_7553_; 
lean_dec_ref(v_remoteScope_7388_);
lean_dec_ref(v_localScope_7387_);
lean_dec_ref(v_service_7386_);
lean_dec_ref(v_rev_7384_);
v___x_7549_ = lean_string_utf8_byte_size(v_platform_7389_);
v___x_7550_ = lean_unsigned_to_nat(0u);
v___x_7551_ = lean_nat_dec_eq(v___x_7549_, v___x_7550_);
v___x_7552_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__2));
v___x_7553_ = l_Lake_CacheMap_load(v_path_7419_, v___x_7551_, v___x_7552_);
if (lean_obj_tag(v___x_7553_) == 0)
{
lean_object* v_a_7554_; lean_object* v_a_7555_; lean_object* v___x_7556_; uint8_t v___x_7557_; 
v_a_7554_ = lean_ctor_get(v___x_7553_, 0);
lean_inc(v_a_7554_);
v_a_7555_ = lean_ctor_get(v___x_7553_, 1);
lean_inc(v_a_7555_);
lean_dec_ref_known(v___x_7553_, 2);
v___x_7556_ = lean_array_get_size(v_a_7555_);
v___x_7557_ = lean_nat_dec_lt(v___x_7550_, v___x_7556_);
if (v___x_7557_ == 0)
{
lean_dec(v_a_7555_);
v_a_7411_ = v_a_7554_;
goto v___jp_7410_;
}
else
{
lean_object* v___x_7558_; size_t v___x_7559_; size_t v___x_7560_; lean_object* v___x_7561_; 
v___x_7558_ = lean_box(0);
v___x_7559_ = ((size_t)0ULL);
v___x_7560_ = lean_usize_of_nat(v___x_7556_);
v___x_7561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7555_, v___x_7559_, v___x_7560_, v___x_7558_, v_a_7392_);
lean_dec(v_a_7555_);
if (lean_obj_tag(v___x_7561_) == 0)
{
lean_dec_ref_known(v___x_7561_, 1);
v_a_7411_ = v_a_7554_;
goto v___jp_7410_;
}
else
{
lean_object* v_a_7562_; lean_object* v___x_7564_; uint8_t v_isShared_7565_; uint8_t v_isSharedCheck_7569_; 
lean_dec(v_a_7554_);
v_a_7562_ = lean_ctor_get(v___x_7561_, 0);
v_isSharedCheck_7569_ = !lean_is_exclusive(v___x_7561_);
if (v_isSharedCheck_7569_ == 0)
{
v___x_7564_ = v___x_7561_;
v_isShared_7565_ = v_isSharedCheck_7569_;
goto v_resetjp_7563_;
}
else
{
lean_inc(v_a_7562_);
lean_dec(v___x_7561_);
v___x_7564_ = lean_box(0);
v_isShared_7565_ = v_isSharedCheck_7569_;
goto v_resetjp_7563_;
}
v_resetjp_7563_:
{
lean_object* v___x_7567_; 
if (v_isShared_7565_ == 0)
{
v___x_7567_ = v___x_7564_;
goto v_reusejp_7566_;
}
else
{
lean_object* v_reuseFailAlloc_7568_; 
v_reuseFailAlloc_7568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7568_, 0, v_a_7562_);
v___x_7567_ = v_reuseFailAlloc_7568_;
goto v_reusejp_7566_;
}
v_reusejp_7566_:
{
return v___x_7567_;
}
}
}
}
}
else
{
lean_object* v_a_7570_; lean_object* v___x_7571_; uint8_t v___x_7572_; 
v_a_7570_ = lean_ctor_get(v___x_7553_, 1);
lean_inc(v_a_7570_);
lean_dec_ref_known(v___x_7553_, 2);
v___x_7571_ = lean_array_get_size(v_a_7570_);
v___x_7572_ = lean_nat_dec_lt(v___x_7550_, v___x_7571_);
if (v___x_7572_ == 0)
{
lean_object* v___x_7573_; lean_object* v___x_7574_; 
lean_dec(v_a_7570_);
v___x_7573_ = lean_box(0);
v___x_7574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7574_, 0, v___x_7573_);
return v___x_7574_;
}
else
{
lean_object* v___x_7575_; size_t v___x_7576_; size_t v___x_7577_; lean_object* v___x_7578_; 
v___x_7575_ = lean_box(0);
v___x_7576_ = ((size_t)0ULL);
v___x_7577_ = lean_usize_of_nat(v___x_7571_);
v___x_7578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_7570_, v___x_7576_, v___x_7577_, v___x_7575_, v_a_7392_);
lean_dec(v_a_7570_);
if (lean_obj_tag(v___x_7578_) == 0)
{
lean_object* v___x_7580_; uint8_t v_isShared_7581_; uint8_t v_isSharedCheck_7585_; 
v_isSharedCheck_7585_ = !lean_is_exclusive(v___x_7578_);
if (v_isSharedCheck_7585_ == 0)
{
lean_object* v_unused_7586_; 
v_unused_7586_ = lean_ctor_get(v___x_7578_, 0);
lean_dec(v_unused_7586_);
v___x_7580_ = v___x_7578_;
v_isShared_7581_ = v_isSharedCheck_7585_;
goto v_resetjp_7579_;
}
else
{
lean_dec(v___x_7578_);
v___x_7580_ = lean_box(0);
v_isShared_7581_ = v_isSharedCheck_7585_;
goto v_resetjp_7579_;
}
v_resetjp_7579_:
{
lean_object* v___x_7583_; 
if (v_isShared_7581_ == 0)
{
lean_ctor_set_tag(v___x_7580_, 1);
lean_ctor_set(v___x_7580_, 0, v___x_7575_);
v___x_7583_ = v___x_7580_;
goto v_reusejp_7582_;
}
else
{
lean_object* v_reuseFailAlloc_7584_; 
v_reuseFailAlloc_7584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7584_, 0, v___x_7575_);
v___x_7583_ = v_reuseFailAlloc_7584_;
goto v_reusejp_7582_;
}
v_reusejp_7582_:
{
return v___x_7583_;
}
}
}
else
{
lean_object* v_a_7587_; lean_object* v___x_7589_; uint8_t v_isShared_7590_; uint8_t v_isSharedCheck_7594_; 
v_a_7587_ = lean_ctor_get(v___x_7578_, 0);
v_isSharedCheck_7594_ = !lean_is_exclusive(v___x_7578_);
if (v_isSharedCheck_7594_ == 0)
{
v___x_7589_ = v___x_7578_;
v_isShared_7590_ = v_isSharedCheck_7594_;
goto v_resetjp_7588_;
}
else
{
lean_inc(v_a_7587_);
lean_dec(v___x_7578_);
v___x_7589_ = lean_box(0);
v_isShared_7590_ = v_isSharedCheck_7594_;
goto v_resetjp_7588_;
}
v_resetjp_7588_:
{
lean_object* v___x_7592_; 
if (v_isShared_7590_ == 0)
{
v___x_7592_ = v___x_7589_;
goto v_reusejp_7591_;
}
else
{
lean_object* v_reuseFailAlloc_7593_; 
v_reuseFailAlloc_7593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7593_, 0, v_a_7587_);
v___x_7592_ = v_reuseFailAlloc_7593_;
goto v_reusejp_7591_;
}
v_reusejp_7591_:
{
return v___x_7592_;
}
}
}
}
}
}
else
{
goto v___jp_7530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_7610_, lean_object* v_cache_7611_, lean_object* v_service_7612_, lean_object* v_localScope_7613_, lean_object* v_remoteScope_7614_, lean_object* v_platform_7615_, lean_object* v_toolchain_7616_, lean_object* v_force_7617_, lean_object* v_a_7618_, lean_object* v_a_7619_){
_start:
{
uint8_t v_force_boxed_7620_; lean_object* v_res_7621_; 
v_force_boxed_7620_ = lean_unbox(v_force_7617_);
v_res_7621_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_7610_, v_cache_7611_, v_service_7612_, v_localScope_7613_, v_remoteScope_7614_, v_platform_7615_, v_toolchain_7616_, v_force_boxed_7620_, v_a_7618_);
lean_dec_ref(v_a_7618_);
lean_dec_ref(v_toolchain_7616_);
lean_dec_ref(v_platform_7615_);
return v_res_7621_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_7623_, lean_object* v_outputs_7624_, lean_object* v_service_7625_, lean_object* v_scope_7626_, lean_object* v_platform_7627_, lean_object* v_toolchain_7628_, lean_object* v_a_7629_){
_start:
{
lean_object* v_url_7631_; lean_object* v___y_7633_; lean_object* v_s_7649_; 
lean_inc_ref(v_scope_7626_);
lean_inc_ref(v_service_7625_);
v_url_7631_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_7623_, v_service_7625_, v_scope_7626_, v_platform_7627_, v_toolchain_7628_);
v_s_7649_ = lean_ctor_get(v_scope_7626_, 0);
lean_inc_ref(v_s_7649_);
lean_dec_ref(v_scope_7626_);
v___y_7633_ = v_s_7649_;
goto v___jp_7632_;
v___jp_7632_:
{
lean_object* v___x_7634_; lean_object* v___x_7635_; lean_object* v___x_7636_; lean_object* v___x_7637_; lean_object* v___x_7638_; lean_object* v___x_7639_; lean_object* v___x_7640_; lean_object* v___x_7641_; lean_object* v___x_7642_; uint8_t v___x_7643_; lean_object* v___x_7644_; lean_object* v___x_7645_; lean_object* v_key_7646_; lean_object* v___x_7647_; lean_object* v___x_7648_; 
v___x_7634_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_7635_ = lean_string_append(v___y_7633_, v___x_7634_);
v___x_7636_ = lean_string_append(v___x_7635_, v_rev_7623_);
v___x_7637_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_7638_ = lean_string_append(v___x_7636_, v___x_7637_);
v___x_7639_ = lean_string_append(v___x_7638_, v_outputs_7624_);
v___x_7640_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_7641_ = lean_string_append(v___x_7639_, v___x_7640_);
v___x_7642_ = lean_string_append(v___x_7641_, v_url_7631_);
v___x_7643_ = 1;
v___x_7644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7644_, 0, v___x_7642_);
lean_ctor_set_uint8(v___x_7644_, sizeof(void*)*1, v___x_7643_);
lean_inc_ref(v_a_7629_);
v___x_7645_ = lean_apply_2(v_a_7629_, v___x_7644_, lean_box(0));
v_key_7646_ = lean_ctor_get(v_service_7625_, 1);
lean_inc_ref(v_key_7646_);
lean_dec_ref(v_service_7625_);
v___x_7647_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_7648_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_7629_, v_outputs_7624_, v___x_7647_, v_url_7631_, v_key_7646_);
return v___x_7648_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_7650_, lean_object* v_outputs_7651_, lean_object* v_service_7652_, lean_object* v_scope_7653_, lean_object* v_platform_7654_, lean_object* v_toolchain_7655_, lean_object* v_a_7656_, lean_object* v_a_7657_){
_start:
{
lean_object* v_res_7658_; 
v_res_7658_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_7650_, v_outputs_7651_, v_service_7652_, v_scope_7653_, v_platform_7654_, v_toolchain_7655_, v_a_7656_);
lean_dec_ref(v_a_7656_);
lean_dec_ref(v_toolchain_7655_);
lean_dec_ref(v_platform_7654_);
lean_dec_ref(v_rev_7650_);
return v_res_7658_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
