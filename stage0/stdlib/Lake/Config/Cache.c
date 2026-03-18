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
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_io_metadata(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lake_normalizeToolchain(lean_object*);
static const lean_string_object l_Lake_CacheMap_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-09-10"};
static const lean_object* l_Lake_CacheMap_schemaVersion___closed__0 = (const lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheMap_schemaVersion = (const lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ": invalid schema version on line 1: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ": unknown schema version '"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "'; may not parse correctly"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": expected schema version on line 1"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__0 = (const lean_object*)&l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__0_value;
static const lean_string_object l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__1 = (const lean_object*)&l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": invalid JSON on line "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheMap_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": failed to open file: "};
static const lean_object* l_Lake_CacheMap_load___closed__0 = (const lean_object*)&l_Lake_CacheMap_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_CacheMap_writeFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value)}};
static const lean_object* l_Lake_CacheMap_writeFile___closed__0 = (const lean_object*)&l_Lake_CacheMap_writeFile___closed__0_value;
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object* v_inputName_7_, lean_object* v_line_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_a_12_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = lean_string_utf8_byte_size(v_line_8_);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_dec_eq(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Json_parse(v_line_8_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_25_);
lean_dec_ref(v___x_24_);
v_a_12_ = v_a_25_;
goto v___jp_11_;
}
else
{
lean_object* v_a_26_; lean_object* v___x_27_; 
v_a_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_26_);
lean_dec_ref(v___x_24_);
v___x_27_ = l_Lean_Json_getStr_x3f(v_a_26_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref(v___x_27_);
v_a_12_ = v_a_28_;
goto v___jp_11_;
}
else
{
lean_object* v_a_29_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_a_29_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v___x_27_);
v___x_41_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion___closed__0));
v___x_42_ = lean_string_dec_eq(v_a_29_, v___x_41_);
if (v___x_42_ == 0)
{
goto v___jp_30_;
}
else
{
if (v___x_23_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_a_29_);
lean_dec_ref(v_inputName_7_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v_a_9_);
return v___x_44_;
}
else
{
goto v___jp_30_;
}
}
v___jp_30_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_31_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1));
v___x_32_ = lean_string_append(v_inputName_7_, v___x_31_);
v___x_33_ = lean_string_append(v___x_32_, v_a_29_);
lean_dec(v_a_29_);
v___x_34_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2));
v___x_35_ = lean_string_append(v___x_33_, v___x_34_);
v___x_36_ = 2;
v___x_37_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*1, v___x_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_array_push(v_a_9_, v___x_37_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
return v___x_40_;
}
}
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec_ref(v_line_8_);
v___x_45_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3));
v___x_46_ = lean_string_append(v_inputName_7_, v___x_45_);
v___x_47_ = 3;
v___x_48_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set_uint8(v___x_48_, sizeof(void*)*1, v___x_47_);
v___x_49_ = lean_array_get_size(v_a_9_);
v___x_50_ = lean_array_push(v_a_9_, v___x_48_);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
v___jp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_13_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0));
v___x_14_ = lean_string_append(v_inputName_7_, v___x_13_);
v___x_15_ = lean_string_append(v___x_14_, v_a_12_);
lean_dec_ref(v_a_12_);
v___x_16_ = 2;
v___x_17_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*1, v___x_16_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_array_push(v_a_9_, v___x_17_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_18_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object* v_inputName_52_, lean_object* v_line_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_52_, v_line_53_, v_a_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object* v_x_59_){
_start:
{
lean_object* v_j_61_; 
if (lean_obj_tag(v_x_59_) == 4)
{
lean_object* v_elems_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_elems_69_ = lean_ctor_get(v_x_59_, 0);
v___x_70_ = lean_array_get_size(v_elems_69_);
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_dec_eq(v___x_70_, v___x_71_);
if (v___x_72_ == 0)
{
v_j_61_ = v_x_59_;
goto v___jp_60_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc_ref(v_elems_69_);
lean_dec_ref(v_x_59_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_array_fget_borrowed(v_elems_69_, v___x_73_);
lean_inc(v___x_74_);
v___x_75_ = l_Lake_Hash_fromJson_x3f(v___x_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec_ref(v_elems_69_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_94_; 
v_a_84_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_94_ == 0)
{
v___x_86_ = v___x_75_;
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_75_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_array_fget(v_elems_69_, v___x_88_);
lean_dec_ref(v_elems_69_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_a_84_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_90_);
v___x_92_ = v___x_86_;
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
else
{
v_j_61_ = v_x_59_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_62_ = ((lean_object*)(l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__0));
v___x_63_ = lean_unsigned_to_nat(80u);
v___x_64_ = l_Lean_Json_pretty(v_j_61_, v___x_63_);
v___x_65_ = lean_string_append(v___x_62_, v___x_64_);
lean_dec_ref(v___x_64_);
v___x_66_ = ((lean_object*)(l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___closed__1));
v___x_67_ = lean_string_append(v___x_65_, v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg(lean_object* v___x_95_, lean_object* v___x_96_, lean_object* v_contents_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_startInclusive_100_; lean_object* v_endExclusive_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_startInclusive_100_ = lean_ctor_get(v___x_95_, 1);
v_endExclusive_101_ = lean_ctor_get(v___x_95_, 2);
v___x_102_ = lean_nat_sub(v_endExclusive_101_, v_startInclusive_100_);
v___x_103_ = lean_nat_dec_eq(v_a_98_, v___x_102_);
lean_dec(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint32_t v___x_105_; uint32_t v___x_106_; uint8_t v___x_107_; 
lean_dec(v_b_99_);
v___x_104_ = lean_nat_add(v___x_96_, v_a_98_);
v___x_105_ = lean_string_utf8_get_fast(v_contents_97_, v___x_104_);
v___x_106_ = 10;
v___x_107_ = lean_uint32_dec_eq(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_a_98_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_string_utf8_next_fast(v_contents_97_, v___x_104_);
lean_dec(v___x_104_);
v___x_110_ = lean_nat_sub(v___x_109_, v___x_96_);
v_a_98_ = v___x_110_;
v_b_99_ = v___x_108_;
goto _start;
}
else
{
lean_object* v___x_112_; 
lean_dec(v___x_104_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_a_98_);
return v___x_112_;
}
}
else
{
lean_dec(v_a_98_);
return v_b_99_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg___boxed(lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_contents_115_, lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg(v___x_113_, v___x_114_, v_contents_115_, v_a_116_, v_b_117_);
lean_dec_ref(v_contents_115_);
lean_dec(v___x_114_);
lean_dec_ref(v___x_113_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
return v_x_119_;
}
else
{
lean_object* v_key_121_; lean_object* v_value_122_; lean_object* v_tail_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_147_; 
v_key_121_ = lean_ctor_get(v_x_120_, 0);
v_value_122_ = lean_ctor_get(v_x_120_, 1);
v_tail_123_ = lean_ctor_get(v_x_120_, 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_147_ == 0)
{
v___x_125_ = v_x_120_;
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_tail_123_);
lean_inc(v_value_122_);
lean_inc(v_key_121_);
lean_dec(v_x_120_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v_fold_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_127_ = lean_array_get_size(v_x_119_);
v___x_128_ = 32ULL;
v___x_129_ = lean_unbox_uint64(v_key_121_);
v___x_130_ = lean_uint64_shift_right(v___x_129_, v___x_128_);
v___x_131_ = lean_unbox_uint64(v_key_121_);
v_fold_132_ = lean_uint64_xor(v___x_131_, v___x_130_);
v___x_133_ = 16ULL;
v___x_134_ = lean_uint64_shift_right(v_fold_132_, v___x_133_);
v___x_135_ = lean_uint64_xor(v_fold_132_, v___x_134_);
v___x_136_ = lean_uint64_to_usize(v___x_135_);
v___x_137_ = lean_usize_of_nat(v___x_127_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_sub(v___x_137_, v___x_138_);
v___x_140_ = lean_usize_land(v___x_136_, v___x_139_);
v___x_141_ = lean_array_uget_borrowed(v_x_119_, v___x_140_);
lean_inc(v___x_141_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 2, v___x_141_);
v___x_143_ = v___x_125_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_key_121_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_value_122_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v___x_141_);
v___x_143_ = v_reuseFailAlloc_146_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_array_uset(v_x_119_, v___x_140_, v___x_143_);
v_x_119_ = v___x_144_;
v_x_120_ = v_tail_123_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5___redArg(lean_object* v_i_148_, lean_object* v_source_149_, lean_object* v_target_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_array_get_size(v_source_149_);
v___x_152_ = lean_nat_dec_lt(v_i_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec_ref(v_source_149_);
lean_dec(v_i_148_);
return v_target_150_;
}
else
{
lean_object* v_es_153_; lean_object* v___x_154_; lean_object* v_source_155_; lean_object* v_target_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_es_153_ = lean_array_fget(v_source_149_, v_i_148_);
v___x_154_ = lean_box(0);
v_source_155_ = lean_array_fset(v_source_149_, v_i_148_, v___x_154_);
v_target_156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5_spec__7___redArg(v_target_150_, v_es_153_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_i_148_, v___x_157_);
lean_dec(v_i_148_);
v_i_148_ = v___x_158_;
v_source_149_ = v_source_155_;
v_target_150_ = v_target_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4___redArg(lean_object* v_data_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_nbuckets_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_161_ = lean_array_get_size(v_data_160_);
v___x_162_ = lean_unsigned_to_nat(2u);
v_nbuckets_163_ = lean_nat_mul(v___x_161_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_box(0);
v___x_166_ = lean_mk_array(v_nbuckets_163_, v___x_165_);
v___x_167_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5___redArg(v___x_164_, v_data_160_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg(uint64_t v_a_168_, lean_object* v_b_169_, lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_dec(v_b_169_);
return v_x_170_;
}
else
{
lean_object* v_key_171_; lean_object* v_value_172_; lean_object* v_tail_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_187_; 
v_key_171_ = lean_ctor_get(v_x_170_, 0);
v_value_172_ = lean_ctor_get(v_x_170_, 1);
v_tail_173_ = lean_ctor_get(v_x_170_, 2);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_170_);
if (v_isSharedCheck_187_ == 0)
{
v___x_175_ = v_x_170_;
v_isShared_176_ = v_isSharedCheck_187_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_tail_173_);
lean_inc(v_value_172_);
lean_inc(v_key_171_);
lean_dec(v_x_170_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_187_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint64_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_unbox_uint64(v_key_171_);
v___x_178_ = lean_uint64_dec_eq(v___x_177_, v_a_168_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg(v_a_168_, v_b_169_, v_tail_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 2, v___x_179_);
v___x_181_ = v___x_175_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_key_171_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_value_172_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_185_; 
lean_dec(v_value_172_);
lean_dec(v_key_171_);
v___x_183_ = lean_box_uint64(v_a_168_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_b_169_);
lean_ctor_set(v___x_175_, 0, v___x_183_);
v___x_185_ = v___x_175_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_b_169_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_tail_173_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg___boxed(lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v_x_190_){
_start:
{
uint64_t v_a_boxed_191_; lean_object* v_res_192_; 
v_a_boxed_191_ = lean_unbox_uint64(v_a_188_);
lean_dec_ref(v_a_188_);
v_res_192_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg(v_a_boxed_191_, v_b_189_, v_x_190_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg(uint64_t v_a_193_, lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
else
{
lean_object* v_key_196_; lean_object* v_tail_197_; uint64_t v___x_198_; uint8_t v___x_199_; 
v_key_196_ = lean_ctor_get(v_x_194_, 0);
v_tail_197_ = lean_ctor_get(v_x_194_, 2);
v___x_198_ = lean_unbox_uint64(v_key_196_);
v___x_199_ = lean_uint64_dec_eq(v___x_198_, v_a_193_);
if (v___x_199_ == 0)
{
v_x_194_ = v_tail_197_;
goto _start;
}
else
{
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg___boxed(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
uint64_t v_a_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_a_boxed_203_ = lean_unbox_uint64(v_a_201_);
lean_dec_ref(v_a_201_);
v_res_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg(v_a_boxed_203_, v_x_202_);
lean_dec(v_x_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object* v_m_206_, uint64_t v_a_207_, lean_object* v_b_208_){
_start:
{
lean_object* v_size_209_; lean_object* v_buckets_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_253_; 
v_size_209_ = lean_ctor_get(v_m_206_, 0);
v_buckets_210_ = lean_ctor_get(v_m_206_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_m_206_);
if (v_isSharedCheck_253_ == 0)
{
v___x_212_ = v_m_206_;
v_isShared_213_ = v_isSharedCheck_253_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_buckets_210_);
lean_inc(v_size_209_);
lean_dec(v_m_206_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_253_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v_fold_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v_bkt_226_; uint8_t v___x_227_; 
v___x_214_ = lean_array_get_size(v_buckets_210_);
v___x_215_ = 32ULL;
v___x_216_ = lean_uint64_shift_right(v_a_207_, v___x_215_);
v_fold_217_ = lean_uint64_xor(v_a_207_, v___x_216_);
v___x_218_ = 16ULL;
v___x_219_ = lean_uint64_shift_right(v_fold_217_, v___x_218_);
v___x_220_ = lean_uint64_xor(v_fold_217_, v___x_219_);
v___x_221_ = lean_uint64_to_usize(v___x_220_);
v___x_222_ = lean_usize_of_nat(v___x_214_);
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_sub(v___x_222_, v___x_223_);
v___x_225_ = lean_usize_land(v___x_221_, v___x_224_);
v_bkt_226_ = lean_array_uget_borrowed(v_buckets_210_, v___x_225_);
v___x_227_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg(v_a_207_, v_bkt_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v_size_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_buckets_x27_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v_size_x27_229_ = lean_nat_add(v_size_209_, v___x_228_);
lean_dec(v_size_209_);
v___x_230_ = lean_box_uint64(v_a_207_);
lean_inc(v_bkt_226_);
v___x_231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_b_208_);
lean_ctor_set(v___x_231_, 2, v_bkt_226_);
v_buckets_x27_232_ = lean_array_uset(v_buckets_210_, v___x_225_, v___x_231_);
v___x_233_ = lean_unsigned_to_nat(4u);
v___x_234_ = lean_nat_mul(v_size_x27_229_, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(3u);
v___x_236_ = lean_nat_div(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_array_get_size(v_buckets_x27_232_);
v___x_238_ = lean_nat_dec_le(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
if (v___x_238_ == 0)
{
lean_object* v_val_239_; lean_object* v___x_241_; 
v_val_239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4___redArg(v_buckets_x27_232_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v_val_239_);
lean_ctor_set(v___x_212_, 0, v_size_x27_229_);
v___x_241_ = v___x_212_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_size_x27_229_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_val_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_244_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v_buckets_x27_232_);
lean_ctor_set(v___x_212_, 0, v_size_x27_229_);
v___x_244_ = v___x_212_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_size_x27_229_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_buckets_x27_232_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v___x_246_; lean_object* v_buckets_x27_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_inc(v_bkt_226_);
v___x_246_ = lean_box(0);
v_buckets_x27_247_ = lean_array_uset(v_buckets_210_, v___x_225_, v___x_246_);
v___x_248_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg(v_a_207_, v_b_208_, v_bkt_226_);
v___x_249_ = lean_array_uset(v_buckets_x27_247_, v___x_225_, v___x_248_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_249_);
v___x_251_ = v___x_212_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_size_209_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object* v_m_254_, lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
uint64_t v_a_boxed_257_; lean_object* v_res_258_; 
v_a_boxed_257_ = lean_unbox_uint64(v_a_255_);
lean_dec_ref(v_a_255_);
v_res_258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_m_254_, v_a_boxed_257_, v_b_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object* v_a_261_, lean_object* v_inputName_262_, lean_object* v_i_263_, lean_object* v_cache_264_, lean_object* v_contents_265_, lean_object* v_pos_266_){
_start:
{
lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v_a_271_; lean_object* v___y_279_; lean_object* v_a_280_; lean_object* v___y_293_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_searcher_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = lean_string_utf8_byte_size(v_contents_265_);
lean_inc(v_pos_266_);
lean_inc_ref(v_contents_265_);
v___x_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_322_, 0, v_contents_265_);
lean_ctor_set(v___x_322_, 1, v_pos_266_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
v_searcher_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_box(0);
v___x_325_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg(v___x_322_, v_pos_266_, v_contents_265_, v_searcher_323_, v___x_324_);
lean_dec_ref(v___x_322_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_nat_sub(v___x_321_, v_pos_266_);
v___y_293_ = v___x_326_;
goto v___jp_292_;
}
else
{
lean_object* v_val_327_; 
v_val_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_327_);
lean_dec_ref(v___x_325_);
v___y_293_ = v_val_327_;
goto v___jp_292_;
}
v___jp_268_:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_string_utf8_byte_size(v_contents_265_);
v___x_273_ = lean_nat_dec_eq(v___y_269_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref(v___y_270_);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_add(v_i_263_, v___x_274_);
lean_dec(v_i_263_);
v___x_276_ = lean_string_utf8_next_fast(v_contents_265_, v___y_269_);
lean_dec(v___y_269_);
v_i_263_ = v___x_275_;
v_cache_264_ = v_a_271_;
v_pos_266_ = v___x_276_;
goto _start;
}
else
{
lean_dec_ref(v_a_271_);
lean_dec(v___y_269_);
lean_dec_ref(v_contents_265_);
lean_dec(v_i_263_);
lean_dec_ref(v_inputName_262_);
lean_dec_ref(v_a_261_);
return v___y_270_;
}
}
v___jp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_281_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0));
lean_inc_ref(v_inputName_262_);
v___x_282_ = lean_string_append(v_inputName_262_, v___x_281_);
lean_inc(v_i_263_);
v___x_283_ = l_Nat_reprFast(v_i_263_);
v___x_284_ = lean_string_append(v___x_282_, v___x_283_);
lean_dec_ref(v___x_283_);
v___x_285_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1));
v___x_286_ = lean_string_append(v___x_284_, v___x_285_);
v___x_287_ = lean_string_append(v___x_286_, v_a_280_);
lean_dec_ref(v_a_280_);
v___x_288_ = 2;
v___x_289_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___x_288_);
lean_inc_ref(v_a_261_);
v___x_290_ = lean_apply_2(v_a_261_, v___x_289_, lean_box(0));
lean_inc_ref(v_cache_264_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_cache_264_);
v___y_269_ = v___y_279_;
v___y_270_ = v___x_291_;
v_a_271_ = v_cache_264_;
goto v___jp_268_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v_line_295_; lean_object* v___x_296_; lean_object* v_startInclusive_297_; lean_object* v_endExclusive_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_294_ = lean_nat_add(v_pos_266_, v___y_293_);
lean_dec(v___y_293_);
lean_inc(v___x_294_);
lean_inc(v_pos_266_);
lean_inc_ref(v_contents_265_);
v_line_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_295_, 0, v_contents_265_);
lean_ctor_set(v_line_295_, 1, v_pos_266_);
lean_ctor_set(v_line_295_, 2, v___x_294_);
v___x_296_ = l_String_Slice_trimAscii(v_line_295_);
lean_dec_ref(v_line_295_);
v_startInclusive_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_startInclusive_297_);
v_endExclusive_298_ = lean_ctor_get(v___x_296_, 2);
lean_inc(v_endExclusive_298_);
lean_dec_ref(v___x_296_);
v___x_299_ = lean_nat_sub(v_endExclusive_298_, v_startInclusive_297_);
lean_dec(v_startInclusive_297_);
lean_dec(v_endExclusive_298_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_string_utf8_extract(v_contents_265_, v_pos_266_, v___x_294_);
lean_dec(v_pos_266_);
v___x_303_ = l_Lean_Json_parse(v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
v___y_279_ = v___x_294_;
v_a_280_ = v_a_304_;
goto v___jp_278_;
}
else
{
lean_object* v_a_305_; lean_object* v___x_306_; 
v_a_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_305_);
lean_dec_ref(v___x_303_);
v___x_306_ = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_306_);
v___y_279_ = v___x_294_;
v_a_280_ = v_a_307_;
goto v___jp_278_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_319_; 
v_a_308_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_319_ == 0)
{
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_319_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_319_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_fst_312_; lean_object* v_snd_313_; uint64_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_fst_312_ = lean_ctor_get(v_a_308_, 0);
lean_inc(v_fst_312_);
v_snd_313_ = lean_ctor_get(v_a_308_, 1);
lean_inc(v_snd_313_);
lean_dec(v_a_308_);
v___x_314_ = lean_unbox_uint64(v_fst_312_);
lean_dec(v_fst_312_);
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_cache_264_, v___x_314_, v_snd_313_);
lean_inc_ref(v___x_315_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 0);
lean_ctor_set(v___x_310_, 0, v___x_315_);
v___x_317_ = v___x_310_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
v___y_269_ = v___x_294_;
v___y_270_ = v___x_317_;
v_a_271_ = v___x_315_;
goto v___jp_268_;
}
}
}
}
}
else
{
lean_object* v___x_320_; 
lean_dec(v___x_294_);
lean_dec(v_pos_266_);
lean_dec_ref(v_contents_265_);
lean_dec(v_i_263_);
lean_dec_ref(v_inputName_262_);
lean_dec_ref(v_a_261_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_cache_264_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object* v_a_328_, lean_object* v_inputName_329_, lean_object* v_i_330_, lean_object* v_cache_331_, lean_object* v_contents_332_, lean_object* v_pos_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_a_328_, v_inputName_329_, v_i_330_, v_cache_331_, v_contents_332_, v_pos_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg(lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v_contents_338_, lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
lean_object* v_startInclusive_341_; lean_object* v_endExclusive_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_startInclusive_341_ = lean_ctor_get(v___x_336_, 1);
v_endExclusive_342_ = lean_ctor_get(v___x_336_, 2);
v___x_343_ = lean_nat_sub(v_endExclusive_342_, v_startInclusive_341_);
v___x_344_ = lean_nat_dec_eq(v_a_339_, v___x_343_);
lean_dec(v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; uint32_t v___x_346_; uint32_t v___x_347_; uint8_t v___x_348_; 
lean_dec(v_b_340_);
v___x_345_ = lean_nat_add(v___x_337_, v_a_339_);
v___x_346_ = lean_string_utf8_get_fast(v_contents_338_, v___x_345_);
v___x_347_ = 10;
v___x_348_ = lean_uint32_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_a_339_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_string_utf8_next_fast(v_contents_338_, v___x_345_);
lean_dec(v___x_345_);
v___x_351_ = lean_nat_sub(v___x_350_, v___x_337_);
v_a_339_ = v___x_351_;
v_b_340_ = v___x_349_;
goto _start;
}
else
{
lean_object* v___x_353_; 
lean_dec(v___x_345_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_a_339_);
return v___x_353_;
}
}
else
{
lean_dec(v_a_339_);
return v_b_340_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg___boxed(lean_object* v___x_354_, lean_object* v___x_355_, lean_object* v_contents_356_, lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg(v___x_354_, v___x_355_, v_contents_356_, v_a_357_, v_b_358_);
lean_dec_ref(v_contents_356_);
lean_dec(v___x_355_);
lean_dec_ref(v___x_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object* v_inputName_360_, lean_object* v_i_361_, lean_object* v_cache_362_, lean_object* v_contents_363_, lean_object* v_pos_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v_a_370_; lean_object* v___y_378_; lean_object* v_a_379_; lean_object* v___y_392_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_searcher_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = lean_string_utf8_byte_size(v_contents_363_);
lean_inc(v_pos_364_);
lean_inc_ref(v_contents_363_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_contents_363_);
lean_ctor_set(v___x_421_, 1, v_pos_364_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
v_searcher_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_box(0);
v___x_424_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg(v___x_421_, v_pos_364_, v_contents_363_, v_searcher_422_, v___x_423_);
lean_dec_ref(v___x_421_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_nat_sub(v___x_420_, v_pos_364_);
v___y_392_ = v___x_425_;
goto v___jp_391_;
}
else
{
lean_object* v_val_426_; 
v_val_426_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_426_);
lean_dec_ref(v___x_424_);
v___y_392_ = v_val_426_;
goto v___jp_391_;
}
v___jp_367_:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_string_utf8_byte_size(v_contents_363_);
v___x_372_ = lean_nat_dec_eq(v___y_368_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v___y_369_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_i_361_, v___x_373_);
lean_dec(v_i_361_);
v___x_375_ = lean_string_utf8_next_fast(v_contents_363_, v___y_368_);
lean_dec(v___y_368_);
v___x_376_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_a_365_, v_inputName_360_, v___x_374_, v_a_370_, v_contents_363_, v___x_375_);
return v___x_376_;
}
else
{
lean_dec_ref(v_a_370_);
lean_dec(v___y_368_);
lean_dec_ref(v_a_365_);
lean_dec_ref(v_contents_363_);
lean_dec(v_i_361_);
lean_dec_ref(v_inputName_360_);
return v___y_369_;
}
}
v___jp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_380_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0));
lean_inc_ref(v_inputName_360_);
v___x_381_ = lean_string_append(v_inputName_360_, v___x_380_);
lean_inc(v_i_361_);
v___x_382_ = l_Nat_reprFast(v_i_361_);
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
lean_dec_ref(v___x_382_);
v___x_384_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1));
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
v___x_386_ = lean_string_append(v___x_385_, v_a_379_);
lean_dec_ref(v_a_379_);
v___x_387_ = 2;
v___x_388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*1, v___x_387_);
lean_inc_ref(v_a_365_);
v___x_389_ = lean_apply_2(v_a_365_, v___x_388_, lean_box(0));
lean_inc_ref(v_cache_362_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_cache_362_);
v___y_368_ = v___y_378_;
v___y_369_ = v___x_390_;
v_a_370_ = v_cache_362_;
goto v___jp_367_;
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v_line_394_; lean_object* v___x_395_; lean_object* v_startInclusive_396_; lean_object* v_endExclusive_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_393_ = lean_nat_add(v_pos_364_, v___y_392_);
lean_dec(v___y_392_);
lean_inc(v___x_393_);
lean_inc(v_pos_364_);
lean_inc_ref(v_contents_363_);
v_line_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_394_, 0, v_contents_363_);
lean_ctor_set(v_line_394_, 1, v_pos_364_);
lean_ctor_set(v_line_394_, 2, v___x_393_);
v___x_395_ = l_String_Slice_trimAscii(v_line_394_);
lean_dec_ref(v_line_394_);
v_startInclusive_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc(v_startInclusive_396_);
v_endExclusive_397_ = lean_ctor_get(v___x_395_, 2);
lean_inc(v_endExclusive_397_);
lean_dec_ref(v___x_395_);
v___x_398_ = lean_nat_sub(v_endExclusive_397_, v_startInclusive_396_);
lean_dec(v_startInclusive_396_);
lean_dec(v_endExclusive_397_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_nat_dec_eq(v___x_398_, v___x_399_);
lean_dec(v___x_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_string_utf8_extract(v_contents_363_, v_pos_364_, v___x_393_);
lean_dec(v_pos_364_);
v___x_402_ = l_Lean_Json_parse(v___x_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
v___y_378_ = v___x_393_;
v_a_379_ = v_a_403_;
goto v___jp_377_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_404_);
lean_dec_ref(v___x_402_);
v___x_405_ = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v___y_378_ = v___x_393_;
v_a_379_ = v_a_406_;
goto v___jp_377_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_418_; 
v_a_407_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_418_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_fst_411_; lean_object* v_snd_412_; uint64_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v_fst_411_ = lean_ctor_get(v_a_407_, 0);
lean_inc(v_fst_411_);
v_snd_412_ = lean_ctor_get(v_a_407_, 1);
lean_inc(v_snd_412_);
lean_dec(v_a_407_);
v___x_413_ = lean_unbox_uint64(v_fst_411_);
lean_dec(v_fst_411_);
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_cache_362_, v___x_413_, v_snd_412_);
lean_inc_ref(v___x_414_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_414_);
v___x_416_ = v___x_409_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
v___y_368_ = v___x_393_;
v___y_369_ = v___x_416_;
v_a_370_ = v___x_414_;
goto v___jp_367_;
}
}
}
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v___x_393_);
lean_dec_ref(v_a_365_);
lean_dec(v_pos_364_);
lean_dec_ref(v_contents_363_);
lean_dec(v_i_361_);
lean_dec_ref(v_inputName_360_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_cache_362_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object* v_inputName_427_, lean_object* v_i_428_, lean_object* v_cache_429_, lean_object* v_contents_430_, lean_object* v_pos_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(v_inputName_427_, v_i_428_, v_cache_429_, v_contents_430_, v_pos_431_, v_a_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object* v_00_u03b2_435_, lean_object* v_m_436_, uint64_t v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_m_436_, v_a_437_, v_b_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object* v_00_u03b2_440_, lean_object* v_m_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
uint64_t v_a_boxed_444_; lean_object* v_res_445_; 
v_a_boxed_444_ = lean_unbox_uint64(v_a_442_);
lean_dec_ref(v_a_442_);
v_res_445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(v_00_u03b2_440_, v_m_441_, v_a_boxed_444_, v_b_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3(lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v_contents_448_, lean_object* v_inst_449_, lean_object* v_R_450_, lean_object* v_a_451_, lean_object* v_b_452_, lean_object* v_c_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___redArg(v___x_446_, v___x_447_, v_contents_448_, v_a_451_, v_b_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3___boxed(lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_contents_457_, lean_object* v_inst_458_, lean_object* v_R_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v_c_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__3(v___x_455_, v___x_456_, v_contents_457_, v_inst_458_, v_R_459_, v_a_460_, v_b_461_, v_c_462_);
lean_dec_ref(v_contents_457_);
lean_dec(v___x_456_);
lean_dec_ref(v___x_455_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v_contents_466_, lean_object* v_inst_467_, lean_object* v_R_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_c_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___redArg(v___x_464_, v___x_465_, v_contents_466_, v_a_469_, v_b_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___boxed(lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v_contents_475_, lean_object* v_inst_476_, lean_object* v_R_477_, lean_object* v_a_478_, lean_object* v_b_479_, lean_object* v_c_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(v___x_473_, v___x_474_, v_contents_475_, v_inst_476_, v_R_477_, v_a_478_, v_b_479_, v_c_480_);
lean_dec_ref(v_contents_475_);
lean_dec(v___x_474_);
lean_dec_ref(v___x_473_);
return v_res_481_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3(lean_object* v_00_u03b2_482_, uint64_t v_a_483_, lean_object* v_x_484_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___redArg(v_a_483_, v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3___boxed(lean_object* v_00_u03b2_486_, lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
uint64_t v_a_boxed_489_; uint8_t v_res_490_; lean_object* v_r_491_; 
v_a_boxed_489_ = lean_unbox_uint64(v_a_487_);
lean_dec_ref(v_a_487_);
v_res_490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__3(v_00_u03b2_486_, v_a_boxed_489_, v_x_488_);
lean_dec(v_x_488_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4(lean_object* v_00_u03b2_492_, lean_object* v_data_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4___redArg(v_data_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5(lean_object* v_00_u03b2_495_, uint64_t v_a_496_, lean_object* v_b_497_, lean_object* v_x_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___redArg(v_a_496_, v_b_497_, v_x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5___boxed(lean_object* v_00_u03b2_500_, lean_object* v_a_501_, lean_object* v_b_502_, lean_object* v_x_503_){
_start:
{
uint64_t v_a_boxed_504_; lean_object* v_res_505_; 
v_a_boxed_504_ = lean_unbox_uint64(v_a_501_);
lean_dec_ref(v_a_501_);
v_res_505_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__5(v_00_u03b2_500_, v_a_boxed_504_, v_b_502_, v_x_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_506_, lean_object* v_i_507_, lean_object* v_source_508_, lean_object* v_target_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5___redArg(v_i_507_, v_source_508_, v_target_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2_spec__4_spec__5_spec__7___redArg(v_x_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_apply_2(v___y_516_, v___y_515_, lean_box(0));
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg___boxed(lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lake_CacheMap_parse___elam__0___redArg(v___y_520_, v___y_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lake_CacheMap_parse___elam__0___redArg(v___y_525_, v___y_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___boxed(lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lake_CacheMap_parse___elam__0(v_x_529_, v___y_530_, v___y_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(lean_object* v___x_534_, lean_object* v_contents_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v_startInclusive_538_; lean_object* v_endExclusive_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_startInclusive_538_ = lean_ctor_get(v___x_534_, 1);
v_endExclusive_539_ = lean_ctor_get(v___x_534_, 2);
v___x_540_ = lean_nat_sub(v_endExclusive_539_, v_startInclusive_538_);
v___x_541_ = lean_nat_dec_eq(v_a_536_, v___x_540_);
lean_dec(v___x_540_);
if (v___x_541_ == 0)
{
uint32_t v___x_542_; uint32_t v___x_543_; uint8_t v___x_544_; 
lean_dec(v_b_537_);
v___x_542_ = lean_string_utf8_get_fast(v_contents_535_, v_a_536_);
v___x_543_ = 10;
v___x_544_ = lean_uint32_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_box(0);
v___x_546_ = lean_string_utf8_next_fast(v_contents_535_, v_a_536_);
lean_dec(v_a_536_);
v_a_536_ = v___x_546_;
v_b_537_ = v___x_545_;
goto _start;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_a_536_);
return v___x_548_;
}
}
else
{
lean_dec(v_a_536_);
return v_b_537_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg___boxed(lean_object* v___x_549_, lean_object* v_contents_550_, lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(v___x_549_, v_contents_550_, v_a_551_, v_b_552_);
lean_dec_ref(v_contents_550_);
lean_dec_ref(v___x_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_apply_2(v___y_554_, v___y_555_, lean_box(0));
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg___boxed(lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(v___y_559_, v___y_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(lean_object* v_as_563_, size_t v_i_564_, size_t v_stop_565_, lean_object* v_b_566_, lean_object* v___y_567_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_eq(v_i_564_, v_stop_565_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_array_uget_borrowed(v_as_563_, v_i_564_);
lean_inc(v___x_570_);
lean_inc_ref(v___y_567_);
v___x_571_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(v___y_567_, v___x_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; size_t v___x_573_; size_t v___x_574_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_564_, v___x_573_);
v_i_564_ = v___x_574_;
v_b_566_ = v_a_572_;
goto _start;
}
else
{
lean_dec_ref(v___y_567_);
return v___x_571_;
}
}
else
{
lean_object* v___x_576_; 
lean_dec_ref(v___y_567_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_b_566_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object* v_as_577_, lean_object* v_i_578_, lean_object* v_stop_579_, lean_object* v_b_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
size_t v_i_boxed_583_; size_t v_stop_boxed_584_; lean_object* v_res_585_; 
v_i_boxed_583_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_stop_boxed_584_ = lean_unbox_usize(v_stop_579_);
lean_dec(v_stop_579_);
v_res_585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_as_577_, v_i_boxed_583_, v_stop_boxed_584_, v_b_580_, v___y_581_);
lean_dec_ref(v_as_577_);
return v_res_585_;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__0(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = lean_unsigned_to_nat(16u);
v___x_588_ = lean_mk_array(v___x_587_, v___x_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* v_inputName_591_, lean_object* v_contents_592_, lean_object* v_a_593_){
_start:
{
uint8_t v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; uint8_t v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_624_; lean_object* v_searcher_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_searcher_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_string_utf8_byte_size(v_contents_592_);
lean_inc_ref(v_contents_592_);
v___x_662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_662_, 0, v_contents_592_);
lean_ctor_set(v___x_662_, 1, v_searcher_660_);
lean_ctor_set(v___x_662_, 2, v___x_661_);
v___x_663_ = lean_box(0);
v___x_664_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(v___x_662_, v_contents_592_, v_searcher_660_, v___x_663_);
lean_dec_ref(v___x_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
v___y_624_ = v___x_661_;
goto v___jp_623_;
}
else
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref(v___x_664_);
v___y_624_ = v_val_665_;
goto v___jp_623_;
}
v___jp_595_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
v___jp_598_:
{
if (v___y_599_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_602_ = lean_unsigned_to_nat(2u);
v___x_603_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___y_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_string_utf8_next_fast(v_contents_592_, v___y_601_);
lean_dec(v___y_601_);
v___x_606_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_a_593_, v_inputName_591_, v___x_602_, v___x_604_, v_contents_592_, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___y_601_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_contents_592_);
lean_dec_ref(v_inputName_591_);
v___x_607_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_600_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
v___jp_610_:
{
if (lean_obj_tag(v___y_614_) == 0)
{
lean_dec_ref(v___y_614_);
v___y_599_ = v___y_611_;
v___y_600_ = v___y_612_;
v___y_601_ = v___y_613_;
goto v___jp_598_;
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_contents_592_);
lean_dec_ref(v_inputName_591_);
v_a_615_ = lean_ctor_get(v___y_614_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___y_614_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___y_614_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___y_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v_line_626_; lean_object* v___x_627_; lean_object* v_str_628_; lean_object* v_startInclusive_629_; lean_object* v_endExclusive_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_625_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_624_);
lean_inc_ref(v_contents_592_);
v_line_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_626_, 0, v_contents_592_);
lean_ctor_set(v_line_626_, 1, v___x_625_);
lean_ctor_set(v_line_626_, 2, v___y_624_);
v___x_627_ = l_String_Slice_trimAscii(v_line_626_);
lean_dec_ref(v_line_626_);
v_str_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_str_628_);
v_startInclusive_629_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_startInclusive_629_);
v_endExclusive_630_ = lean_ctor_get(v___x_627_, 2);
lean_inc(v_endExclusive_630_);
lean_dec_ref(v___x_627_);
v___x_631_ = lean_string_utf8_extract(v_str_628_, v_startInclusive_629_, v_endExclusive_630_);
lean_dec(v_endExclusive_630_);
lean_dec(v_startInclusive_629_);
lean_dec_ref(v_str_628_);
v___x_632_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
lean_inc_ref(v_inputName_591_);
v___x_633_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_591_, v___x_631_, v___x_632_);
v___x_634_ = lean_string_utf8_byte_size(v_contents_592_);
v___x_635_ = lean_nat_dec_eq(v___y_624_, v___x_634_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_a_636_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_636_);
lean_dec_ref(v___x_633_);
v___x_637_ = lean_array_get_size(v_a_636_);
v___x_638_ = lean_nat_dec_lt(v___x_625_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v_a_636_);
v___y_599_ = v___x_635_;
v___y_600_ = v___x_625_;
v___y_601_ = v___y_624_;
goto v___jp_598_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_nat_dec_le(v___x_637_, v___x_637_);
if (v___x_640_ == 0)
{
if (v___x_638_ == 0)
{
lean_dec(v_a_636_);
v___y_599_ = v___x_635_;
v___y_600_ = v___x_625_;
v___y_601_ = v___y_624_;
goto v___jp_598_;
}
else
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_637_);
lean_inc_ref(v_a_593_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_636_, v___x_641_, v___x_642_, v___x_639_, v_a_593_);
lean_dec(v_a_636_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref(v___x_643_);
v___y_599_ = v___x_635_;
v___y_600_ = v___x_625_;
v___y_601_ = v___y_624_;
goto v___jp_598_;
}
else
{
v___y_611_ = v___x_635_;
v___y_612_ = v___x_625_;
v___y_613_ = v___y_624_;
v___y_614_ = v___x_643_;
goto v___jp_610_;
}
}
}
else
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((size_t)0ULL);
v___x_645_ = lean_usize_of_nat(v___x_637_);
lean_inc_ref(v_a_593_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_636_, v___x_644_, v___x_645_, v___x_639_, v_a_593_);
lean_dec(v_a_636_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref(v___x_646_);
v___y_599_ = v___x_635_;
v___y_600_ = v___x_625_;
v___y_601_ = v___y_624_;
goto v___jp_598_;
}
else
{
v___y_611_ = v___x_635_;
v___y_612_ = v___x_625_;
v___y_613_ = v___y_624_;
v___y_614_ = v___x_646_;
goto v___jp_610_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_a_647_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_a_647_);
lean_dec_ref(v___x_633_);
v___x_648_ = lean_array_get_size(v_a_647_);
v___x_649_ = lean_nat_dec_lt(v___x_625_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec(v_a_647_);
lean_dec(v___y_624_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_contents_592_);
lean_dec_ref(v_inputName_591_);
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_box(0);
v___x_653_ = lean_nat_dec_le(v___x_648_, v___x_648_);
if (v___x_653_ == 0)
{
if (v___x_649_ == 0)
{
lean_dec(v_a_647_);
lean_dec(v___y_624_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_contents_592_);
lean_dec_ref(v_inputName_591_);
goto v___jp_595_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_648_);
lean_inc_ref(v_a_593_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_647_, v___x_654_, v___x_655_, v___x_652_, v_a_593_);
lean_dec(v_a_647_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_dec_ref(v___x_656_);
lean_dec(v___y_624_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_contents_592_);
lean_dec_ref(v_inputName_591_);
goto v___jp_595_;
}
else
{
v___y_611_ = v___x_635_;
v___y_612_ = v___x_625_;
v___y_613_ = v___y_624_;
v___y_614_ = v___x_656_;
goto v___jp_610_;
}
}
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_648_);
lean_inc_ref(v_a_593_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_647_, v___x_657_, v___x_658_, v___x_652_, v_a_593_);
lean_dec(v_a_647_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_dec_ref(v___x_659_);
lean_dec(v___y_624_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_contents_592_);
lean_dec_ref(v_inputName_591_);
goto v___jp_595_;
}
else
{
v___y_611_ = v___x_635_;
v___y_612_ = v___x_625_;
v___y_613_ = v___y_624_;
v___y_614_ = v___x_659_;
goto v___jp_610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* v_inputName_666_, lean_object* v_contents_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lake_CacheMap_parse(v_inputName_666_, v_contents_667_, v_a_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1(lean_object* v___y_671_, lean_object* v_x_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___redArg(v___y_671_, v___y_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1___boxed(lean_object* v___y_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1_spec__1(v___y_676_, v_x_677_, v___y_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2(lean_object* v___x_681_, lean_object* v_contents_682_, lean_object* v_inst_683_, lean_object* v_R_684_, lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_c_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___redArg(v___x_681_, v_contents_682_, v_a_685_, v_b_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2___boxed(lean_object* v___x_689_, lean_object* v_contents_690_, lean_object* v_inst_691_, lean_object* v_R_692_, lean_object* v_a_693_, lean_object* v_b_694_, lean_object* v_c_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__2(v___x_689_, v_contents_690_, v_inst_691_, v_R_692_, v_a_693_, v_b_694_, v_c_695_);
lean_dec_ref(v_contents_690_);
lean_dec_ref(v___x_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* v_h_697_, lean_object* v_fileName_698_, lean_object* v_i_699_, lean_object* v_cache_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_io_prim_handle_get_line(v_h_697_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v_a_706_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_703_);
v___x_720_ = lean_string_utf8_byte_size(v_a_704_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_nat_dec_eq(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Json_parse(v_a_704_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v_a_706_ = v_a_724_;
goto v___jp_705_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_723_);
v___x_726_ = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_726_);
v_a_706_ = v_a_727_;
goto v___jp_705_;
}
else
{
lean_object* v_a_728_; lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint64_t v___x_733_; lean_object* v___x_734_; 
v_a_728_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_728_);
lean_dec_ref(v___x_726_);
v_fst_729_ = lean_ctor_get(v_a_728_, 0);
lean_inc(v_fst_729_);
v_snd_730_ = lean_ctor_get(v_a_728_, 1);
lean_inc(v_snd_730_);
lean_dec(v_a_728_);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_i_699_, v___x_731_);
lean_dec(v_i_699_);
v___x_733_ = lean_unbox_uint64(v_fst_729_);
lean_dec(v_fst_729_);
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_cache_700_, v___x_733_, v_snd_730_);
v_i_699_ = v___x_732_;
v_cache_700_ = v___x_734_;
goto _start;
}
}
}
else
{
lean_object* v___x_736_; 
lean_dec(v_a_704_);
lean_dec(v_i_699_);
lean_dec_ref(v_fileName_698_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_cache_700_);
lean_ctor_set(v___x_736_, 1, v_a_701_);
return v___x_736_;
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_707_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0));
lean_inc_ref(v_fileName_698_);
v___x_708_ = lean_string_append(v_fileName_698_, v___x_707_);
lean_inc(v_i_699_);
v___x_709_ = l_Nat_reprFast(v_i_699_);
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
lean_dec_ref(v___x_709_);
v___x_711_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1));
v___x_712_ = lean_string_append(v___x_710_, v___x_711_);
v___x_713_ = lean_string_append(v___x_712_, v_a_706_);
lean_dec_ref(v_a_706_);
v___x_714_ = 2;
v___x_715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*1, v___x_714_);
v___x_716_ = lean_array_push(v_a_701_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_add(v_i_699_, v___x_717_);
lean_dec(v_i_699_);
v_i_699_ = v___x_718_;
v_a_701_ = v___x_716_;
goto _start;
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref(v_cache_700_);
lean_dec(v_i_699_);
lean_dec_ref(v_fileName_698_);
v_a_737_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_703_);
v___x_738_ = lean_io_error_to_string(v_a_737_);
v___x_739_ = 3;
v___x_740_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_739_);
v___x_741_ = lean_array_get_size(v_a_701_);
v___x_742_ = lean_array_push(v_a_701_, v___x_740_);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* v_h_744_, lean_object* v_fileName_745_, lean_object* v_i_746_, lean_object* v_cache_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_744_, v_fileName_745_, v_i_746_, v_cache_747_, v_a_748_);
lean_dec(v_h_744_);
return v_res_750_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* v_h_754_, lean_object* v_fileName_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_io_prim_handle_get_line(v_h_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
lean_inc_ref(v_fileName_755_);
v___x_760_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_fileName_755_, v_a_759_, v_a_756_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_a_761_ = lean_ctor_get(v___x_760_, 1);
lean_inc(v_a_761_);
lean_dec_ref(v___x_760_);
v___x_762_ = lean_unsigned_to_nat(2u);
v___x_763_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_764_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_754_, v_fileName_755_, v___x_762_, v___x_763_, v_a_761_);
return v___x_764_;
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_fileName_755_);
v_a_765_ = lean_ctor_get(v___x_760_, 0);
v_a_766_ = lean_ctor_get(v___x_760_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_760_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v___x_760_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_fileName_755_);
v_a_774_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_758_);
v___x_775_ = lean_io_error_to_string(v_a_774_);
v___x_776_ = 3;
v___x_777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v___x_776_);
v___x_778_ = lean_array_get_size(v_a_756_);
v___x_779_ = lean_array_push(v_a_756_, v___x_777_);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* v_h_781_, lean_object* v_fileName_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(v_h_781_, v_fileName_782_, v_a_783_);
lean_dec(v_h_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* v_file_787_, lean_object* v_a_788_){
_start:
{
uint8_t v___x_790_; lean_object* v___x_791_; 
v___x_790_ = 0;
v___x_791_ = lean_io_prim_handle_mk(v_file_787_, v___x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; uint8_t v___x_793_; lean_object* v___x_794_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
v___x_793_ = 0;
v___x_794_ = lean_io_prim_handle_lock(v_a_792_, v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
lean_dec_ref(v___x_794_);
v___x_795_ = lean_io_prim_handle_get_line(v_a_792_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
lean_inc_ref(v_file_787_);
v___x_797_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_787_, v_a_796_, v_a_788_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_798_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = lean_unsigned_to_nat(2u);
v___x_800_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_801_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_792_, v_file_787_, v___x_799_, v___x_800_, v_a_798_);
lean_dec(v_a_792_);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_a_792_);
lean_dec_ref(v_file_787_);
v_a_802_ = lean_ctor_get(v___x_797_, 0);
v_a_803_ = lean_ctor_get(v___x_797_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_797_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_inc(v_a_802_);
lean_dec(v___x_797_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_802_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_a_803_);
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
else
{
lean_object* v_a_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v_a_792_);
lean_dec_ref(v_file_787_);
v_a_811_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_811_);
lean_dec_ref(v___x_795_);
v___x_812_ = lean_io_error_to_string(v_a_811_);
v___x_813_ = 3;
v___x_814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_813_);
v___x_815_ = lean_array_get_size(v_a_788_);
v___x_816_ = lean_array_push(v_a_788_, v___x_814_);
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
return v___x_817_;
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_a_792_);
lean_dec_ref(v_file_787_);
v_a_818_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_794_);
v___x_819_ = lean_io_error_to_string(v_a_818_);
v___x_820_ = 3;
v___x_821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v___x_820_);
v___x_822_ = lean_array_get_size(v_a_788_);
v___x_823_ = lean_array_push(v_a_788_, v___x_821_);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
return v___x_824_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_825_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_825_);
lean_dec_ref(v___x_791_);
v___x_826_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_827_ = lean_string_append(v_file_787_, v___x_826_);
v___x_828_ = lean_io_error_to_string(v_a_825_);
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
lean_dec_ref(v___x_828_);
v___x_830_ = 3;
v___x_831_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*1, v___x_830_);
v___x_832_ = lean_array_get_size(v_a_788_);
v___x_833_ = lean_array_push(v_a_788_, v___x_831_);
v___x_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object* v_file_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lake_CacheMap_load(v_file_835_, v_a_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* v_file_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_a_843_; lean_object* v_a_844_; uint8_t v___x_846_; lean_object* v___x_847_; 
v___x_846_ = 0;
v___x_847_ = lean_io_prim_handle_mk(v_file_839_, v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; uint8_t v___x_849_; lean_object* v___x_850_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = 0;
v___x_850_ = lean_io_prim_handle_lock(v_a_848_, v___x_849_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v___x_850_);
v___x_851_ = lean_io_prim_handle_get_line(v_a_848_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_877_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_877_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_877_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_877_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; 
lean_inc_ref(v_file_839_);
v___x_856_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_839_, v_a_852_, v_a_840_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_a_857_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___x_858_ = lean_unsigned_to_nat(2u);
v___x_859_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_860_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_848_, v_file_839_, v___x_858_, v___x_859_, v_a_857_);
lean_dec(v_a_848_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_872_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_a_862_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_872_ == 0)
{
v___x_864_ = v___x_860_;
v_isShared_865_ = v_isSharedCheck_872_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_872_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 1);
lean_ctor_set(v___x_854_, 0, v_a_861_);
v___x_867_ = v___x_854_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_861_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_a_862_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v_a_874_; 
lean_del_object(v___x_854_);
v_a_873_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_873_);
v_a_874_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_a_874_);
lean_dec_ref(v___x_860_);
v_a_843_ = v_a_873_;
v_a_844_ = v_a_874_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_875_; lean_object* v_a_876_; 
lean_del_object(v___x_854_);
lean_dec(v_a_848_);
lean_dec_ref(v_file_839_);
v_a_875_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_875_);
v_a_876_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_a_876_);
lean_dec_ref(v___x_856_);
v_a_843_ = v_a_875_;
v_a_844_ = v_a_876_;
goto v___jp_842_;
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec(v_a_848_);
lean_dec_ref(v_file_839_);
v_a_878_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_851_);
v___x_879_ = lean_io_error_to_string(v_a_878_);
v___x_880_ = 3;
v___x_881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_880_);
v___x_882_ = lean_array_get_size(v_a_840_);
v___x_883_ = lean_array_push(v_a_840_, v___x_881_);
v_a_843_ = v___x_882_;
v_a_844_ = v___x_883_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_a_848_);
lean_dec_ref(v_file_839_);
v_a_884_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_850_);
v___x_885_ = lean_io_error_to_string(v_a_884_);
v___x_886_ = 3;
v___x_887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_886_);
v___x_888_ = lean_array_get_size(v_a_840_);
v___x_889_ = lean_array_push(v_a_840_, v___x_887_);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
}
else
{
lean_object* v_a_891_; 
v_a_891_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_847_);
if (lean_obj_tag(v_a_891_) == 11)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v_a_891_);
lean_dec_ref(v_file_839_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_a_840_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_894_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_895_ = lean_string_append(v_file_839_, v___x_894_);
v___x_896_ = lean_io_error_to_string(v_a_891_);
v___x_897_ = lean_string_append(v___x_895_, v___x_896_);
lean_dec_ref(v___x_896_);
v___x_898_ = 3;
v___x_899_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*1, v___x_898_);
v___x_900_ = lean_array_get_size(v_a_840_);
v___x_901_ = lean_array_push(v_a_840_, v___x_899_);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
return v___x_902_;
}
}
v___jp_842_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_845_, 0, v_a_843_);
lean_ctor_set(v___x_845_, 1, v_a_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object* v_file_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lake_CacheMap_load_x3f(v_file_903_, v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0(lean_object* v_x_907_){
_start:
{
lean_object* v_fst_908_; lean_object* v_snd_909_; uint64_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_fst_908_ = lean_ctor_get(v_x_907_, 0);
lean_inc(v_fst_908_);
v_snd_909_ = lean_ctor_get(v_x_907_, 1);
lean_inc(v_snd_909_);
lean_dec_ref(v_x_907_);
v___x_910_ = lean_unbox_uint64(v_fst_908_);
lean_dec(v_fst_908_);
v___x_911_ = l_Lake_Hash_hex(v___x_910_);
v___x_912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = lean_unsigned_to_nat(2u);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_915_ = lean_array_push(v___x_914_, v___x_912_);
v___x_916_ = lean_array_push(v___x_915_, v_snd_909_);
v___x_917_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3(lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
return v_x_918_;
}
else
{
lean_object* v_key_920_; lean_object* v_value_921_; lean_object* v_tail_922_; uint64_t v___x_923_; lean_object* v___x_924_; 
v_key_920_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_key_920_);
v_value_921_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_value_921_);
v_tail_922_ = lean_ctor_get(v_x_919_, 2);
lean_inc(v_tail_922_);
lean_dec_ref(v_x_919_);
v___x_923_ = lean_unbox_uint64(v_key_920_);
lean_dec(v_key_920_);
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_x_918_, v___x_923_, v_value_921_);
v_x_918_ = v___x_924_;
v_x_919_ = v_tail_922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_, lean_object* v_b_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_eq(v_i_927_, v_stop_928_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; 
v___x_931_ = lean_array_uget_borrowed(v_as_926_, v_i_927_);
lean_inc(v___x_931_);
v___x_932_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3(v_b_929_, v___x_931_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_927_, v___x_933_);
v_i_927_ = v___x_934_;
v_b_929_ = v___x_932_;
goto _start;
}
else
{
return v_b_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4___boxed(lean_object* v_as_936_, lean_object* v_i_937_, lean_object* v_stop_938_, lean_object* v_b_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; lean_object* v_res_942_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_938_);
lean_dec(v_stop_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(v_as_936_, v_i_boxed_940_, v_stop_boxed_941_, v_b_939_);
lean_dec_ref(v_as_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(lean_object* v_a_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v___y_946_){
_start:
{
if (lean_obj_tag(v_x_945_) == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_x_944_);
lean_ctor_set(v___x_948_, 1, v___y_946_);
return v___x_948_;
}
else
{
lean_object* v_key_949_; lean_object* v_value_950_; lean_object* v_tail_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_key_949_ = lean_ctor_get(v_x_945_, 0);
v_value_950_ = lean_ctor_get(v_x_945_, 1);
v_tail_951_ = lean_ctor_get(v_x_945_, 2);
lean_inc(v_value_950_);
lean_inc(v_key_949_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_key_949_);
lean_ctor_set(v___x_952_, 1, v_value_950_);
v___x_953_ = l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0(v___x_952_);
v___x_954_ = l_Lean_Json_compress(v___x_953_);
v___x_955_ = l_IO_FS_Handle_putStrLn(v_a_943_, v___x_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v___x_955_);
v_x_944_ = v_a_956_;
v_x_945_ = v_tail_951_;
goto _start;
}
else
{
lean_object* v_a_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_958_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_955_);
v___x_959_ = lean_io_error_to_string(v_a_958_);
v___x_960_ = 3;
v___x_961_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_960_);
v___x_962_ = lean_array_get_size(v___y_946_);
v___x_963_ = lean_array_push(v___y_946_, v___x_961_);
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object* v_a_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(v_a_965_, v_x_966_, v_x_967_, v___y_968_);
lean_dec(v_x_967_);
lean_dec(v_a_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(lean_object* v_a_971_, lean_object* v_as_972_, size_t v_i_973_, size_t v_stop_974_, lean_object* v_b_975_, lean_object* v___y_976_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_eq(v_i_973_, v_stop_974_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_array_uget_borrowed(v_as_972_, v_i_973_);
v___x_980_ = lean_box(0);
v___x_981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(v_a_971_, v___x_980_, v___x_979_, v___y_976_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_a_983_; size_t v___x_984_; size_t v___x_985_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
v_a_983_ = lean_ctor_get(v___x_981_, 1);
lean_inc(v_a_983_);
lean_dec_ref(v___x_981_);
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_i_973_, v___x_984_);
v_i_973_ = v___x_985_;
v_b_975_ = v_a_982_;
v___y_976_ = v_a_983_;
goto _start;
}
else
{
return v___x_981_;
}
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_b_975_);
lean_ctor_set(v___x_987_, 1, v___y_976_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2___boxed(lean_object* v_a_988_, lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
size_t v_i_boxed_995_; size_t v_stop_boxed_996_; lean_object* v_res_997_; 
v_i_boxed_995_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_996_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(v_a_988_, v_as_989_, v_i_boxed_995_, v_stop_boxed_996_, v_b_992_, v___y_993_);
lean_dec_ref(v_as_989_);
lean_dec(v_a_988_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* v_file_998_, lean_object* v_cache_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_a_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; 
lean_inc_ref(v_file_998_);
v___x_1006_ = l_Lake_createParentDirs(v_file_998_);
if (lean_obj_tag(v___x_1006_) == 0)
{
uint8_t v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___x_1006_);
v___x_1007_ = 4;
v___x_1008_ = lean_io_prim_handle_mk(v_file_998_, v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
uint8_t v___x_1009_; lean_object* v___x_1010_; 
lean_dec_ref(v___x_1008_);
v___x_1009_ = 3;
v___x_1010_ = lean_io_prim_handle_mk(v_file_998_, v___x_1009_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = 1;
v___x_1013_ = lean_io_prim_handle_lock(v_a_1011_, v___x_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; 
lean_dec_ref(v___x_1013_);
v___x_1014_ = lean_io_prim_handle_get_line(v_a_1011_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref(v___x_1014_);
lean_inc_ref(v_file_998_);
v___x_1016_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_998_, v_a_1015_, v_a_1000_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = lean_unsigned_to_nat(2u);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_1021_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_1011_, v_file_998_, v___x_1018_, v___x_1020_, v_a_1017_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1066_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1025_ = v___x_1021_;
v_isShared_1026_ = v_isSharedCheck_1066_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1066_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___y_1028_; lean_object* v_buckets_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_buckets_1056_ = lean_ctor_get(v_cache_999_, 1);
v___x_1057_ = lean_array_get_size(v_buckets_1056_);
v___x_1058_ = lean_nat_dec_lt(v___x_1019_, v___x_1057_);
if (v___x_1058_ == 0)
{
v___y_1028_ = v_a_1022_;
goto v___jp_1027_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_le(v___x_1057_, v___x_1057_);
if (v___x_1059_ == 0)
{
if (v___x_1058_ == 0)
{
v___y_1028_ = v_a_1022_;
goto v___jp_1027_;
}
else
{
size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1057_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(v_buckets_1056_, v___x_1060_, v___x_1061_, v_a_1022_);
v___y_1028_ = v___x_1062_;
goto v___jp_1027_;
}
}
else
{
size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = lean_usize_of_nat(v___x_1057_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(v_buckets_1056_, v___x_1063_, v___x_1064_, v_a_1022_);
v___y_1028_ = v___x_1065_;
goto v___jp_1027_;
}
}
v___jp_1027_:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_io_prim_handle_rewind(v_a_1011_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_buckets_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_dec_ref(v___x_1029_);
v_buckets_1030_ = lean_ctor_get(v___y_1028_, 1);
lean_inc_ref(v_buckets_1030_);
lean_dec_ref(v___y_1028_);
v___x_1031_ = lean_array_get_size(v_buckets_1030_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_nat_dec_lt(v___x_1019_, v___x_1031_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_buckets_1030_);
lean_dec(v_a_1011_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1032_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_a_1023_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
else
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_nat_dec_le(v___x_1031_, v___x_1031_);
if (v___x_1037_ == 0)
{
if (v___x_1033_ == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref(v_buckets_1030_);
lean_dec(v_a_1011_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1032_);
v___x_1039_ = v___x_1025_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_a_1023_);
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
size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
lean_del_object(v___x_1025_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = lean_usize_of_nat(v___x_1031_);
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(v_a_1011_, v_buckets_1030_, v___x_1041_, v___x_1042_, v___x_1032_, v_a_1023_);
lean_dec_ref(v_buckets_1030_);
lean_dec(v_a_1011_);
return v___x_1043_;
}
}
else
{
size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
lean_del_object(v___x_1025_);
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = lean_usize_of_nat(v___x_1031_);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(v_a_1011_, v_buckets_1030_, v___x_1044_, v___x_1045_, v___x_1032_, v_a_1023_);
lean_dec_ref(v_buckets_1030_);
lean_dec(v_a_1011_);
return v___x_1046_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_dec_ref(v___y_1028_);
lean_dec(v_a_1011_);
v_a_1047_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1029_);
v___x_1048_ = lean_io_error_to_string(v_a_1047_);
v___x_1049_ = 3;
v___x_1050_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*1, v___x_1049_);
v___x_1051_ = lean_array_get_size(v_a_1023_);
v___x_1052_ = lean_array_push(v_a_1023_, v___x_1050_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
lean_ctor_set(v___x_1025_, 1, v___x_1052_);
lean_ctor_set(v___x_1025_, 0, v___x_1051_);
v___x_1054_ = v___x_1025_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v_a_1068_; 
lean_dec(v_a_1011_);
v_a_1067_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1067_);
v_a_1068_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1021_);
v_a_1003_ = v_a_1067_;
v_a_1004_ = v_a_1068_;
goto v___jp_1002_;
}
}
else
{
lean_object* v_a_1069_; lean_object* v_a_1070_; 
lean_dec(v_a_1011_);
lean_dec_ref(v_file_998_);
v_a_1069_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1069_);
v_a_1070_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1016_);
v_a_1003_ = v_a_1069_;
v_a_1004_ = v_a_1070_;
goto v___jp_1002_;
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_a_1011_);
lean_dec_ref(v_file_998_);
v_a_1071_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1071_);
lean_dec_ref(v___x_1014_);
v___x_1072_ = lean_io_error_to_string(v_a_1071_);
v___x_1073_ = 3;
v___x_1074_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_1073_);
v___x_1075_ = lean_array_get_size(v_a_1000_);
v___x_1076_ = lean_array_push(v_a_1000_, v___x_1074_);
v_a_1003_ = v___x_1075_;
v_a_1004_ = v___x_1076_;
goto v___jp_1002_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_a_1011_);
lean_dec_ref(v_file_998_);
v_a_1077_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1013_);
v___x_1078_ = lean_io_error_to_string(v_a_1077_);
v___x_1079_ = 3;
v___x_1080_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*1, v___x_1079_);
v___x_1081_ = lean_array_get_size(v_a_1000_);
v___x_1082_ = lean_array_push(v_a_1000_, v___x_1080_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
return v___x_1083_;
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1084_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1010_);
v___x_1085_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1086_ = lean_string_append(v_file_998_, v___x_1085_);
v___x_1087_ = lean_io_error_to_string(v_a_1084_);
v___x_1088_ = lean_string_append(v___x_1086_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = 3;
v___x_1090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*1, v___x_1089_);
v___x_1091_ = lean_array_get_size(v_a_1000_);
v___x_1092_ = lean_array_push(v_a_1000_, v___x_1090_);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
return v___x_1093_;
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v_file_998_);
v_a_1094_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1008_);
v___x_1095_ = lean_io_error_to_string(v_a_1094_);
v___x_1096_ = 3;
v___x_1097_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1, v___x_1096_);
v___x_1098_ = lean_array_get_size(v_a_1000_);
v___x_1099_ = lean_array_push(v_a_1000_, v___x_1097_);
v___x_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
return v___x_1100_;
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_file_998_);
v_a_1101_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v___x_1006_);
v___x_1102_ = lean_io_error_to_string(v_a_1101_);
v___x_1103_ = 3;
v___x_1104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*1, v___x_1103_);
v___x_1105_ = lean_array_get_size(v_a_1000_);
v___x_1106_ = lean_array_push(v_a_1000_, v___x_1104_);
v___x_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
return v___x_1107_;
}
v___jp_1002_:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_a_1003_);
lean_ctor_set(v___x_1005_, 1, v_a_1004_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object* v_file_1108_, lean_object* v_cache_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lake_CacheMap_updateFile(v_file_1108_, v_cache_1109_, v_a_1110_);
lean_dec_ref(v_cache_1109_);
return v_res_1112_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__1(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lake_CacheMap_writeFile___closed__0));
v___x_1116_ = l_Lean_Json_compress(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* v_file_1117_, lean_object* v_cache_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc_ref(v_file_1117_);
v___x_1121_ = l_Lake_createParentDirs(v_file_1117_);
if (lean_obj_tag(v___x_1121_) == 0)
{
uint8_t v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v___x_1121_);
v___x_1122_ = 1;
v___x_1123_ = lean_io_prim_handle_mk(v_file_1117_, v___x_1122_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; 
lean_dec_ref(v_file_1117_);
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = 1;
v___x_1126_ = lean_io_prim_handle_lock(v_a_1124_, v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec_ref(v___x_1126_);
v___x_1127_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__1, &l_Lake_CacheMap_writeFile___closed__1_once, _init_l_Lake_CacheMap_writeFile___closed__1);
v___x_1128_ = l_IO_FS_Handle_putStrLn(v_a_1124_, v___x_1127_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_buckets_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v___x_1128_);
v_buckets_1129_ = lean_ctor_get(v_cache_1118_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_cache_1118_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_cache_1118_, 0);
lean_dec(v_unused_1151_);
v___x_1131_ = v_cache_1118_;
v_isShared_1132_ = v_isSharedCheck_1150_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_buckets_1129_);
lean_dec(v_cache_1118_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1150_;
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
lean_dec(v_a_1124_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_a_1119_);
lean_ctor_set(v___x_1131_, 0, v___x_1135_);
v___x_1138_ = v___x_1131_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_a_1119_);
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
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
if (v___x_1140_ == 0)
{
if (v___x_1136_ == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref(v_buckets_1129_);
lean_dec(v_a_1124_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_a_1119_);
lean_ctor_set(v___x_1131_, 0, v___x_1135_);
v___x_1142_ = v___x_1131_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_a_1119_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1131_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1134_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(v_a_1124_, v_buckets_1129_, v___x_1144_, v___x_1145_, v___x_1135_, v_a_1119_);
lean_dec_ref(v_buckets_1129_);
lean_dec(v_a_1124_);
return v___x_1146_;
}
}
else
{
size_t v___x_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
lean_del_object(v___x_1131_);
v___x_1147_ = ((size_t)0ULL);
v___x_1148_ = lean_usize_of_nat(v___x_1134_);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(v_a_1124_, v_buckets_1129_, v___x_1147_, v___x_1148_, v___x_1135_, v_a_1119_);
lean_dec_ref(v_buckets_1129_);
lean_dec(v_a_1124_);
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_cache_1118_);
v_a_1152_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___x_1128_);
v___x_1153_ = lean_io_error_to_string(v_a_1152_);
v___x_1154_ = 3;
v___x_1155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*1, v___x_1154_);
v___x_1156_ = lean_array_get_size(v_a_1119_);
v___x_1157_ = lean_array_push(v_a_1119_, v___x_1155_);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v_a_1124_);
lean_dec_ref(v_cache_1118_);
v_a_1159_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1159_);
lean_dec_ref(v___x_1126_);
v___x_1160_ = lean_io_error_to_string(v_a_1159_);
v___x_1161_ = 3;
v___x_1162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*1, v___x_1161_);
v___x_1163_ = lean_array_get_size(v_a_1119_);
v___x_1164_ = lean_array_push(v_a_1119_, v___x_1162_);
v___x_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
return v___x_1165_;
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref(v_cache_1118_);
v_a_1166_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1123_);
v___x_1167_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1168_ = lean_string_append(v_file_1117_, v___x_1167_);
v___x_1169_ = lean_io_error_to_string(v_a_1166_);
v___x_1170_ = lean_string_append(v___x_1168_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = 3;
v___x_1172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*1, v___x_1171_);
v___x_1173_ = lean_array_get_size(v_a_1119_);
v___x_1174_ = lean_array_push(v_a_1119_, v___x_1172_);
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
return v___x_1175_;
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec_ref(v_cache_1118_);
lean_dec_ref(v_file_1117_);
v_a_1176_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1176_);
lean_dec_ref(v___x_1121_);
v___x_1177_ = lean_io_error_to_string(v_a_1176_);
v___x_1178_ = 3;
v___x_1179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*1, v___x_1178_);
v___x_1180_ = lean_array_get_size(v_a_1119_);
v___x_1181_ = lean_array_push(v_a_1119_, v___x_1179_);
v___x_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object* v_file_1183_, lean_object* v_cache_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lake_CacheMap_writeFile(v_file_1183_, v_cache_1184_, v_a_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t v_a_1188_, lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_box(0);
return v___x_1190_;
}
else
{
lean_object* v_key_1191_; lean_object* v_value_1192_; lean_object* v_tail_1193_; uint64_t v___x_1194_; uint8_t v___x_1195_; 
v_key_1191_ = lean_ctor_get(v_x_1189_, 0);
v_value_1192_ = lean_ctor_get(v_x_1189_, 1);
v_tail_1193_ = lean_ctor_get(v_x_1189_, 2);
v___x_1194_ = lean_unbox_uint64(v_key_1191_);
v___x_1195_ = lean_uint64_dec_eq(v___x_1194_, v_a_1188_);
if (v___x_1195_ == 0)
{
v_x_1189_ = v_tail_1193_;
goto _start;
}
else
{
lean_object* v___x_1197_; 
lean_inc(v_value_1192_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_value_1192_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1198_, lean_object* v_x_1199_){
_start:
{
uint64_t v_a_boxed_1200_; lean_object* v_res_1201_; 
v_a_boxed_1200_ = lean_unbox_uint64(v_a_1198_);
lean_dec_ref(v_a_1198_);
v_res_1201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_boxed_1200_, v_x_1199_);
lean_dec(v_x_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* v_m_1202_, uint64_t v_a_1203_){
_start:
{
lean_object* v_buckets_1204_; lean_object* v___x_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v_fold_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_buckets_1204_ = lean_ctor_get(v_m_1202_, 1);
v___x_1205_ = lean_array_get_size(v_buckets_1204_);
v___x_1206_ = 32ULL;
v___x_1207_ = lean_uint64_shift_right(v_a_1203_, v___x_1206_);
v_fold_1208_ = lean_uint64_xor(v_a_1203_, v___x_1207_);
v___x_1209_ = 16ULL;
v___x_1210_ = lean_uint64_shift_right(v_fold_1208_, v___x_1209_);
v___x_1211_ = lean_uint64_xor(v_fold_1208_, v___x_1210_);
v___x_1212_ = lean_uint64_to_usize(v___x_1211_);
v___x_1213_ = lean_usize_of_nat(v___x_1205_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_sub(v___x_1213_, v___x_1214_);
v___x_1216_ = lean_usize_land(v___x_1212_, v___x_1215_);
v___x_1217_ = lean_array_uget_borrowed(v_buckets_1204_, v___x_1216_);
v___x_1218_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1203_, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* v_m_1219_, lean_object* v_a_1220_){
_start:
{
uint64_t v_a_boxed_1221_; lean_object* v_res_1222_; 
v_a_boxed_1221_ = lean_unbox_uint64(v_a_1220_);
lean_dec_ref(v_a_1220_);
v_res_1222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1219_, v_a_boxed_1221_);
lean_dec_ref(v_m_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t v_inputHash_1223_, lean_object* v_cache_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_cache_1224_, v_inputHash_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* v_inputHash_1226_, lean_object* v_cache_1227_){
_start:
{
uint64_t v_inputHash_boxed_1228_; lean_object* v_res_1229_; 
v_inputHash_boxed_1228_ = lean_unbox_uint64(v_inputHash_1226_);
lean_dec_ref(v_inputHash_1226_);
v_res_1229_ = l_Lake_CacheMap_get_x3f(v_inputHash_boxed_1228_, v_cache_1227_);
lean_dec_ref(v_cache_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object* v_00_u03b2_1230_, lean_object* v_m_1231_, uint64_t v_a_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1231_, v_a_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* v_00_u03b2_1234_, lean_object* v_m_1235_, lean_object* v_a_1236_){
_start:
{
uint64_t v_a_boxed_1237_; lean_object* v_res_1238_; 
v_a_boxed_1237_ = lean_unbox_uint64(v_a_1236_);
lean_dec_ref(v_a_1236_);
v_res_1238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(v_00_u03b2_1234_, v_m_1235_, v_a_boxed_1237_);
lean_dec_ref(v_m_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1239_, uint64_t v_a_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1240_, v_x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1243_, lean_object* v_a_1244_, lean_object* v_x_1245_){
_start:
{
uint64_t v_a_boxed_1246_; lean_object* v_res_1247_; 
v_a_boxed_1246_ = lean_unbox_uint64(v_a_1244_);
lean_dec_ref(v_a_1244_);
v_res_1247_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(v_00_u03b2_1243_, v_a_boxed_1246_, v_x_1245_);
lean_dec(v_x_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t v_inputHash_1248_, lean_object* v_val_1249_, lean_object* v_cache_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_cache_1250_, v_inputHash_1248_, v_val_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object* v_inputHash_1252_, lean_object* v_val_1253_, lean_object* v_cache_1254_){
_start:
{
uint64_t v_inputHash_boxed_1255_; lean_object* v_res_1256_; 
v_inputHash_boxed_1255_ = lean_unbox_uint64(v_inputHash_1252_);
lean_dec_ref(v_inputHash_1252_);
v_res_1256_ = l_Lake_CacheMap_insertCore(v_inputHash_boxed_1255_, v_val_1253_, v_cache_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* v_inst_1257_, uint64_t v_inputHash_1258_, lean_object* v_val_1259_, lean_object* v_cache_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_apply_1(v_inst_1257_, v_val_1259_);
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_cache_1260_, v_inputHash_1258_, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* v_inst_1263_, lean_object* v_inputHash_1264_, lean_object* v_val_1265_, lean_object* v_cache_1266_){
_start:
{
uint64_t v_inputHash_boxed_1267_; lean_object* v_res_1268_; 
v_inputHash_boxed_1267_ = lean_unbox_uint64(v_inputHash_1264_);
lean_dec_ref(v_inputHash_1264_);
v_res_1268_ = l_Lake_CacheMap_insert___redArg(v_inst_1263_, v_inputHash_boxed_1267_, v_val_1265_, v_cache_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* v_00_u03b1_1269_, lean_object* v_inst_1270_, uint64_t v_inputHash_1271_, lean_object* v_val_1272_, lean_object* v_cache_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_apply_1(v_inst_1270_, v_val_1272_);
v___x_1275_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v_cache_1273_, v_inputHash_1271_, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_inst_1277_, lean_object* v_inputHash_1278_, lean_object* v_val_1279_, lean_object* v_cache_1280_){
_start:
{
uint64_t v_inputHash_boxed_1281_; lean_object* v_res_1282_; 
v_inputHash_boxed_1281_ = lean_unbox_uint64(v_inputHash_1278_);
lean_dec_ref(v_inputHash_1278_);
v_res_1282_ = l_Lake_CacheMap_insert(v_00_u03b1_1276_, v_inst_1277_, v_inputHash_boxed_1281_, v_val_1279_, v_cache_1280_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* v_init_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
lean_object* v_v_1290_; lean_object* v_l_1291_; lean_object* v_r_1292_; lean_object* v___x_1293_; 
v_v_1290_ = lean_ctor_get(v_x_1287_, 2);
lean_inc(v_v_1290_);
v_l_1291_ = lean_ctor_get(v_x_1287_, 3);
lean_inc(v_l_1291_);
v_r_1292_ = lean_ctor_get(v_x_1287_, 4);
lean_inc(v_r_1292_);
lean_dec_ref(v_x_1287_);
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1286_, v_l_1291_, v___y_1288_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_a_1295_; lean_object* v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
v_a_1295_ = lean_ctor_get(v___x_1293_, 1);
lean_inc(v_a_1295_);
lean_dec_ref(v___x_1293_);
v___x_1296_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1294_, v_v_1290_, v_a_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_a_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v_a_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1296_);
v_init_1286_ = v_a_1297_;
v_x_1287_ = v_r_1292_;
v___y_1288_ = v_a_1298_;
goto _start;
}
else
{
lean_dec(v_r_1292_);
return v___x_1296_;
}
}
else
{
lean_dec(v_r_1292_);
lean_dec(v_v_1290_);
return v___x_1293_;
}
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_init_1286_);
lean_ctor_set(v___x_1300_, 1, v___y_1288_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* v_as_1301_, lean_object* v_o_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___y_1306_; 
switch(lean_obj_tag(v_o_1302_))
{
case 0:
{
v___y_1306_ = v_a_1303_;
goto v___jp_1305_;
}
case 1:
{
lean_object* v___x_1308_; 
lean_dec_ref(v_o_1302_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_as_1301_);
lean_ctor_set(v___x_1308_, 1, v_a_1303_);
return v___x_1308_;
}
case 2:
{
lean_object* v_n_1309_; lean_object* v___x_1310_; 
v_n_1309_ = lean_ctor_get(v_o_1302_, 0);
lean_inc_ref(v_n_1309_);
lean_dec_ref(v_o_1302_);
v___x_1310_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
v___x_1313_ = lean_string_append(v___x_1312_, v_a_1311_);
lean_dec(v_a_1311_);
v___x_1314_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1));
v___x_1315_ = lean_string_append(v___x_1313_, v___x_1314_);
v___x_1316_ = l_Lean_JsonNumber_toString(v_n_1309_);
v___x_1317_ = lean_string_append(v___x_1315_, v___x_1316_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = 3;
v___x_1319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*1, v___x_1318_);
v___x_1320_ = lean_array_push(v_a_1303_, v___x_1319_);
v___y_1306_ = v___x_1320_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint64_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref(v_n_1309_);
v_a_1321_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1310_);
v___x_1322_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1));
v___x_1323_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_unbox_uint64(v_a_1321_);
lean_dec(v_a_1321_);
lean_ctor_set_uint64(v___x_1323_, sizeof(void*)*1, v___x_1324_);
v___x_1325_ = lean_array_push(v_as_1301_, v___x_1323_);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_a_1303_);
return v___x_1326_;
}
}
case 3:
{
lean_object* v_s_1327_; lean_object* v___x_1328_; 
v_s_1327_ = lean_ctor_get(v_o_1302_, 0);
lean_inc_ref(v_s_1327_);
lean_dec_ref(v_o_1302_);
v___x_1328_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2));
v___x_1331_ = lean_string_append(v___x_1330_, v_a_1329_);
lean_dec(v_a_1329_);
v___x_1332_ = 3;
v___x_1333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
v___x_1334_ = lean_array_push(v_a_1303_, v___x_1333_);
v___y_1306_ = v___x_1334_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_a_1335_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v___x_1328_);
v___x_1336_ = lean_array_push(v_as_1301_, v_a_1335_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v_a_1303_);
return v___x_1337_;
}
}
case 4:
{
lean_object* v_elems_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_elems_1338_ = lean_ctor_get(v_o_1302_, 0);
lean_inc_ref(v_elems_1338_);
lean_dec_ref(v_o_1302_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_array_get_size(v_elems_1338_);
v___x_1341_ = lean_nat_dec_lt(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v_elems_1338_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v_as_1301_);
lean_ctor_set(v___x_1342_, 1, v_a_1303_);
return v___x_1342_;
}
else
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
if (v___x_1343_ == 0)
{
if (v___x_1341_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v_elems_1338_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_as_1301_);
lean_ctor_set(v___x_1344_, 1, v_a_1303_);
return v___x_1344_;
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_of_nat(v___x_1340_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1338_, v___x_1345_, v___x_1346_, v_as_1301_, v_a_1303_);
lean_dec_ref(v_elems_1338_);
return v___x_1347_;
}
}
else
{
size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1340_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1338_, v___x_1348_, v___x_1349_, v_as_1301_, v_a_1303_);
lean_dec_ref(v_elems_1338_);
return v___x_1350_;
}
}
}
default: 
{
lean_object* v_kvPairs_1351_; lean_object* v___x_1352_; 
v_kvPairs_1351_ = lean_ctor_get(v_o_1302_, 0);
lean_inc(v_kvPairs_1351_);
lean_dec_ref(v_o_1302_);
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_as_1301_, v_kvPairs_1351_, v_a_1303_);
return v___x_1352_;
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_as_1301_);
lean_ctor_set(v___x_1307_, 1, v___y_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* v_as_1353_, size_t v_i_1354_, size_t v_stop_1355_, lean_object* v_b_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_usize_dec_eq(v_i_1354_, v_stop_1355_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_array_uget_borrowed(v_as_1353_, v_i_1354_);
lean_inc(v___x_1360_);
v___x_1361_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_b_1356_, v___x_1360_, v___y_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v_a_1363_; size_t v___x_1364_; size_t v___x_1365_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
v_a_1363_ = lean_ctor_get(v___x_1361_, 1);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1361_);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_add(v_i_1354_, v___x_1364_);
v_i_1354_ = v___x_1365_;
v_b_1356_ = v_a_1362_;
v___y_1357_ = v_a_1363_;
goto _start;
}
else
{
return v___x_1361_;
}
}
else
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_b_1356_);
lean_ctor_set(v___x_1367_, 1, v___y_1357_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* v_as_1368_, lean_object* v_i_1369_, lean_object* v_stop_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
size_t v_i_boxed_1374_; size_t v_stop_boxed_1375_; lean_object* v_res_1376_; 
v_i_boxed_1374_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_stop_boxed_1375_ = lean_unbox_usize(v_stop_1370_);
lean_dec(v_stop_1370_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_as_1368_, v_i_boxed_1374_, v_stop_boxed_1375_, v_b_1371_, v___y_1372_);
lean_dec_ref(v_as_1368_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* v_init_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1377_, v_x_1378_, v___y_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* v_as_1382_, lean_object* v_o_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_as_1382_, v_o_1383_, v_a_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v___y_1389_){
_start:
{
if (lean_obj_tag(v_x_1388_) == 0)
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_x_1387_);
lean_ctor_set(v___x_1391_, 1, v___y_1389_);
return v___x_1391_;
}
else
{
lean_object* v_value_1392_; lean_object* v_tail_1393_; lean_object* v___x_1394_; 
v_value_1392_ = lean_ctor_get(v_x_1388_, 1);
lean_inc(v_value_1392_);
v_tail_1393_ = lean_ctor_get(v_x_1388_, 2);
lean_inc(v_tail_1393_);
lean_dec_ref(v_x_1388_);
v___x_1394_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_x_1387_, v_value_1392_, v___y_1389_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_a_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
v_a_1396_ = lean_ctor_get(v___x_1394_, 1);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1394_);
v_x_1387_ = v_a_1395_;
v_x_1388_ = v_tail_1393_;
v___y_1389_ = v_a_1396_;
goto _start;
}
else
{
lean_dec(v_tail_1393_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_x_1398_, v_x_1399_, v___y_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* v_as_1403_, size_t v_i_1404_, size_t v_stop_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_eq(v_i_1404_, v_stop_1405_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_array_uget_borrowed(v_as_1403_, v_i_1404_);
lean_inc(v___x_1410_);
v___x_1411_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_b_1406_, v___x_1410_, v___y_1407_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v_a_1413_; size_t v___x_1414_; size_t v___x_1415_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
v_a_1413_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1411_);
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_add(v_i_1404_, v___x_1414_);
v_i_1404_ = v___x_1415_;
v_b_1406_ = v_a_1412_;
v___y_1407_ = v_a_1413_;
goto _start;
}
else
{
return v___x_1411_;
}
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_b_1406_);
lean_ctor_set(v___x_1417_, 1, v___y_1407_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* v_as_1418_, lean_object* v_i_1419_, lean_object* v_stop_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
size_t v_i_boxed_1424_; size_t v_stop_boxed_1425_; lean_object* v_res_1426_; 
v_i_boxed_1424_ = lean_unbox_usize(v_i_1419_);
lean_dec(v_i_1419_);
v_stop_boxed_1425_ = lean_unbox_usize(v_stop_1420_);
lean_dec(v_stop_1420_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_as_1418_, v_i_boxed_1424_, v_stop_boxed_1425_, v_b_1421_, v___y_1422_);
lean_dec_ref(v_as_1418_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* v_map_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_buckets_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1461_; 
v_buckets_1432_ = lean_ctor_get(v_map_1429_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_map_1429_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_map_1429_, 0);
lean_dec(v_unused_1462_);
v___x_1434_ = v_map_1429_;
v_isShared_1435_ = v_isSharedCheck_1461_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_buckets_1432_);
lean_dec(v_map_1429_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1461_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___y_1440_; lean_object* v_a_1441_; lean_object* v___y_1448_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = ((lean_object*)(l_Lake_CacheMap_collectOutputDescrs___closed__0));
v___x_1438_ = lean_array_get_size(v_a_1430_);
v___x_1450_ = lean_array_get_size(v_buckets_1432_);
v___x_1451_ = lean_nat_dec_lt(v___x_1436_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
lean_dec_ref(v_buckets_1432_);
lean_inc_ref(v_a_1430_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1437_);
lean_ctor_set(v___x_1452_, 1, v_a_1430_);
v___y_1440_ = v___x_1452_;
v_a_1441_ = v_a_1430_;
goto v___jp_1439_;
}
else
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_nat_dec_le(v___x_1450_, v___x_1450_);
if (v___x_1453_ == 0)
{
if (v___x_1451_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref(v_buckets_1432_);
lean_inc_ref(v_a_1430_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1437_);
lean_ctor_set(v___x_1454_, 1, v_a_1430_);
v___y_1440_ = v___x_1454_;
v_a_1441_ = v_a_1430_;
goto v___jp_1439_;
}
else
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = lean_usize_of_nat(v___x_1450_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1432_, v___x_1455_, v___x_1456_, v___x_1437_, v_a_1430_);
lean_dec_ref(v_buckets_1432_);
v___y_1448_ = v___x_1457_;
goto v___jp_1447_;
}
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1450_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1432_, v___x_1458_, v___x_1459_, v___x_1437_, v_a_1430_);
lean_dec_ref(v_buckets_1432_);
v___y_1448_ = v___x_1460_;
goto v___jp_1447_;
}
}
v___jp_1439_:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = lean_array_get_size(v_a_1441_);
v___x_1443_ = lean_nat_dec_eq(v___x_1438_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref(v___y_1440_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 1);
lean_ctor_set(v___x_1434_, 1, v_a_1441_);
lean_ctor_set(v___x_1434_, 0, v___x_1438_);
v___x_1445_ = v___x_1434_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1441_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_dec_ref(v_a_1441_);
lean_del_object(v___x_1434_);
return v___y_1440_;
}
}
v___jp_1447_:
{
if (lean_obj_tag(v___y_1448_) == 0)
{
lean_object* v_a_1449_; 
v_a_1449_ = lean_ctor_get(v___y_1448_, 1);
lean_inc(v_a_1449_);
v___y_1440_ = v___y_1448_;
v_a_1441_ = v_a_1449_;
goto v___jp_1439_;
}
else
{
lean_del_object(v___x_1434_);
return v___y_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* v_map_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lake_CacheMap_collectOutputDescrs(v_map_1463_, v_a_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* v_init_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_st_mk_ref(v_init_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* v_init_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lake_CacheRef_mk(v_init_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t v_inputHash_1473_, lean_object* v_cache_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_st_ref_take(v_cache_1474_);
v___x_1477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v___x_1476_, v_inputHash_1473_);
v___x_1478_ = lean_st_ref_set(v_cache_1474_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* v_inputHash_1479_, lean_object* v_cache_1480_, lean_object* v_a_1481_){
_start:
{
uint64_t v_inputHash_boxed_1482_; lean_object* v_res_1483_; 
v_inputHash_boxed_1482_ = lean_unbox_uint64(v_inputHash_1479_);
lean_dec_ref(v_inputHash_1479_);
v_res_1483_ = l_Lake_CacheRef_get_x3f(v_inputHash_boxed_1482_, v_cache_1480_);
lean_dec(v_cache_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* v_inst_1484_, uint64_t v_inputHash_1485_, lean_object* v_val_1486_, lean_object* v_cache_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_st_ref_take(v_cache_1487_);
v___x_1490_ = lean_apply_1(v_inst_1484_, v_val_1486_);
v___x_1491_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_1489_, v_inputHash_1485_, v___x_1490_);
v___x_1492_ = lean_st_ref_set(v_cache_1487_, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* v_inst_1493_, lean_object* v_inputHash_1494_, lean_object* v_val_1495_, lean_object* v_cache_1496_, lean_object* v_a_1497_){
_start:
{
uint64_t v_inputHash_boxed_1498_; lean_object* v_res_1499_; 
v_inputHash_boxed_1498_ = lean_unbox_uint64(v_inputHash_1494_);
lean_dec_ref(v_inputHash_1494_);
v_res_1499_ = l_Lake_CacheRef_insert___redArg(v_inst_1493_, v_inputHash_boxed_1498_, v_val_1495_, v_cache_1496_);
lean_dec(v_cache_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* v_00_u03b1_1500_, lean_object* v_inst_1501_, uint64_t v_inputHash_1502_, lean_object* v_val_1503_, lean_object* v_cache_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = lean_st_ref_take(v_cache_1504_);
v___x_1507_ = lean_apply_1(v_inst_1501_, v_val_1503_);
v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_1506_, v_inputHash_1502_, v___x_1507_);
v___x_1509_ = lean_st_ref_set(v_cache_1504_, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_inst_1511_, lean_object* v_inputHash_1512_, lean_object* v_val_1513_, lean_object* v_cache_1514_, lean_object* v_a_1515_){
_start:
{
uint64_t v_inputHash_boxed_1516_; lean_object* v_res_1517_; 
v_inputHash_boxed_1516_ = lean_unbox_uint64(v_inputHash_1512_);
lean_dec_ref(v_inputHash_1512_);
v_res_1517_ = l_Lake_CacheRef_insert(v_00_u03b1_1510_, v_inst_1511_, v_inputHash_boxed_1516_, v_val_1513_, v_cache_1514_);
lean_dec(v_cache_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object* v_s_1520_){
_start:
{
lean_inc_ref(v_s_1520_);
return v_s_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object* v_s_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lake_CacheServiceName_ofString(v_s_1521_);
lean_dec_ref(v_s_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object* v_self_1523_){
_start:
{
lean_inc_ref(v_self_1523_);
return v_self_1523_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object* v_self_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lake_CacheServiceName_toString(v_self_1524_);
lean_dec_ref(v_self_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object* v_j_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Json_getStr_x3f(v_j_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1538_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1529_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1529_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object* v_self_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_self_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object* v_x_1552_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_unsigned_to_nat(1u);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object* v_x_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(v_x_1555_);
lean_dec_ref(v_x_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object* v_t_1557_, lean_object* v_k_1558_){
_start:
{
lean_object* v_s_1559_; lean_object* v___x_1560_; 
v_s_1559_ = lean_ctor_get(v_t_1557_, 0);
lean_inc_ref(v_s_1559_);
lean_dec_ref(v_t_1557_);
v___x_1560_ = lean_apply_1(v_k_1558_, v_s_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object* v_motive_1561_, lean_object* v_ctorIdx_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1563_, v_k_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object* v_motive_1567_, lean_object* v_ctorIdx_1568_, lean_object* v_t_1569_, lean_object* v_h_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(v_motive_1567_, v_ctorIdx_1568_, v_t_1569_, v_h_1570_, v_k_1571_);
lean_dec(v_ctorIdx_1568_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object* v_t_1573_, lean_object* v_str_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1573_, v_str_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object* v_motive_1576_, lean_object* v_t_1577_, lean_object* v_h_1578_, lean_object* v_str_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1577_, v_str_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object* v_t_1581_, lean_object* v_repo_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1581_, v_repo_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object* v_motive_1584_, lean_object* v_t_1585_, lean_object* v_h_1586_, lean_object* v_repo_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1585_, v_repo_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object* v_s_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_s_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object* v_fullName_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_fullName_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object* v_self_1593_){
_start:
{
if (lean_obj_tag(v_self_1593_) == 1)
{
uint8_t v___x_1594_; 
v___x_1594_ = 1;
return v___x_1594_;
}
else
{
uint8_t v___x_1595_; 
v___x_1595_ = 0;
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object* v_self_1596_){
_start:
{
uint8_t v_res_1597_; lean_object* v_r_1598_; 
v_res_1597_ = l_Lake_CacheServiceScope_isRepo(v_self_1596_);
lean_dec_ref(v_self_1596_);
v_r_1598_ = lean_box(v_res_1597_);
return v_r_1598_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object* v_self_1599_){
_start:
{
lean_object* v_s_1600_; 
v_s_1600_ = lean_ctor_get(v_self_1599_, 0);
lean_inc_ref(v_s_1600_);
return v_s_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object* v_self_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lake_CacheServiceScope_toString(v_self_1601_);
lean_dec_ref(v_self_1601_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object* v_self_1605_){
_start:
{
lean_object* v_s_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_s_1606_ = lean_ctor_get(v_self_1605_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_self_1605_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v_self_1605_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_s_1606_);
lean_dec(v_self_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 3);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_s_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object* v_data_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1625_, 0, v_data_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1626_){
_start:
{
if (lean_obj_tag(v_x_1626_) == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_box(0);
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_val_1628_ = lean_ctor_get(v_x_1626_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1626_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v_x_1626_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v_x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 3);
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_val_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
static lean_object* _init_l_Lake_CacheOutput_toJson___closed__3(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__2));
v___x_1641_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1642_ = lean_box(1);
v___x_1643_ = l_Lake_JsonObject_insertJson(v___x_1642_, v___x_1641_, v___x_1640_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object* v_out_1647_){
_start:
{
lean_object* v_data_1648_; lean_object* v_service_x3f_1649_; lean_object* v_scope_x3f_1650_; lean_object* v_obj_1652_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_obj_1659_; 
v_data_1648_ = lean_ctor_get(v_out_1647_, 0);
lean_inc(v_data_1648_);
v_service_x3f_1649_ = lean_ctor_get(v_out_1647_, 1);
lean_inc(v_service_x3f_1649_);
v_scope_x3f_1650_ = lean_ctor_get(v_out_1647_, 2);
lean_inc(v_scope_x3f_1650_);
lean_dec_ref(v_out_1647_);
v___x_1656_ = lean_obj_once(&l_Lake_CacheOutput_toJson___closed__3, &l_Lake_CacheOutput_toJson___closed__3_once, _init_l_Lake_CacheOutput_toJson___closed__3);
v___x_1657_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1658_ = l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1649_);
v_obj_1659_ = l_Lake_JsonObject_insertJson(v___x_1656_, v___x_1657_, v___x_1658_);
if (lean_obj_tag(v_scope_x3f_1650_) == 1)
{
lean_object* v_val_1660_; lean_object* v___y_1662_; uint8_t v___x_1665_; 
v_val_1660_ = lean_ctor_get(v_scope_x3f_1650_, 0);
lean_inc(v_val_1660_);
lean_dec_ref(v_scope_x3f_1650_);
v___x_1665_ = l_Lake_CacheServiceScope_isRepo(v_val_1660_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___y_1662_ = v___x_1666_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___y_1662_ = v___x_1667_;
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___x_1663_; lean_object* v_obj_1664_; 
v___x_1663_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(v_val_1660_);
v_obj_1664_ = l_Lake_JsonObject_insertJson(v_obj_1659_, v___y_1662_, v___x_1663_);
v_obj_1652_ = v_obj_1664_;
goto v___jp_1651_;
}
}
else
{
lean_dec(v_scope_x3f_1650_);
v_obj_1652_ = v_obj_1659_;
goto v___jp_1651_;
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1654_ = l_Lake_JsonObject_insertJson(v_obj_1652_, v___x_1653_, v_data_1648_);
v___x_1655_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1672_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Json_getStr_x3f(v_x_1672_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1691_; 
v_a_1683_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1685_ = v___x_1674_;
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1674_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1683_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1687_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1692_) == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Json_getStr_x3f(v_x_1692_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1711_; 
v_a_1703_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1705_ = v___x_1694_;
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1694_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1703_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1707_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object* v_k_1712_, lean_object* v_t_1713_){
_start:
{
if (lean_obj_tag(v_t_1713_) == 0)
{
lean_object* v_k_1714_; lean_object* v_l_1715_; lean_object* v_r_1716_; uint8_t v___x_1717_; 
v_k_1714_ = lean_ctor_get(v_t_1713_, 1);
v_l_1715_ = lean_ctor_get(v_t_1713_, 3);
v_r_1716_ = lean_ctor_get(v_t_1713_, 4);
v___x_1717_ = lean_string_dec_lt(v_k_1712_, v_k_1714_);
if (v___x_1717_ == 0)
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_string_dec_eq(v_k_1712_, v_k_1714_);
if (v___x_1718_ == 0)
{
v_t_1713_ = v_r_1716_;
goto _start;
}
else
{
return v___x_1718_;
}
}
else
{
v_t_1713_ = v_l_1715_;
goto _start;
}
}
else
{
uint8_t v___x_1721_; 
v___x_1721_ = 0;
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object* v_k_1722_, lean_object* v_t_1723_){
_start:
{
uint8_t v_res_1724_; lean_object* v_r_1725_; 
v_res_1724_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1722_, v_t_1723_);
lean_dec(v_t_1723_);
lean_dec_ref(v_k_1722_);
v_r_1725_ = lean_box(v_res_1724_);
return v_r_1725_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object* v_json_1732_){
_start:
{
if (lean_obj_tag(v_json_1732_) == 5)
{
lean_object* v_kvPairs_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_kvPairs_1737_ = lean_ctor_get(v_json_1732_, 0);
v___x_1738_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1739_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v___x_1738_, v_kvPairs_1737_);
if (v___x_1739_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_inc(v_kvPairs_1737_);
lean_dec_ref(v_json_1732_);
v___x_1740_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1741_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1737_, v___x_1740_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1742_; 
lean_dec(v_kvPairs_1737_);
v___x_1742_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__1));
return v___x_1742_;
}
else
{
lean_object* v_val_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1861_; 
v_val_1743_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1745_ = v___x_1741_;
v_isShared_1746_ = v_isSharedCheck_1861_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_val_1743_);
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1861_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___y_1748_; lean_object* v_a_1749_; lean_object* v___y_1755_; lean_object* v___y_1758_; lean_object* v_a_1798_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1838_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1737_, v___x_1837_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_box(0);
v_a_1798_ = v___x_1839_;
goto v___jp_1797_;
}
else
{
lean_object* v_val_1840_; lean_object* v___x_1841_; 
v_val_1840_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_val_1840_);
lean_dec_ref(v___x_1838_);
v___x_1841_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
lean_del_object(v___x_1745_);
lean_dec(v_val_1743_);
lean_dec(v_kvPairs_1737_);
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__4));
v___x_1847_ = lean_string_append(v___x_1846_, v_a_1842_);
lean_dec(v_a_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1847_);
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_del_object(v___x_1745_);
lean_dec(v_val_1743_);
lean_dec(v_kvPairs_1737_);
v_a_1852_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1841_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1841_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set_tag(v___x_1854_, 0);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1860_; 
v_a_1860_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1841_);
v_a_1798_ = v_a_1860_;
goto v___jp_1797_;
}
}
}
v___jp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1750_, 0, v_val_1743_);
lean_ctor_set(v___x_1750_, 1, v___y_1748_);
lean_ctor_set(v___x_1750_, 2, v_a_1749_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1750_);
v___x_1752_ = v___x_1745_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
v___jp_1754_:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_box(0);
v___y_1748_ = v___y_1755_;
v_a_1749_ = v___x_1756_;
goto v___jp_1747_;
}
v___jp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___x_1760_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1737_, v___x_1759_);
lean_dec(v_kvPairs_1737_);
if (lean_obj_tag(v___x_1760_) == 0)
{
v___y_1755_ = v___y_1758_;
goto v___jp_1754_;
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1796_; 
v_val_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1796_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_val_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1796_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1761_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1775_; 
lean_del_object(v___x_1763_);
lean_dec(v___y_1758_);
lean_del_object(v___x_1745_);
lean_dec(v_val_1743_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1775_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1775_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1770_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__2));
v___x_1771_ = lean_string_append(v___x_1770_, v_a_1766_);
lean_dec(v_a_1766_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1771_);
v___x_1773_ = v___x_1768_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_del_object(v___x_1763_);
lean_dec(v___y_1758_);
lean_del_object(v___x_1745_);
lean_dec(v_val_1743_);
v_a_1776_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1765_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1765_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 0);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1765_);
if (lean_obj_tag(v_a_1784_) == 1)
{
lean_object* v_val_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_val_1785_ = lean_ctor_get(v_a_1784_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1784_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1787_ = v_a_1784_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_val_1785_);
lean_dec(v_a_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 0);
lean_ctor_set(v___x_1763_, 0, v_val_1785_);
v___x_1790_ = v___x_1763_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_val_1785_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v___y_1748_ = v___y_1758_;
v_a_1749_ = v___x_1792_;
goto v___jp_1747_;
}
}
}
}
else
{
lean_dec(v_a_1784_);
lean_del_object(v___x_1763_);
v___y_1755_ = v___y_1758_;
goto v___jp_1754_;
}
}
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___x_1800_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1737_, v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
v___y_1758_ = v_a_1798_;
goto v___jp_1757_;
}
else
{
lean_object* v_val_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1836_; 
v_val_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1836_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_val_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1836_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1801_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1815_; 
lean_del_object(v___x_1803_);
lean_dec(v_a_1798_);
lean_del_object(v___x_1745_);
lean_dec(v_val_1743_);
lean_dec(v_kvPairs_1737_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1815_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1815_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1810_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__3));
v___x_1811_ = lean_string_append(v___x_1810_, v_a_1806_);
lean_dec(v_a_1806_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1811_);
v___x_1813_ = v___x_1808_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_del_object(v___x_1803_);
lean_dec(v_a_1798_);
lean_del_object(v___x_1745_);
lean_dec(v_val_1743_);
lean_dec(v_kvPairs_1737_);
v_a_1816_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1805_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1805_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 0);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; 
v_a_1824_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1805_);
if (lean_obj_tag(v_a_1824_) == 1)
{
lean_object* v_val_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_kvPairs_1737_);
v_val_1825_ = lean_ctor_get(v_a_1824_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1824_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1827_ = v_a_1824_;
v_isShared_1828_ = v_isSharedCheck_1835_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_val_1825_);
lean_dec(v_a_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1835_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_val_1825_);
v___x_1830_ = v___x_1803_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_val_1825_);
v___x_1830_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1830_);
v___x_1832_ = v___x_1827_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
v___y_1748_ = v_a_1798_;
v_a_1749_ = v___x_1832_;
goto v___jp_1747_;
}
}
}
}
else
{
lean_dec(v_a_1824_);
lean_del_object(v___x_1803_);
v___y_1758_ = v_a_1798_;
goto v___jp_1757_;
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
goto v___jp_1733_;
}
v___jp_1733_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1735_, 0, v_json_1732_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
lean_ctor_set(v___x_1735_, 2, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object* v_00_u03b2_1862_, lean_object* v_k_1863_, lean_object* v_t_1864_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1863_, v_t_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object* v_00_u03b2_1866_, lean_object* v_k_1867_, lean_object* v_t_1868_){
_start:
{
uint8_t v_res_1869_; lean_object* v_r_1870_; 
v_res_1869_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(v_00_u03b2_1866_, v_k_1867_, v_t_1868_);
lean_dec(v_t_1868_);
lean_dec_ref(v_k_1867_);
v_r_1870_ = lean_box(v_res_1869_);
return v_r_1870_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache_default(void){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_System_instInhabitedFilePath_default;
return v___x_1873_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache(void){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_System_instInhabitedFilePath_default;
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1878_ = l_System_FilePath_join(v_cache_1876_, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_1880_, uint64_t v_contentHash_1881_, lean_object* v_ext_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1883_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1884_ = l_System_FilePath_join(v_cache_1880_, v___x_1883_);
v___x_1885_ = lean_string_utf8_byte_size(v_ext_1882_);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_nat_dec_eq(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1888_ = l_Lake_Hash_hex(v_contentHash_1881_);
v___x_1889_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_1890_ = lean_string_append(v___x_1888_, v___x_1889_);
v___x_1891_ = lean_string_append(v___x_1890_, v_ext_1882_);
v___x_1892_ = l_System_FilePath_join(v___x_1884_, v___x_1891_);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = l_Lake_Hash_hex(v_contentHash_1881_);
v___x_1894_ = l_System_FilePath_join(v___x_1884_, v___x_1893_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_1895_, lean_object* v_contentHash_1896_, lean_object* v_ext_1897_){
_start:
{
uint64_t v_contentHash_boxed_1898_; lean_object* v_res_1899_; 
v_contentHash_boxed_1898_ = lean_unbox_uint64(v_contentHash_1896_);
lean_dec_ref(v_contentHash_1896_);
v_res_1899_ = l_Lake_Cache_artifactPath(v_cache_1895_, v_contentHash_boxed_1898_, v_ext_1897_);
lean_dec_ref(v_ext_1897_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_1900_, lean_object* v_descr_1901_){
_start:
{
uint64_t v_hash_1903_; lean_object* v_ext_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___y_1908_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_hash_1903_ = lean_ctor_get_uint64(v_descr_1901_, sizeof(void*)*1);
v_ext_1904_ = lean_ctor_get(v_descr_1901_, 0);
v___x_1905_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1906_ = l_System_FilePath_join(v_cache_1900_, v___x_1905_);
v___x_1922_ = lean_string_utf8_byte_size(v_ext_1904_);
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_nat_dec_eq(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1925_ = l_Lake_Hash_hex(v_hash_1903_);
v___x_1926_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_1927_ = lean_string_append(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_string_append(v___x_1927_, v_ext_1904_);
v___y_1908_ = v___x_1928_;
goto v___jp_1907_;
}
else
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lake_Hash_hex(v_hash_1903_);
v___y_1908_ = v___x_1929_;
goto v___jp_1907_;
}
v___jp_1907_:
{
lean_object* v_path_1909_; lean_object* v___x_1910_; 
v_path_1909_ = l_System_FilePath_join(v___x_1906_, v___y_1908_);
v___x_1910_ = lean_io_metadata(v_path_1909_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1920_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1920_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1920_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_modified_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v_modified_1915_ = lean_ctor_get(v_a_1911_, 1);
lean_inc_ref(v_modified_1915_);
lean_dec(v_a_1911_);
lean_inc_ref(v_path_1909_);
v___x_1916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1916_, 0, v_descr_1901_);
lean_ctor_set(v___x_1916_, 1, v_path_1909_);
lean_ctor_set(v___x_1916_, 2, v_path_1909_);
lean_ctor_set(v___x_1916_, 3, v_modified_1915_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
lean_ctor_set(v___x_1913_, 0, v___x_1916_);
v___x_1918_ = v___x_1913_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v___x_1921_; 
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_path_1909_);
lean_dec_ref(v_descr_1901_);
v___x_1921_ = lean_box(0);
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_1930_, lean_object* v_descr_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lake_Cache_getArtifact_x3f(v_cache_1930_, v_descr_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_1936_, lean_object* v_descr_1937_){
_start:
{
uint64_t v_hash_1939_; lean_object* v_ext_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___y_1944_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_hash_1939_ = lean_ctor_get_uint64(v_descr_1937_, sizeof(void*)*1);
v_ext_1940_ = lean_ctor_get(v_descr_1937_, 0);
v___x_1941_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1942_ = l_System_FilePath_join(v_cache_1936_, v___x_1941_);
v___x_1973_ = lean_string_utf8_byte_size(v_ext_1940_);
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_nat_dec_eq(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1976_ = l_Lake_Hash_hex(v_hash_1939_);
v___x_1977_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_1978_ = lean_string_append(v___x_1976_, v___x_1977_);
v___x_1979_ = lean_string_append(v___x_1978_, v_ext_1940_);
v___y_1944_ = v___x_1979_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lake_Hash_hex(v_hash_1939_);
v___y_1944_ = v___x_1980_;
goto v___jp_1943_;
}
v___jp_1943_:
{
lean_object* v_path_1945_; lean_object* v___x_1946_; 
v_path_1945_ = l_System_FilePath_join(v___x_1942_, v___y_1944_);
v___x_1946_ = lean_io_metadata(v_path_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1956_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1956_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1956_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_modified_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_modified_1951_ = lean_ctor_get(v_a_1947_, 1);
lean_inc_ref(v_modified_1951_);
lean_dec(v_a_1947_);
lean_inc_ref(v_path_1945_);
v___x_1952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1952_, 0, v_descr_1937_);
lean_ctor_set(v___x_1952_, 1, v_path_1945_);
lean_ctor_set(v___x_1952_, 2, v_path_1945_);
lean_ctor_set(v___x_1952_, 3, v_modified_1951_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_descr_1937_);
v_a_1957_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1959_ = v___x_1946_;
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1946_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
if (lean_obj_tag(v_a_1957_) == 11)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec_ref(v_a_1957_);
v___x_1961_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_1962_ = lean_string_append(v___x_1961_, v_path_1945_);
lean_dec_ref(v_path_1945_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1962_);
v___x_1964_ = v___x_1959_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
lean_dec_ref(v_path_1945_);
v___x_1966_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_1967_ = lean_io_error_to_string(v_a_1957_);
v___x_1968_ = lean_string_append(v___x_1966_, v___x_1967_);
lean_dec_ref(v___x_1967_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1968_);
v___x_1970_ = v___x_1959_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_1981_, lean_object* v_descr_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lake_Cache_getArtifact(v_cache_1981_, v_descr_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object* v_cache_1985_, lean_object* v_out_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___y_1990_; lean_object* v___y_1991_; uint64_t v_hash_1993_; lean_object* v_ext_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___y_1998_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_hash_1993_ = lean_ctor_get_uint64(v_out_1986_, sizeof(void*)*1);
v_ext_1994_ = lean_ctor_get(v_out_1986_, 0);
v___x_1995_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1996_ = l_System_FilePath_join(v_cache_1985_, v___x_1995_);
v___x_2006_ = lean_string_utf8_byte_size(v_ext_1994_);
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_nat_dec_eq(v___x_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2009_ = l_Lake_Hash_hex(v_hash_1993_);
v___x_2010_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2011_ = lean_string_append(v___x_2009_, v___x_2010_);
v___x_2012_ = lean_string_append(v___x_2011_, v_ext_1994_);
v___y_1998_ = v___x_2012_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lake_Hash_hex(v_hash_1993_);
v___y_1998_ = v___x_2013_;
goto v___jp_1997_;
}
v___jp_1989_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1990_);
lean_ctor_set(v___x_1992_, 1, v___y_1991_);
return v___x_1992_;
}
v___jp_1997_:
{
lean_object* v_art_1999_; uint8_t v___x_2000_; 
v_art_1999_ = l_System_FilePath_join(v___x_1996_, v___y_1998_);
v___x_2000_ = l_System_FilePath_pathExists(v_art_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2001_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2002_ = lean_string_append(v___x_2001_, v_art_1999_);
v___x_2003_ = 3;
v___x_2004_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*1, v___x_2003_);
v___x_2005_ = lean_array_push(v___y_1987_, v___x_2004_);
v___y_1990_ = v_art_1999_;
v___y_1991_ = v___x_2005_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v_art_1999_;
v___y_1991_ = v___y_1987_;
goto v___jp_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object* v_cache_2014_, lean_object* v_out_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lake_Cache_getArtifactPaths___lam__0(v_cache_2014_, v_out_2015_, v___y_2016_);
lean_dec_ref(v_out_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object* v_n_2019_, lean_object* v_f_2020_, lean_object* v_xs_2021_, lean_object* v_k_2022_, lean_object* v_acc_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_nat_dec_lt(v_k_2022_, v_n_2019_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v_k_2022_);
lean_dec_ref(v_f_2020_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_acc_2023_);
lean_ctor_set(v___x_2027_, 1, v___y_2024_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_array_fget_borrowed(v_xs_2021_, v_k_2022_);
lean_inc_ref(v_f_2020_);
lean_inc(v___x_2028_);
v___x_2029_ = lean_apply_3(v_f_2020_, v___x_2028_, v___y_2024_, lean_box(0));
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
v_a_2031_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2029_);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_k_2022_, v___x_2032_);
lean_dec(v_k_2022_);
v___x_2034_ = lean_array_push(v_acc_2023_, v_a_2030_);
v_k_2022_ = v___x_2033_;
v_acc_2023_ = v___x_2034_;
v___y_2024_ = v_a_2031_;
goto _start;
}
else
{
lean_object* v_a_2036_; lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_acc_2023_);
lean_dec(v_k_2022_);
lean_dec_ref(v_f_2020_);
v_a_2036_ = lean_ctor_get(v___x_2029_, 0);
v_a_2037_ = lean_ctor_get(v___x_2029_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2029_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_inc(v_a_2036_);
lean_dec(v___x_2029_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object* v_n_2045_, lean_object* v_f_2046_, lean_object* v_xs_2047_, lean_object* v_k_2048_, lean_object* v_acc_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2045_, v_f_2046_, v_xs_2047_, v_k_2048_, v_acc_2049_, v___y_2050_);
lean_dec_ref(v_xs_2047_);
lean_dec(v_n_2045_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object* v_cache_2055_, lean_object* v_descrs_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___f_2059_ = lean_alloc_closure((void*)(l_Lake_Cache_getArtifactPaths___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2059_, 0, v_cache_2055_);
v___x_2060_ = lean_array_get_size(v_descrs_2056_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_a_2057_);
v___x_2063_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v___x_2060_, v___f_2059_, v_descrs_2056_, v___x_2061_, v___x_2062_, v_a_2057_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_a_2064_);
v___x_2065_ = lean_array_get_size(v_a_2057_);
lean_dec_ref(v_a_2057_);
v___x_2066_ = lean_array_get_size(v_a_2064_);
v___x_2067_ = lean_nat_dec_eq(v___x_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; lean_object* v_unused_2076_; 
v_unused_2075_ = lean_ctor_get(v___x_2063_, 1);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2076_);
v___x_2069_ = v___x_2063_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_dec(v___x_2063_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2065_);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_a_2064_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_dec(v_a_2064_);
return v___x_2063_;
}
}
else
{
lean_dec_ref(v_a_2057_);
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object* v_cache_2077_, lean_object* v_descrs_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lake_Cache_getArtifactPaths(v_cache_2077_, v_descrs_2078_, v_a_2079_);
lean_dec_ref(v_descrs_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_n_2084_, lean_object* v_f_2085_, lean_object* v_xs_2086_, lean_object* v_k_2087_, lean_object* v_h_2088_, lean_object* v_acc_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2084_, v_f_2085_, v_xs_2086_, v_k_2087_, v_acc_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object* v_00_u03b1_2093_, lean_object* v_00_u03b2_2094_, lean_object* v_n_2095_, lean_object* v_f_2096_, lean_object* v_xs_2097_, lean_object* v_k_2098_, lean_object* v_h_2099_, lean_object* v_acc_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(v_00_u03b1_2093_, v_00_u03b2_2094_, v_n_2095_, v_f_2096_, v_xs_2097_, v_k_2098_, v_h_2099_, v_acc_2100_, v___y_2101_);
lean_dec_ref(v_xs_2097_);
lean_dec(v_n_2095_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2107_ = l_System_FilePath_join(v_cache_2105_, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2109_, lean_object* v_scope_2110_, uint64_t v_inputHash_2111_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2112_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2113_ = l_System_FilePath_join(v_cache_2109_, v___x_2112_);
v___x_2114_ = l_System_FilePath_join(v___x_2113_, v_scope_2110_);
v___x_2115_ = l_Lake_Hash_hex(v_inputHash_2111_);
v___x_2116_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
v___x_2118_ = l_System_FilePath_join(v___x_2114_, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2119_, lean_object* v_scope_2120_, lean_object* v_inputHash_2121_){
_start:
{
uint64_t v_inputHash_boxed_2122_; lean_object* v_res_2123_; 
v_inputHash_boxed_2122_ = lean_unbox_uint64(v_inputHash_2121_);
lean_dec_ref(v_inputHash_2121_);
v_res_2123_ = l_Lake_Cache_outputsFile(v_cache_2119_, v_scope_2120_, v_inputHash_boxed_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2124_, lean_object* v_scope_2125_, uint64_t v_inputHash_2126_, lean_object* v_out_2127_, lean_object* v_service_x3f_2128_, lean_object* v_remoteScope_x3f_2129_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_file_2137_; lean_object* v___x_2138_; 
v___x_2131_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2132_ = l_System_FilePath_join(v_cache_2124_, v___x_2131_);
v___x_2133_ = l_System_FilePath_join(v___x_2132_, v_scope_2125_);
v___x_2134_ = l_Lake_Hash_hex(v_inputHash_2126_);
v___x_2135_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2136_ = lean_string_append(v___x_2134_, v___x_2135_);
v_file_2137_ = l_System_FilePath_join(v___x_2133_, v___x_2136_);
lean_inc_ref(v_file_2137_);
v___x_2138_ = l_Lake_createParentDirs(v_file_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v___x_2138_);
v___x_2139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2139_, 0, v_out_2127_);
lean_ctor_set(v___x_2139_, 1, v_service_x3f_2128_);
lean_ctor_set(v___x_2139_, 2, v_remoteScope_x3f_2129_);
v___x_2140_ = l_Lake_CacheOutput_toJson(v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(80u);
v___x_2142_ = l_Lean_Json_pretty(v___x_2140_, v___x_2141_);
v___x_2143_ = l_IO_FS_writeFile(v_file_2137_, v___x_2142_);
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_file_2137_);
return v___x_2143_;
}
else
{
lean_dec_ref(v_file_2137_);
lean_dec(v_remoteScope_x3f_2129_);
lean_dec(v_service_x3f_2128_);
lean_dec(v_out_2127_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2144_, lean_object* v_scope_2145_, lean_object* v_inputHash_2146_, lean_object* v_out_2147_, lean_object* v_service_x3f_2148_, lean_object* v_remoteScope_x3f_2149_, lean_object* v_a_2150_){
_start:
{
uint64_t v_inputHash_boxed_2151_; lean_object* v_res_2152_; 
v_inputHash_boxed_2151_ = lean_unbox_uint64(v_inputHash_2146_);
lean_dec_ref(v_inputHash_2146_);
v_res_2152_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2144_, v_scope_2145_, v_inputHash_boxed_2151_, v_out_2147_, v_service_x3f_2148_, v_remoteScope_x3f_2149_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2153_, lean_object* v_cache_2154_, lean_object* v_scope_2155_, uint64_t v_inputHash_2156_, lean_object* v_outputs_2157_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_apply_1(v_inst_2153_, v_outputs_2157_);
v___x_2160_ = lean_box(0);
v___x_2161_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2154_, v_scope_2155_, v_inputHash_2156_, v___x_2159_, v___x_2160_, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2162_, lean_object* v_cache_2163_, lean_object* v_scope_2164_, lean_object* v_inputHash_2165_, lean_object* v_outputs_2166_, lean_object* v_a_2167_){
_start:
{
uint64_t v_inputHash_boxed_2168_; lean_object* v_res_2169_; 
v_inputHash_boxed_2168_ = lean_unbox_uint64(v_inputHash_2165_);
lean_dec_ref(v_inputHash_2165_);
v_res_2169_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2162_, v_cache_2163_, v_scope_2164_, v_inputHash_boxed_2168_, v_outputs_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2170_, lean_object* v_inst_2171_, lean_object* v_cache_2172_, lean_object* v_scope_2173_, uint64_t v_inputHash_2174_, lean_object* v_outputs_2175_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_apply_1(v_inst_2171_, v_outputs_2175_);
v___x_2178_ = lean_box(0);
v___x_2179_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2172_, v_scope_2173_, v_inputHash_2174_, v___x_2177_, v___x_2178_, v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_inst_2181_, lean_object* v_cache_2182_, lean_object* v_scope_2183_, lean_object* v_inputHash_2184_, lean_object* v_outputs_2185_, lean_object* v_a_2186_){
_start:
{
uint64_t v_inputHash_boxed_2187_; lean_object* v_res_2188_; 
v_inputHash_boxed_2187_ = lean_unbox_uint64(v_inputHash_2184_);
lean_dec_ref(v_inputHash_2184_);
v_res_2188_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2180_, v_inst_2181_, v_cache_2182_, v_scope_2183_, v_inputHash_boxed_2187_, v_outputs_2185_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2189_, lean_object* v_scope_2190_, lean_object* v_service_x3f_2191_, lean_object* v_remoteScope_x3f_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v___x_2196_; 
lean_dec(v_remoteScope_x3f_2192_);
lean_dec(v_service_x3f_2191_);
lean_dec_ref(v_scope_2190_);
lean_dec_ref(v_cache_2189_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_x_2193_);
return v___x_2196_;
}
else
{
lean_object* v_key_2197_; lean_object* v_value_2198_; lean_object* v_tail_2199_; uint64_t v___x_2200_; lean_object* v___x_2201_; 
v_key_2197_ = lean_ctor_get(v_x_2194_, 0);
lean_inc(v_key_2197_);
v_value_2198_ = lean_ctor_get(v_x_2194_, 1);
lean_inc(v_value_2198_);
v_tail_2199_ = lean_ctor_get(v_x_2194_, 2);
lean_inc(v_tail_2199_);
lean_dec_ref(v_x_2194_);
v___x_2200_ = lean_unbox_uint64(v_key_2197_);
lean_dec(v_key_2197_);
lean_inc(v_remoteScope_x3f_2192_);
lean_inc(v_service_x3f_2191_);
lean_inc_ref(v_scope_2190_);
lean_inc_ref(v_cache_2189_);
v___x_2201_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2189_, v_scope_2190_, v___x_2200_, v_value_2198_, v_service_x3f_2191_, v_remoteScope_x3f_2192_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v_x_2193_ = v_a_2202_;
v_x_2194_ = v_tail_2199_;
goto _start;
}
else
{
lean_dec(v_tail_2199_);
lean_dec(v_remoteScope_x3f_2192_);
lean_dec(v_service_x3f_2191_);
lean_dec_ref(v_scope_2190_);
lean_dec_ref(v_cache_2189_);
return v___x_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2204_, lean_object* v_scope_2205_, lean_object* v_service_x3f_2206_, lean_object* v_remoteScope_x3f_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2204_, v_scope_2205_, v_service_x3f_2206_, v_remoteScope_x3f_2207_, v_x_2208_, v_x_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2212_, lean_object* v_scope_2213_, lean_object* v_service_x3f_2214_, lean_object* v_remoteScope_x3f_2215_, lean_object* v_as_2216_, size_t v_i_2217_, size_t v_stop_2218_, lean_object* v_b_2219_){
_start:
{
uint8_t v___x_2221_; 
v___x_2221_ = lean_usize_dec_eq(v_i_2217_, v_stop_2218_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_array_uget_borrowed(v_as_2216_, v_i_2217_);
v___x_2223_ = lean_box(0);
lean_inc(v___x_2222_);
lean_inc(v_remoteScope_x3f_2215_);
lean_inc(v_service_x3f_2214_);
lean_inc_ref(v_scope_2213_);
lean_inc_ref(v_cache_2212_);
v___x_2224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2212_, v_scope_2213_, v_service_x3f_2214_, v_remoteScope_x3f_2215_, v___x_2223_, v___x_2222_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; size_t v___x_2226_; size_t v___x_2227_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = ((size_t)1ULL);
v___x_2227_ = lean_usize_add(v_i_2217_, v___x_2226_);
v_i_2217_ = v___x_2227_;
v_b_2219_ = v_a_2225_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2215_);
lean_dec(v_service_x3f_2214_);
lean_dec_ref(v_scope_2213_);
lean_dec_ref(v_cache_2212_);
return v___x_2224_;
}
}
else
{
lean_object* v___x_2229_; 
lean_dec(v_remoteScope_x3f_2215_);
lean_dec(v_service_x3f_2214_);
lean_dec_ref(v_scope_2213_);
lean_dec_ref(v_cache_2212_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_b_2219_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2230_, lean_object* v_scope_2231_, lean_object* v_service_x3f_2232_, lean_object* v_remoteScope_x3f_2233_, lean_object* v_as_2234_, lean_object* v_i_2235_, lean_object* v_stop_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_){
_start:
{
size_t v_i_boxed_2239_; size_t v_stop_boxed_2240_; lean_object* v_res_2241_; 
v_i_boxed_2239_ = lean_unbox_usize(v_i_2235_);
lean_dec(v_i_2235_);
v_stop_boxed_2240_ = lean_unbox_usize(v_stop_2236_);
lean_dec(v_stop_2236_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2230_, v_scope_2231_, v_service_x3f_2232_, v_remoteScope_x3f_2233_, v_as_2234_, v_i_boxed_2239_, v_stop_boxed_2240_, v_b_2237_);
lean_dec_ref(v_as_2234_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2242_, lean_object* v_scope_2243_, lean_object* v_map_2244_, lean_object* v_service_x3f_2245_, lean_object* v_remoteScope_x3f_2246_){
_start:
{
lean_object* v_buckets_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_buckets_2248_ = lean_ctor_get(v_map_2244_, 1);
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = lean_array_get_size(v_buckets_2248_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_nat_dec_lt(v___x_2249_, v___x_2250_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_remoteScope_x3f_2246_);
lean_dec(v_service_x3f_2245_);
lean_dec_ref(v_scope_2243_);
lean_dec_ref(v_cache_2242_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
return v___x_2253_;
}
else
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_nat_dec_le(v___x_2250_, v___x_2250_);
if (v___x_2254_ == 0)
{
if (v___x_2252_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_remoteScope_x3f_2246_);
lean_dec(v_service_x3f_2245_);
lean_dec_ref(v_scope_2243_);
lean_dec_ref(v_cache_2242_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2251_);
return v___x_2255_;
}
else
{
size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2250_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2242_, v_scope_2243_, v_service_x3f_2245_, v_remoteScope_x3f_2246_, v_buckets_2248_, v___x_2256_, v___x_2257_, v___x_2251_);
return v___x_2258_;
}
}
else
{
size_t v___x_2259_; size_t v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = ((size_t)0ULL);
v___x_2260_ = lean_usize_of_nat(v___x_2250_);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2242_, v_scope_2243_, v_service_x3f_2245_, v_remoteScope_x3f_2246_, v_buckets_2248_, v___x_2259_, v___x_2260_, v___x_2251_);
return v___x_2261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2262_, lean_object* v_scope_2263_, lean_object* v_map_2264_, lean_object* v_service_x3f_2265_, lean_object* v_remoteScope_x3f_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lake_Cache_writeMap(v_cache_2262_, v_scope_2263_, v_map_2264_, v_service_x3f_2265_, v_remoteScope_x3f_2266_);
lean_dec_ref(v_map_2264_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lake_CacheOutput_fromJson_x3f(v_x_2271_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
v_a_2282_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2284_ = v___x_2273_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2273_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_a_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2293_, lean_object* v_scope_2294_, uint64_t v_inputHash_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v_path_2304_; lean_object* v___x_2305_; 
v___x_2298_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2299_ = l_System_FilePath_join(v_cache_2293_, v___x_2298_);
v___x_2300_ = l_System_FilePath_join(v___x_2299_, v_scope_2294_);
v___x_2301_ = l_Lake_Hash_hex(v_inputHash_2295_);
v___x_2302_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2303_ = lean_string_append(v___x_2301_, v___x_2302_);
v_path_2304_ = l_System_FilePath_join(v___x_2300_, v___x_2303_);
v___x_2305_ = l_IO_FS_readFile(v_path_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_a_2308_; lean_object* v___x_2317_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2305_);
v___x_2317_ = l_Lean_Json_parse(v_a_2306_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref(v___x_2317_);
v_a_2308_ = v_a_2318_;
goto v___jp_2307_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2317_);
v___x_2320_ = l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v_a_2308_ = v_a_2321_;
goto v___jp_2307_;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_path_2304_);
v_a_2322_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2320_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2322_);
lean_ctor_set(v___x_2323_, 1, v_a_2296_);
return v___x_2323_;
}
}
v___jp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2309_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2310_ = lean_string_append(v_path_2304_, v___x_2309_);
v___x_2311_ = lean_string_append(v___x_2310_, v_a_2308_);
lean_dec_ref(v_a_2308_);
v___x_2312_ = 2;
v___x_2313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*1, v___x_2312_);
v___x_2314_ = lean_array_push(v_a_2296_, v___x_2313_);
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2314_);
return v___x_2316_;
}
}
else
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2305_);
if (lean_obj_tag(v_a_2324_) == 11)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v_a_2324_);
lean_dec_ref(v_path_2304_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_a_2296_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2327_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2328_ = lean_string_append(v_path_2304_, v___x_2327_);
v___x_2329_ = lean_io_error_to_string(v_a_2324_);
v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = 3;
v___x_2332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*1, v___x_2331_);
v___x_2333_ = lean_array_get_size(v_a_2296_);
v___x_2334_ = lean_array_push(v_a_2296_, v___x_2332_);
v___x_2335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2336_, lean_object* v_scope_2337_, lean_object* v_inputHash_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
uint64_t v_inputHash_boxed_2341_; lean_object* v_res_2342_; 
v_inputHash_boxed_2341_ = lean_unbox_uint64(v_inputHash_2338_);
lean_dec_ref(v_inputHash_2338_);
v_res_2342_ = l_Lake_Cache_readOutputs_x3f(v_cache_2336_, v_scope_2337_, v_inputHash_boxed_2341_, v_a_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2346_ = l_System_FilePath_join(v_cache_2344_, v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2348_, lean_object* v_scope_2349_, lean_object* v_rev_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2352_ = l_System_FilePath_join(v_cache_2348_, v___x_2351_);
v___x_2353_ = l_System_FilePath_join(v___x_2352_, v_scope_2349_);
v___x_2354_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2355_ = lean_string_append(v_rev_2350_, v___x_2354_);
v___x_2356_ = l_System_FilePath_join(v___x_2353_, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2359_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2360_ = lean_string_utf8_byte_size(v_self_2359_);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_nat_dec_eq(v___x_2360_, v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l_Lake_CachePlatform_isNone(v_self_2363_);
lean_dec_ref(v_self_2363_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_System_Platform_target;
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2367_){
_start:
{
lean_inc_ref(v_s_2367_);
return v_s_2367_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lake_CachePlatform_ofString(v_s_2368_);
lean_dec_ref(v_s_2368_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_string_length(v_self_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object* v_self_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lake_CachePlatform_length(v_self_2372_);
lean_dec_ref(v_self_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2375_){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2376_ = lean_string_utf8_byte_size(v_self_2375_);
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = lean_nat_dec_eq(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_inc_ref(v_self_2375_);
return v_self_2375_;
}
else
{
lean_object* v___x_2379_; 
v___x_2379_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lake_CachePlatform_toString(v_self_2380_);
lean_dec_ref(v_self_2380_);
return v_res_2381_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2385_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2386_ = lean_string_utf8_byte_size(v_self_2385_);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_nat_dec_eq(v___x_2386_, v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2389_){
_start:
{
uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_res_2390_ = l_Lake_CacheToolchain_isNone(v_self_2389_);
lean_dec_ref(v_self_2389_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lake_normalizeToolchain(v_s_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2394_){
_start:
{
lean_inc_ref(v_s_2394_);
return v_s_2394_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2395_);
lean_dec_ref(v_s_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_string_length(v_self_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object* v_self_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lake_CacheToolchain_length(v_self_2399_);
lean_dec_ref(v_self_2399_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2401_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_string_utf8_byte_size(v_self_2401_);
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_nat_dec_eq(v___x_2402_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_inc_ref(v_self_2401_);
return v_self_2401_;
}
else
{
lean_object* v___x_2405_; 
v___x_2405_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lake_CacheToolchain_toString(v_self_2406_);
lean_dec_ref(v_self_2406_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2411_, lean_object* v_url_2412_, lean_object* v_path_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_path_2413_);
v___x_2417_ = l_Lake_download(v_url_2412_, v_path_2413_, v___x_2416_, v_a_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2457_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; 
v_unused_2458_ = lean_ctor_get(v___x_2417_, 0);
lean_dec(v_unused_2458_);
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2457_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2457_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lake_computeBinFileHash(v_path_2413_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; uint64_t v___x_2424_; uint8_t v___x_2425_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref(v___x_2422_);
v___x_2424_ = lean_unbox_uint64(v_a_2423_);
lean_dec(v_a_2423_);
v___x_2425_ = lean_uint64_dec_eq(v___x_2424_, v_hash_2411_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2426_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2413_);
v___x_2427_ = lean_string_append(v_path_2413_, v___x_2426_);
v___x_2428_ = 3;
v___x_2429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set_uint8(v___x_2429_, sizeof(void*)*1, v___x_2428_);
v___x_2430_ = lean_array_push(v_a_2418_, v___x_2429_);
v___x_2431_ = lean_io_remove_file(v_path_2413_);
lean_dec_ref(v_path_2413_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_dec_ref(v___x_2431_);
v___x_2432_ = lean_array_get_size(v___x_2430_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 1);
lean_ctor_set(v___x_2420_, 1, v___x_2430_);
lean_ctor_set(v___x_2420_, 0, v___x_2432_);
v___x_2434_ = v___x_2420_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v___x_2430_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v_a_2436_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2436_);
lean_dec_ref(v___x_2431_);
v___x_2437_ = lean_io_error_to_string(v_a_2436_);
v___x_2438_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*1, v___x_2428_);
v___x_2439_ = lean_array_get_size(v___x_2430_);
v___x_2440_ = lean_array_push(v___x_2430_, v___x_2438_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 1);
lean_ctor_set(v___x_2420_, 1, v___x_2440_);
lean_ctor_set(v___x_2420_, 0, v___x_2439_);
v___x_2442_ = v___x_2420_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec_ref(v_path_2413_);
v___x_2444_ = lean_box(0);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2444_);
v___x_2446_ = v___x_2420_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_a_2418_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec_ref(v_path_2413_);
v_a_2448_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v___x_2422_);
v___x_2449_ = lean_io_error_to_string(v_a_2448_);
v___x_2450_ = 3;
v___x_2451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*1, v___x_2450_);
v___x_2452_ = lean_array_get_size(v_a_2418_);
v___x_2453_ = lean_array_push(v_a_2418_, v___x_2451_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 1);
lean_ctor_set(v___x_2420_, 1, v___x_2453_);
lean_ctor_set(v___x_2420_, 0, v___x_2452_);
v___x_2455_ = v___x_2420_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_dec_ref(v_path_2413_);
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2459_, lean_object* v_url_2460_, lean_object* v_path_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
uint64_t v_hash_boxed_2464_; lean_object* v_res_2465_; 
v_hash_boxed_2464_ = lean_unbox_uint64(v_hash_2459_);
lean_dec_ref(v_hash_2459_);
v_res_2465_ = l_Lake_downloadArtifactCore(v_hash_boxed_2464_, v_url_2460_, v_path_2461_, v_a_2462_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2468_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_Json_getNat_x3f(v_x_2468_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2487_; 
v_a_2479_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2481_ = v___x_2470_;
v_isShared_2482_ = v_isSharedCheck_2487_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2470_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2487_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2479_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2483_);
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2511_ = lean_unsigned_to_nat(14u);
v___x_2512_ = lean_mk_empty_array_with_capacity(v___x_2511_);
v___x_2513_ = lean_array_push(v___x_2512_, v___x_2510_);
return v___x_2513_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2515_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2516_ = lean_array_push(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2518_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2519_ = lean_array_push(v___x_2518_, v___x_2517_);
return v___x_2519_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2521_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2522_ = lean_array_push(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2524_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2525_ = lean_array_push(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2527_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2528_ = lean_array_push(v___x_2527_, v___x_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2532_, lean_object* v_contentType_2533_, lean_object* v_url_2534_, lean_object* v_key_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___y_2539_; lean_object* v_a_2540_; lean_object* v_stderr_2553_; lean_object* v___y_2562_; lean_object* v___y_2565_; lean_object* v_a_2566_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v_stderr_2605_; lean_object* v_a_2606_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2620_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2621_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2622_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2623_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2624_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2625_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2626_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2627_ = lean_string_append(v___x_2626_, v_contentType_2533_);
v___x_2628_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2629_ = lean_array_push(v___x_2628_, v_key_2535_);
v___x_2630_ = lean_array_push(v___x_2629_, v___x_2622_);
v___x_2631_ = lean_array_push(v___x_2630_, v___x_2623_);
v___x_2632_ = lean_array_push(v___x_2631_, v___x_2624_);
v___x_2633_ = lean_array_push(v___x_2632_, v_file_2532_);
v___x_2634_ = lean_array_push(v___x_2633_, v_url_2534_);
v___x_2635_ = lean_array_push(v___x_2634_, v___x_2625_);
v___x_2636_ = lean_array_push(v___x_2635_, v___x_2627_);
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2640_ = 1;
v___x_2641_ = 0;
v___x_2642_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2642_, 0, v___x_2620_);
lean_ctor_set(v___x_2642_, 1, v___x_2621_);
lean_ctor_set(v___x_2642_, 2, v___x_2636_);
lean_ctor_set(v___x_2642_, 3, v___x_2637_);
lean_ctor_set(v___x_2642_, 4, v___x_2639_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*5, v___x_2640_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*5 + 1, v___x_2641_);
v___x_2643_ = l_Lake_captureProc_x27(v___x_2642_, v___x_2639_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v_a_2645_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
v_a_2645_ = lean_ctor_get(v___x_2643_, 1);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2643_);
v___x_2659_ = lean_array_get_size(v_a_2645_);
v___x_2660_ = lean_nat_dec_lt(v___x_2638_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec(v_a_2645_);
goto v___jp_2646_;
}
else
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_nat_dec_le(v___x_2659_, v___x_2659_);
if (v___x_2662_ == 0)
{
if (v___x_2660_ == 0)
{
lean_dec(v_a_2645_);
goto v___jp_2646_;
}
else
{
size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = lean_usize_of_nat(v___x_2659_);
lean_inc_ref(v_a_2536_);
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2645_, v___x_2663_, v___x_2664_, v___x_2661_, v_a_2536_);
lean_dec(v_a_2645_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_dec_ref(v___x_2665_);
goto v___jp_2646_;
}
else
{
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2536_);
return v___x_2665_;
}
}
}
else
{
size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = lean_usize_of_nat(v___x_2659_);
lean_inc_ref(v_a_2536_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2645_, v___x_2666_, v___x_2667_, v___x_2661_, v_a_2536_);
lean_dec(v_a_2645_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref(v___x_2668_);
goto v___jp_2646_;
}
else
{
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2536_);
return v___x_2668_;
}
}
}
v___jp_2646_:
{
lean_object* v_stderr_2647_; lean_object* v___x_2648_; 
v_stderr_2647_ = lean_ctor_get(v_a_2644_, 1);
lean_inc_ref(v_stderr_2647_);
v___x_2648_ = l_Lean_Json_parse(v_stderr_2647_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; 
lean_inc_ref(v_stderr_2647_);
lean_dec(v_a_2644_);
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v_stderr_2605_ = v_stderr_2647_;
v_a_2606_ = v_a_2649_;
goto v___jp_2604_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2648_);
v___x_2651_ = l_Lean_Json_getObj_x3f(v_a_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; 
lean_inc_ref(v_stderr_2647_);
lean_dec(v_a_2644_);
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v_stderr_2605_ = v_stderr_2647_;
v_a_2606_ = v_a_2652_;
goto v___jp_2604_;
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2651_);
v___x_2654_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2655_ = l_Lake_JsonObject_getJson_x3f(v_a_2653_, v___x_2654_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_inc_ref(v_stderr_2647_);
lean_dec(v_a_2653_);
lean_dec(v_a_2644_);
v_stderr_2553_ = v_stderr_2647_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2656_; lean_object* v___x_2657_; 
v_val_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_val_2656_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2656_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref(v___x_2657_);
v___y_2593_ = v_a_2653_;
v___y_2594_ = v_a_2644_;
goto v___jp_2592_;
}
else
{
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref(v___x_2657_);
v___y_2593_ = v_a_2653_;
v___y_2594_ = v_a_2644_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2658_; 
lean_dec(v_a_2653_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v___y_2565_ = v_a_2644_;
v_a_2566_ = v_a_2658_;
goto v___jp_2564_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_a_2669_ = lean_ctor_get(v___x_2643_, 1);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2643_);
v___x_2670_ = lean_array_get_size(v_a_2669_);
v___x_2671_ = lean_nat_dec_lt(v___x_2638_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2536_);
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_nat_dec_le(v___x_2670_, v___x_2670_);
if (v___x_2675_ == 0)
{
if (v___x_2671_ == 0)
{
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2536_);
goto v___jp_2617_;
}
else
{
size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = lean_usize_of_nat(v___x_2670_);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2669_, v___x_2676_, v___x_2677_, v___x_2674_, v_a_2536_);
lean_dec(v_a_2669_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_dec_ref(v___x_2678_);
goto v___jp_2617_;
}
else
{
return v___x_2678_;
}
}
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2670_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2669_, v___x_2679_, v___x_2680_, v___x_2674_, v_a_2536_);
lean_dec(v_a_2669_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref(v___x_2681_);
goto v___jp_2617_;
}
else
{
return v___x_2681_;
}
}
}
}
v___jp_2538_:
{
lean_object* v_stderr_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_stderr_2541_ = lean_ctor_get(v___y_2539_, 1);
lean_inc_ref(v_stderr_2541_);
lean_dec_ref(v___y_2539_);
v___x_2542_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2543_ = lean_string_append(v___x_2542_, v_a_2540_);
lean_dec_ref(v_a_2540_);
v___x_2544_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
v___x_2546_ = lean_string_append(v___x_2545_, v_stderr_2541_);
lean_dec_ref(v_stderr_2541_);
v___x_2547_ = 3;
v___x_2548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*1, v___x_2547_);
v___x_2549_ = lean_apply_2(v_a_2536_, v___x_2548_, lean_box(0));
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2554_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2555_ = lean_string_append(v___x_2554_, v_stderr_2553_);
lean_dec_ref(v_stderr_2553_);
v___x_2556_ = 3;
v___x_2557_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set_uint8(v___x_2557_, sizeof(void*)*1, v___x_2556_);
v___x_2558_ = lean_apply_2(v_a_2536_, v___x_2557_, lean_box(0));
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
v___jp_2561_:
{
lean_object* v_stderr_2563_; 
v_stderr_2563_ = lean_ctor_get(v___y_2562_, 1);
lean_inc_ref(v_stderr_2563_);
lean_dec_ref(v___y_2562_);
v_stderr_2553_ = v_stderr_2563_;
goto v___jp_2552_;
}
v___jp_2564_:
{
if (lean_obj_tag(v_a_2566_) == 0)
{
v___y_2562_ = v___y_2565_;
goto v___jp_2561_;
}
else
{
lean_object* v_val_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2591_; 
v_val_2567_ = lean_ctor_get(v_a_2566_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_a_2566_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2569_ = v_a_2566_;
v_isShared_2570_ = v_isSharedCheck_2591_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_val_2567_);
lean_dec(v_a_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2591_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_unsigned_to_nat(200u);
v___x_2572_ = lean_nat_dec_eq(v_val_2567_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v_stdout_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v_stdout_2573_ = lean_ctor_get(v___y_2565_, 0);
lean_inc_ref(v_stdout_2573_);
lean_dec_ref(v___y_2565_);
v___x_2574_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2575_ = l_Nat_reprFast(v_val_2567_);
v___x_2576_ = lean_string_append(v___x_2574_, v___x_2575_);
lean_dec_ref(v___x_2575_);
v___x_2577_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2578_ = lean_string_append(v___x_2576_, v___x_2577_);
v___x_2579_ = lean_string_append(v___x_2578_, v_stdout_2573_);
lean_dec_ref(v_stdout_2573_);
v___x_2580_ = 3;
v___x_2581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*1, v___x_2580_);
v___x_2582_ = lean_apply_2(v_a_2536_, v___x_2581_, lean_box(0));
v___x_2583_ = lean_box(0);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2583_);
v___x_2585_ = v___x_2569_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec(v_val_2567_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v_a_2536_);
v___x_2587_ = lean_box(0);
if (v_isShared_2570_ == 0)
{
lean_ctor_set_tag(v___x_2569_, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2587_);
v___x_2589_ = v___x_2569_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
v___jp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2596_ = l_Lake_JsonObject_getJson_x3f(v___y_2593_, v___x_2595_);
lean_dec(v___y_2593_);
if (lean_obj_tag(v___x_2596_) == 0)
{
v___y_2562_ = v___y_2594_;
goto v___jp_2561_;
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2598_; 
v_val_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_val_2597_);
lean_dec_ref(v___x_2596_);
v___x_2598_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2597_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
v___x_2600_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2601_ = lean_string_append(v___x_2600_, v_a_2599_);
lean_dec(v_a_2599_);
v___y_2539_ = v___y_2594_;
v_a_2540_ = v___x_2601_;
goto v___jp_2538_;
}
else
{
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2602_; 
v_a_2602_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2598_);
v___y_2539_ = v___y_2594_;
v_a_2540_ = v_a_2602_;
goto v___jp_2538_;
}
else
{
lean_object* v_a_2603_; 
v_a_2603_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2603_);
lean_dec_ref(v___x_2598_);
v___y_2565_ = v___y_2594_;
v_a_2566_ = v_a_2603_;
goto v___jp_2564_;
}
}
}
}
v___jp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2607_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2608_ = lean_string_append(v___x_2607_, v_a_2606_);
lean_dec_ref(v_a_2606_);
v___x_2609_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2610_ = lean_string_append(v___x_2608_, v___x_2609_);
v___x_2611_ = lean_string_append(v___x_2610_, v_stderr_2605_);
lean_dec_ref(v_stderr_2605_);
v___x_2612_ = 3;
v___x_2613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*1, v___x_2612_);
v___x_2614_ = lean_apply_2(v_a_2536_, v___x_2613_, lean_box(0));
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
v___jp_2617_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_box(0);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2682_, lean_object* v_contentType_2683_, lean_object* v_url_2684_, lean_object* v_key_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2682_, v_contentType_2683_, v_url_2684_, v_key_2685_, v_a_2686_);
lean_dec_ref(v_contentType_2683_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2689_){
_start:
{
lean_object* v_name_x3f_2690_; 
v_name_x3f_2690_ = lean_ctor_get(v_service_2689_, 0);
lean_inc(v_name_x3f_2690_);
return v_name_x3f_2690_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lake_CacheService_name_x3f(v_service_2691_);
lean_dec_ref(v_service_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2693_){
_start:
{
uint8_t v_isReservoir_2694_; 
v_isReservoir_2694_ = lean_ctor_get_uint8(v_service_2693_, sizeof(void*)*5);
return v_isReservoir_2694_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2695_){
_start:
{
uint8_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = l_Lake_CacheService_isReservoir(v_service_2695_);
lean_dec_ref(v_service_2695_);
v_r_2697_ = lean_box(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2698_, lean_object* v_name_x3f_2699_){
_start:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2701_ = 1;
v___x_2702_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2702_, 0, v_name_x3f_2699_);
lean_ctor_set(v___x_2702_, 1, v___x_2700_);
lean_ctor_set(v___x_2702_, 2, v___x_2700_);
lean_ctor_set(v___x_2702_, 3, v___x_2700_);
lean_ctor_set(v___x_2702_, 4, v_apiEndpoint_2698_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*5, v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2703_, lean_object* v_artifactEndpoint_2704_, lean_object* v_revisionEndpoint_2705_){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = lean_box(0);
v___x_2707_ = 0;
v___x_2708_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2709_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
lean_ctor_set(v___x_2709_, 1, v_key_2703_);
lean_ctor_set(v___x_2709_, 2, v_artifactEndpoint_2704_);
lean_ctor_set(v___x_2709_, 3, v_revisionEndpoint_2705_);
lean_ctor_set(v___x_2709_, 4, v___x_2708_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*5, v___x_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2710_, lean_object* v_revisionEndpoint_2711_, lean_object* v_name_x3f_2712_){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2714_ = 0;
v___x_2715_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2715_, 0, v_name_x3f_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2713_);
lean_ctor_set(v___x_2715_, 2, v_artifactEndpoint_2710_);
lean_ctor_set(v___x_2715_, 3, v_revisionEndpoint_2711_);
lean_ctor_set(v___x_2715_, 4, v___x_2713_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*5, v___x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2716_, lean_object* v_name_x3f_2717_){
_start:
{
lean_object* v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2719_ = 0;
v___x_2720_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2720_, 0, v_name_x3f_2717_);
lean_ctor_set(v___x_2720_, 1, v___x_2718_);
lean_ctor_set(v___x_2720_, 2, v_artifactEndpoint_2716_);
lean_ctor_set(v___x_2720_, 3, v___x_2718_);
lean_ctor_set(v___x_2720_, 4, v___x_2718_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*5, v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2721_, lean_object* v_key_2722_){
_start:
{
lean_object* v_name_x3f_2723_; lean_object* v_artifactEndpoint_2724_; lean_object* v_revisionEndpoint_2725_; uint8_t v_isReservoir_2726_; lean_object* v_apiEndpoint_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
v_name_x3f_2723_ = lean_ctor_get(v_service_2721_, 0);
v_artifactEndpoint_2724_ = lean_ctor_get(v_service_2721_, 2);
v_revisionEndpoint_2725_ = lean_ctor_get(v_service_2721_, 3);
v_isReservoir_2726_ = lean_ctor_get_uint8(v_service_2721_, sizeof(void*)*5);
v_apiEndpoint_2727_ = lean_ctor_get(v_service_2721_, 4);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_service_2721_);
if (v_isSharedCheck_2734_ == 0)
{
lean_object* v_unused_2735_; 
v_unused_2735_ = lean_ctor_get(v_service_2721_, 1);
lean_dec(v_unused_2735_);
v___x_2729_ = v_service_2721_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_apiEndpoint_2727_);
lean_inc(v_revisionEndpoint_2725_);
lean_inc(v_artifactEndpoint_2724_);
lean_inc(v_name_x3f_2723_);
lean_dec(v_service_2721_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 1, v_key_2722_);
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_name_x3f_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_key_2722_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_artifactEndpoint_2724_);
lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_revisionEndpoint_2725_);
lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_apiEndpoint_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2733_, sizeof(void*)*5, v_isReservoir_2726_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2742_);
lean_dec_ref(v_s_2742_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2744_, lean_object* v___x_2745_, lean_object* v___x_2746_, lean_object* v_a_2747_, lean_object* v_b_2748_){
_start:
{
if (lean_obj_tag(v_a_2747_) == 0)
{
lean_object* v_currPos_2749_; lean_object* v_searcher_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2784_; 
v_currPos_2749_ = lean_ctor_get(v_a_2747_, 0);
v_searcher_2750_ = lean_ctor_get(v_a_2747_, 1);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2752_ = v_a_2747_;
v_isShared_2753_ = v_isSharedCheck_2784_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_searcher_2750_);
lean_inc(v_currPos_2749_);
lean_dec(v_a_2747_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2784_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_startInclusive_2754_; lean_object* v_endExclusive_2755_; uint32_t v___x_2756_; lean_object* v_it_2758_; lean_object* v_startInclusive_2759_; lean_object* v_endExclusive_2760_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v_startInclusive_2754_ = lean_ctor_get(v___x_2745_, 1);
v_endExclusive_2755_ = lean_ctor_get(v___x_2745_, 2);
v___x_2756_ = 47;
v___x_2765_ = lean_nat_sub(v_endExclusive_2755_, v_startInclusive_2754_);
v___x_2766_ = lean_nat_dec_eq(v_searcher_2750_, v___x_2765_);
lean_dec(v___x_2765_);
if (v___x_2766_ == 0)
{
uint32_t v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_string_utf8_get_fast(v_scope_2744_, v_searcher_2750_);
v___x_2768_ = lean_uint32_dec_eq(v___x_2767_, v___x_2756_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = lean_string_utf8_next_fast(v_scope_2744_, v_searcher_2750_);
lean_dec(v_searcher_2750_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v___x_2769_);
v___x_2771_ = v___x_2752_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_currPos_2749_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
v_a_2747_ = v___x_2771_;
goto _start;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_slice_2777_; lean_object* v_nextIt_2779_; 
v___x_2774_ = lean_string_utf8_next_fast(v_scope_2744_, v_searcher_2750_);
v___x_2775_ = lean_nat_sub(v___x_2774_, v_searcher_2750_);
v___x_2776_ = lean_nat_add(v_searcher_2750_, v___x_2775_);
lean_dec(v___x_2775_);
v_slice_2777_ = l_String_Slice_subslice_x21(v___x_2745_, v_currPos_2749_, v_searcher_2750_);
lean_inc(v___x_2776_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v___x_2776_);
lean_ctor_set(v___x_2752_, 0, v___x_2776_);
v_nextIt_2779_ = v___x_2752_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2776_);
v_nextIt_2779_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v_startInclusive_2780_; lean_object* v_endExclusive_2781_; 
v_startInclusive_2780_ = lean_ctor_get(v_slice_2777_, 0);
lean_inc(v_startInclusive_2780_);
v_endExclusive_2781_ = lean_ctor_get(v_slice_2777_, 1);
lean_inc(v_endExclusive_2781_);
lean_dec_ref(v_slice_2777_);
v_it_2758_ = v_nextIt_2779_;
v_startInclusive_2759_ = v_startInclusive_2780_;
v_endExclusive_2760_ = v_endExclusive_2781_;
goto v___jp_2757_;
}
}
}
else
{
lean_object* v___x_2783_; 
lean_del_object(v___x_2752_);
lean_dec(v_searcher_2750_);
v___x_2783_ = lean_box(1);
lean_inc(v___x_2746_);
v_it_2758_ = v___x_2783_;
v_startInclusive_2759_ = v_currPos_2749_;
v_endExclusive_2760_ = v___x_2746_;
goto v___jp_2757_;
}
v___jp_2757_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = lean_string_utf8_extract(v_scope_2744_, v_startInclusive_2759_, v_endExclusive_2760_);
lean_dec(v_endExclusive_2760_);
lean_dec(v_startInclusive_2759_);
v___x_2762_ = lean_string_push(v_b_2748_, v___x_2756_);
v___x_2763_ = l_Lake_uriEncode(v___x_2761_, v___x_2762_);
v_a_2747_ = v_it_2758_;
v_b_2748_ = v___x_2763_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2746_);
return v_b_2748_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_2785_, lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v_a_2788_, lean_object* v_b_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2785_, v___x_2786_, v___x_2787_, v_a_2788_, v_b_2789_);
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_scope_2785_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_2791_, lean_object* v_scope_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_string_utf8_byte_size(v_scope_2792_);
lean_inc_ref(v_scope_2792_);
v___x_2795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2795_, 0, v_scope_2792_);
lean_ctor_set(v___x_2795_, 1, v___x_2793_);
lean_ctor_set(v___x_2795_, 2, v___x_2794_);
v___x_2796_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_2795_);
v___x_2797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2792_, v___x_2795_, v___x_2794_, v___x_2796_, v_endpoint_2791_);
lean_dec_ref(v___x_2795_);
lean_dec_ref(v_scope_2792_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_2798_, lean_object* v___x_2799_, lean_object* v___x_2800_, lean_object* v_inst_2801_, lean_object* v_R_2802_, lean_object* v_a_2803_, lean_object* v_b_2804_, lean_object* v_c_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2798_, v___x_2799_, v___x_2800_, v_a_2803_, v_b_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_inst_2810_, lean_object* v_R_2811_, lean_object* v_a_2812_, lean_object* v_b_2813_, lean_object* v_c_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_2807_, v___x_2808_, v___x_2809_, v_inst_2810_, v_R_2811_, v_a_2812_, v_b_2813_, v_c_2814_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_scope_2807_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_2816_, lean_object* v_scope_2817_){
_start:
{
lean_object* v_artifactEndpoint_2818_; lean_object* v___x_2819_; 
v_artifactEndpoint_2818_ = lean_ctor_get(v_service_2816_, 2);
lean_inc_ref(v_artifactEndpoint_2818_);
lean_dec_ref(v_service_2816_);
v___x_2819_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_2818_, v_scope_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_2822_, lean_object* v_service_2823_, lean_object* v_scope_2824_){
_start:
{
lean_object* v___y_2826_; lean_object* v_s_2833_; lean_object* v___x_2834_; 
v_s_2833_ = lean_ctor_get(v_scope_2824_, 0);
lean_inc_ref(v_s_2833_);
lean_dec_ref(v_scope_2824_);
v___x_2834_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_2823_, v_s_2833_);
v___y_2826_ = v___x_2834_;
goto v___jp_2825_;
v___jp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2827_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_2828_ = lean_string_append(v___y_2826_, v___x_2827_);
v___x_2829_ = l_Lake_Hash_hex(v_contentHash_2822_);
v___x_2830_ = lean_string_append(v___x_2828_, v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2832_ = lean_string_append(v___x_2830_, v___x_2831_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_2835_, lean_object* v_service_2836_, lean_object* v_scope_2837_){
_start:
{
uint64_t v_contentHash_boxed_2838_; lean_object* v_res_2839_; 
v_contentHash_boxed_2838_ = lean_unbox_uint64(v_contentHash_2835_);
lean_dec_ref(v_contentHash_2835_);
v_res_2839_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_2838_, v_service_2836_, v_scope_2837_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_2843_, lean_object* v_service_2844_, lean_object* v_scope_2845_){
_start:
{
lean_object* v___y_2847_; uint8_t v_isReservoir_2854_; 
v_isReservoir_2854_ = lean_ctor_get_uint8(v_service_2844_, sizeof(void*)*5);
if (v_isReservoir_2854_ == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_2843_, v_service_2844_, v_scope_2845_);
return v___x_2855_;
}
else
{
if (lean_obj_tag(v_scope_2845_) == 0)
{
lean_object* v_apiEndpoint_2856_; lean_object* v_s_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_apiEndpoint_2856_ = lean_ctor_get(v_service_2844_, 4);
lean_inc_ref(v_apiEndpoint_2856_);
lean_dec_ref(v_service_2844_);
v_s_2857_ = lean_ctor_get(v_scope_2845_, 0);
lean_inc_ref(v_s_2857_);
lean_dec_ref(v_scope_2845_);
v___x_2858_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_2859_ = lean_string_append(v_apiEndpoint_2856_, v___x_2858_);
v___x_2860_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2859_, v_s_2857_);
v___y_2847_ = v___x_2860_;
goto v___jp_2846_;
}
else
{
lean_object* v_apiEndpoint_2861_; lean_object* v_s_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_apiEndpoint_2861_ = lean_ctor_get(v_service_2844_, 4);
lean_inc_ref(v_apiEndpoint_2861_);
lean_dec_ref(v_service_2844_);
v_s_2862_ = lean_ctor_get(v_scope_2845_, 0);
lean_inc_ref(v_s_2862_);
lean_dec_ref(v_scope_2845_);
v___x_2863_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_2864_ = lean_string_append(v_apiEndpoint_2861_, v___x_2863_);
v___x_2865_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2864_, v_s_2862_);
v___y_2847_ = v___x_2865_;
goto v___jp_2846_;
}
}
v___jp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2848_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_2849_ = lean_string_append(v___y_2847_, v___x_2848_);
v___x_2850_ = l_Lake_Hash_hex(v_contentHash_2843_);
v___x_2851_ = lean_string_append(v___x_2849_, v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_2866_, lean_object* v_service_2867_, lean_object* v_scope_2868_){
_start:
{
uint64_t v_contentHash_boxed_2869_; lean_object* v_res_2870_; 
v_contentHash_boxed_2869_ = lean_unbox_uint64(v_contentHash_2866_);
lean_dec_ref(v_contentHash_2866_);
v_res_2870_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_2869_, v_service_2867_, v_scope_2868_);
return v_res_2870_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_2875_ = lean_array_get_size(v___x_2874_);
return v___x_2875_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2876_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_2877_ = lean_unsigned_to_nat(0u);
v___x_2878_ = lean_nat_dec_lt(v___x_2877_, v___x_2876_);
return v___x_2878_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_2880_ = lean_nat_dec_le(v___x_2879_, v___x_2879_);
return v___x_2880_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_2881_; size_t v___x_2882_; 
v___x_2881_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_2882_ = lean_usize_of_nat(v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_2883_, lean_object* v_cache_2884_, lean_object* v_service_2885_, lean_object* v_scope_2886_, uint8_t v_force_2887_, lean_object* v_a_2888_){
_start:
{
uint64_t v_hash_2893_; lean_object* v_ext_2894_; lean_object* v_url_2895_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2959_; lean_object* v___y_2962_; uint8_t v_a_2963_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___y_2969_; lean_object* v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_hash_2893_ = lean_ctor_get_uint64(v_descr_2883_, sizeof(void*)*1);
v_ext_2894_ = lean_ctor_get(v_descr_2883_, 0);
lean_inc_ref(v_scope_2886_);
v_url_2895_ = l_Lake_CacheService_artifactUrl(v_hash_2893_, v_service_2885_, v_scope_2886_);
v___x_2966_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2967_ = l_System_FilePath_join(v_cache_2884_, v___x_2966_);
v___x_2982_ = lean_string_utf8_byte_size(v_ext_2894_);
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_nat_dec_eq(v___x_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2985_ = l_Lake_Hash_hex(v_hash_2893_);
v___x_2986_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2987_ = lean_string_append(v___x_2985_, v___x_2986_);
v___x_2988_ = lean_string_append(v___x_2987_, v_ext_2894_);
v___y_2969_ = v___x_2988_;
goto v___jp_2968_;
}
else
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lake_Hash_hex(v_hash_2893_);
v___y_2969_ = v___x_2989_;
goto v___jp_2968_;
}
v___jp_2890_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
v___jp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2899_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_2900_ = lean_string_append(v___y_2898_, v___x_2899_);
v___x_2901_ = l_Lake_Hash_hex(v_hash_2893_);
v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_2904_ = lean_string_append(v___x_2902_, v___x_2903_);
v___x_2905_ = lean_string_append(v___x_2904_, v___y_2897_);
v___x_2906_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
v___x_2908_ = lean_string_append(v___x_2907_, v_url_2895_);
v___x_2909_ = 1;
v___x_2910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*1, v___x_2909_);
lean_inc_ref(v_a_2888_);
v___x_2911_ = lean_apply_2(v_a_2888_, v___x_2910_, lean_box(0));
v___x_2912_ = lean_unsigned_to_nat(0u);
v___x_2913_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_2914_ = l_Lake_downloadArtifactCore(v_hash_2893_, v_url_2895_, v___y_2897_, v___x_2913_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v_a_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
v_a_2916_ = lean_ctor_get(v___x_2914_, 1);
lean_inc(v_a_2916_);
lean_dec_ref(v___x_2914_);
v___x_2917_ = lean_array_get_size(v_a_2916_);
v___x_2918_ = lean_nat_dec_lt(v___x_2912_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2888_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v_a_2915_);
return v___x_2919_;
}
else
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_nat_dec_le(v___x_2917_, v___x_2917_);
if (v___x_2921_ == 0)
{
if (v___x_2918_ == 0)
{
lean_object* v___x_2922_; 
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2888_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_a_2915_);
return v___x_2922_;
}
else
{
size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = lean_usize_of_nat(v___x_2917_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2916_, v___x_2923_, v___x_2924_, v___x_2920_, v_a_2888_);
lean_dec(v_a_2916_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2925_, 0);
lean_dec(v_unused_2933_);
v___x_2927_ = v___x_2925_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_dec(v___x_2925_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v_a_2915_);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2915_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_dec(v_a_2915_);
return v___x_2925_;
}
}
}
else
{
size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = ((size_t)0ULL);
v___x_2935_ = lean_usize_of_nat(v___x_2917_);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2916_, v___x_2934_, v___x_2935_, v___x_2920_, v_a_2888_);
lean_dec(v_a_2916_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v___x_2936_, 0);
lean_dec(v_unused_2944_);
v___x_2938_ = v___x_2936_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_dec(v___x_2936_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v_a_2915_);
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2915_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
else
{
lean_dec(v_a_2915_);
return v___x_2936_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v_a_2945_ = lean_ctor_get(v___x_2914_, 1);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2914_);
v___x_2946_ = lean_array_get_size(v_a_2945_);
v___x_2947_ = lean_nat_dec_lt(v___x_2912_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2888_);
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_nat_dec_le(v___x_2946_, v___x_2946_);
if (v___x_2951_ == 0)
{
if (v___x_2947_ == 0)
{
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2888_);
goto v___jp_2890_;
}
else
{
size_t v___x_2952_; size_t v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = ((size_t)0ULL);
v___x_2953_ = lean_usize_of_nat(v___x_2946_);
v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2945_, v___x_2952_, v___x_2953_, v___x_2950_, v_a_2888_);
lean_dec(v_a_2945_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_dec_ref(v___x_2954_);
goto v___jp_2890_;
}
else
{
return v___x_2954_;
}
}
}
else
{
size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = ((size_t)0ULL);
v___x_2956_ = lean_usize_of_nat(v___x_2946_);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2945_, v___x_2955_, v___x_2956_, v___x_2950_, v_a_2888_);
lean_dec(v_a_2945_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_dec_ref(v___x_2957_);
goto v___jp_2890_;
}
else
{
return v___x_2957_;
}
}
}
}
}
v___jp_2958_:
{
lean_object* v_s_2960_; 
v_s_2960_ = lean_ctor_get(v_scope_2886_, 0);
lean_inc_ref(v_s_2960_);
lean_dec_ref(v_scope_2886_);
v___y_2897_ = v___y_2959_;
v___y_2898_ = v_s_2960_;
goto v___jp_2896_;
}
v___jp_2961_:
{
if (v_a_2963_ == 0)
{
v___y_2959_ = v___y_2962_;
goto v___jp_2958_;
}
else
{
if (v_force_2887_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_url_2895_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_scope_2886_);
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
else
{
v___y_2959_ = v___y_2962_;
goto v___jp_2958_;
}
}
}
v___jp_2968_:
{
lean_object* v_path_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_path_2970_ = l_System_FilePath_join(v___x_2967_, v___y_2969_);
v___x_2971_ = l_System_FilePath_pathExists(v_path_2970_);
v___x_2972_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_2973_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_2973_ == 0)
{
v___y_2962_ = v_path_2970_;
v_a_2963_ = v___x_2971_;
goto v___jp_2961_;
}
else
{
lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_2975_ == 0)
{
if (v___x_2973_ == 0)
{
v___y_2962_ = v_path_2970_;
v_a_2963_ = v___x_2971_;
goto v___jp_2961_;
}
else
{
size_t v___x_2976_; size_t v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = ((size_t)0ULL);
v___x_2977_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_2888_);
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_2972_, v___x_2976_, v___x_2977_, v___x_2974_, v_a_2888_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_dec_ref(v___x_2978_);
v___y_2962_ = v_path_2970_;
v_a_2963_ = v___x_2971_;
goto v___jp_2961_;
}
else
{
lean_dec_ref(v_path_2970_);
lean_dec_ref(v_url_2895_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_scope_2886_);
return v___x_2978_;
}
}
}
else
{
size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = ((size_t)0ULL);
v___x_2980_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_2888_);
v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_2972_, v___x_2979_, v___x_2980_, v___x_2974_, v_a_2888_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_dec_ref(v___x_2981_);
v___y_2962_ = v_path_2970_;
v_a_2963_ = v___x_2971_;
goto v___jp_2961_;
}
else
{
lean_dec_ref(v_path_2970_);
lean_dec_ref(v_url_2895_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_scope_2886_);
return v___x_2981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_2990_, lean_object* v_cache_2991_, lean_object* v_service_2992_, lean_object* v_scope_2993_, lean_object* v_force_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
uint8_t v_force_boxed_2997_; lean_object* v_res_2998_; 
v_force_boxed_2997_ = lean_unbox(v_force_2994_);
v_res_2998_ = l_Lake_CacheService_downloadArtifact(v_descr_2990_, v_cache_2991_, v_service_2992_, v_scope_2993_, v_force_boxed_2997_, v_a_2995_);
lean_dec_ref(v_descr_2990_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object* v___y_2999_, lean_object* v_descr_3000_, lean_object* v_cache_3001_, lean_object* v_service_3002_, lean_object* v_scope_3003_, uint8_t v_force_3004_){
_start:
{
uint64_t v_hash_3009_; lean_object* v_ext_3010_; lean_object* v_url_3011_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3075_; lean_object* v___y_3078_; uint8_t v_a_3079_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___y_3085_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_hash_3009_ = lean_ctor_get_uint64(v_descr_3000_, sizeof(void*)*1);
v_ext_3010_ = lean_ctor_get(v_descr_3000_, 0);
lean_inc_ref(v_scope_3003_);
v_url_3011_ = l_Lake_CacheService_artifactUrl(v_hash_3009_, v_service_3002_, v_scope_3003_);
v___x_3082_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3083_ = l_System_FilePath_join(v_cache_3001_, v___x_3082_);
v___x_3098_ = lean_string_utf8_byte_size(v_ext_3010_);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_nat_dec_eq(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3101_ = l_Lake_Hash_hex(v_hash_3009_);
v___x_3102_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3103_ = lean_string_append(v___x_3101_, v___x_3102_);
v___x_3104_ = lean_string_append(v___x_3103_, v_ext_3010_);
v___y_3085_ = v___x_3104_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lake_Hash_hex(v_hash_3009_);
v___y_3085_ = v___x_3105_;
goto v___jp_3084_;
}
v___jp_3006_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
v___jp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3015_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3016_ = lean_string_append(v___y_3014_, v___x_3015_);
v___x_3017_ = l_Lake_Hash_hex(v_hash_3009_);
v___x_3018_ = lean_string_append(v___x_3016_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3020_ = lean_string_append(v___x_3018_, v___x_3019_);
v___x_3021_ = lean_string_append(v___x_3020_, v___y_3013_);
v___x_3022_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3023_ = lean_string_append(v___x_3021_, v___x_3022_);
v___x_3024_ = lean_string_append(v___x_3023_, v_url_3011_);
v___x_3025_ = 1;
v___x_3026_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*1, v___x_3025_);
lean_inc_ref(v___y_2999_);
v___x_3027_ = lean_apply_2(v___y_2999_, v___x_3026_, lean_box(0));
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3030_ = l_Lake_downloadArtifactCore(v_hash_3009_, v_url_3011_, v___y_3013_, v___x_3029_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_a_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
v_a_3032_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3030_);
v___x_3033_ = lean_array_get_size(v_a_3032_);
v___x_3034_ = lean_nat_dec_lt(v___x_3028_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
lean_dec(v_a_3032_);
lean_dec_ref(v___y_2999_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_a_3031_);
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_nat_dec_le(v___x_3033_, v___x_3033_);
if (v___x_3037_ == 0)
{
if (v___x_3034_ == 0)
{
lean_object* v___x_3038_; 
lean_dec(v_a_3032_);
lean_dec_ref(v___y_2999_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_a_3031_);
return v___x_3038_;
}
else
{
size_t v___x_3039_; size_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = lean_usize_of_nat(v___x_3033_);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3032_, v___x_3039_, v___x_3040_, v___x_3036_, v___y_2999_);
lean_dec(v_a_3032_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v___x_3041_, 0);
lean_dec(v_unused_3049_);
v___x_3043_ = v___x_3041_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v___x_3041_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_a_3031_);
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3031_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_dec(v_a_3031_);
return v___x_3041_;
}
}
}
else
{
size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = lean_usize_of_nat(v___x_3033_);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3032_, v___x_3050_, v___x_3051_, v___x_3036_, v___y_2999_);
lean_dec(v_a_3032_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3060_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v_a_3031_);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3031_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_dec(v_a_3031_);
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_a_3061_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_a_3061_);
lean_dec_ref(v___x_3030_);
v___x_3062_ = lean_array_get_size(v_a_3061_);
v___x_3063_ = lean_nat_dec_lt(v___x_3028_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_a_3061_);
lean_dec_ref(v___y_2999_);
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_nat_dec_le(v___x_3062_, v___x_3062_);
if (v___x_3067_ == 0)
{
if (v___x_3063_ == 0)
{
lean_dec(v_a_3061_);
lean_dec_ref(v___y_2999_);
goto v___jp_3006_;
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3062_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3061_, v___x_3068_, v___x_3069_, v___x_3066_, v___y_2999_);
lean_dec(v_a_3061_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_dec_ref(v___x_3070_);
goto v___jp_3006_;
}
else
{
return v___x_3070_;
}
}
}
else
{
size_t v___x_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = lean_usize_of_nat(v___x_3062_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3061_, v___x_3071_, v___x_3072_, v___x_3066_, v___y_2999_);
lean_dec(v_a_3061_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_dec_ref(v___x_3073_);
goto v___jp_3006_;
}
else
{
return v___x_3073_;
}
}
}
}
}
v___jp_3074_:
{
lean_object* v_s_3076_; 
v_s_3076_ = lean_ctor_get(v_scope_3003_, 0);
lean_inc_ref(v_s_3076_);
lean_dec_ref(v_scope_3003_);
v___y_3013_ = v___y_3075_;
v___y_3014_ = v_s_3076_;
goto v___jp_3012_;
}
v___jp_3077_:
{
if (v_a_3079_ == 0)
{
v___y_3075_ = v___y_3078_;
goto v___jp_3074_;
}
else
{
if (v_force_3004_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v___y_3078_);
lean_dec_ref(v_url_3011_);
lean_dec_ref(v_scope_3003_);
lean_dec_ref(v___y_2999_);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
else
{
v___y_3075_ = v___y_3078_;
goto v___jp_3074_;
}
}
}
v___jp_3084_:
{
lean_object* v_path_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_path_3086_ = l_System_FilePath_join(v___x_3083_, v___y_3085_);
v___x_3087_ = l_System_FilePath_pathExists(v_path_3086_);
v___x_3088_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3089_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3089_ == 0)
{
v___y_3078_ = v_path_3086_;
v_a_3079_ = v___x_3087_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3091_ == 0)
{
if (v___x_3089_ == 0)
{
v___y_3078_ = v_path_3086_;
v_a_3079_ = v___x_3087_;
goto v___jp_3077_;
}
else
{
size_t v___x_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((size_t)0ULL);
v___x_3093_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v___y_2999_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3088_, v___x_3092_, v___x_3093_, v___x_3090_, v___y_2999_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_dec_ref(v___x_3094_);
v___y_3078_ = v_path_3086_;
v_a_3079_ = v___x_3087_;
goto v___jp_3077_;
}
else
{
lean_dec_ref(v_path_3086_);
lean_dec_ref(v_url_3011_);
lean_dec_ref(v_scope_3003_);
lean_dec_ref(v___y_2999_);
return v___x_3094_;
}
}
}
else
{
size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v___y_2999_);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3088_, v___x_3095_, v___x_3096_, v___x_3090_, v___y_2999_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_dec_ref(v___x_3097_);
v___y_3078_ = v_path_3086_;
v_a_3079_ = v___x_3087_;
goto v___jp_3077_;
}
else
{
lean_dec_ref(v_path_3086_);
lean_dec_ref(v_url_3011_);
lean_dec_ref(v_scope_3003_);
lean_dec_ref(v___y_2999_);
return v___x_3097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object* v___y_3106_, lean_object* v_descr_3107_, lean_object* v_cache_3108_, lean_object* v_service_3109_, lean_object* v_scope_3110_, lean_object* v_force_3111_, lean_object* v_a_3112_){
_start:
{
uint8_t v_force_boxed_3113_; lean_object* v_res_3114_; 
v_force_boxed_3113_ = lean_unbox(v_force_3111_);
v_res_3114_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3106_, v_descr_3107_, v_cache_3108_, v_service_3109_, v_scope_3110_, v_force_boxed_3113_);
lean_dec_ref(v_descr_3107_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object* v_cache_3115_, lean_object* v_service_3116_, lean_object* v_scope_3117_, uint8_t v_force_3118_, uint8_t v_ok_3119_, lean_object* v_descr_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3121_, v_descr_3120_, v_cache_3115_, v_service_3116_, v_scope_3117_, v_force_3118_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3131_; 
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v___x_3123_, 0);
lean_dec(v_unused_3132_);
v___x_3125_ = v___x_3123_;
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
else
{
lean_dec(v___x_3123_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = lean_box(v_ok_3119_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
else
{
lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3141_; 
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3123_, 0);
lean_dec(v_unused_3142_);
v___x_3134_ = v___x_3123_;
v_isShared_3135_ = v_isSharedCheck_3141_;
goto v_resetjp_3133_;
}
else
{
lean_dec(v___x_3123_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3141_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3136_ = 0;
v___x_3137_ = lean_box(v___x_3136_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3137_);
v___x_3139_ = v___x_3134_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object* v_cache_3143_, lean_object* v_service_3144_, lean_object* v_scope_3145_, lean_object* v_force_3146_, lean_object* v_ok_3147_, lean_object* v_descr_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
uint8_t v_force_boxed_3151_; uint8_t v_ok_boxed_3152_; lean_object* v_res_3153_; 
v_force_boxed_3151_ = lean_unbox(v_force_3146_);
v_ok_boxed_3152_ = lean_unbox(v_ok_3147_);
v_res_3153_ = l_Lake_CacheService_downloadArtifacts___elam__0(v_cache_3143_, v_service_3144_, v_scope_3145_, v_force_boxed_3151_, v_ok_boxed_3152_, v_descr_3148_, v___y_3149_);
lean_dec_ref(v_descr_3148_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(lean_object* v___y_3154_, lean_object* v_cache_3155_, lean_object* v_service_3156_, lean_object* v_scope_3157_, uint8_t v_force_3158_, uint8_t v_ok_3159_, lean_object* v_descr_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3154_, v_descr_3160_, v_cache_3155_, v_service_3156_, v_scope_3157_, v_force_3158_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3170_; 
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v___x_3162_, 0);
lean_dec(v_unused_3171_);
v___x_3164_ = v___x_3162_;
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v___x_3162_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_box(v_ok_3159_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3166_);
v___x_3168_ = v___x_3164_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
else
{
lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3180_; 
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3162_, 0);
lean_dec(v_unused_3181_);
v___x_3173_ = v___x_3162_;
v_isShared_3174_ = v_isSharedCheck_3180_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v___x_3162_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3180_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3175_ = 0;
v___x_3176_ = lean_box(v___x_3175_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3176_);
v___x_3178_ = v___x_3173_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2___boxed(lean_object* v___y_3182_, lean_object* v_cache_3183_, lean_object* v_service_3184_, lean_object* v_scope_3185_, lean_object* v_force_3186_, lean_object* v_ok_3187_, lean_object* v_descr_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v_force_boxed_3190_; uint8_t v_ok_boxed_3191_; lean_object* v_res_3192_; 
v_force_boxed_3190_ = lean_unbox(v_force_3186_);
v_ok_boxed_3191_ = lean_unbox(v_ok_3187_);
v_res_3192_ = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(v___y_3182_, v_cache_3183_, v_service_3184_, v_scope_3185_, v_force_boxed_3190_, v_ok_boxed_3191_, v_descr_3188_);
lean_dec_ref(v_descr_3188_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object* v_cache_3193_, lean_object* v_service_3194_, lean_object* v_scope_3195_, uint8_t v_force_3196_, lean_object* v_as_3197_, size_t v_i_3198_, size_t v_stop_3199_, uint8_t v_b_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_usize_dec_eq(v_i_3198_, v_stop_3199_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_array_uget_borrowed(v_as_3197_, v_i_3198_);
lean_inc_ref(v_scope_3195_);
lean_inc_ref(v_service_3194_);
lean_inc_ref(v_cache_3193_);
lean_inc_ref(v___y_3201_);
v___x_3205_ = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(v___y_3201_, v_cache_3193_, v_service_3194_, v_scope_3195_, v_force_3196_, v_b_3200_, v___x_3204_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; size_t v___x_3207_; size_t v___x_3208_; uint8_t v___x_3209_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = ((size_t)1ULL);
v___x_3208_ = lean_usize_add(v_i_3198_, v___x_3207_);
v___x_3209_ = lean_unbox(v_a_3206_);
lean_dec(v_a_3206_);
v_i_3198_ = v___x_3208_;
v_b_3200_ = v___x_3209_;
goto _start;
}
else
{
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_scope_3195_);
lean_dec_ref(v_service_3194_);
lean_dec_ref(v_cache_3193_);
return v___x_3205_;
}
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_scope_3195_);
lean_dec_ref(v_service_3194_);
lean_dec_ref(v_cache_3193_);
v___x_3211_ = lean_box(v_b_3200_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_cache_3213_, lean_object* v_service_3214_, lean_object* v_scope_3215_, lean_object* v_force_3216_, lean_object* v_as_3217_, lean_object* v_i_3218_, lean_object* v_stop_3219_, lean_object* v_b_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v_force_boxed_3223_; size_t v_i_boxed_3224_; size_t v_stop_boxed_3225_; uint8_t v_b_boxed_3226_; lean_object* v_res_3227_; 
v_force_boxed_3223_ = lean_unbox(v_force_3216_);
v_i_boxed_3224_ = lean_unbox_usize(v_i_3218_);
lean_dec(v_i_3218_);
v_stop_boxed_3225_ = lean_unbox_usize(v_stop_3219_);
lean_dec(v_stop_3219_);
v_b_boxed_3226_ = lean_unbox(v_b_3220_);
v_res_3227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3213_, v_service_3214_, v_scope_3215_, v_force_boxed_3223_, v_as_3217_, v_i_boxed_3224_, v_stop_boxed_3225_, v_b_boxed_3226_, v___y_3221_);
lean_dec_ref(v_as_3217_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_3229_, lean_object* v_cache_3230_, lean_object* v_service_3231_, lean_object* v_scope_3232_, uint8_t v_force_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___y_3240_; lean_object* v___y_3249_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = lean_array_get_size(v_descrs_3229_);
v___x_3263_ = lean_nat_dec_lt(v___x_3261_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_dec_ref(v_a_3234_);
lean_dec_ref(v_scope_3232_);
lean_dec_ref(v_service_3231_);
lean_dec_ref(v_cache_3230_);
goto v___jp_3236_;
}
else
{
uint8_t v___x_3264_; 
v___x_3264_ = lean_nat_dec_le(v___x_3262_, v___x_3262_);
if (v___x_3264_ == 0)
{
if (v___x_3263_ == 0)
{
lean_dec_ref(v_a_3234_);
lean_dec_ref(v_scope_3232_);
lean_dec_ref(v_service_3231_);
lean_dec_ref(v_cache_3230_);
goto v___jp_3236_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = lean_usize_of_nat(v___x_3262_);
lean_inc_ref(v_a_3234_);
lean_inc_ref(v_scope_3232_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3230_, v_service_3231_, v_scope_3232_, v_force_3233_, v_descrs_3229_, v___x_3265_, v___x_3266_, v___x_3263_, v_a_3234_);
v___y_3249_ = v___x_3267_;
goto v___jp_3248_;
}
}
else
{
size_t v___x_3268_; size_t v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = ((size_t)0ULL);
v___x_3269_ = lean_usize_of_nat(v___x_3262_);
lean_inc_ref(v_a_3234_);
lean_inc_ref(v_scope_3232_);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3230_, v_service_3231_, v_scope_3232_, v_force_3233_, v_descrs_3229_, v___x_3268_, v___x_3269_, v___x_3263_, v_a_3234_);
v___y_3249_ = v___x_3270_;
goto v___jp_3248_;
}
}
v___jp_3236_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
v___jp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3241_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_3242_ = lean_string_append(v___y_3240_, v___x_3241_);
v___x_3243_ = 3;
v___x_3244_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*1, v___x_3243_);
v___x_3245_ = lean_apply_2(v_a_3234_, v___x_3244_, lean_box(0));
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
v___jp_3248_:
{
if (lean_obj_tag(v___y_3249_) == 0)
{
lean_object* v_a_3250_; uint8_t v___x_3251_; 
v_a_3250_ = lean_ctor_get(v___y_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___y_3249_);
v___x_3251_ = lean_unbox(v_a_3250_);
lean_dec(v_a_3250_);
if (v___x_3251_ == 0)
{
lean_object* v_s_3252_; 
v_s_3252_ = lean_ctor_get(v_scope_3232_, 0);
lean_inc_ref(v_s_3252_);
lean_dec_ref(v_scope_3232_);
v___y_3240_ = v_s_3252_;
goto v___jp_3239_;
}
else
{
lean_dec_ref(v_a_3234_);
lean_dec_ref(v_scope_3232_);
goto v___jp_3236_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v_a_3234_);
lean_dec_ref(v_scope_3232_);
v_a_3253_ = lean_ctor_get(v___y_3249_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___y_3249_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___y_3249_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___y_3249_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_3271_, lean_object* v_cache_3272_, lean_object* v_service_3273_, lean_object* v_scope_3274_, lean_object* v_force_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
uint8_t v_force_boxed_3278_; lean_object* v_res_3279_; 
v_force_boxed_3278_ = lean_unbox(v_force_3275_);
v_res_3279_ = l_Lake_CacheService_downloadArtifacts(v_descrs_3271_, v_cache_3272_, v_service_3273_, v_scope_3274_, v_force_boxed_3278_, v_a_3276_);
lean_dec_ref(v_descrs_3271_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_3280_, lean_object* v_descrs_3281_, lean_object* v_cache_3282_, lean_object* v_service_3283_, lean_object* v_scope_3284_, uint8_t v_force_3285_){
_start:
{
lean_object* v___y_3291_; lean_object* v___y_3300_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3312_ = lean_unsigned_to_nat(0u);
v___x_3313_ = lean_array_get_size(v_descrs_3281_);
v___x_3314_ = lean_nat_dec_lt(v___x_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v_scope_3284_);
lean_dec_ref(v_service_3283_);
lean_dec_ref(v_cache_3282_);
lean_dec_ref(v_a_3280_);
goto v___jp_3287_;
}
else
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_nat_dec_le(v___x_3313_, v___x_3313_);
if (v___x_3315_ == 0)
{
if (v___x_3314_ == 0)
{
lean_dec_ref(v_scope_3284_);
lean_dec_ref(v_service_3283_);
lean_dec_ref(v_cache_3282_);
lean_dec_ref(v_a_3280_);
goto v___jp_3287_;
}
else
{
size_t v___x_3316_; size_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = ((size_t)0ULL);
v___x_3317_ = lean_usize_of_nat(v___x_3313_);
lean_inc_ref(v_a_3280_);
lean_inc_ref(v_scope_3284_);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3282_, v_service_3283_, v_scope_3284_, v_force_3285_, v_descrs_3281_, v___x_3316_, v___x_3317_, v___x_3314_, v_a_3280_);
v___y_3300_ = v___x_3318_;
goto v___jp_3299_;
}
}
else
{
size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = ((size_t)0ULL);
v___x_3320_ = lean_usize_of_nat(v___x_3313_);
lean_inc_ref(v_a_3280_);
lean_inc_ref(v_scope_3284_);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3282_, v_service_3283_, v_scope_3284_, v_force_3285_, v_descrs_3281_, v___x_3319_, v___x_3320_, v___x_3314_, v_a_3280_);
v___y_3300_ = v___x_3321_;
goto v___jp_3299_;
}
}
v___jp_3287_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = lean_box(0);
v___x_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
return v___x_3289_;
}
v___jp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3292_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_3293_ = lean_string_append(v___y_3291_, v___x_3292_);
v___x_3294_ = 3;
v___x_3295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*1, v___x_3294_);
v___x_3296_ = lean_apply_2(v_a_3280_, v___x_3295_, lean_box(0));
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
v___jp_3299_:
{
if (lean_obj_tag(v___y_3300_) == 0)
{
lean_object* v_a_3301_; uint8_t v___x_3302_; 
v_a_3301_ = lean_ctor_get(v___y_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref(v___y_3300_);
v___x_3302_ = lean_unbox(v_a_3301_);
lean_dec(v_a_3301_);
if (v___x_3302_ == 0)
{
lean_object* v_s_3303_; 
v_s_3303_ = lean_ctor_get(v_scope_3284_, 0);
lean_inc_ref(v_s_3303_);
lean_dec_ref(v_scope_3284_);
v___y_3291_ = v_s_3303_;
goto v___jp_3290_;
}
else
{
lean_dec_ref(v_scope_3284_);
lean_dec_ref(v_a_3280_);
goto v___jp_3287_;
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref(v_scope_3284_);
lean_dec_ref(v_a_3280_);
v_a_3304_ = lean_ctor_get(v___y_3300_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___y_3300_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___y_3300_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___y_3300_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_3322_, lean_object* v_descrs_3323_, lean_object* v_cache_3324_, lean_object* v_service_3325_, lean_object* v_scope_3326_, lean_object* v_force_3327_, lean_object* v_a_3328_){
_start:
{
uint8_t v_force_boxed_3329_; lean_object* v_res_3330_; 
v_force_boxed_3329_ = lean_unbox(v_force_3327_);
v_res_3330_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3322_, v_descrs_3323_, v_cache_3324_, v_service_3325_, v_scope_3326_, v_force_boxed_3329_);
lean_dec_ref(v_descrs_3323_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_3331_, lean_object* v_cache_3332_, lean_object* v_service_3333_, lean_object* v_localScope_3334_, lean_object* v_remoteScope_3335_, uint8_t v_force_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_name_x3f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_name_x3f_3342_ = lean_ctor_get(v_service_3333_, 0);
lean_inc_ref(v_remoteScope_3335_);
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_remoteScope_3335_);
lean_inc(v_name_x3f_3342_);
lean_inc_ref(v_cache_3332_);
v___x_3344_ = l_Lake_Cache_writeMap(v_cache_3332_, v_localScope_3334_, v_map_3331_, v_name_x3f_3342_, v___x_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3382_; 
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; 
v_unused_3383_ = lean_ctor_get(v___x_3344_, 0);
lean_dec(v_unused_3383_);
v___x_3346_ = v___x_3344_;
v_isShared_3347_ = v_isSharedCheck_3382_;
goto v_resetjp_3345_;
}
else
{
lean_dec(v___x_3344_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3382_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3350_ = l_Lake_CacheMap_collectOutputDescrs(v_map_3331_, v___x_3349_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v_a_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
lean_del_object(v___x_3346_);
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
v_a_3352_ = lean_ctor_get(v___x_3350_, 1);
lean_inc(v_a_3352_);
lean_dec_ref(v___x_3350_);
v___x_3353_ = lean_array_get_size(v_a_3352_);
v___x_3354_ = lean_nat_dec_lt(v___x_3348_, v___x_3353_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v_a_3352_);
v___x_3355_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3337_, v_a_3351_, v_cache_3332_, v_service_3333_, v_remoteScope_3335_, v_force_3336_);
lean_dec(v_a_3351_);
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_nat_dec_le(v___x_3353_, v___x_3353_);
if (v___x_3357_ == 0)
{
if (v___x_3354_ == 0)
{
lean_object* v___x_3358_; 
lean_dec(v_a_3352_);
v___x_3358_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3337_, v_a_3351_, v_cache_3332_, v_service_3333_, v_remoteScope_3335_, v_force_3336_);
lean_dec(v_a_3351_);
return v___x_3358_;
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3353_);
lean_inc_ref(v_a_3337_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3352_, v___x_3359_, v___x_3360_, v___x_3356_, v_a_3337_);
lean_dec(v_a_3352_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref(v___x_3361_);
v___x_3362_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3337_, v_a_3351_, v_cache_3332_, v_service_3333_, v_remoteScope_3335_, v_force_3336_);
lean_dec(v_a_3351_);
return v___x_3362_;
}
else
{
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3337_);
lean_dec_ref(v_remoteScope_3335_);
lean_dec_ref(v_service_3333_);
lean_dec_ref(v_cache_3332_);
return v___x_3361_;
}
}
}
else
{
size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((size_t)0ULL);
v___x_3364_ = lean_usize_of_nat(v___x_3353_);
lean_inc_ref(v_a_3337_);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3352_, v___x_3363_, v___x_3364_, v___x_3356_, v_a_3337_);
lean_dec(v_a_3352_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref(v___x_3365_);
v___x_3366_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3337_, v_a_3351_, v_cache_3332_, v_service_3333_, v_remoteScope_3335_, v_force_3336_);
lean_dec(v_a_3351_);
return v___x_3366_;
}
else
{
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3337_);
lean_dec_ref(v_remoteScope_3335_);
lean_dec_ref(v_service_3333_);
lean_dec_ref(v_cache_3332_);
return v___x_3365_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
lean_dec_ref(v_remoteScope_3335_);
lean_dec_ref(v_service_3333_);
lean_dec_ref(v_cache_3332_);
v_a_3367_ = lean_ctor_get(v___x_3350_, 1);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3350_);
v___x_3368_ = lean_array_get_size(v_a_3367_);
v___x_3369_ = lean_nat_dec_lt(v___x_3348_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3337_);
v___x_3370_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 1);
lean_ctor_set(v___x_3346_, 0, v___x_3370_);
v___x_3372_ = v___x_3346_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
else
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
lean_del_object(v___x_3346_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_nat_dec_le(v___x_3368_, v___x_3368_);
if (v___x_3375_ == 0)
{
if (v___x_3369_ == 0)
{
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3337_);
goto v___jp_3339_;
}
else
{
size_t v___x_3376_; size_t v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = ((size_t)0ULL);
v___x_3377_ = lean_usize_of_nat(v___x_3368_);
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3367_, v___x_3376_, v___x_3377_, v___x_3374_, v_a_3337_);
lean_dec(v_a_3367_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec_ref(v___x_3378_);
goto v___jp_3339_;
}
else
{
return v___x_3378_;
}
}
}
else
{
size_t v___x_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = ((size_t)0ULL);
v___x_3380_ = lean_usize_of_nat(v___x_3368_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3367_, v___x_3379_, v___x_3380_, v___x_3374_, v_a_3337_);
lean_dec(v_a_3367_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_dec_ref(v___x_3381_);
goto v___jp_3339_;
}
else
{
return v___x_3381_;
}
}
}
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_remoteScope_3335_);
lean_dec_ref(v_service_3333_);
lean_dec_ref(v_cache_3332_);
lean_dec_ref(v_map_3331_);
v_a_3384_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3386_ = v___x_3344_;
v_isShared_3387_ = v_isSharedCheck_3396_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3344_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3396_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3388_ = lean_io_error_to_string(v_a_3384_);
v___x_3389_ = 3;
v___x_3390_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set_uint8(v___x_3390_, sizeof(void*)*1, v___x_3389_);
v___x_3391_ = lean_apply_2(v_a_3337_, v___x_3390_, lean_box(0));
v___x_3392_ = lean_box(0);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3392_);
v___x_3394_ = v___x_3386_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
v___jp_3339_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_3397_, lean_object* v_cache_3398_, lean_object* v_service_3399_, lean_object* v_localScope_3400_, lean_object* v_remoteScope_3401_, lean_object* v_force_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
uint8_t v_force_boxed_3405_; lean_object* v_res_3406_; 
v_force_boxed_3405_ = lean_unbox(v_force_3402_);
v_res_3406_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_3397_, v_cache_3398_, v_service_3399_, v_localScope_3400_, v_remoteScope_3401_, v_force_boxed_3405_, v_a_3403_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3407_, lean_object* v_file_3408_, lean_object* v_contentType_3409_, lean_object* v_url_3410_, lean_object* v_key_3411_){
_start:
{
lean_object* v___y_3414_; lean_object* v_a_3415_; lean_object* v_stderr_3428_; lean_object* v___y_3437_; lean_object* v___y_3440_; lean_object* v_a_3441_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v_stderr_3480_; lean_object* v_a_3481_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3495_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3496_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3497_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3498_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3499_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3500_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3501_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3502_ = lean_string_append(v___x_3501_, v_contentType_3409_);
v___x_3503_ = lean_unsigned_to_nat(14u);
v___x_3504_ = lean_mk_empty_array_with_capacity(v___x_3503_);
lean_dec_ref(v___x_3504_);
v___x_3505_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3506_ = lean_array_push(v___x_3505_, v_key_3411_);
v___x_3507_ = lean_array_push(v___x_3506_, v___x_3497_);
v___x_3508_ = lean_array_push(v___x_3507_, v___x_3498_);
v___x_3509_ = lean_array_push(v___x_3508_, v___x_3499_);
v___x_3510_ = lean_array_push(v___x_3509_, v_file_3408_);
v___x_3511_ = lean_array_push(v___x_3510_, v_url_3410_);
v___x_3512_ = lean_array_push(v___x_3511_, v___x_3500_);
v___x_3513_ = lean_array_push(v___x_3512_, v___x_3502_);
v___x_3514_ = lean_box(0);
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3517_ = 1;
v___x_3518_ = 0;
v___x_3519_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3519_, 0, v___x_3495_);
lean_ctor_set(v___x_3519_, 1, v___x_3496_);
lean_ctor_set(v___x_3519_, 2, v___x_3513_);
lean_ctor_set(v___x_3519_, 3, v___x_3514_);
lean_ctor_set(v___x_3519_, 4, v___x_3516_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*5, v___x_3517_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*5 + 1, v___x_3518_);
v___x_3520_ = l_Lake_captureProc_x27(v___x_3519_, v___x_3516_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_a_3522_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
v_a_3522_ = lean_ctor_get(v___x_3520_, 1);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3520_);
v___x_3536_ = lean_array_get_size(v_a_3522_);
v___x_3537_ = lean_nat_dec_lt(v___x_3515_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_dec(v_a_3522_);
goto v___jp_3523_;
}
else
{
lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3538_ = lean_box(0);
v___x_3539_ = lean_nat_dec_le(v___x_3536_, v___x_3536_);
if (v___x_3539_ == 0)
{
if (v___x_3537_ == 0)
{
lean_dec(v_a_3522_);
goto v___jp_3523_;
}
else
{
size_t v___x_3540_; size_t v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = ((size_t)0ULL);
v___x_3541_ = lean_usize_of_nat(v___x_3536_);
lean_inc_ref(v_a_3407_);
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3522_, v___x_3540_, v___x_3541_, v___x_3538_, v_a_3407_);
lean_dec(v_a_3522_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_dec_ref(v___x_3542_);
goto v___jp_3523_;
}
else
{
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3407_);
return v___x_3542_;
}
}
}
else
{
size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = lean_usize_of_nat(v___x_3536_);
lean_inc_ref(v_a_3407_);
v___x_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3522_, v___x_3543_, v___x_3544_, v___x_3538_, v_a_3407_);
lean_dec(v_a_3522_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_dec_ref(v___x_3545_);
goto v___jp_3523_;
}
else
{
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3407_);
return v___x_3545_;
}
}
}
v___jp_3523_:
{
lean_object* v_stderr_3524_; lean_object* v___x_3525_; 
v_stderr_3524_ = lean_ctor_get(v_a_3521_, 1);
lean_inc_ref(v_stderr_3524_);
v___x_3525_ = l_Lean_Json_parse(v_stderr_3524_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; 
lean_inc_ref(v_stderr_3524_);
lean_dec(v_a_3521_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
v_stderr_3480_ = v_stderr_3524_;
v_a_3481_ = v_a_3526_;
goto v___jp_3479_;
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3525_);
v___x_3528_ = l_Lean_Json_getObj_x3f(v_a_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; 
lean_inc_ref(v_stderr_3524_);
lean_dec(v_a_3521_);
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3528_);
v_stderr_3480_ = v_stderr_3524_;
v_a_3481_ = v_a_3529_;
goto v___jp_3479_;
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v_a_3530_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v___x_3528_);
v___x_3531_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3532_ = l_Lake_JsonObject_getJson_x3f(v_a_3530_, v___x_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_inc_ref(v_stderr_3524_);
lean_dec(v_a_3530_);
lean_dec(v_a_3521_);
v_stderr_3428_ = v_stderr_3524_;
goto v___jp_3427_;
}
else
{
lean_object* v_val_3533_; lean_object* v___x_3534_; 
v_val_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_val_3533_);
lean_dec_ref(v___x_3532_);
v___x_3534_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3533_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_dec_ref(v___x_3534_);
v___y_3468_ = v_a_3521_;
v___y_3469_ = v_a_3530_;
goto v___jp_3467_;
}
else
{
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_dec_ref(v___x_3534_);
v___y_3468_ = v_a_3521_;
v___y_3469_ = v_a_3530_;
goto v___jp_3467_;
}
else
{
lean_object* v_a_3535_; 
lean_dec(v_a_3530_);
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3534_);
v___y_3440_ = v_a_3521_;
v_a_3441_ = v_a_3535_;
goto v___jp_3439_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_a_3546_ = lean_ctor_get(v___x_3520_, 1);
lean_inc(v_a_3546_);
lean_dec_ref(v___x_3520_);
v___x_3547_ = lean_array_get_size(v_a_3546_);
v___x_3548_ = lean_nat_dec_lt(v___x_3515_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3407_);
v___x_3549_ = lean_box(0);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; uint8_t v___x_3552_; 
v___x_3551_ = lean_box(0);
v___x_3552_ = lean_nat_dec_le(v___x_3547_, v___x_3547_);
if (v___x_3552_ == 0)
{
if (v___x_3548_ == 0)
{
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3407_);
goto v___jp_3492_;
}
else
{
size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((size_t)0ULL);
v___x_3554_ = lean_usize_of_nat(v___x_3547_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3546_, v___x_3553_, v___x_3554_, v___x_3551_, v_a_3407_);
lean_dec(v_a_3546_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_dec_ref(v___x_3555_);
goto v___jp_3492_;
}
else
{
return v___x_3555_;
}
}
}
else
{
size_t v___x_3556_; size_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = ((size_t)0ULL);
v___x_3557_ = lean_usize_of_nat(v___x_3547_);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3546_, v___x_3556_, v___x_3557_, v___x_3551_, v_a_3407_);
lean_dec(v_a_3546_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_dec_ref(v___x_3558_);
goto v___jp_3492_;
}
else
{
return v___x_3558_;
}
}
}
}
v___jp_3413_:
{
lean_object* v_stderr_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_stderr_3416_ = lean_ctor_get(v___y_3414_, 1);
lean_inc_ref(v_stderr_3416_);
lean_dec_ref(v___y_3414_);
v___x_3417_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3418_ = lean_string_append(v___x_3417_, v_a_3415_);
lean_dec_ref(v_a_3415_);
v___x_3419_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3420_ = lean_string_append(v___x_3418_, v___x_3419_);
v___x_3421_ = lean_string_append(v___x_3420_, v_stderr_3416_);
lean_dec_ref(v_stderr_3416_);
v___x_3422_ = 3;
v___x_3423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*1, v___x_3422_);
v___x_3424_ = lean_apply_2(v_a_3407_, v___x_3423_, lean_box(0));
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
return v___x_3426_;
}
v___jp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3429_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3430_ = lean_string_append(v___x_3429_, v_stderr_3428_);
lean_dec_ref(v_stderr_3428_);
v___x_3431_ = 3;
v___x_3432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*1, v___x_3431_);
v___x_3433_ = lean_apply_2(v_a_3407_, v___x_3432_, lean_box(0));
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
v___jp_3436_:
{
lean_object* v_stderr_3438_; 
v_stderr_3438_ = lean_ctor_get(v___y_3437_, 1);
lean_inc_ref(v_stderr_3438_);
lean_dec_ref(v___y_3437_);
v_stderr_3428_ = v_stderr_3438_;
goto v___jp_3427_;
}
v___jp_3439_:
{
if (lean_obj_tag(v_a_3441_) == 0)
{
v___y_3437_ = v___y_3440_;
goto v___jp_3436_;
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3466_; 
v_val_3442_ = lean_ctor_get(v_a_3441_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_a_3441_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3444_ = v_a_3441_;
v_isShared_3445_ = v_isSharedCheck_3466_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_val_3442_);
lean_dec(v_a_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3466_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(200u);
v___x_3447_ = lean_nat_dec_eq(v_val_3442_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v_stdout_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v_stdout_3448_ = lean_ctor_get(v___y_3440_, 0);
lean_inc_ref(v_stdout_3448_);
lean_dec_ref(v___y_3440_);
v___x_3449_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3450_ = l_Nat_reprFast(v_val_3442_);
v___x_3451_ = lean_string_append(v___x_3449_, v___x_3450_);
lean_dec_ref(v___x_3450_);
v___x_3452_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3453_ = lean_string_append(v___x_3451_, v___x_3452_);
v___x_3454_ = lean_string_append(v___x_3453_, v_stdout_3448_);
lean_dec_ref(v_stdout_3448_);
v___x_3455_ = 3;
v___x_3456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*1, v___x_3455_);
v___x_3457_ = lean_apply_2(v_a_3407_, v___x_3456_, lean_box(0));
v___x_3458_ = lean_box(0);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3458_);
v___x_3460_ = v___x_3444_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec(v_val_3442_);
lean_dec_ref(v___y_3440_);
lean_dec_ref(v_a_3407_);
v___x_3462_ = lean_box(0);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3462_);
v___x_3464_ = v___x_3444_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
v___jp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3471_ = l_Lake_JsonObject_getJson_x3f(v___y_3469_, v___x_3470_);
lean_dec(v___y_3469_);
if (lean_obj_tag(v___x_3471_) == 0)
{
v___y_3437_ = v___y_3468_;
goto v___jp_3436_;
}
else
{
lean_object* v_val_3472_; lean_object* v___x_3473_; 
v_val_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_val_3472_);
lean_dec_ref(v___x_3471_);
v___x_3473_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3472_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3476_ = lean_string_append(v___x_3475_, v_a_3474_);
lean_dec(v_a_3474_);
v___y_3414_ = v___y_3468_;
v_a_3415_ = v___x_3476_;
goto v___jp_3413_;
}
else
{
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3477_);
lean_dec_ref(v___x_3473_);
v___y_3414_ = v___y_3468_;
v_a_3415_ = v_a_3477_;
goto v___jp_3413_;
}
else
{
lean_object* v_a_3478_; 
v_a_3478_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3473_);
v___y_3440_ = v___y_3468_;
v_a_3441_ = v_a_3478_;
goto v___jp_3439_;
}
}
}
}
v___jp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3482_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3483_ = lean_string_append(v___x_3482_, v_a_3481_);
lean_dec_ref(v_a_3481_);
v___x_3484_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3485_ = lean_string_append(v___x_3483_, v___x_3484_);
v___x_3486_ = lean_string_append(v___x_3485_, v_stderr_3480_);
lean_dec_ref(v_stderr_3480_);
v___x_3487_ = 3;
v___x_3488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3488_, 0, v___x_3486_);
lean_ctor_set_uint8(v___x_3488_, sizeof(void*)*1, v___x_3487_);
v___x_3489_ = lean_apply_2(v_a_3407_, v___x_3488_, lean_box(0));
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
return v___x_3491_;
}
v___jp_3492_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = lean_box(0);
v___x_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3559_, lean_object* v_file_3560_, lean_object* v_contentType_3561_, lean_object* v_url_3562_, lean_object* v_key_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3559_, v_file_3560_, v_contentType_3561_, v_url_3562_, v_key_3563_);
lean_dec_ref(v_contentType_3561_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3567_, lean_object* v_art_3568_, lean_object* v_service_3569_, lean_object* v_scope_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_url_3573_; lean_object* v___y_3575_; lean_object* v_s_3592_; 
lean_inc_ref(v_scope_3570_);
lean_inc_ref(v_service_3569_);
v_url_3573_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3567_, v_service_3569_, v_scope_3570_);
v_s_3592_ = lean_ctor_get(v_scope_3570_, 0);
lean_inc_ref(v_s_3592_);
lean_dec_ref(v_scope_3570_);
v___y_3575_ = v_s_3592_;
goto v___jp_3574_;
v___jp_3574_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_key_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3576_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3577_ = lean_string_append(v___y_3575_, v___x_3576_);
v___x_3578_ = l_Lake_Hash_hex(v_contentHash_3567_);
v___x_3579_ = lean_string_append(v___x_3577_, v___x_3578_);
lean_dec_ref(v___x_3578_);
v___x_3580_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3581_ = lean_string_append(v___x_3579_, v___x_3580_);
v___x_3582_ = lean_string_append(v___x_3581_, v_art_3568_);
v___x_3583_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3584_ = lean_string_append(v___x_3582_, v___x_3583_);
v___x_3585_ = lean_string_append(v___x_3584_, v_url_3573_);
v___x_3586_ = 1;
v___x_3587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set_uint8(v___x_3587_, sizeof(void*)*1, v___x_3586_);
lean_inc_ref(v_a_3571_);
v___x_3588_ = lean_apply_2(v_a_3571_, v___x_3587_, lean_box(0));
v_key_3589_ = lean_ctor_get(v_service_3569_, 1);
lean_inc_ref(v_key_3589_);
lean_dec_ref(v_service_3569_);
v___x_3590_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3591_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3571_, v_art_3568_, v___x_3590_, v_url_3573_, v_key_3589_);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3593_, lean_object* v_art_3594_, lean_object* v_service_3595_, lean_object* v_scope_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
uint64_t v_contentHash_boxed_3599_; lean_object* v_res_3600_; 
v_contentHash_boxed_3599_ = lean_unbox_uint64(v_contentHash_3593_);
lean_dec_ref(v_contentHash_3593_);
v_res_3600_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3599_, v_art_3594_, v_service_3595_, v_scope_3596_, v_a_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object* v___y_3601_, uint64_t v_contentHash_3602_, lean_object* v_art_3603_, lean_object* v_service_3604_, lean_object* v_scope_3605_){
_start:
{
lean_object* v_url_3607_; lean_object* v___y_3609_; lean_object* v_s_3626_; 
lean_inc_ref(v_scope_3605_);
lean_inc_ref(v_service_3604_);
v_url_3607_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3602_, v_service_3604_, v_scope_3605_);
v_s_3626_ = lean_ctor_get(v_scope_3605_, 0);
lean_inc_ref(v_s_3626_);
lean_dec_ref(v_scope_3605_);
v___y_3609_ = v_s_3626_;
goto v___jp_3608_;
v___jp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v_key_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3610_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3611_ = lean_string_append(v___y_3609_, v___x_3610_);
v___x_3612_ = l_Lake_Hash_hex(v_contentHash_3602_);
v___x_3613_ = lean_string_append(v___x_3611_, v___x_3612_);
lean_dec_ref(v___x_3612_);
v___x_3614_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3615_ = lean_string_append(v___x_3613_, v___x_3614_);
v___x_3616_ = lean_string_append(v___x_3615_, v_art_3603_);
v___x_3617_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3618_ = lean_string_append(v___x_3616_, v___x_3617_);
v___x_3619_ = lean_string_append(v___x_3618_, v_url_3607_);
v___x_3620_ = 1;
v___x_3621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set_uint8(v___x_3621_, sizeof(void*)*1, v___x_3620_);
lean_inc_ref(v___y_3601_);
v___x_3622_ = lean_apply_2(v___y_3601_, v___x_3621_, lean_box(0));
v_key_3623_ = lean_ctor_get(v_service_3604_, 1);
lean_inc_ref(v_key_3623_);
lean_dec_ref(v_service_3604_);
v___x_3624_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3625_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v___y_3601_, v_art_3603_, v___x_3624_, v_url_3607_, v_key_3623_);
return v___x_3625_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object* v___y_3627_, lean_object* v_contentHash_3628_, lean_object* v_art_3629_, lean_object* v_service_3630_, lean_object* v_scope_3631_, lean_object* v_a_3632_){
_start:
{
uint64_t v_contentHash_boxed_3633_; lean_object* v_res_3634_; 
v_contentHash_boxed_3633_ = lean_unbox_uint64(v_contentHash_3628_);
lean_dec_ref(v_contentHash_3628_);
v_res_3634_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3627_, v_contentHash_boxed_3633_, v_art_3629_, v_service_3630_, v_scope_3631_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object* v_descrs_3635_, lean_object* v_paths_3636_, lean_object* v_service_3637_, lean_object* v_scope_3638_, lean_object* v_n_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; uint64_t v_hash_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3642_ = lean_array_fget_borrowed(v_descrs_3635_, v_n_3639_);
v_hash_3643_ = lean_ctor_get_uint64(v___x_3642_, sizeof(void*)*1);
v___x_3644_ = lean_array_fget_borrowed(v_paths_3636_, v_n_3639_);
lean_inc(v___x_3644_);
v___x_3645_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3640_, v_hash_3643_, v___x_3644_, v_service_3637_, v_scope_3638_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object* v_descrs_3646_, lean_object* v_paths_3647_, lean_object* v_service_3648_, lean_object* v_scope_3649_, lean_object* v_n_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(v_descrs_3646_, v_paths_3647_, v_service_3648_, v_scope_3649_, v_n_3650_, v___y_3651_);
lean_dec(v_n_3650_);
lean_dec_ref(v_paths_3647_);
lean_dec_ref(v_descrs_3646_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object* v_descrs_3654_, lean_object* v_paths_3655_, lean_object* v_service_3656_, lean_object* v_scope_3657_, lean_object* v_n_3658_, lean_object* v_h_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(v_descrs_3654_, v_paths_3655_, v_service_3656_, v_scope_3657_, v_n_3658_, v___y_3660_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object* v_descrs_3663_, lean_object* v_paths_3664_, lean_object* v_service_3665_, lean_object* v_scope_3666_, lean_object* v_n_3667_, lean_object* v_h_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lake_CacheService_uploadArtifacts___elam__0(v_descrs_3663_, v_paths_3664_, v_service_3665_, v_scope_3666_, v_n_3667_, v_h_3668_, v___y_3669_);
lean_dec(v_n_3667_);
lean_dec_ref(v_paths_3664_);
lean_dec_ref(v_descrs_3663_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(lean_object* v___y_3672_, lean_object* v_descrs_3673_, lean_object* v_paths_3674_, lean_object* v_service_3675_, lean_object* v_scope_3676_, lean_object* v_n_3677_){
_start:
{
lean_object* v___x_3679_; uint64_t v_hash_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3679_ = lean_array_fget_borrowed(v_descrs_3673_, v_n_3677_);
v_hash_3680_ = lean_ctor_get_uint64(v___x_3679_, sizeof(void*)*1);
v___x_3681_ = lean_array_fget_borrowed(v_paths_3674_, v_n_3677_);
lean_inc(v___x_3681_);
v___x_3682_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3672_, v_hash_3680_, v___x_3681_, v_service_3675_, v_scope_3676_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg___boxed(lean_object* v___y_3683_, lean_object* v_descrs_3684_, lean_object* v_paths_3685_, lean_object* v_service_3686_, lean_object* v_scope_3687_, lean_object* v_n_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3683_, v_descrs_3684_, v_paths_3685_, v_service_3686_, v_scope_3687_, v_n_3688_);
lean_dec(v_n_3688_);
lean_dec_ref(v_paths_3685_);
lean_dec_ref(v_descrs_3684_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(lean_object* v_descrs_3691_, lean_object* v_paths_3692_, lean_object* v_service_3693_, lean_object* v_scope_3694_, lean_object* v_n_3695_, lean_object* v_i_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_zero_3699_; uint8_t v_isZero_3700_; 
v_zero_3699_ = lean_unsigned_to_nat(0u);
v_isZero_3700_ = lean_nat_dec_eq(v_i_3696_, v_zero_3699_);
if (v_isZero_3700_ == 1)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec_ref(v___y_3697_);
lean_dec(v_i_3696_);
lean_dec_ref(v_scope_3694_);
lean_dec_ref(v_service_3693_);
v___x_3701_ = lean_box(0);
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
return v___x_3702_;
}
else
{
lean_object* v_one_3703_; lean_object* v_n_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_one_3703_ = lean_unsigned_to_nat(1u);
v_n_3704_ = lean_nat_sub(v_i_3696_, v_one_3703_);
lean_dec(v_i_3696_);
v___x_3705_ = lean_nat_sub(v_n_3695_, v_n_3704_);
v___x_3706_ = lean_nat_sub(v___x_3705_, v_one_3703_);
lean_dec(v___x_3705_);
lean_inc_ref(v_scope_3694_);
lean_inc_ref(v_service_3693_);
lean_inc_ref(v___y_3697_);
v___x_3707_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3697_, v_descrs_3691_, v_paths_3692_, v_service_3693_, v_scope_3694_, v___x_3706_);
lean_dec(v___x_3706_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_dec_ref(v___x_3707_);
v_i_3696_ = v_n_3704_;
goto _start;
}
else
{
lean_dec(v_n_3704_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v_scope_3694_);
lean_dec_ref(v_service_3693_);
return v___x_3707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg___boxed(lean_object* v_descrs_3709_, lean_object* v_paths_3710_, lean_object* v_service_3711_, lean_object* v_scope_3712_, lean_object* v_n_3713_, lean_object* v_i_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3709_, v_paths_3710_, v_service_3711_, v_scope_3712_, v_n_3713_, v_i_3714_, v___y_3715_);
lean_dec(v_n_3713_);
lean_dec_ref(v_paths_3710_);
lean_dec_ref(v_descrs_3709_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_3718_, lean_object* v_descrs_3719_, lean_object* v_paths_3720_, lean_object* v_service_3721_, lean_object* v_scope_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v___x_3725_; 
lean_inc(v_n_3718_);
v___x_3725_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3719_, v_paths_3720_, v_service_3721_, v_scope_3722_, v_n_3718_, v_n_3718_, v_a_3723_);
lean_dec(v_n_3718_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_3726_, lean_object* v_descrs_3727_, lean_object* v_paths_3728_, lean_object* v_service_3729_, lean_object* v_scope_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Lake_CacheService_uploadArtifacts(v_n_3726_, v_descrs_3727_, v_paths_3728_, v_service_3729_, v_scope_3730_, v_a_3731_);
lean_dec_ref(v_paths_3728_);
lean_dec_ref(v_descrs_3727_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(lean_object* v_descrs_3734_, lean_object* v_paths_3735_, lean_object* v_service_3736_, lean_object* v_scope_3737_, lean_object* v_n_3738_, lean_object* v_i_3739_, lean_object* v_a_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3734_, v_paths_3735_, v_service_3736_, v_scope_3737_, v_n_3738_, v_i_3739_, v___y_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___boxed(lean_object* v_descrs_3744_, lean_object* v_paths_3745_, lean_object* v_service_3746_, lean_object* v_scope_3747_, lean_object* v_n_3748_, lean_object* v_i_3749_, lean_object* v_a_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(v_descrs_3744_, v_paths_3745_, v_service_3746_, v_scope_3747_, v_n_3748_, v_i_3749_, v_a_3750_, v___y_3751_);
lean_dec(v_n_3748_);
lean_dec_ref(v_paths_3745_);
lean_dec_ref(v_descrs_3744_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(lean_object* v___y_3754_, lean_object* v_descrs_3755_, lean_object* v_paths_3756_, lean_object* v_service_3757_, lean_object* v_scope_3758_, lean_object* v_n_3759_, lean_object* v_h_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3754_, v_descrs_3755_, v_paths_3756_, v_service_3757_, v_scope_3758_, v_n_3759_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___boxed(lean_object* v___y_3763_, lean_object* v_descrs_3764_, lean_object* v_paths_3765_, lean_object* v_service_3766_, lean_object* v_scope_3767_, lean_object* v_n_3768_, lean_object* v_h_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(v___y_3763_, v_descrs_3764_, v_paths_3765_, v_service_3766_, v_scope_3767_, v_n_3768_, v_h_3769_);
lean_dec(v_n_3768_);
lean_dec_ref(v_paths_3765_);
lean_dec_ref(v_descrs_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_3776_, lean_object* v_service_3777_, lean_object* v_scope_3778_, lean_object* v_platform_3779_, lean_object* v_toolchain_3780_){
_start:
{
lean_object* v_url_3782_; lean_object* v_url_3789_; 
if (lean_obj_tag(v_scope_3778_) == 0)
{
lean_object* v_s_3798_; lean_object* v_revisionEndpoint_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec_ref(v_platform_3779_);
v_s_3798_ = lean_ctor_get(v_scope_3778_, 0);
lean_inc_ref(v_s_3798_);
lean_dec_ref(v_scope_3778_);
v_revisionEndpoint_3799_ = lean_ctor_get(v_service_3777_, 3);
lean_inc_ref(v_revisionEndpoint_3799_);
lean_dec_ref(v_service_3777_);
v___x_3800_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_3799_, v_s_3798_);
v___x_3801_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_3802_ = lean_string_append(v___x_3801_, v_rev_3776_);
v___x_3803_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_3804_ = lean_string_append(v___x_3802_, v___x_3803_);
v___x_3805_ = lean_string_append(v___x_3800_, v___x_3804_);
lean_dec_ref(v___x_3804_);
return v___x_3805_;
}
else
{
lean_object* v_s_3806_; lean_object* v_revisionEndpoint_3807_; lean_object* v_url_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_s_3806_ = lean_ctor_get(v_scope_3778_, 0);
lean_inc_ref(v_s_3806_);
lean_dec_ref(v_scope_3778_);
v_revisionEndpoint_3807_ = lean_ctor_get(v_service_3777_, 3);
lean_inc_ref(v_revisionEndpoint_3807_);
lean_dec_ref(v_service_3777_);
v_url_3808_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_3807_, v_s_3806_);
v___x_3809_ = lean_string_utf8_byte_size(v_platform_3779_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = lean_nat_dec_eq(v___x_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v_url_3814_; 
v___x_3812_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_3813_ = lean_string_append(v_url_3808_, v___x_3812_);
v_url_3814_ = l_Lake_uriEncode(v_platform_3779_, v___x_3813_);
v_url_3789_ = v_url_3814_;
goto v___jp_3788_;
}
else
{
lean_dec_ref(v_platform_3779_);
v_url_3789_ = v_url_3808_;
goto v___jp_3788_;
}
}
v___jp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3783_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_3784_ = lean_string_append(v_url_3782_, v___x_3783_);
v___x_3785_ = lean_string_append(v___x_3784_, v_rev_3776_);
v___x_3786_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_3787_ = lean_string_append(v___x_3785_, v___x_3786_);
return v___x_3787_;
}
v___jp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = lean_string_utf8_byte_size(v_toolchain_3780_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = lean_nat_dec_eq(v___x_3790_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v_url_3797_; 
v___x_3793_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_3794_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_3780_, v___x_3793_, v___x_3791_);
v___x_3795_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_3796_ = lean_string_append(v_url_3789_, v___x_3795_);
v_url_3797_ = l_Lake_uriEncode(v___x_3794_, v___x_3796_);
v_url_3782_ = v_url_3797_;
goto v___jp_3781_;
}
else
{
v_url_3782_ = v_url_3789_;
goto v___jp_3781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_3815_, lean_object* v_service_3816_, lean_object* v_scope_3817_, lean_object* v_platform_3818_, lean_object* v_toolchain_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_3815_, v_service_3816_, v_scope_3817_, v_platform_3818_, v_toolchain_3819_);
lean_dec_ref(v_toolchain_3819_);
lean_dec_ref(v_rev_3815_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_3824_, lean_object* v_service_3825_, lean_object* v_scope_3826_, lean_object* v_platform_3827_, lean_object* v_toolchain_3828_){
_start:
{
lean_object* v_url_3830_; lean_object* v___y_3838_; uint8_t v_isReservoir_3848_; 
v_isReservoir_3848_ = lean_ctor_get_uint8(v_service_3825_, sizeof(void*)*5);
if (v_isReservoir_3848_ == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_3824_, v_service_3825_, v_scope_3826_, v_platform_3827_, v_toolchain_3828_);
lean_dec_ref(v_toolchain_3828_);
return v___x_3849_;
}
else
{
if (lean_obj_tag(v_scope_3826_) == 0)
{
lean_object* v_apiEndpoint_3850_; lean_object* v_s_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_apiEndpoint_3850_ = lean_ctor_get(v_service_3825_, 4);
lean_inc_ref(v_apiEndpoint_3850_);
lean_dec_ref(v_service_3825_);
v_s_3851_ = lean_ctor_get(v_scope_3826_, 0);
lean_inc_ref(v_s_3851_);
lean_dec_ref(v_scope_3826_);
v___x_3852_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_3853_ = lean_string_append(v_apiEndpoint_3850_, v___x_3852_);
v___x_3854_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3853_, v_s_3851_);
v___y_3838_ = v___x_3854_;
goto v___jp_3837_;
}
else
{
lean_object* v_apiEndpoint_3855_; lean_object* v_s_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_apiEndpoint_3855_ = lean_ctor_get(v_service_3825_, 4);
lean_inc_ref(v_apiEndpoint_3855_);
lean_dec_ref(v_service_3825_);
v_s_3856_ = lean_ctor_get(v_scope_3826_, 0);
lean_inc_ref(v_s_3856_);
lean_dec_ref(v_scope_3826_);
v___x_3857_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3858_ = lean_string_append(v_apiEndpoint_3855_, v___x_3857_);
v___x_3859_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3858_, v_s_3856_);
v___y_3838_ = v___x_3859_;
goto v___jp_3837_;
}
}
v___jp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3831_ = lean_string_utf8_byte_size(v_toolchain_3828_);
v___x_3832_ = lean_unsigned_to_nat(0u);
v___x_3833_ = lean_nat_dec_eq(v___x_3831_, v___x_3832_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v_url_3836_; 
v___x_3834_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_3835_ = lean_string_append(v_url_3830_, v___x_3834_);
v_url_3836_ = l_Lake_uriEncode(v_toolchain_3828_, v___x_3835_);
return v_url_3836_;
}
else
{
lean_dec_ref(v_toolchain_3828_);
return v_url_3830_;
}
}
v___jp_3837_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v_url_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3839_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_3840_ = lean_string_append(v___y_3838_, v___x_3839_);
v_url_3841_ = lean_string_append(v___x_3840_, v_rev_3824_);
v___x_3842_ = lean_string_utf8_byte_size(v_platform_3827_);
v___x_3843_ = lean_unsigned_to_nat(0u);
v___x_3844_ = lean_nat_dec_eq(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_url_3847_; 
v___x_3845_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_3846_ = lean_string_append(v_url_3841_, v___x_3845_);
v_url_3847_ = l_Lake_uriEncode(v_platform_3827_, v___x_3846_);
v_url_3830_ = v_url_3847_;
goto v___jp_3829_;
}
else
{
lean_dec_ref(v_platform_3827_);
v_url_3830_ = v_url_3841_;
goto v___jp_3829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_3860_, lean_object* v_service_3861_, lean_object* v_scope_3862_, lean_object* v_platform_3863_, lean_object* v_toolchain_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lake_CacheService_revisionUrl(v_rev_3860_, v_service_3861_, v_scope_3862_, v_platform_3863_, v_toolchain_3864_);
lean_dec_ref(v_rev_3860_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_3870_, lean_object* v_cache_3871_, lean_object* v_service_3872_, lean_object* v_localScope_3873_, lean_object* v_remoteScope_3874_, lean_object* v_platform_3875_, lean_object* v_toolchain_3876_, uint8_t v_force_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_a_3884_; lean_object* v_a_3891_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v_a_3904_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v_path_3913_; lean_object* v_a_3915_; lean_object* v___y_4015_; lean_object* v___y_4016_; uint8_t v___x_4065_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_3908_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_3909_ = l_System_FilePath_join(v_cache_3871_, v___x_3908_);
lean_inc_ref(v_localScope_3873_);
v___x_3910_ = l_System_FilePath_join(v___x_3909_, v_localScope_3873_);
v___x_3911_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_3870_);
v___x_3912_ = lean_string_append(v_rev_3870_, v___x_3911_);
v_path_3913_ = l_System_FilePath_join(v___x_3910_, v___x_3912_);
v___x_4065_ = l_System_FilePath_pathExists(v_path_3913_);
v___x_4127_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4128_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_4128_ == 0)
{
goto v___jp_4066_;
}
else
{
lean_object* v___x_4129_; uint8_t v___x_4130_; 
v___x_4129_ = lean_box(0);
v___x_4130_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_4130_ == 0)
{
if (v___x_4128_ == 0)
{
goto v___jp_4066_;
}
else
{
size_t v___x_4131_; size_t v___x_4132_; lean_object* v___x_4133_; 
v___x_4131_ = ((size_t)0ULL);
v___x_4132_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_3878_);
v___x_4133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_4127_, v___x_4131_, v___x_4132_, v___x_4129_, v_a_3878_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_dec_ref(v___x_4133_);
goto v___jp_4066_;
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v_path_3913_);
lean_dec_ref(v_a_3878_);
lean_dec_ref(v_toolchain_3876_);
lean_dec_ref(v_platform_3875_);
lean_dec_ref(v_remoteScope_3874_);
lean_dec_ref(v_localScope_3873_);
lean_dec_ref(v_service_3872_);
lean_dec_ref(v_rev_3870_);
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
else
{
size_t v___x_4142_; size_t v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = ((size_t)0ULL);
v___x_4143_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_3878_);
v___x_4144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_4127_, v___x_4142_, v___x_4143_, v___x_4129_, v_a_3878_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_dec_ref(v___x_4144_);
goto v___jp_4066_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v_path_3913_);
lean_dec_ref(v_a_3878_);
lean_dec_ref(v_toolchain_3876_);
lean_dec_ref(v_platform_3875_);
lean_dec_ref(v_remoteScope_3874_);
lean_dec_ref(v_localScope_3873_);
lean_dec_ref(v_service_3872_);
lean_dec_ref(v_rev_3870_);
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
v___jp_3880_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_box(0);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
v___jp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v_a_3884_);
v___x_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
return v___x_3886_;
}
v___jp_3887_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
v___jp_3890_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3892_, 0, v_a_3891_);
v___x_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
return v___x_3893_;
}
v___jp_3894_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3897_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_3898_ = lean_string_append(v___y_3896_, v___x_3897_);
v___x_3899_ = 3;
v___x_3900_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3900_, 0, v___x_3898_);
lean_ctor_set_uint8(v___x_3900_, sizeof(void*)*1, v___x_3899_);
v___x_3901_ = lean_apply_2(v_a_3878_, v___x_3900_, lean_box(0));
v___x_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___y_3895_);
return v___x_3902_;
}
v___jp_3903_:
{
lean_object* v_s_3905_; 
v_s_3905_ = lean_ctor_get(v_remoteScope_3874_, 0);
lean_inc_ref(v_s_3905_);
lean_dec_ref(v_remoteScope_3874_);
v___y_3895_ = v_a_3904_;
v___y_3896_ = v_s_3905_;
goto v___jp_3894_;
}
v___jp_3906_:
{
lean_object* v___x_3907_; 
v___x_3907_ = lean_box(0);
v_a_3904_ = v___x_3907_;
goto v___jp_3903_;
}
v___jp_3914_:
{
if (lean_obj_tag(v_a_3915_) == 1)
{
lean_object* v_val_3916_; lean_object* v___x_3917_; 
v_val_3916_ = lean_ctor_get(v_a_3915_, 0);
lean_inc(v_val_3916_);
lean_dec_ref(v_a_3915_);
lean_inc_ref(v_path_3913_);
v___x_3917_ = l_Lake_createParentDirs(v_path_3913_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v___x_3918_; 
lean_dec_ref(v___x_3917_);
v___x_3918_ = l_IO_FS_writeFile(v_path_3913_, v_val_3916_);
lean_dec(v_val_3916_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3984_; 
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v___x_3918_, 0);
lean_dec(v_unused_3985_);
v___x_3920_ = v___x_3918_;
v_isShared_3921_ = v_isSharedCheck_3984_;
goto v_resetjp_3919_;
}
else
{
lean_dec(v___x_3918_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3984_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = lean_unsigned_to_nat(0u);
v___x_3923_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3924_ = l_Lake_CacheMap_load(v_path_3913_, v___x_3923_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v_a_3926_; lean_object* v___x_3927_; uint8_t v___x_3928_; 
lean_del_object(v___x_3920_);
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
v_a_3926_ = lean_ctor_get(v___x_3924_, 1);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3924_);
v___x_3927_ = lean_array_get_size(v_a_3926_);
v___x_3928_ = lean_nat_dec_lt(v___x_3922_, v___x_3927_);
if (v___x_3928_ == 0)
{
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3878_);
v_a_3891_ = v_a_3925_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3929_; uint8_t v___x_3930_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = lean_nat_dec_le(v___x_3927_, v___x_3927_);
if (v___x_3930_ == 0)
{
if (v___x_3928_ == 0)
{
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3878_);
v_a_3891_ = v_a_3925_;
goto v___jp_3890_;
}
else
{
size_t v___x_3931_; size_t v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = ((size_t)0ULL);
v___x_3932_ = lean_usize_of_nat(v___x_3927_);
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3926_, v___x_3931_, v___x_3932_, v___x_3929_, v_a_3878_);
lean_dec(v_a_3926_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_dec_ref(v___x_3933_);
v_a_3891_ = v_a_3925_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v_a_3925_);
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3933_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
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
size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = ((size_t)0ULL);
v___x_3943_ = lean_usize_of_nat(v___x_3927_);
v___x_3944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3926_, v___x_3942_, v___x_3943_, v___x_3929_, v_a_3878_);
lean_dec(v_a_3926_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_dec_ref(v___x_3944_);
v_a_3891_ = v_a_3925_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_a_3925_);
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
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
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v_a_3953_ = lean_ctor_get(v___x_3924_, 1);
lean_inc(v_a_3953_);
lean_dec_ref(v___x_3924_);
v___x_3954_ = lean_array_get_size(v_a_3953_);
v___x_3955_ = lean_nat_dec_lt(v___x_3922_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3878_);
v___x_3956_ = lean_box(0);
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 1);
lean_ctor_set(v___x_3920_, 0, v___x_3956_);
v___x_3958_ = v___x_3920_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
else
{
lean_object* v___x_3960_; uint8_t v___x_3961_; 
lean_del_object(v___x_3920_);
v___x_3960_ = lean_box(0);
v___x_3961_ = lean_nat_dec_le(v___x_3954_, v___x_3954_);
if (v___x_3961_ == 0)
{
if (v___x_3955_ == 0)
{
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3878_);
goto v___jp_3887_;
}
else
{
size_t v___x_3962_; size_t v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = ((size_t)0ULL);
v___x_3963_ = lean_usize_of_nat(v___x_3954_);
v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3953_, v___x_3962_, v___x_3963_, v___x_3960_, v_a_3878_);
lean_dec(v_a_3953_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_dec_ref(v___x_3964_);
goto v___jp_3887_;
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
else
{
size_t v___x_3973_; size_t v___x_3974_; lean_object* v___x_3975_; 
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = lean_usize_of_nat(v___x_3954_);
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3953_, v___x_3973_, v___x_3974_, v___x_3960_, v_a_3878_);
lean_dec(v_a_3953_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_dec_ref(v___x_3975_);
goto v___jp_3887_;
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
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
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v_path_3913_);
v_a_3986_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3988_ = v___x_3918_;
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3918_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; uint8_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3990_ = lean_io_error_to_string(v_a_3986_);
v___x_3991_ = 3;
v___x_3992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*1, v___x_3991_);
v___x_3993_ = lean_apply_2(v_a_3878_, v___x_3992_, lean_box(0));
v___x_3994_ = lean_box(0);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3994_);
v___x_3996_ = v___x_3988_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4011_; 
lean_dec(v_val_3916_);
lean_dec_ref(v_path_3913_);
v_a_3999_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4001_ = v___x_3917_;
v_isShared_4002_ = v_isSharedCheck_4011_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3917_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4011_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; uint8_t v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4003_ = lean_io_error_to_string(v_a_3999_);
v___x_4004_ = 3;
v___x_4005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set_uint8(v___x_4005_, sizeof(void*)*1, v___x_4004_);
v___x_4006_ = lean_apply_2(v_a_3878_, v___x_4005_, lean_box(0));
v___x_4007_ = lean_box(0);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4007_);
v___x_4009_ = v___x_4001_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_dec(v_a_3915_);
lean_dec_ref(v_path_3913_);
lean_dec_ref(v_a_3878_);
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
v___jp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4019_ = l_Lake_getUrl_x3f(v___y_4015_, v___y_4016_, v___x_4018_);
lean_dec_ref(v___y_4016_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v_a_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
v_a_4021_ = lean_ctor_get(v___x_4019_, 1);
lean_inc(v_a_4021_);
lean_dec_ref(v___x_4019_);
v___x_4022_ = lean_array_get_size(v_a_4021_);
v___x_4023_ = lean_nat_dec_lt(v___x_4017_, v___x_4022_);
if (v___x_4023_ == 0)
{
lean_dec(v_a_4021_);
lean_dec_ref(v_remoteScope_3874_);
v_a_3915_ = v_a_4020_;
goto v___jp_3914_;
}
else
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = lean_box(0);
v___x_4025_ = lean_nat_dec_le(v___x_4022_, v___x_4022_);
if (v___x_4025_ == 0)
{
if (v___x_4023_ == 0)
{
lean_dec(v_a_4021_);
lean_dec_ref(v_remoteScope_3874_);
v_a_3915_ = v_a_4020_;
goto v___jp_3914_;
}
else
{
size_t v___x_4026_; size_t v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = ((size_t)0ULL);
v___x_4027_ = lean_usize_of_nat(v___x_4022_);
lean_inc_ref(v_a_3878_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4021_, v___x_4026_, v___x_4027_, v___x_4024_, v_a_3878_);
lean_dec(v_a_4021_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_dec_ref(v___x_4028_);
lean_dec_ref(v_remoteScope_3874_);
v_a_3915_ = v_a_4020_;
goto v___jp_3914_;
}
else
{
lean_object* v_a_4029_; 
lean_dec(v_a_4020_);
lean_dec_ref(v_path_3913_);
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v___x_4028_);
v_a_3904_ = v_a_4029_;
goto v___jp_3903_;
}
}
}
else
{
size_t v___x_4030_; size_t v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = ((size_t)0ULL);
v___x_4031_ = lean_usize_of_nat(v___x_4022_);
lean_inc_ref(v_a_3878_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4021_, v___x_4030_, v___x_4031_, v___x_4024_, v_a_3878_);
lean_dec(v_a_4021_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_dec_ref(v___x_4032_);
lean_dec_ref(v_remoteScope_3874_);
v_a_3915_ = v_a_4020_;
goto v___jp_3914_;
}
else
{
lean_object* v_a_4033_; 
lean_dec(v_a_4020_);
lean_dec_ref(v_path_3913_);
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref(v___x_4032_);
v_a_3904_ = v_a_4033_;
goto v___jp_3903_;
}
}
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
lean_dec_ref(v_path_3913_);
v_a_4034_ = lean_ctor_get(v___x_4019_, 1);
lean_inc(v_a_4034_);
lean_dec_ref(v___x_4019_);
v___x_4035_ = lean_array_get_size(v_a_4034_);
v___x_4036_ = lean_nat_dec_lt(v___x_4017_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; 
lean_dec(v_a_4034_);
v___x_4037_ = lean_box(0);
v_a_3904_ = v___x_4037_;
goto v___jp_3903_;
}
else
{
lean_object* v___x_4038_; uint8_t v___x_4039_; 
v___x_4038_ = lean_box(0);
v___x_4039_ = lean_nat_dec_le(v___x_4035_, v___x_4035_);
if (v___x_4039_ == 0)
{
if (v___x_4036_ == 0)
{
lean_dec(v_a_4034_);
goto v___jp_3906_;
}
else
{
size_t v___x_4040_; size_t v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = lean_usize_of_nat(v___x_4035_);
lean_inc_ref(v_a_3878_);
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4034_, v___x_4040_, v___x_4041_, v___x_4038_, v_a_3878_);
lean_dec(v_a_4034_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_dec_ref(v___x_4042_);
goto v___jp_3906_;
}
else
{
lean_object* v_a_4043_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref(v___x_4042_);
v_a_3904_ = v_a_4043_;
goto v___jp_3903_;
}
}
}
else
{
size_t v___x_4044_; size_t v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = ((size_t)0ULL);
v___x_4045_ = lean_usize_of_nat(v___x_4035_);
lean_inc_ref(v_a_3878_);
v___x_4046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4034_, v___x_4044_, v___x_4045_, v___x_4038_, v_a_3878_);
lean_dec(v_a_4034_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_dec_ref(v___x_4046_);
goto v___jp_3906_;
}
else
{
lean_object* v_a_4047_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref(v___x_4046_);
v_a_3904_ = v_a_4047_;
goto v___jp_3903_;
}
}
}
}
}
v___jp_4048_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v_isReservoir_4062_; 
lean_inc_ref(v_remoteScope_3874_);
lean_inc_ref(v_service_3872_);
v___x_4049_ = l_Lake_CacheService_revisionUrl(v_rev_3870_, v_service_3872_, v_remoteScope_3874_, v_platform_3875_, v_toolchain_3876_);
v___x_4050_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_4051_ = lean_string_append(v_localScope_3873_, v___x_4050_);
v___x_4052_ = lean_string_append(v___x_4051_, v_rev_3870_);
lean_dec_ref(v_rev_3870_);
v___x_4053_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4054_ = lean_string_append(v___x_4052_, v___x_4053_);
v___x_4055_ = lean_string_append(v___x_4054_, v_path_3913_);
v___x_4056_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4057_ = lean_string_append(v___x_4055_, v___x_4056_);
v___x_4058_ = lean_string_append(v___x_4057_, v___x_4049_);
v___x_4059_ = 1;
v___x_4060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4060_, 0, v___x_4058_);
lean_ctor_set_uint8(v___x_4060_, sizeof(void*)*1, v___x_4059_);
lean_inc_ref(v_a_3878_);
v___x_4061_ = lean_apply_2(v_a_3878_, v___x_4060_, lean_box(0));
v_isReservoir_4062_ = lean_ctor_get_uint8(v_service_3872_, sizeof(void*)*5);
lean_dec_ref(v_service_3872_);
if (v_isReservoir_4062_ == 0)
{
lean_object* v___x_4063_; 
v___x_4063_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_4015_ = v___x_4049_;
v___y_4016_ = v___x_4063_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lake_Reservoir_lakeHeaders;
v___y_4015_ = v___x_4049_;
v___y_4016_ = v___x_4064_;
goto v___jp_4014_;
}
}
v___jp_4066_:
{
if (v___x_4065_ == 0)
{
goto v___jp_4048_;
}
else
{
if (v_force_3877_ == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_dec_ref(v_toolchain_3876_);
lean_dec_ref(v_platform_3875_);
lean_dec_ref(v_remoteScope_3874_);
lean_dec_ref(v_localScope_3873_);
lean_dec_ref(v_service_3872_);
lean_dec_ref(v_rev_3870_);
v___x_4067_ = lean_unsigned_to_nat(0u);
v___x_4068_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4069_ = l_Lake_CacheMap_load(v_path_3913_, v___x_4068_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v_a_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
v_a_4071_ = lean_ctor_get(v___x_4069_, 1);
lean_inc(v_a_4071_);
lean_dec_ref(v___x_4069_);
v___x_4072_ = lean_array_get_size(v_a_4071_);
v___x_4073_ = lean_nat_dec_lt(v___x_4067_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_dec(v_a_4071_);
lean_dec_ref(v_a_3878_);
v_a_3884_ = v_a_4070_;
goto v___jp_3883_;
}
else
{
lean_object* v___x_4074_; uint8_t v___x_4075_; 
v___x_4074_ = lean_box(0);
v___x_4075_ = lean_nat_dec_le(v___x_4072_, v___x_4072_);
if (v___x_4075_ == 0)
{
if (v___x_4073_ == 0)
{
lean_dec(v_a_4071_);
lean_dec_ref(v_a_3878_);
v_a_3884_ = v_a_4070_;
goto v___jp_3883_;
}
else
{
size_t v___x_4076_; size_t v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = ((size_t)0ULL);
v___x_4077_ = lean_usize_of_nat(v___x_4072_);
v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4071_, v___x_4076_, v___x_4077_, v___x_4074_, v_a_3878_);
lean_dec(v_a_4071_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_dec_ref(v___x_4078_);
v_a_3884_ = v_a_4070_;
goto v___jp_3883_;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_a_4070_);
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
else
{
size_t v___x_4087_; size_t v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = ((size_t)0ULL);
v___x_4088_ = lean_usize_of_nat(v___x_4072_);
v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4071_, v___x_4087_, v___x_4088_, v___x_4074_, v_a_3878_);
lean_dec(v_a_4071_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_dec_ref(v___x_4089_);
v_a_3884_ = v_a_4070_;
goto v___jp_3883_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_a_4070_);
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
v_a_4098_ = lean_ctor_get(v___x_4069_, 1);
lean_inc(v_a_4098_);
lean_dec_ref(v___x_4069_);
v___x_4099_ = lean_array_get_size(v_a_4098_);
v___x_4100_ = lean_nat_dec_lt(v___x_4067_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec(v_a_4098_);
lean_dec_ref(v_a_3878_);
v___x_4101_ = lean_box(0);
v___x_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
else
{
lean_object* v___x_4103_; uint8_t v___x_4104_; 
v___x_4103_ = lean_box(0);
v___x_4104_ = lean_nat_dec_le(v___x_4099_, v___x_4099_);
if (v___x_4104_ == 0)
{
if (v___x_4100_ == 0)
{
lean_dec(v_a_4098_);
lean_dec_ref(v_a_3878_);
goto v___jp_3880_;
}
else
{
size_t v___x_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
v___x_4105_ = ((size_t)0ULL);
v___x_4106_ = lean_usize_of_nat(v___x_4099_);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4098_, v___x_4105_, v___x_4106_, v___x_4103_, v_a_3878_);
lean_dec(v_a_4098_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_dec_ref(v___x_4107_);
goto v___jp_3880_;
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
else
{
size_t v___x_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = ((size_t)0ULL);
v___x_4117_ = lean_usize_of_nat(v___x_4099_);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4098_, v___x_4116_, v___x_4117_, v___x_4103_, v_a_3878_);
lean_dec(v_a_4098_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_dec_ref(v___x_4118_);
goto v___jp_3880_;
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
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
}
}
else
{
goto v___jp_4048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_4153_, lean_object* v_cache_4154_, lean_object* v_service_4155_, lean_object* v_localScope_4156_, lean_object* v_remoteScope_4157_, lean_object* v_platform_4158_, lean_object* v_toolchain_4159_, lean_object* v_force_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_){
_start:
{
uint8_t v_force_boxed_4163_; lean_object* v_res_4164_; 
v_force_boxed_4163_ = lean_unbox(v_force_4160_);
v_res_4164_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_4153_, v_cache_4154_, v_service_4155_, v_localScope_4156_, v_remoteScope_4157_, v_platform_4158_, v_toolchain_4159_, v_force_boxed_4163_, v_a_4161_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_4166_, lean_object* v_outputs_4167_, lean_object* v_service_4168_, lean_object* v_scope_4169_, lean_object* v_platform_4170_, lean_object* v_toolchain_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v_url_4174_; lean_object* v___y_4176_; lean_object* v_s_4192_; 
lean_inc_ref(v_scope_4169_);
lean_inc_ref(v_service_4168_);
v_url_4174_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_4166_, v_service_4168_, v_scope_4169_, v_platform_4170_, v_toolchain_4171_);
v_s_4192_ = lean_ctor_get(v_scope_4169_, 0);
lean_inc_ref(v_s_4192_);
lean_dec_ref(v_scope_4169_);
v___y_4176_ = v_s_4192_;
goto v___jp_4175_;
v___jp_4175_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v_key_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4177_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_4178_ = lean_string_append(v___y_4176_, v___x_4177_);
v___x_4179_ = lean_string_append(v___x_4178_, v_rev_4166_);
v___x_4180_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4181_ = lean_string_append(v___x_4179_, v___x_4180_);
v___x_4182_ = lean_string_append(v___x_4181_, v_outputs_4167_);
v___x_4183_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4184_ = lean_string_append(v___x_4182_, v___x_4183_);
v___x_4185_ = lean_string_append(v___x_4184_, v_url_4174_);
v___x_4186_ = 1;
v___x_4187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4187_, 0, v___x_4185_);
lean_ctor_set_uint8(v___x_4187_, sizeof(void*)*1, v___x_4186_);
lean_inc_ref(v_a_4172_);
v___x_4188_ = lean_apply_2(v_a_4172_, v___x_4187_, lean_box(0));
v_key_4189_ = lean_ctor_get(v_service_4168_, 1);
lean_inc_ref(v_key_4189_);
lean_dec_ref(v_service_4168_);
v___x_4190_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_4191_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_4172_, v_outputs_4167_, v___x_4190_, v_url_4174_, v_key_4189_);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_4193_, lean_object* v_outputs_4194_, lean_object* v_service_4195_, lean_object* v_scope_4196_, lean_object* v_platform_4197_, lean_object* v_toolchain_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_4193_, v_outputs_4194_, v_service_4195_, v_scope_4196_, v_platform_4197_, v_toolchain_4198_, v_a_4199_);
lean_dec_ref(v_toolchain_4198_);
lean_dec_ref(v_rev_4193_);
return v_res_4201_;
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
