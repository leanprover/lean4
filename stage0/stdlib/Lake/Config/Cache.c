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
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unsupported output: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unsupported output; "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheOutput_ofData(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* v_init_1288_, lean_object* v_x_1289_, lean_object* v___y_1290_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_object* v_v_1292_; lean_object* v_l_1293_; lean_object* v_r_1294_; lean_object* v___x_1295_; 
v_v_1292_ = lean_ctor_get(v_x_1289_, 2);
lean_inc(v_v_1292_);
v_l_1293_ = lean_ctor_get(v_x_1289_, 3);
lean_inc(v_l_1293_);
v_r_1294_ = lean_ctor_get(v_x_1289_, 4);
lean_inc(v_r_1294_);
lean_dec_ref(v_x_1289_);
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1288_, v_l_1293_, v___y_1290_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
v_a_1297_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1295_);
v___x_1298_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1296_, v_v_1292_, v_a_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v_a_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
v_a_1300_ = lean_ctor_get(v___x_1298_, 1);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1298_);
v_init_1288_ = v_a_1299_;
v_x_1289_ = v_r_1294_;
v___y_1290_ = v_a_1300_;
goto _start;
}
else
{
lean_dec(v_r_1294_);
return v___x_1298_;
}
}
else
{
lean_dec(v_r_1294_);
lean_dec(v_v_1292_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_init_1288_);
lean_ctor_set(v___x_1302_, 1, v___y_1290_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* v_as_1303_, lean_object* v_o_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___y_1308_; 
switch(lean_obj_tag(v_o_1304_))
{
case 0:
{
v___y_1308_ = v_a_1305_;
goto v___jp_1307_;
}
case 1:
{
uint8_t v_b_1310_; lean_object* v___x_1311_; lean_object* v___y_1313_; 
v_b_1310_ = lean_ctor_get_uint8(v_o_1304_, 0);
lean_dec_ref(v_o_1304_);
v___x_1311_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
if (v_b_1310_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1));
v___y_1313_ = v___x_1318_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2));
v___y_1313_ = v___x_1319_;
goto v___jp_1312_;
}
v___jp_1312_:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = lean_string_append(v___x_1311_, v___y_1313_);
lean_dec_ref(v___y_1313_);
v___x_1315_ = 3;
v___x_1316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*1, v___x_1315_);
v___x_1317_ = lean_array_push(v_a_1305_, v___x_1316_);
v___y_1308_ = v___x_1317_;
goto v___jp_1307_;
}
}
case 2:
{
lean_object* v_n_1320_; lean_object* v___x_1321_; 
v_n_1320_ = lean_ctor_get(v_o_1304_, 0);
lean_inc_ref(v_n_1320_);
lean_dec_ref(v_o_1304_);
v___x_1321_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3));
v___x_1324_ = lean_string_append(v___x_1323_, v_a_1322_);
lean_dec(v_a_1322_);
v___x_1325_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1));
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
v___x_1327_ = l_Lean_JsonNumber_toString(v_n_1320_);
v___x_1328_ = lean_string_append(v___x_1326_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = 3;
v___x_1330_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*1, v___x_1329_);
v___x_1331_ = lean_array_push(v_a_1305_, v___x_1330_);
v___y_1308_ = v___x_1331_;
goto v___jp_1307_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint64_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_n_1320_);
v_a_1332_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1332_);
lean_dec_ref(v___x_1321_);
v___x_1333_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4));
v___x_1334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = lean_unbox_uint64(v_a_1332_);
lean_dec(v_a_1332_);
lean_ctor_set_uint64(v___x_1334_, sizeof(void*)*1, v___x_1335_);
v___x_1336_ = lean_array_push(v_as_1303_, v___x_1334_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v_a_1305_);
return v___x_1337_;
}
}
case 3:
{
lean_object* v_s_1338_; lean_object* v___x_1339_; 
v_s_1338_ = lean_ctor_get(v_o_1304_, 0);
lean_inc_ref(v_s_1338_);
lean_dec_ref(v_o_1304_);
v___x_1339_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
v___x_1342_ = lean_string_append(v___x_1341_, v_a_1340_);
lean_dec(v_a_1340_);
v___x_1343_ = 3;
v___x_1344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*1, v___x_1343_);
v___x_1345_ = lean_array_push(v_a_1305_, v___x_1344_);
v___y_1308_ = v___x_1345_;
goto v___jp_1307_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1339_);
v___x_1347_ = lean_array_push(v_as_1303_, v_a_1346_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_a_1305_);
return v___x_1348_;
}
}
case 4:
{
lean_object* v_elems_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_elems_1349_ = lean_ctor_get(v_o_1304_, 0);
lean_inc_ref(v_elems_1349_);
lean_dec_ref(v_o_1304_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_elems_1349_);
v___x_1352_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec_ref(v_elems_1349_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_as_1303_);
lean_ctor_set(v___x_1353_, 1, v_a_1305_);
return v___x_1353_;
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_nat_dec_le(v___x_1351_, v___x_1351_);
if (v___x_1354_ == 0)
{
if (v___x_1352_ == 0)
{
lean_object* v___x_1355_; 
lean_dec_ref(v_elems_1349_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_as_1303_);
lean_ctor_set(v___x_1355_, 1, v_a_1305_);
return v___x_1355_;
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_of_nat(v___x_1351_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1349_, v___x_1356_, v___x_1357_, v_as_1303_, v_a_1305_);
lean_dec_ref(v_elems_1349_);
return v___x_1358_;
}
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1351_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1349_, v___x_1359_, v___x_1360_, v_as_1303_, v_a_1305_);
lean_dec_ref(v_elems_1349_);
return v___x_1361_;
}
}
}
default: 
{
lean_object* v_kvPairs_1362_; lean_object* v___x_1363_; 
v_kvPairs_1362_ = lean_ctor_get(v_o_1304_, 0);
lean_inc(v_kvPairs_1362_);
lean_dec_ref(v_o_1304_);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_as_1303_, v_kvPairs_1362_, v_a_1305_);
return v___x_1363_;
}
}
v___jp_1307_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_as_1303_);
lean_ctor_set(v___x_1309_, 1, v___y_1308_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* v_as_1364_, size_t v_i_1365_, size_t v_stop_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_usize_dec_eq(v_i_1365_, v_stop_1366_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_array_uget_borrowed(v_as_1364_, v_i_1365_);
lean_inc(v___x_1371_);
v___x_1372_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_b_1367_, v___x_1371_, v___y_1368_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v_a_1374_; size_t v___x_1375_; size_t v___x_1376_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
v_a_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1372_);
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1365_, v___x_1375_);
v_i_1365_ = v___x_1376_;
v_b_1367_ = v_a_1373_;
v___y_1368_ = v_a_1374_;
goto _start;
}
else
{
return v___x_1372_;
}
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_b_1367_);
lean_ctor_set(v___x_1378_, 1, v___y_1368_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_stop_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; lean_object* v_res_1387_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1381_);
lean_dec(v_stop_1381_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_as_1379_, v_i_boxed_1385_, v_stop_boxed_1386_, v_b_1382_, v___y_1383_);
lean_dec_ref(v_as_1379_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* v_init_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1388_, v_x_1389_, v___y_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* v_as_1393_, lean_object* v_o_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_as_1393_, v_o_1394_, v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v___y_1400_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_x_1398_);
lean_ctor_set(v___x_1402_, 1, v___y_1400_);
return v___x_1402_;
}
else
{
lean_object* v_value_1403_; lean_object* v_tail_1404_; lean_object* v___x_1405_; 
v_value_1403_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_value_1403_);
v_tail_1404_ = lean_ctor_get(v_x_1399_, 2);
lean_inc(v_tail_1404_);
lean_dec_ref(v_x_1399_);
v___x_1405_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_x_1398_, v_value_1403_, v___y_1400_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_a_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
v_a_1407_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1405_);
v_x_1398_ = v_a_1406_;
v_x_1399_ = v_tail_1404_;
v___y_1400_ = v_a_1407_;
goto _start;
}
else
{
lean_dec(v_tail_1404_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_x_1409_, v_x_1410_, v___y_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* v_as_1414_, size_t v_i_1415_, size_t v_stop_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_eq(v_i_1415_, v_stop_1416_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_array_uget_borrowed(v_as_1414_, v_i_1415_);
lean_inc(v___x_1421_);
v___x_1422_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_b_1417_, v___x_1421_, v___y_1418_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_a_1424_; size_t v___x_1425_; size_t v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
v_a_1424_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1422_);
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_add(v_i_1415_, v___x_1425_);
v_i_1415_ = v___x_1426_;
v_b_1417_ = v_a_1423_;
v___y_1418_ = v_a_1424_;
goto _start;
}
else
{
return v___x_1422_;
}
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1417_);
lean_ctor_set(v___x_1428_, 1, v___y_1418_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* v_as_1429_, lean_object* v_i_1430_, lean_object* v_stop_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
size_t v_i_boxed_1435_; size_t v_stop_boxed_1436_; lean_object* v_res_1437_; 
v_i_boxed_1435_ = lean_unbox_usize(v_i_1430_);
lean_dec(v_i_1430_);
v_stop_boxed_1436_ = lean_unbox_usize(v_stop_1431_);
lean_dec(v_stop_1431_);
v_res_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_as_1429_, v_i_boxed_1435_, v_stop_boxed_1436_, v_b_1432_, v___y_1433_);
lean_dec_ref(v_as_1429_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* v_map_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_buckets_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1472_; 
v_buckets_1443_ = lean_ctor_get(v_map_1440_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_map_1440_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_map_1440_, 0);
lean_dec(v_unused_1473_);
v___x_1445_ = v_map_1440_;
v_isShared_1446_ = v_isSharedCheck_1472_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_buckets_1443_);
lean_dec(v_map_1440_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1472_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___y_1451_; lean_object* v_a_1452_; lean_object* v___y_1459_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = ((lean_object*)(l_Lake_CacheMap_collectOutputDescrs___closed__0));
v___x_1449_ = lean_array_get_size(v_a_1441_);
v___x_1461_ = lean_array_get_size(v_buckets_1443_);
v___x_1462_ = lean_nat_dec_lt(v___x_1447_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec_ref(v_buckets_1443_);
lean_inc_ref(v_a_1441_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1448_);
lean_ctor_set(v___x_1463_, 1, v_a_1441_);
v___y_1451_ = v___x_1463_;
v_a_1452_ = v_a_1441_;
goto v___jp_1450_;
}
else
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_nat_dec_le(v___x_1461_, v___x_1461_);
if (v___x_1464_ == 0)
{
if (v___x_1462_ == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref(v_buckets_1443_);
lean_inc_ref(v_a_1441_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1448_);
lean_ctor_set(v___x_1465_, 1, v_a_1441_);
v___y_1451_ = v___x_1465_;
v_a_1452_ = v_a_1441_;
goto v___jp_1450_;
}
else
{
size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = lean_usize_of_nat(v___x_1461_);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1443_, v___x_1466_, v___x_1467_, v___x_1448_, v_a_1441_);
lean_dec_ref(v_buckets_1443_);
v___y_1459_ = v___x_1468_;
goto v___jp_1458_;
}
}
else
{
size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = lean_usize_of_nat(v___x_1461_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1443_, v___x_1469_, v___x_1470_, v___x_1448_, v_a_1441_);
lean_dec_ref(v_buckets_1443_);
v___y_1459_ = v___x_1471_;
goto v___jp_1458_;
}
}
v___jp_1450_:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_array_get_size(v_a_1452_);
v___x_1454_ = lean_nat_dec_eq(v___x_1449_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref(v___y_1451_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 1);
lean_ctor_set(v___x_1445_, 1, v_a_1452_);
lean_ctor_set(v___x_1445_, 0, v___x_1449_);
v___x_1456_ = v___x_1445_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_a_1452_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_dec_ref(v_a_1452_);
lean_del_object(v___x_1445_);
return v___y_1451_;
}
}
v___jp_1458_:
{
if (lean_obj_tag(v___y_1459_) == 0)
{
lean_object* v_a_1460_; 
v_a_1460_ = lean_ctor_get(v___y_1459_, 1);
lean_inc(v_a_1460_);
v___y_1451_ = v___y_1459_;
v_a_1452_ = v_a_1460_;
goto v___jp_1450_;
}
else
{
lean_del_object(v___x_1445_);
return v___y_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* v_map_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lake_CacheMap_collectOutputDescrs(v_map_1474_, v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* v_init_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_st_mk_ref(v_init_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* v_init_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lake_CacheRef_mk(v_init_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t v_inputHash_1484_, lean_object* v_cache_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_st_ref_take(v_cache_1485_);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v___x_1487_, v_inputHash_1484_);
v___x_1489_ = lean_st_ref_set(v_cache_1485_, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* v_inputHash_1490_, lean_object* v_cache_1491_, lean_object* v_a_1492_){
_start:
{
uint64_t v_inputHash_boxed_1493_; lean_object* v_res_1494_; 
v_inputHash_boxed_1493_ = lean_unbox_uint64(v_inputHash_1490_);
lean_dec_ref(v_inputHash_1490_);
v_res_1494_ = l_Lake_CacheRef_get_x3f(v_inputHash_boxed_1493_, v_cache_1491_);
lean_dec(v_cache_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* v_inst_1495_, uint64_t v_inputHash_1496_, lean_object* v_val_1497_, lean_object* v_cache_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1500_ = lean_st_ref_take(v_cache_1498_);
v___x_1501_ = lean_apply_1(v_inst_1495_, v_val_1497_);
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_1500_, v_inputHash_1496_, v___x_1501_);
v___x_1503_ = lean_st_ref_set(v_cache_1498_, v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* v_inst_1504_, lean_object* v_inputHash_1505_, lean_object* v_val_1506_, lean_object* v_cache_1507_, lean_object* v_a_1508_){
_start:
{
uint64_t v_inputHash_boxed_1509_; lean_object* v_res_1510_; 
v_inputHash_boxed_1509_ = lean_unbox_uint64(v_inputHash_1505_);
lean_dec_ref(v_inputHash_1505_);
v_res_1510_ = l_Lake_CacheRef_insert___redArg(v_inst_1504_, v_inputHash_boxed_1509_, v_val_1506_, v_cache_1507_);
lean_dec(v_cache_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* v_00_u03b1_1511_, lean_object* v_inst_1512_, uint64_t v_inputHash_1513_, lean_object* v_val_1514_, lean_object* v_cache_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = lean_st_ref_take(v_cache_1515_);
v___x_1518_ = lean_apply_1(v_inst_1512_, v_val_1514_);
v___x_1519_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_1517_, v_inputHash_1513_, v___x_1518_);
v___x_1520_ = lean_st_ref_set(v_cache_1515_, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_inst_1522_, lean_object* v_inputHash_1523_, lean_object* v_val_1524_, lean_object* v_cache_1525_, lean_object* v_a_1526_){
_start:
{
uint64_t v_inputHash_boxed_1527_; lean_object* v_res_1528_; 
v_inputHash_boxed_1527_ = lean_unbox_uint64(v_inputHash_1523_);
lean_dec_ref(v_inputHash_1523_);
v_res_1528_ = l_Lake_CacheRef_insert(v_00_u03b1_1521_, v_inst_1522_, v_inputHash_boxed_1527_, v_val_1524_, v_cache_1525_);
lean_dec(v_cache_1525_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object* v_s_1531_){
_start:
{
lean_inc_ref(v_s_1531_);
return v_s_1531_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object* v_s_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lake_CacheServiceName_ofString(v_s_1532_);
lean_dec_ref(v_s_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object* v_self_1534_){
_start:
{
lean_inc_ref(v_self_1534_);
return v_self_1534_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object* v_self_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lake_CacheServiceName_toString(v_self_1535_);
lean_dec_ref(v_self_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object* v_j_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Json_getStr_x3f(v_j_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1540_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1540_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object* v_self_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_self_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object* v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1563_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_unsigned_to_nat(0u);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object* v_x_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(v_x_1566_);
lean_dec_ref(v_x_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object* v_t_1568_, lean_object* v_k_1569_){
_start:
{
lean_object* v_s_1570_; lean_object* v___x_1571_; 
v_s_1570_ = lean_ctor_get(v_t_1568_, 0);
lean_inc_ref(v_s_1570_);
lean_dec_ref(v_t_1568_);
v___x_1571_ = lean_apply_1(v_k_1569_, v_s_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object* v_motive_1572_, lean_object* v_ctorIdx_1573_, lean_object* v_t_1574_, lean_object* v_h_1575_, lean_object* v_k_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1574_, v_k_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object* v_motive_1578_, lean_object* v_ctorIdx_1579_, lean_object* v_t_1580_, lean_object* v_h_1581_, lean_object* v_k_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(v_motive_1578_, v_ctorIdx_1579_, v_t_1580_, v_h_1581_, v_k_1582_);
lean_dec(v_ctorIdx_1579_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object* v_t_1584_, lean_object* v_str_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1584_, v_str_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object* v_motive_1587_, lean_object* v_t_1588_, lean_object* v_h_1589_, lean_object* v_str_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1588_, v_str_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object* v_t_1592_, lean_object* v_repo_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1592_, v_repo_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object* v_motive_1595_, lean_object* v_t_1596_, lean_object* v_h_1597_, lean_object* v_repo_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1596_, v_repo_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object* v_s_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_s_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object* v_fullName_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_fullName_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object* v_self_1604_){
_start:
{
if (lean_obj_tag(v_self_1604_) == 1)
{
uint8_t v___x_1605_; 
v___x_1605_ = 1;
return v___x_1605_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = 0;
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object* v_self_1607_){
_start:
{
uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_res_1608_ = l_Lake_CacheServiceScope_isRepo(v_self_1607_);
lean_dec_ref(v_self_1607_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object* v_self_1610_){
_start:
{
lean_object* v_s_1611_; 
v_s_1611_ = lean_ctor_get(v_self_1610_, 0);
lean_inc_ref(v_s_1611_);
return v_s_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object* v_self_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lake_CacheServiceScope_toString(v_self_1612_);
lean_dec_ref(v_self_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object* v_self_1616_){
_start:
{
lean_object* v_s_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_s_1617_ = lean_ctor_get(v_self_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_self_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v_self_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_s_1617_);
lean_dec(v_self_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 3);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_s_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheOutput_ofData(lean_object* v_data_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1636_, 0, v_data_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_ctor_set(v___x_1636_, 2, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 0)
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_box(0);
return v___x_1638_;
}
else
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_val_1639_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v_x_1637_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v_x_1637_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 3);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_val_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
static lean_object* _init_l_Lake_CacheOutput_toJson___closed__3(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1651_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__2));
v___x_1652_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1653_ = lean_box(1);
v___x_1654_ = l_Lake_JsonObject_insertJson(v___x_1653_, v___x_1652_, v___x_1651_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object* v_out_1658_){
_start:
{
lean_object* v_data_1659_; lean_object* v_service_x3f_1660_; lean_object* v_scope_x3f_1661_; lean_object* v_obj_1663_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_obj_1670_; 
v_data_1659_ = lean_ctor_get(v_out_1658_, 0);
lean_inc(v_data_1659_);
v_service_x3f_1660_ = lean_ctor_get(v_out_1658_, 1);
lean_inc(v_service_x3f_1660_);
v_scope_x3f_1661_ = lean_ctor_get(v_out_1658_, 2);
lean_inc(v_scope_x3f_1661_);
lean_dec_ref(v_out_1658_);
v___x_1667_ = lean_obj_once(&l_Lake_CacheOutput_toJson___closed__3, &l_Lake_CacheOutput_toJson___closed__3_once, _init_l_Lake_CacheOutput_toJson___closed__3);
v___x_1668_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1669_ = l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1660_);
v_obj_1670_ = l_Lake_JsonObject_insertJson(v___x_1667_, v___x_1668_, v___x_1669_);
if (lean_obj_tag(v_scope_x3f_1661_) == 1)
{
lean_object* v_val_1671_; lean_object* v___y_1673_; uint8_t v___x_1676_; 
v_val_1671_ = lean_ctor_get(v_scope_x3f_1661_, 0);
lean_inc(v_val_1671_);
lean_dec_ref(v_scope_x3f_1661_);
v___x_1676_ = l_Lake_CacheServiceScope_isRepo(v_val_1671_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___y_1673_ = v___x_1677_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___y_1673_ = v___x_1678_;
goto v___jp_1672_;
}
v___jp_1672_:
{
lean_object* v___x_1674_; lean_object* v_obj_1675_; 
v___x_1674_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(v_val_1671_);
v_obj_1675_ = l_Lake_JsonObject_insertJson(v_obj_1670_, v___y_1673_, v___x_1674_);
v_obj_1663_ = v_obj_1675_;
goto v___jp_1662_;
}
}
else
{
lean_dec(v_scope_x3f_1661_);
v_obj_1663_ = v_obj_1670_;
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1665_ = l_Lake_JsonObject_insertJson(v_obj_1663_, v___x_1664_, v_data_1659_);
v___x_1666_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1683_){
_start:
{
if (lean_obj_tag(v_x_1683_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Json_getStr_x3f(v_x_1683_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_a_1694_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v___x_1685_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1685_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_a_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Json_getStr_x3f(v_x_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1722_; 
v_a_1714_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1716_ = v___x_1705_;
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1705_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_a_1714_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1718_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object* v_k_1723_, lean_object* v_t_1724_){
_start:
{
if (lean_obj_tag(v_t_1724_) == 0)
{
lean_object* v_k_1725_; lean_object* v_l_1726_; lean_object* v_r_1727_; uint8_t v___x_1728_; 
v_k_1725_ = lean_ctor_get(v_t_1724_, 1);
v_l_1726_ = lean_ctor_get(v_t_1724_, 3);
v_r_1727_ = lean_ctor_get(v_t_1724_, 4);
v___x_1728_ = lean_string_dec_lt(v_k_1723_, v_k_1725_);
if (v___x_1728_ == 0)
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_string_dec_eq(v_k_1723_, v_k_1725_);
if (v___x_1729_ == 0)
{
v_t_1724_ = v_r_1727_;
goto _start;
}
else
{
return v___x_1729_;
}
}
else
{
v_t_1724_ = v_l_1726_;
goto _start;
}
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = 0;
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object* v_k_1733_, lean_object* v_t_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1733_, v_t_1734_);
lean_dec(v_t_1734_);
lean_dec_ref(v_k_1733_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object* v_json_1743_){
_start:
{
if (lean_obj_tag(v_json_1743_) == 5)
{
lean_object* v_kvPairs_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_kvPairs_1748_ = lean_ctor_get(v_json_1743_, 0);
v___x_1749_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1750_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v___x_1749_, v_kvPairs_1748_);
if (v___x_1750_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_inc(v_kvPairs_1748_);
lean_dec_ref(v_json_1743_);
v___x_1751_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1752_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1748_, v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; 
lean_dec(v_kvPairs_1748_);
v___x_1753_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__1));
return v___x_1753_;
}
else
{
lean_object* v_val_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1872_; 
v_val_1754_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1756_ = v___x_1752_;
v_isShared_1757_ = v_isSharedCheck_1872_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_val_1754_);
lean_dec(v___x_1752_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1872_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___y_1759_; lean_object* v_a_1760_; lean_object* v___y_1766_; lean_object* v___y_1769_; lean_object* v_a_1809_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1849_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1748_, v___x_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_box(0);
v_a_1809_ = v___x_1850_;
goto v___jp_1808_;
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1852_; 
v_val_1851_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_val_1851_);
lean_dec_ref(v___x_1849_);
v___x_1852_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_1851_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1756_);
lean_dec(v_val_1754_);
lean_dec(v_kvPairs_1748_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__4));
v___x_1858_ = lean_string_append(v___x_1857_, v_a_1853_);
lean_dec(v_a_1853_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_del_object(v___x_1756_);
lean_dec(v_val_1754_);
lean_dec(v_kvPairs_1748_);
v_a_1863_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1852_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1852_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 0);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1852_);
v_a_1809_ = v_a_1871_;
goto v___jp_1808_;
}
}
}
v___jp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1761_, 0, v_val_1754_);
lean_ctor_set(v___x_1761_, 1, v___y_1759_);
lean_ctor_set(v___x_1761_, 2, v_a_1760_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1761_);
v___x_1763_ = v___x_1756_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
v___jp_1765_:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_box(0);
v___y_1759_ = v___y_1766_;
v_a_1760_ = v___x_1767_;
goto v___jp_1758_;
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___x_1771_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1748_, v___x_1770_);
lean_dec(v_kvPairs_1748_);
if (lean_obj_tag(v___x_1771_) == 0)
{
v___y_1766_ = v___y_1769_;
goto v___jp_1765_;
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1807_; 
v_val_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1807_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_val_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1807_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1772_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1786_; 
lean_del_object(v___x_1774_);
lean_dec(v___y_1769_);
lean_del_object(v___x_1756_);
lean_dec(v_val_1754_);
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1786_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1786_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1781_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__2));
v___x_1782_ = lean_string_append(v___x_1781_, v_a_1777_);
lean_dec(v_a_1777_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1782_);
v___x_1784_ = v___x_1779_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_del_object(v___x_1774_);
lean_dec(v___y_1769_);
lean_del_object(v___x_1756_);
lean_dec(v_val_1754_);
v_a_1787_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1776_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1776_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 0);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v___x_1776_);
if (lean_obj_tag(v_a_1795_) == 1)
{
lean_object* v_val_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1806_; 
v_val_1796_ = lean_ctor_get(v_a_1795_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1798_ = v_a_1795_;
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_val_1796_);
lean_dec(v_a_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set_tag(v___x_1774_, 0);
lean_ctor_set(v___x_1774_, 0, v_val_1796_);
v___x_1801_ = v___x_1774_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_val_1796_);
v___x_1801_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
v___y_1759_ = v___y_1769_;
v_a_1760_ = v___x_1803_;
goto v___jp_1758_;
}
}
}
}
else
{
lean_dec(v_a_1795_);
lean_del_object(v___x_1774_);
v___y_1766_ = v___y_1769_;
goto v___jp_1765_;
}
}
}
}
}
}
v___jp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___x_1811_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1748_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
v___y_1769_ = v_a_1809_;
goto v___jp_1768_;
}
else
{
lean_object* v_val_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1847_; 
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1847_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_val_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1847_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1812_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1826_; 
lean_del_object(v___x_1814_);
lean_dec(v_a_1809_);
lean_del_object(v___x_1756_);
lean_dec(v_val_1754_);
lean_dec(v_kvPairs_1748_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__3));
v___x_1822_ = lean_string_append(v___x_1821_, v_a_1817_);
lean_dec(v_a_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_del_object(v___x_1814_);
lean_dec(v_a_1809_);
lean_del_object(v___x_1756_);
lean_dec(v_val_1754_);
lean_dec(v_kvPairs_1748_);
v_a_1827_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1816_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1816_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 0);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1835_; 
v_a_1835_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1816_);
if (lean_obj_tag(v_a_1835_) == 1)
{
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_kvPairs_1748_);
v_val_1836_ = lean_ctor_get(v_a_1835_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1838_ = v_a_1835_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v_a_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_val_1836_);
v___x_1841_ = v___x_1814_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_val_1836_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
v___y_1759_ = v_a_1809_;
v_a_1760_ = v___x_1843_;
goto v___jp_1758_;
}
}
}
}
else
{
lean_dec(v_a_1835_);
lean_del_object(v___x_1814_);
v___y_1769_ = v_a_1809_;
goto v___jp_1768_;
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
goto v___jp_1744_;
}
v___jp_1744_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1746_, 0, v_json_1743_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object* v_00_u03b2_1873_, lean_object* v_k_1874_, lean_object* v_t_1875_){
_start:
{
uint8_t v___x_1876_; 
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1874_, v_t_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object* v_00_u03b2_1877_, lean_object* v_k_1878_, lean_object* v_t_1879_){
_start:
{
uint8_t v_res_1880_; lean_object* v_r_1881_; 
v_res_1880_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(v_00_u03b2_1877_, v_k_1878_, v_t_1879_);
lean_dec(v_t_1879_);
lean_dec_ref(v_k_1878_);
v_r_1881_ = lean_box(v_res_1880_);
return v_r_1881_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache_default(void){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_System_instInhabitedFilePath_default;
return v___x_1884_;
}
}
static lean_object* _init_l_Lake_instInhabitedCache(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_System_instInhabitedFilePath_default;
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_1887_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1889_ = l_System_FilePath_join(v_cache_1887_, v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_1891_, uint64_t v_contentHash_1892_, lean_object* v_ext_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1894_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1895_ = l_System_FilePath_join(v_cache_1891_, v___x_1894_);
v___x_1896_ = lean_string_utf8_byte_size(v_ext_1893_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_nat_dec_eq(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1899_ = l_Lake_Hash_hex(v_contentHash_1892_);
v___x_1900_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_1901_ = lean_string_append(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_string_append(v___x_1901_, v_ext_1893_);
v___x_1903_ = l_System_FilePath_join(v___x_1895_, v___x_1902_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = l_Lake_Hash_hex(v_contentHash_1892_);
v___x_1905_ = l_System_FilePath_join(v___x_1895_, v___x_1904_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_1906_, lean_object* v_contentHash_1907_, lean_object* v_ext_1908_){
_start:
{
uint64_t v_contentHash_boxed_1909_; lean_object* v_res_1910_; 
v_contentHash_boxed_1909_ = lean_unbox_uint64(v_contentHash_1907_);
lean_dec_ref(v_contentHash_1907_);
v_res_1910_ = l_Lake_Cache_artifactPath(v_cache_1906_, v_contentHash_boxed_1909_, v_ext_1908_);
lean_dec_ref(v_ext_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_1911_, lean_object* v_descr_1912_){
_start:
{
uint64_t v_hash_1914_; lean_object* v_ext_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___y_1919_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_hash_1914_ = lean_ctor_get_uint64(v_descr_1912_, sizeof(void*)*1);
v_ext_1915_ = lean_ctor_get(v_descr_1912_, 0);
v___x_1916_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1917_ = l_System_FilePath_join(v_cache_1911_, v___x_1916_);
v___x_1933_ = lean_string_utf8_byte_size(v_ext_1915_);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_nat_dec_eq(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = l_Lake_Hash_hex(v_hash_1914_);
v___x_1937_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_1938_ = lean_string_append(v___x_1936_, v___x_1937_);
v___x_1939_ = lean_string_append(v___x_1938_, v_ext_1915_);
v___y_1919_ = v___x_1939_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lake_Hash_hex(v_hash_1914_);
v___y_1919_ = v___x_1940_;
goto v___jp_1918_;
}
v___jp_1918_:
{
lean_object* v_path_1920_; lean_object* v___x_1921_; 
v_path_1920_ = l_System_FilePath_join(v___x_1917_, v___y_1919_);
v___x_1921_ = lean_io_metadata(v_path_1920_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1931_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_modified_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v_modified_1926_ = lean_ctor_get(v_a_1922_, 1);
lean_inc_ref(v_modified_1926_);
lean_dec(v_a_1922_);
lean_inc_ref(v_path_1920_);
v___x_1927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1927_, 0, v_descr_1912_);
lean_ctor_set(v___x_1927_, 1, v_path_1920_);
lean_ctor_set(v___x_1927_, 2, v_path_1920_);
lean_ctor_set(v___x_1927_, 3, v_modified_1926_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 1);
lean_ctor_set(v___x_1924_, 0, v___x_1927_);
v___x_1929_ = v___x_1924_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
lean_object* v___x_1932_; 
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_path_1920_);
lean_dec_ref(v_descr_1912_);
v___x_1932_ = lean_box(0);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_1941_, lean_object* v_descr_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lake_Cache_getArtifact_x3f(v_cache_1941_, v_descr_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_1947_, lean_object* v_descr_1948_){
_start:
{
uint64_t v_hash_1950_; lean_object* v_ext_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___y_1955_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_hash_1950_ = lean_ctor_get_uint64(v_descr_1948_, sizeof(void*)*1);
v_ext_1951_ = lean_ctor_get(v_descr_1948_, 0);
v___x_1952_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_1953_ = l_System_FilePath_join(v_cache_1947_, v___x_1952_);
v___x_1984_ = lean_string_utf8_byte_size(v_ext_1951_);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_nat_dec_eq(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1987_ = l_Lake_Hash_hex(v_hash_1950_);
v___x_1988_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_1989_ = lean_string_append(v___x_1987_, v___x_1988_);
v___x_1990_ = lean_string_append(v___x_1989_, v_ext_1951_);
v___y_1955_ = v___x_1990_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lake_Hash_hex(v_hash_1950_);
v___y_1955_ = v___x_1991_;
goto v___jp_1954_;
}
v___jp_1954_:
{
lean_object* v_path_1956_; lean_object* v___x_1957_; 
v_path_1956_ = l_System_FilePath_join(v___x_1953_, v___y_1955_);
v___x_1957_ = lean_io_metadata(v_path_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1967_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1967_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1967_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_modified_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v_modified_1962_ = lean_ctor_get(v_a_1958_, 1);
lean_inc_ref(v_modified_1962_);
lean_dec(v_a_1958_);
lean_inc_ref(v_path_1956_);
v___x_1963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1963_, 0, v_descr_1948_);
lean_ctor_set(v___x_1963_, 1, v_path_1956_);
lean_ctor_set(v___x_1963_, 2, v_path_1956_);
lean_ctor_set(v___x_1963_, 3, v_modified_1962_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1963_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v_descr_1948_);
v_a_1968_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1970_ = v___x_1957_;
v_isShared_1971_ = v_isSharedCheck_1983_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1957_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1983_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
if (lean_obj_tag(v_a_1968_) == 11)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
lean_dec_ref(v_a_1968_);
v___x_1972_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_1973_ = lean_string_append(v___x_1972_, v_path_1956_);
lean_dec_ref(v_path_1956_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1973_);
v___x_1975_ = v___x_1970_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
lean_dec_ref(v_path_1956_);
v___x_1977_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_1978_ = lean_io_error_to_string(v_a_1968_);
v___x_1979_ = lean_string_append(v___x_1977_, v___x_1978_);
lean_dec_ref(v___x_1978_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1979_);
v___x_1981_ = v___x_1970_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_1992_, lean_object* v_descr_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lake_Cache_getArtifact(v_cache_1992_, v_descr_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object* v_cache_1996_, lean_object* v_out_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___y_2001_; lean_object* v___y_2002_; uint64_t v_hash_2004_; lean_object* v_ext_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___y_2009_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_hash_2004_ = lean_ctor_get_uint64(v_out_1997_, sizeof(void*)*1);
v_ext_2005_ = lean_ctor_get(v_out_1997_, 0);
v___x_2006_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2007_ = l_System_FilePath_join(v_cache_1996_, v___x_2006_);
v___x_2017_ = lean_string_utf8_byte_size(v_ext_2005_);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_nat_dec_eq(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2020_ = l_Lake_Hash_hex(v_hash_2004_);
v___x_2021_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2022_ = lean_string_append(v___x_2020_, v___x_2021_);
v___x_2023_ = lean_string_append(v___x_2022_, v_ext_2005_);
v___y_2009_ = v___x_2023_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lake_Hash_hex(v_hash_2004_);
v___y_2009_ = v___x_2024_;
goto v___jp_2008_;
}
v___jp_2000_:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___y_2001_);
lean_ctor_set(v___x_2003_, 1, v___y_2002_);
return v___x_2003_;
}
v___jp_2008_:
{
lean_object* v_art_2010_; uint8_t v___x_2011_; 
v_art_2010_ = l_System_FilePath_join(v___x_2007_, v___y_2009_);
v___x_2011_ = l_System_FilePath_pathExists(v_art_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2012_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2013_ = lean_string_append(v___x_2012_, v_art_2010_);
v___x_2014_ = 3;
v___x_2015_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*1, v___x_2014_);
v___x_2016_ = lean_array_push(v___y_1998_, v___x_2015_);
v___y_2001_ = v_art_2010_;
v___y_2002_ = v___x_2016_;
goto v___jp_2000_;
}
else
{
v___y_2001_ = v_art_2010_;
v___y_2002_ = v___y_1998_;
goto v___jp_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object* v_cache_2025_, lean_object* v_out_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lake_Cache_getArtifactPaths___lam__0(v_cache_2025_, v_out_2026_, v___y_2027_);
lean_dec_ref(v_out_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object* v_n_2030_, lean_object* v_f_2031_, lean_object* v_xs_2032_, lean_object* v_k_2033_, lean_object* v_acc_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_nat_dec_lt(v_k_2033_, v_n_2030_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_dec(v_k_2033_);
lean_dec_ref(v_f_2031_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_acc_2034_);
lean_ctor_set(v___x_2038_, 1, v___y_2035_);
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_array_fget_borrowed(v_xs_2032_, v_k_2033_);
lean_inc_ref(v_f_2031_);
lean_inc(v___x_2039_);
v___x_2040_ = lean_apply_3(v_f_2031_, v___x_2039_, v___y_2035_, lean_box(0));
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
v_a_2042_ = lean_ctor_get(v___x_2040_, 1);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2040_);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_nat_add(v_k_2033_, v___x_2043_);
lean_dec(v_k_2033_);
v___x_2045_ = lean_array_push(v_acc_2034_, v_a_2041_);
v_k_2033_ = v___x_2044_;
v_acc_2034_ = v___x_2045_;
v___y_2035_ = v_a_2042_;
goto _start;
}
else
{
lean_object* v_a_2047_; lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_acc_2034_);
lean_dec(v_k_2033_);
lean_dec_ref(v_f_2031_);
v_a_2047_ = lean_ctor_get(v___x_2040_, 0);
v_a_2048_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2040_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_inc(v_a_2047_);
lean_dec(v___x_2040_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2047_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object* v_n_2056_, lean_object* v_f_2057_, lean_object* v_xs_2058_, lean_object* v_k_2059_, lean_object* v_acc_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2056_, v_f_2057_, v_xs_2058_, v_k_2059_, v_acc_2060_, v___y_2061_);
lean_dec_ref(v_xs_2058_);
lean_dec(v_n_2056_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object* v_cache_2066_, lean_object* v_descrs_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___f_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___f_2070_ = lean_alloc_closure((void*)(l_Lake_Cache_getArtifactPaths___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2070_, 0, v_cache_2066_);
v___x_2071_ = lean_array_get_size(v_descrs_2067_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_a_2068_);
v___x_2074_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v___x_2071_, v___f_2070_, v_descrs_2067_, v___x_2072_, v___x_2073_, v_a_2068_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 1);
lean_inc(v_a_2075_);
v___x_2076_ = lean_array_get_size(v_a_2068_);
lean_dec_ref(v_a_2068_);
v___x_2077_ = lean_array_get_size(v_a_2075_);
v___x_2078_ = lean_nat_dec_eq(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; lean_object* v_unused_2087_; 
v_unused_2086_ = lean_ctor_get(v___x_2074_, 1);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v___x_2074_, 0);
lean_dec(v_unused_2087_);
v___x_2080_ = v___x_2074_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_dec(v___x_2074_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 1);
lean_ctor_set(v___x_2080_, 0, v___x_2076_);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_a_2075_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_dec(v_a_2075_);
return v___x_2074_;
}
}
else
{
lean_dec_ref(v_a_2068_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object* v_cache_2088_, lean_object* v_descrs_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lake_Cache_getArtifactPaths(v_cache_2088_, v_descrs_2089_, v_a_2090_);
lean_dec_ref(v_descrs_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object* v_00_u03b1_2093_, lean_object* v_00_u03b2_2094_, lean_object* v_n_2095_, lean_object* v_f_2096_, lean_object* v_xs_2097_, lean_object* v_k_2098_, lean_object* v_h_2099_, lean_object* v_acc_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(v_n_2095_, v_f_2096_, v_xs_2097_, v_k_2098_, v_acc_2100_, v___y_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_n_2106_, lean_object* v_f_2107_, lean_object* v_xs_2108_, lean_object* v_k_2109_, lean_object* v_h_2110_, lean_object* v_acc_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(v_00_u03b1_2104_, v_00_u03b2_2105_, v_n_2106_, v_f_2107_, v_xs_2108_, v_k_2109_, v_h_2110_, v_acc_2111_, v___y_2112_);
lean_dec_ref(v_xs_2108_);
lean_dec(v_n_2106_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2118_ = l_System_FilePath_join(v_cache_2116_, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2120_, lean_object* v_scope_2121_, uint64_t v_inputHash_2122_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2123_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2124_ = l_System_FilePath_join(v_cache_2120_, v___x_2123_);
v___x_2125_ = l_System_FilePath_join(v___x_2124_, v_scope_2121_);
v___x_2126_ = l_Lake_Hash_hex(v_inputHash_2122_);
v___x_2127_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2128_ = lean_string_append(v___x_2126_, v___x_2127_);
v___x_2129_ = l_System_FilePath_join(v___x_2125_, v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2130_, lean_object* v_scope_2131_, lean_object* v_inputHash_2132_){
_start:
{
uint64_t v_inputHash_boxed_2133_; lean_object* v_res_2134_; 
v_inputHash_boxed_2133_ = lean_unbox_uint64(v_inputHash_2132_);
lean_dec_ref(v_inputHash_2132_);
v_res_2134_ = l_Lake_Cache_outputsFile(v_cache_2130_, v_scope_2131_, v_inputHash_boxed_2133_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2135_, lean_object* v_scope_2136_, uint64_t v_inputHash_2137_, lean_object* v_out_2138_, lean_object* v_service_x3f_2139_, lean_object* v_remoteScope_x3f_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_file_2148_; lean_object* v___x_2149_; 
v___x_2142_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2143_ = l_System_FilePath_join(v_cache_2135_, v___x_2142_);
v___x_2144_ = l_System_FilePath_join(v___x_2143_, v_scope_2136_);
v___x_2145_ = l_Lake_Hash_hex(v_inputHash_2137_);
v___x_2146_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2147_ = lean_string_append(v___x_2145_, v___x_2146_);
v_file_2148_ = l_System_FilePath_join(v___x_2144_, v___x_2147_);
lean_inc_ref(v_file_2148_);
v___x_2149_ = l_Lake_createParentDirs(v_file_2148_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v___x_2149_);
v___x_2150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2150_, 0, v_out_2138_);
lean_ctor_set(v___x_2150_, 1, v_service_x3f_2139_);
lean_ctor_set(v___x_2150_, 2, v_remoteScope_x3f_2140_);
v___x_2151_ = l_Lake_CacheOutput_toJson(v___x_2150_);
v___x_2152_ = lean_unsigned_to_nat(80u);
v___x_2153_ = l_Lean_Json_pretty(v___x_2151_, v___x_2152_);
v___x_2154_ = l_IO_FS_writeFile(v_file_2148_, v___x_2153_);
lean_dec_ref(v___x_2153_);
lean_dec_ref(v_file_2148_);
return v___x_2154_;
}
else
{
lean_dec_ref(v_file_2148_);
lean_dec(v_remoteScope_x3f_2140_);
lean_dec(v_service_x3f_2139_);
lean_dec(v_out_2138_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2155_, lean_object* v_scope_2156_, lean_object* v_inputHash_2157_, lean_object* v_out_2158_, lean_object* v_service_x3f_2159_, lean_object* v_remoteScope_x3f_2160_, lean_object* v_a_2161_){
_start:
{
uint64_t v_inputHash_boxed_2162_; lean_object* v_res_2163_; 
v_inputHash_boxed_2162_ = lean_unbox_uint64(v_inputHash_2157_);
lean_dec_ref(v_inputHash_2157_);
v_res_2163_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2155_, v_scope_2156_, v_inputHash_boxed_2162_, v_out_2158_, v_service_x3f_2159_, v_remoteScope_x3f_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2164_, lean_object* v_cache_2165_, lean_object* v_scope_2166_, uint64_t v_inputHash_2167_, lean_object* v_outputs_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_apply_1(v_inst_2164_, v_outputs_2168_);
v___x_2171_ = lean_box(0);
v___x_2172_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2165_, v_scope_2166_, v_inputHash_2167_, v___x_2170_, v___x_2171_, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2173_, lean_object* v_cache_2174_, lean_object* v_scope_2175_, lean_object* v_inputHash_2176_, lean_object* v_outputs_2177_, lean_object* v_a_2178_){
_start:
{
uint64_t v_inputHash_boxed_2179_; lean_object* v_res_2180_; 
v_inputHash_boxed_2179_ = lean_unbox_uint64(v_inputHash_2176_);
lean_dec_ref(v_inputHash_2176_);
v_res_2180_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2173_, v_cache_2174_, v_scope_2175_, v_inputHash_boxed_2179_, v_outputs_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2181_, lean_object* v_inst_2182_, lean_object* v_cache_2183_, lean_object* v_scope_2184_, uint64_t v_inputHash_2185_, lean_object* v_outputs_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_apply_1(v_inst_2182_, v_outputs_2186_);
v___x_2189_ = lean_box(0);
v___x_2190_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2183_, v_scope_2184_, v_inputHash_2185_, v___x_2188_, v___x_2189_, v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_inst_2192_, lean_object* v_cache_2193_, lean_object* v_scope_2194_, lean_object* v_inputHash_2195_, lean_object* v_outputs_2196_, lean_object* v_a_2197_){
_start:
{
uint64_t v_inputHash_boxed_2198_; lean_object* v_res_2199_; 
v_inputHash_boxed_2198_ = lean_unbox_uint64(v_inputHash_2195_);
lean_dec_ref(v_inputHash_2195_);
v_res_2199_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2191_, v_inst_2192_, v_cache_2193_, v_scope_2194_, v_inputHash_boxed_2198_, v_outputs_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2200_, lean_object* v_scope_2201_, lean_object* v_service_x3f_2202_, lean_object* v_remoteScope_x3f_2203_, lean_object* v_x_2204_, lean_object* v_x_2205_){
_start:
{
if (lean_obj_tag(v_x_2205_) == 0)
{
lean_object* v___x_2207_; 
lean_dec(v_remoteScope_x3f_2203_);
lean_dec(v_service_x3f_2202_);
lean_dec_ref(v_scope_2201_);
lean_dec_ref(v_cache_2200_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v_x_2204_);
return v___x_2207_;
}
else
{
lean_object* v_key_2208_; lean_object* v_value_2209_; lean_object* v_tail_2210_; uint64_t v___x_2211_; lean_object* v___x_2212_; 
v_key_2208_ = lean_ctor_get(v_x_2205_, 0);
lean_inc(v_key_2208_);
v_value_2209_ = lean_ctor_get(v_x_2205_, 1);
lean_inc(v_value_2209_);
v_tail_2210_ = lean_ctor_get(v_x_2205_, 2);
lean_inc(v_tail_2210_);
lean_dec_ref(v_x_2205_);
v___x_2211_ = lean_unbox_uint64(v_key_2208_);
lean_dec(v_key_2208_);
lean_inc(v_remoteScope_x3f_2203_);
lean_inc(v_service_x3f_2202_);
lean_inc_ref(v_scope_2201_);
lean_inc_ref(v_cache_2200_);
v___x_2212_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2200_, v_scope_2201_, v___x_2211_, v_value_2209_, v_service_x3f_2202_, v_remoteScope_x3f_2203_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___x_2212_);
v_x_2204_ = v_a_2213_;
v_x_2205_ = v_tail_2210_;
goto _start;
}
else
{
lean_dec(v_tail_2210_);
lean_dec(v_remoteScope_x3f_2203_);
lean_dec(v_service_x3f_2202_);
lean_dec_ref(v_scope_2201_);
lean_dec_ref(v_cache_2200_);
return v___x_2212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2215_, lean_object* v_scope_2216_, lean_object* v_service_x3f_2217_, lean_object* v_remoteScope_x3f_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2215_, v_scope_2216_, v_service_x3f_2217_, v_remoteScope_x3f_2218_, v_x_2219_, v_x_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2223_, lean_object* v_scope_2224_, lean_object* v_service_x3f_2225_, lean_object* v_remoteScope_x3f_2226_, lean_object* v_as_2227_, size_t v_i_2228_, size_t v_stop_2229_, lean_object* v_b_2230_){
_start:
{
uint8_t v___x_2232_; 
v___x_2232_ = lean_usize_dec_eq(v_i_2228_, v_stop_2229_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_array_uget_borrowed(v_as_2227_, v_i_2228_);
v___x_2234_ = lean_box(0);
lean_inc(v___x_2233_);
lean_inc(v_remoteScope_x3f_2226_);
lean_inc(v_service_x3f_2225_);
lean_inc_ref(v_scope_2224_);
lean_inc_ref(v_cache_2223_);
v___x_2235_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2223_, v_scope_2224_, v_service_x3f_2225_, v_remoteScope_x3f_2226_, v___x_2234_, v___x_2233_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; size_t v___x_2237_; size_t v___x_2238_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2228_, v___x_2237_);
v_i_2228_ = v___x_2238_;
v_b_2230_ = v_a_2236_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2226_);
lean_dec(v_service_x3f_2225_);
lean_dec_ref(v_scope_2224_);
lean_dec_ref(v_cache_2223_);
return v___x_2235_;
}
}
else
{
lean_object* v___x_2240_; 
lean_dec(v_remoteScope_x3f_2226_);
lean_dec(v_service_x3f_2225_);
lean_dec_ref(v_scope_2224_);
lean_dec_ref(v_cache_2223_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_b_2230_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2241_, lean_object* v_scope_2242_, lean_object* v_service_x3f_2243_, lean_object* v_remoteScope_x3f_2244_, lean_object* v_as_2245_, lean_object* v_i_2246_, lean_object* v_stop_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_){
_start:
{
size_t v_i_boxed_2250_; size_t v_stop_boxed_2251_; lean_object* v_res_2252_; 
v_i_boxed_2250_ = lean_unbox_usize(v_i_2246_);
lean_dec(v_i_2246_);
v_stop_boxed_2251_ = lean_unbox_usize(v_stop_2247_);
lean_dec(v_stop_2247_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2241_, v_scope_2242_, v_service_x3f_2243_, v_remoteScope_x3f_2244_, v_as_2245_, v_i_boxed_2250_, v_stop_boxed_2251_, v_b_2248_);
lean_dec_ref(v_as_2245_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2253_, lean_object* v_scope_2254_, lean_object* v_map_2255_, lean_object* v_service_x3f_2256_, lean_object* v_remoteScope_x3f_2257_){
_start:
{
lean_object* v_buckets_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_buckets_2259_ = lean_ctor_get(v_map_2255_, 1);
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = lean_array_get_size(v_buckets_2259_);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_nat_dec_lt(v___x_2260_, v___x_2261_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
lean_dec(v_remoteScope_x3f_2257_);
lean_dec(v_service_x3f_2256_);
lean_dec_ref(v_scope_2254_);
lean_dec_ref(v_cache_2253_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
return v___x_2264_;
}
else
{
uint8_t v___x_2265_; 
v___x_2265_ = lean_nat_dec_le(v___x_2261_, v___x_2261_);
if (v___x_2265_ == 0)
{
if (v___x_2263_ == 0)
{
lean_object* v___x_2266_; 
lean_dec(v_remoteScope_x3f_2257_);
lean_dec(v_service_x3f_2256_);
lean_dec_ref(v_scope_2254_);
lean_dec_ref(v_cache_2253_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2262_);
return v___x_2266_;
}
else
{
size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = lean_usize_of_nat(v___x_2261_);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2253_, v_scope_2254_, v_service_x3f_2256_, v_remoteScope_x3f_2257_, v_buckets_2259_, v___x_2267_, v___x_2268_, v___x_2262_);
return v___x_2269_;
}
}
else
{
size_t v___x_2270_; size_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = lean_usize_of_nat(v___x_2261_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2253_, v_scope_2254_, v_service_x3f_2256_, v_remoteScope_x3f_2257_, v_buckets_2259_, v___x_2270_, v___x_2271_, v___x_2262_);
return v___x_2272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2273_, lean_object* v_scope_2274_, lean_object* v_map_2275_, lean_object* v_service_x3f_2276_, lean_object* v_remoteScope_x3f_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lake_Cache_writeMap(v_cache_2273_, v_scope_2274_, v_map_2275_, v_service_x3f_2276_, v_remoteScope_x3f_2277_);
lean_dec_ref(v_map_2275_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2282_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 0)
{
lean_object* v___x_2283_; 
v___x_2283_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
return v___x_2283_;
}
else
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lake_CacheOutput_fromJson_x3f(v_x_2282_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2301_; 
v_a_2293_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2295_ = v___x_2284_;
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2284_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2297_);
v___x_2299_ = v___x_2295_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2304_, lean_object* v_scope_2305_, uint64_t v_inputHash_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_path_2315_; lean_object* v___x_2316_; 
v___x_2309_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2310_ = l_System_FilePath_join(v_cache_2304_, v___x_2309_);
v___x_2311_ = l_System_FilePath_join(v___x_2310_, v_scope_2305_);
v___x_2312_ = l_Lake_Hash_hex(v_inputHash_2306_);
v___x_2313_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2314_ = lean_string_append(v___x_2312_, v___x_2313_);
v_path_2315_ = l_System_FilePath_join(v___x_2311_, v___x_2314_);
v___x_2316_ = l_IO_FS_readFile(v_path_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v_a_2319_; lean_object* v___x_2328_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2316_);
v___x_2328_ = l_Lean_Json_parse(v_a_2317_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v_a_2319_ = v_a_2329_;
goto v___jp_2318_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2328_);
v___x_2331_ = l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2330_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
v_a_2319_ = v_a_2332_;
goto v___jp_2318_;
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v_path_2315_);
v_a_2333_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2331_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_a_2333_);
lean_ctor_set(v___x_2334_, 1, v_a_2307_);
return v___x_2334_;
}
}
v___jp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2320_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2321_ = lean_string_append(v_path_2315_, v___x_2320_);
v___x_2322_ = lean_string_append(v___x_2321_, v_a_2319_);
lean_dec_ref(v_a_2319_);
v___x_2323_ = 2;
v___x_2324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*1, v___x_2323_);
v___x_2325_ = lean_array_push(v_a_2307_, v___x_2324_);
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
return v___x_2327_;
}
}
else
{
lean_object* v_a_2335_; 
v_a_2335_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2316_);
if (lean_obj_tag(v_a_2335_) == 11)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v_a_2335_);
lean_dec_ref(v_path_2315_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_a_2307_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2338_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2339_ = lean_string_append(v_path_2315_, v___x_2338_);
v___x_2340_ = lean_io_error_to_string(v_a_2335_);
v___x_2341_ = lean_string_append(v___x_2339_, v___x_2340_);
lean_dec_ref(v___x_2340_);
v___x_2342_ = 3;
v___x_2343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*1, v___x_2342_);
v___x_2344_ = lean_array_get_size(v_a_2307_);
v___x_2345_ = lean_array_push(v_a_2307_, v___x_2343_);
v___x_2346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
return v___x_2346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2347_, lean_object* v_scope_2348_, lean_object* v_inputHash_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
uint64_t v_inputHash_boxed_2352_; lean_object* v_res_2353_; 
v_inputHash_boxed_2352_ = lean_unbox_uint64(v_inputHash_2349_);
lean_dec_ref(v_inputHash_2349_);
v_res_2353_ = l_Lake_Cache_readOutputs_x3f(v_cache_2347_, v_scope_2348_, v_inputHash_boxed_2352_, v_a_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2355_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2357_ = l_System_FilePath_join(v_cache_2355_, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2359_, lean_object* v_scope_2360_, lean_object* v_rev_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2362_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2363_ = l_System_FilePath_join(v_cache_2359_, v___x_2362_);
v___x_2364_ = l_System_FilePath_join(v___x_2363_, v_scope_2360_);
v___x_2365_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2366_ = lean_string_append(v_rev_2361_, v___x_2365_);
v___x_2367_ = l_System_FilePath_join(v___x_2364_, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2371_ = lean_string_utf8_byte_size(v_self_2370_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_nat_dec_eq(v___x_2371_, v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lake_CachePlatform_isNone(v_self_2374_);
lean_dec_ref(v_self_2374_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_System_Platform_target;
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2378_){
_start:
{
lean_inc_ref(v_s_2378_);
return v_s_2378_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lake_CachePlatform_ofString(v_s_2379_);
lean_dec_ref(v_s_2379_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_string_length(v_self_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length___boxed(lean_object* v_self_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lake_CachePlatform_length(v_self_2383_);
lean_dec_ref(v_self_2383_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_string_utf8_byte_size(v_self_2386_);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = lean_nat_dec_eq(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_inc_ref(v_self_2386_);
return v_self_2386_;
}
else
{
lean_object* v___x_2390_; 
v___x_2390_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lake_CachePlatform_toString(v_self_2391_);
lean_dec_ref(v_self_2391_);
return v_res_2392_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2396_){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2397_ = lean_string_utf8_byte_size(v_self_2396_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = lean_nat_dec_eq(v___x_2397_, v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2400_){
_start:
{
uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_res_2401_ = l_Lake_CacheToolchain_isNone(v_self_2400_);
lean_dec_ref(v_self_2400_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lake_normalizeToolchain(v_s_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2405_){
_start:
{
lean_inc_ref(v_s_2405_);
return v_s_2405_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2406_);
lean_dec_ref(v_s_2406_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_string_length(v_self_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length___boxed(lean_object* v_self_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lake_CacheToolchain_length(v_self_2410_);
lean_dec_ref(v_self_2410_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2412_){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2413_ = lean_string_utf8_byte_size(v_self_2412_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_nat_dec_eq(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_inc_ref(v_self_2412_);
return v_self_2412_;
}
else
{
lean_object* v___x_2416_; 
v___x_2416_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lake_CacheToolchain_toString(v_self_2417_);
lean_dec_ref(v_self_2417_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2422_, lean_object* v_url_2423_, lean_object* v_path_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lake_Cache_getArtifactPaths___closed__0));
lean_inc_ref(v_path_2424_);
v___x_2428_ = l_Lake_download(v_url_2423_, v_path_2424_, v___x_2427_, v_a_2425_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2468_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2428_, 0);
lean_dec(v_unused_2469_);
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2468_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2468_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lake_computeBinFileHash(v_path_2424_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; uint64_t v___x_2435_; uint8_t v___x_2436_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref(v___x_2433_);
v___x_2435_ = lean_unbox_uint64(v_a_2434_);
lean_dec(v_a_2434_);
v___x_2436_ = lean_uint64_dec_eq(v___x_2435_, v_hash_2422_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2424_);
v___x_2438_ = lean_string_append(v_path_2424_, v___x_2437_);
v___x_2439_ = 3;
v___x_2440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*1, v___x_2439_);
v___x_2441_ = lean_array_push(v_a_2429_, v___x_2440_);
v___x_2442_ = lean_io_remove_file(v_path_2424_);
lean_dec_ref(v_path_2424_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
lean_dec_ref(v___x_2442_);
v___x_2443_ = lean_array_get_size(v___x_2441_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 1);
lean_ctor_set(v___x_2431_, 1, v___x_2441_);
lean_ctor_set(v___x_2431_, 0, v___x_2443_);
v___x_2445_ = v___x_2431_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2441_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v_a_2447_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2447_);
lean_dec_ref(v___x_2442_);
v___x_2448_ = lean_io_error_to_string(v_a_2447_);
v___x_2449_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set_uint8(v___x_2449_, sizeof(void*)*1, v___x_2439_);
v___x_2450_ = lean_array_get_size(v___x_2441_);
v___x_2451_ = lean_array_push(v___x_2441_, v___x_2449_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 1);
lean_ctor_set(v___x_2431_, 1, v___x_2451_);
lean_ctor_set(v___x_2431_, 0, v___x_2450_);
v___x_2453_ = v___x_2431_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
lean_dec_ref(v_path_2424_);
v___x_2455_ = lean_box(0);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2455_);
v___x_2457_ = v___x_2431_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_a_2429_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_dec_ref(v_path_2424_);
v_a_2459_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2459_);
lean_dec_ref(v___x_2433_);
v___x_2460_ = lean_io_error_to_string(v_a_2459_);
v___x_2461_ = 3;
v___x_2462_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*1, v___x_2461_);
v___x_2463_ = lean_array_get_size(v_a_2429_);
v___x_2464_ = lean_array_push(v_a_2429_, v___x_2462_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 1);
lean_ctor_set(v___x_2431_, 1, v___x_2464_);
lean_ctor_set(v___x_2431_, 0, v___x_2463_);
v___x_2466_ = v___x_2431_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_dec_ref(v_path_2424_);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2470_, lean_object* v_url_2471_, lean_object* v_path_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
uint64_t v_hash_boxed_2475_; lean_object* v_res_2476_; 
v_hash_boxed_2475_ = lean_unbox_uint64(v_hash_2470_);
lean_dec_ref(v_hash_2470_);
v_res_2476_ = l_Lake_downloadArtifactCore(v_hash_boxed_2475_, v_url_2471_, v_path_2472_, v_a_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Json_getNat_x3f(v_x_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2498_; 
v_a_2490_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2492_ = v___x_2481_;
v_isShared_2493_ = v_isSharedCheck_2498_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2481_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2498_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_a_2490_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2494_);
v___x_2496_ = v___x_2492_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2521_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2522_ = lean_unsigned_to_nat(14u);
v___x_2523_ = lean_mk_empty_array_with_capacity(v___x_2522_);
v___x_2524_ = lean_array_push(v___x_2523_, v___x_2521_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2526_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2527_ = lean_array_push(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2529_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2530_ = lean_array_push(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2532_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2533_ = lean_array_push(v___x_2532_, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2535_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2536_ = lean_array_push(v___x_2535_, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2538_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2539_ = lean_array_push(v___x_2538_, v___x_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2543_, lean_object* v_contentType_2544_, lean_object* v_url_2545_, lean_object* v_key_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___y_2550_; lean_object* v_a_2551_; lean_object* v_stderr_2564_; lean_object* v___y_2573_; lean_object* v___y_2576_; lean_object* v_a_2577_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v_stderr_2616_; lean_object* v_a_2617_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2631_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2632_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2633_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2634_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2635_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2636_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2637_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2638_ = lean_string_append(v___x_2637_, v_contentType_2544_);
v___x_2639_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2640_ = lean_array_push(v___x_2639_, v_key_2546_);
v___x_2641_ = lean_array_push(v___x_2640_, v___x_2633_);
v___x_2642_ = lean_array_push(v___x_2641_, v___x_2634_);
v___x_2643_ = lean_array_push(v___x_2642_, v___x_2635_);
v___x_2644_ = lean_array_push(v___x_2643_, v_file_2543_);
v___x_2645_ = lean_array_push(v___x_2644_, v_url_2545_);
v___x_2646_ = lean_array_push(v___x_2645_, v___x_2636_);
v___x_2647_ = lean_array_push(v___x_2646_, v___x_2638_);
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2651_ = 1;
v___x_2652_ = 0;
v___x_2653_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2653_, 0, v___x_2631_);
lean_ctor_set(v___x_2653_, 1, v___x_2632_);
lean_ctor_set(v___x_2653_, 2, v___x_2647_);
lean_ctor_set(v___x_2653_, 3, v___x_2648_);
lean_ctor_set(v___x_2653_, 4, v___x_2650_);
lean_ctor_set_uint8(v___x_2653_, sizeof(void*)*5, v___x_2651_);
lean_ctor_set_uint8(v___x_2653_, sizeof(void*)*5 + 1, v___x_2652_);
v___x_2654_ = l_Lake_captureProc_x27(v___x_2653_, v___x_2650_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_a_2656_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
v_a_2656_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2656_);
lean_dec_ref(v___x_2654_);
v___x_2670_ = lean_array_get_size(v_a_2656_);
v___x_2671_ = lean_nat_dec_lt(v___x_2649_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_dec(v_a_2656_);
goto v___jp_2657_;
}
else
{
lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_nat_dec_le(v___x_2670_, v___x_2670_);
if (v___x_2673_ == 0)
{
if (v___x_2671_ == 0)
{
lean_dec(v_a_2656_);
goto v___jp_2657_;
}
else
{
size_t v___x_2674_; size_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = ((size_t)0ULL);
v___x_2675_ = lean_usize_of_nat(v___x_2670_);
lean_inc_ref(v_a_2547_);
v___x_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2656_, v___x_2674_, v___x_2675_, v___x_2672_, v_a_2547_);
lean_dec(v_a_2656_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_dec_ref(v___x_2676_);
goto v___jp_2657_;
}
else
{
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2547_);
return v___x_2676_;
}
}
}
else
{
size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = lean_usize_of_nat(v___x_2670_);
lean_inc_ref(v_a_2547_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2656_, v___x_2677_, v___x_2678_, v___x_2672_, v_a_2547_);
lean_dec(v_a_2656_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2657_;
}
else
{
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2547_);
return v___x_2679_;
}
}
}
v___jp_2657_:
{
lean_object* v_stderr_2658_; lean_object* v___x_2659_; 
v_stderr_2658_ = lean_ctor_get(v_a_2655_, 1);
lean_inc_ref(v_stderr_2658_);
v___x_2659_ = l_Lean_Json_parse(v_stderr_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; 
lean_inc_ref(v_stderr_2658_);
lean_dec(v_a_2655_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v_stderr_2616_ = v_stderr_2658_;
v_a_2617_ = v_a_2660_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2659_);
v___x_2662_ = l_Lean_Json_getObj_x3f(v_a_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; 
lean_inc_ref(v_stderr_2658_);
lean_dec(v_a_2655_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2662_);
v_stderr_2616_ = v_stderr_2658_;
v_a_2617_ = v_a_2663_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_a_2664_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2662_);
v___x_2665_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2666_ = l_Lake_JsonObject_getJson_x3f(v_a_2664_, v___x_2665_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_inc_ref(v_stderr_2658_);
lean_dec(v_a_2664_);
lean_dec(v_a_2655_);
v_stderr_2564_ = v_stderr_2658_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_val_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref(v___x_2666_);
v___x_2668_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2667_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref(v___x_2668_);
v___y_2604_ = v_a_2664_;
v___y_2605_ = v_a_2655_;
goto v___jp_2603_;
}
else
{
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref(v___x_2668_);
v___y_2604_ = v_a_2664_;
v___y_2605_ = v_a_2655_;
goto v___jp_2603_;
}
else
{
lean_object* v_a_2669_; 
lean_dec(v_a_2664_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v___y_2576_ = v_a_2655_;
v_a_2577_ = v_a_2669_;
goto v___jp_2575_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v_a_2680_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2654_);
v___x_2681_ = lean_array_get_size(v_a_2680_);
v___x_2682_ = lean_nat_dec_lt(v___x_2649_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2547_);
v___x_2683_ = lean_box(0);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
else
{
lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = lean_box(0);
v___x_2686_ = lean_nat_dec_le(v___x_2681_, v___x_2681_);
if (v___x_2686_ == 0)
{
if (v___x_2682_ == 0)
{
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2547_);
goto v___jp_2628_;
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = lean_usize_of_nat(v___x_2681_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2680_, v___x_2687_, v___x_2688_, v___x_2685_, v_a_2547_);
lean_dec(v_a_2680_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_dec_ref(v___x_2689_);
goto v___jp_2628_;
}
else
{
return v___x_2689_;
}
}
}
else
{
size_t v___x_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = lean_usize_of_nat(v___x_2681_);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2680_, v___x_2690_, v___x_2691_, v___x_2685_, v_a_2547_);
lean_dec(v_a_2680_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_dec_ref(v___x_2692_);
goto v___jp_2628_;
}
else
{
return v___x_2692_;
}
}
}
}
v___jp_2549_:
{
lean_object* v_stderr_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_stderr_2552_ = lean_ctor_get(v___y_2550_, 1);
lean_inc_ref(v_stderr_2552_);
lean_dec_ref(v___y_2550_);
v___x_2553_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2554_ = lean_string_append(v___x_2553_, v_a_2551_);
lean_dec_ref(v_a_2551_);
v___x_2555_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2556_ = lean_string_append(v___x_2554_, v___x_2555_);
v___x_2557_ = lean_string_append(v___x_2556_, v_stderr_2552_);
lean_dec_ref(v_stderr_2552_);
v___x_2558_ = 3;
v___x_2559_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*1, v___x_2558_);
v___x_2560_ = lean_apply_2(v_a_2547_, v___x_2559_, lean_box(0));
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
v___jp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2565_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2566_ = lean_string_append(v___x_2565_, v_stderr_2564_);
lean_dec_ref(v_stderr_2564_);
v___x_2567_ = 3;
v___x_2568_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*1, v___x_2567_);
v___x_2569_ = lean_apply_2(v_a_2547_, v___x_2568_, lean_box(0));
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
v___jp_2572_:
{
lean_object* v_stderr_2574_; 
v_stderr_2574_ = lean_ctor_get(v___y_2573_, 1);
lean_inc_ref(v_stderr_2574_);
lean_dec_ref(v___y_2573_);
v_stderr_2564_ = v_stderr_2574_;
goto v___jp_2563_;
}
v___jp_2575_:
{
if (lean_obj_tag(v_a_2577_) == 0)
{
v___y_2573_ = v___y_2576_;
goto v___jp_2572_;
}
else
{
lean_object* v_val_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2602_; 
v_val_2578_ = lean_ctor_get(v_a_2577_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2580_ = v_a_2577_;
v_isShared_2581_ = v_isSharedCheck_2602_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_val_2578_);
lean_dec(v_a_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2602_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = lean_unsigned_to_nat(200u);
v___x_2583_ = lean_nat_dec_eq(v_val_2578_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v_stdout_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v_stdout_2584_ = lean_ctor_get(v___y_2576_, 0);
lean_inc_ref(v_stdout_2584_);
lean_dec_ref(v___y_2576_);
v___x_2585_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2586_ = l_Nat_reprFast(v_val_2578_);
v___x_2587_ = lean_string_append(v___x_2585_, v___x_2586_);
lean_dec_ref(v___x_2586_);
v___x_2588_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2589_ = lean_string_append(v___x_2587_, v___x_2588_);
v___x_2590_ = lean_string_append(v___x_2589_, v_stdout_2584_);
lean_dec_ref(v_stdout_2584_);
v___x_2591_ = 3;
v___x_2592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set_uint8(v___x_2592_, sizeof(void*)*1, v___x_2591_);
v___x_2593_ = lean_apply_2(v_a_2547_, v___x_2592_, lean_box(0));
v___x_2594_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2594_);
v___x_2596_ = v___x_2580_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_val_2578_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v_a_2547_);
v___x_2598_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2598_);
v___x_2600_ = v___x_2580_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
v___jp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2607_ = l_Lake_JsonObject_getJson_x3f(v___y_2604_, v___x_2606_);
lean_dec(v___y_2604_);
if (lean_obj_tag(v___x_2607_) == 0)
{
v___y_2573_ = v___y_2605_;
goto v___jp_2572_;
}
else
{
lean_object* v_val_2608_; lean_object* v___x_2609_; 
v_val_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_val_2608_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2608_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
v___x_2611_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2612_ = lean_string_append(v___x_2611_, v_a_2610_);
lean_dec(v_a_2610_);
v___y_2550_ = v___y_2605_;
v_a_2551_ = v___x_2612_;
goto v___jp_2549_;
}
else
{
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2613_; 
v_a_2613_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2609_);
v___y_2550_ = v___y_2605_;
v_a_2551_ = v_a_2613_;
goto v___jp_2549_;
}
else
{
lean_object* v_a_2614_; 
v_a_2614_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2609_);
v___y_2576_ = v___y_2605_;
v_a_2577_ = v_a_2614_;
goto v___jp_2575_;
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2618_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2619_ = lean_string_append(v___x_2618_, v_a_2617_);
lean_dec_ref(v_a_2617_);
v___x_2620_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2621_ = lean_string_append(v___x_2619_, v___x_2620_);
v___x_2622_ = lean_string_append(v___x_2621_, v_stderr_2616_);
lean_dec_ref(v_stderr_2616_);
v___x_2623_ = 3;
v___x_2624_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*1, v___x_2623_);
v___x_2625_ = lean_apply_2(v_a_2547_, v___x_2624_, lean_box(0));
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
v___jp_2628_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_box(0);
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2693_, lean_object* v_contentType_2694_, lean_object* v_url_2695_, lean_object* v_key_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2693_, v_contentType_2694_, v_url_2695_, v_key_2696_, v_a_2697_);
lean_dec_ref(v_contentType_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2700_){
_start:
{
lean_object* v_name_x3f_2701_; 
v_name_x3f_2701_ = lean_ctor_get(v_service_2700_, 0);
lean_inc(v_name_x3f_2701_);
return v_name_x3f_2701_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lake_CacheService_name_x3f(v_service_2702_);
lean_dec_ref(v_service_2702_);
return v_res_2703_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2704_){
_start:
{
uint8_t v_isReservoir_2705_; 
v_isReservoir_2705_ = lean_ctor_get_uint8(v_service_2704_, sizeof(void*)*5);
return v_isReservoir_2705_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2706_){
_start:
{
uint8_t v_res_2707_; lean_object* v_r_2708_; 
v_res_2707_ = l_Lake_CacheService_isReservoir(v_service_2706_);
lean_dec_ref(v_service_2706_);
v_r_2708_ = lean_box(v_res_2707_);
return v_r_2708_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2709_, lean_object* v_name_x3f_2710_){
_start:
{
lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2712_ = 1;
v___x_2713_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2713_, 0, v_name_x3f_2710_);
lean_ctor_set(v___x_2713_, 1, v___x_2711_);
lean_ctor_set(v___x_2713_, 2, v___x_2711_);
lean_ctor_set(v___x_2713_, 3, v___x_2711_);
lean_ctor_set(v___x_2713_, 4, v_apiEndpoint_2709_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*5, v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2714_, lean_object* v_artifactEndpoint_2715_, lean_object* v_revisionEndpoint_2716_){
_start:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2717_ = lean_box(0);
v___x_2718_ = 0;
v___x_2719_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2720_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2720_, 0, v___x_2717_);
lean_ctor_set(v___x_2720_, 1, v_key_2714_);
lean_ctor_set(v___x_2720_, 2, v_artifactEndpoint_2715_);
lean_ctor_set(v___x_2720_, 3, v_revisionEndpoint_2716_);
lean_ctor_set(v___x_2720_, 4, v___x_2719_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*5, v___x_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2721_, lean_object* v_revisionEndpoint_2722_, lean_object* v_name_x3f_2723_){
_start:
{
lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2725_ = 0;
v___x_2726_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2726_, 0, v_name_x3f_2723_);
lean_ctor_set(v___x_2726_, 1, v___x_2724_);
lean_ctor_set(v___x_2726_, 2, v_artifactEndpoint_2721_);
lean_ctor_set(v___x_2726_, 3, v_revisionEndpoint_2722_);
lean_ctor_set(v___x_2726_, 4, v___x_2724_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*5, v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2727_, lean_object* v_name_x3f_2728_){
_start:
{
lean_object* v___x_2729_; uint8_t v___x_2730_; lean_object* v___x_2731_; 
v___x_2729_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_2730_ = 0;
v___x_2731_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2731_, 0, v_name_x3f_2728_);
lean_ctor_set(v___x_2731_, 1, v___x_2729_);
lean_ctor_set(v___x_2731_, 2, v_artifactEndpoint_2727_);
lean_ctor_set(v___x_2731_, 3, v___x_2729_);
lean_ctor_set(v___x_2731_, 4, v___x_2729_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*5, v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2732_, lean_object* v_key_2733_){
_start:
{
lean_object* v_name_x3f_2734_; lean_object* v_artifactEndpoint_2735_; lean_object* v_revisionEndpoint_2736_; uint8_t v_isReservoir_2737_; lean_object* v_apiEndpoint_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
v_name_x3f_2734_ = lean_ctor_get(v_service_2732_, 0);
v_artifactEndpoint_2735_ = lean_ctor_get(v_service_2732_, 2);
v_revisionEndpoint_2736_ = lean_ctor_get(v_service_2732_, 3);
v_isReservoir_2737_ = lean_ctor_get_uint8(v_service_2732_, sizeof(void*)*5);
v_apiEndpoint_2738_ = lean_ctor_get(v_service_2732_, 4);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_service_2732_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; 
v_unused_2746_ = lean_ctor_get(v_service_2732_, 1);
lean_dec(v_unused_2746_);
v___x_2740_ = v_service_2732_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_apiEndpoint_2738_);
lean_inc(v_revisionEndpoint_2736_);
lean_inc(v_artifactEndpoint_2735_);
lean_inc(v_name_x3f_2734_);
lean_dec(v_service_2732_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 1, v_key_2733_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_name_x3f_2734_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_key_2733_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_artifactEndpoint_2735_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_revisionEndpoint_2736_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_apiEndpoint_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*5, v_isReservoir_2737_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2753_);
lean_dec_ref(v_s_2753_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2755_, lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v_a_2758_, lean_object* v_b_2759_){
_start:
{
if (lean_obj_tag(v_a_2758_) == 0)
{
lean_object* v_currPos_2760_; lean_object* v_searcher_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2795_; 
v_currPos_2760_ = lean_ctor_get(v_a_2758_, 0);
v_searcher_2761_ = lean_ctor_get(v_a_2758_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_a_2758_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2763_ = v_a_2758_;
v_isShared_2764_ = v_isSharedCheck_2795_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_searcher_2761_);
lean_inc(v_currPos_2760_);
lean_dec(v_a_2758_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2795_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v_startInclusive_2765_; lean_object* v_endExclusive_2766_; uint32_t v___x_2767_; lean_object* v_it_2769_; lean_object* v_startInclusive_2770_; lean_object* v_endExclusive_2771_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v_startInclusive_2765_ = lean_ctor_get(v___x_2756_, 1);
v_endExclusive_2766_ = lean_ctor_get(v___x_2756_, 2);
v___x_2767_ = 47;
v___x_2776_ = lean_nat_sub(v_endExclusive_2766_, v_startInclusive_2765_);
v___x_2777_ = lean_nat_dec_eq(v_searcher_2761_, v___x_2776_);
lean_dec(v___x_2776_);
if (v___x_2777_ == 0)
{
uint32_t v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = lean_string_utf8_get_fast(v_scope_2755_, v_searcher_2761_);
v___x_2779_ = lean_uint32_dec_eq(v___x_2778_, v___x_2767_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = lean_string_utf8_next_fast(v_scope_2755_, v_searcher_2761_);
lean_dec(v_searcher_2761_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 1, v___x_2780_);
v___x_2782_ = v___x_2763_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_currPos_2760_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
v_a_2758_ = v___x_2782_;
goto _start;
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v_slice_2788_; lean_object* v_nextIt_2790_; 
v___x_2785_ = lean_string_utf8_next_fast(v_scope_2755_, v_searcher_2761_);
v___x_2786_ = lean_nat_sub(v___x_2785_, v_searcher_2761_);
v___x_2787_ = lean_nat_add(v_searcher_2761_, v___x_2786_);
lean_dec(v___x_2786_);
v_slice_2788_ = l_String_Slice_subslice_x21(v___x_2756_, v_currPos_2760_, v_searcher_2761_);
lean_inc(v___x_2787_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 1, v___x_2787_);
lean_ctor_set(v___x_2763_, 0, v___x_2787_);
v_nextIt_2790_ = v___x_2763_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___x_2787_);
v_nextIt_2790_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v_startInclusive_2791_; lean_object* v_endExclusive_2792_; 
v_startInclusive_2791_ = lean_ctor_get(v_slice_2788_, 0);
lean_inc(v_startInclusive_2791_);
v_endExclusive_2792_ = lean_ctor_get(v_slice_2788_, 1);
lean_inc(v_endExclusive_2792_);
lean_dec_ref(v_slice_2788_);
v_it_2769_ = v_nextIt_2790_;
v_startInclusive_2770_ = v_startInclusive_2791_;
v_endExclusive_2771_ = v_endExclusive_2792_;
goto v___jp_2768_;
}
}
}
else
{
lean_object* v___x_2794_; 
lean_del_object(v___x_2763_);
lean_dec(v_searcher_2761_);
v___x_2794_ = lean_box(1);
lean_inc(v___x_2757_);
v_it_2769_ = v___x_2794_;
v_startInclusive_2770_ = v_currPos_2760_;
v_endExclusive_2771_ = v___x_2757_;
goto v___jp_2768_;
}
v___jp_2768_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_string_utf8_extract(v_scope_2755_, v_startInclusive_2770_, v_endExclusive_2771_);
lean_dec(v_endExclusive_2771_);
lean_dec(v_startInclusive_2770_);
v___x_2773_ = lean_string_push(v_b_2759_, v___x_2767_);
v___x_2774_ = l_Lake_uriEncode(v___x_2772_, v___x_2773_);
v_a_2758_ = v_it_2769_;
v_b_2759_ = v___x_2774_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2757_);
return v_b_2759_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_2796_, lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v_a_2799_, lean_object* v_b_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2796_, v___x_2797_, v___x_2798_, v_a_2799_, v_b_2800_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_scope_2796_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_2802_, lean_object* v_scope_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = lean_string_utf8_byte_size(v_scope_2803_);
lean_inc_ref(v_scope_2803_);
v___x_2806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2806_, 0, v_scope_2803_);
lean_ctor_set(v___x_2806_, 1, v___x_2804_);
lean_ctor_set(v___x_2806_, 2, v___x_2805_);
v___x_2807_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_2806_);
v___x_2808_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2803_, v___x_2806_, v___x_2805_, v___x_2807_, v_endpoint_2802_);
lean_dec_ref(v___x_2806_);
lean_dec_ref(v_scope_2803_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_2809_, lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v_inst_2812_, lean_object* v_R_2813_, lean_object* v_a_2814_, lean_object* v_b_2815_, lean_object* v_c_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2809_, v___x_2810_, v___x_2811_, v_a_2814_, v_b_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v_inst_2821_, lean_object* v_R_2822_, lean_object* v_a_2823_, lean_object* v_b_2824_, lean_object* v_c_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_2818_, v___x_2819_, v___x_2820_, v_inst_2821_, v_R_2822_, v_a_2823_, v_b_2824_, v_c_2825_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v_scope_2818_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_2827_, lean_object* v_scope_2828_){
_start:
{
lean_object* v_artifactEndpoint_2829_; lean_object* v___x_2830_; 
v_artifactEndpoint_2829_ = lean_ctor_get(v_service_2827_, 2);
lean_inc_ref(v_artifactEndpoint_2829_);
lean_dec_ref(v_service_2827_);
v___x_2830_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_2829_, v_scope_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_2833_, lean_object* v_service_2834_, lean_object* v_scope_2835_){
_start:
{
lean_object* v___y_2837_; lean_object* v_s_2844_; lean_object* v___x_2845_; 
v_s_2844_ = lean_ctor_get(v_scope_2835_, 0);
lean_inc_ref(v_s_2844_);
lean_dec_ref(v_scope_2835_);
v___x_2845_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_2834_, v_s_2844_);
v___y_2837_ = v___x_2845_;
goto v___jp_2836_;
v___jp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2838_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_2839_ = lean_string_append(v___y_2837_, v___x_2838_);
v___x_2840_ = l_Lake_Hash_hex(v_contentHash_2833_);
v___x_2841_ = lean_string_append(v___x_2839_, v___x_2840_);
lean_dec_ref(v___x_2840_);
v___x_2842_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2843_ = lean_string_append(v___x_2841_, v___x_2842_);
return v___x_2843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_2846_, lean_object* v_service_2847_, lean_object* v_scope_2848_){
_start:
{
uint64_t v_contentHash_boxed_2849_; lean_object* v_res_2850_; 
v_contentHash_boxed_2849_ = lean_unbox_uint64(v_contentHash_2846_);
lean_dec_ref(v_contentHash_2846_);
v_res_2850_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_2849_, v_service_2847_, v_scope_2848_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_2854_, lean_object* v_service_2855_, lean_object* v_scope_2856_){
_start:
{
lean_object* v___y_2858_; uint8_t v_isReservoir_2865_; 
v_isReservoir_2865_ = lean_ctor_get_uint8(v_service_2855_, sizeof(void*)*5);
if (v_isReservoir_2865_ == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_2854_, v_service_2855_, v_scope_2856_);
return v___x_2866_;
}
else
{
if (lean_obj_tag(v_scope_2856_) == 0)
{
lean_object* v_apiEndpoint_2867_; lean_object* v_s_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_apiEndpoint_2867_ = lean_ctor_get(v_service_2855_, 4);
lean_inc_ref(v_apiEndpoint_2867_);
lean_dec_ref(v_service_2855_);
v_s_2868_ = lean_ctor_get(v_scope_2856_, 0);
lean_inc_ref(v_s_2868_);
lean_dec_ref(v_scope_2856_);
v___x_2869_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_2870_ = lean_string_append(v_apiEndpoint_2867_, v___x_2869_);
v___x_2871_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2870_, v_s_2868_);
v___y_2858_ = v___x_2871_;
goto v___jp_2857_;
}
else
{
lean_object* v_apiEndpoint_2872_; lean_object* v_s_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_apiEndpoint_2872_ = lean_ctor_get(v_service_2855_, 4);
lean_inc_ref(v_apiEndpoint_2872_);
lean_dec_ref(v_service_2855_);
v_s_2873_ = lean_ctor_get(v_scope_2856_, 0);
lean_inc_ref(v_s_2873_);
lean_dec_ref(v_scope_2856_);
v___x_2874_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_2875_ = lean_string_append(v_apiEndpoint_2872_, v___x_2874_);
v___x_2876_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2875_, v_s_2873_);
v___y_2858_ = v___x_2876_;
goto v___jp_2857_;
}
}
v___jp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2859_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_2860_ = lean_string_append(v___y_2858_, v___x_2859_);
v___x_2861_ = l_Lake_Hash_hex(v_contentHash_2854_);
v___x_2862_ = lean_string_append(v___x_2860_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2864_ = lean_string_append(v___x_2862_, v___x_2863_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_2877_, lean_object* v_service_2878_, lean_object* v_scope_2879_){
_start:
{
uint64_t v_contentHash_boxed_2880_; lean_object* v_res_2881_; 
v_contentHash_boxed_2880_ = lean_unbox_uint64(v_contentHash_2877_);
lean_dec_ref(v_contentHash_2877_);
v_res_2881_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_2880_, v_service_2878_, v_scope_2879_);
return v_res_2881_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_2886_ = lean_array_get_size(v___x_2885_);
return v___x_2886_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = lean_nat_dec_lt(v___x_2888_, v___x_2887_);
return v___x_2889_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_2891_ = lean_nat_dec_le(v___x_2890_, v___x_2890_);
return v___x_2891_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_2892_; size_t v___x_2893_; 
v___x_2892_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_2893_ = lean_usize_of_nat(v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_2894_, lean_object* v_cache_2895_, lean_object* v_service_2896_, lean_object* v_scope_2897_, uint8_t v_force_2898_, lean_object* v_a_2899_){
_start:
{
uint64_t v_hash_2904_; lean_object* v_ext_2905_; lean_object* v_url_2906_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2970_; lean_object* v___y_2973_; uint8_t v_a_2974_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___y_2980_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_hash_2904_ = lean_ctor_get_uint64(v_descr_2894_, sizeof(void*)*1);
v_ext_2905_ = lean_ctor_get(v_descr_2894_, 0);
lean_inc_ref(v_scope_2897_);
v_url_2906_ = l_Lake_CacheService_artifactUrl(v_hash_2904_, v_service_2896_, v_scope_2897_);
v___x_2977_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2978_ = l_System_FilePath_join(v_cache_2895_, v___x_2977_);
v___x_2993_ = lean_string_utf8_byte_size(v_ext_2905_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_nat_dec_eq(v___x_2993_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2996_ = l_Lake_Hash_hex(v_hash_2904_);
v___x_2997_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2998_ = lean_string_append(v___x_2996_, v___x_2997_);
v___x_2999_ = lean_string_append(v___x_2998_, v_ext_2905_);
v___y_2980_ = v___x_2999_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lake_Hash_hex(v_hash_2904_);
v___y_2980_ = v___x_3000_;
goto v___jp_2979_;
}
v___jp_2901_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
v___jp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2910_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_2911_ = lean_string_append(v___y_2909_, v___x_2910_);
v___x_2912_ = l_Lake_Hash_hex(v_hash_2904_);
v___x_2913_ = lean_string_append(v___x_2911_, v___x_2912_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_2915_ = lean_string_append(v___x_2913_, v___x_2914_);
v___x_2916_ = lean_string_append(v___x_2915_, v___y_2908_);
v___x_2917_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_2918_ = lean_string_append(v___x_2916_, v___x_2917_);
v___x_2919_ = lean_string_append(v___x_2918_, v_url_2906_);
v___x_2920_ = 1;
v___x_2921_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*1, v___x_2920_);
lean_inc_ref(v_a_2899_);
v___x_2922_ = lean_apply_2(v_a_2899_, v___x_2921_, lean_box(0));
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_2925_ = l_Lake_downloadArtifactCore(v_hash_2904_, v_url_2906_, v___y_2908_, v___x_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v_a_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
v_a_2927_ = lean_ctor_get(v___x_2925_, 1);
lean_inc(v_a_2927_);
lean_dec_ref(v___x_2925_);
v___x_2928_ = lean_array_get_size(v_a_2927_);
v___x_2929_ = lean_nat_dec_lt(v___x_2923_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2899_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v_a_2926_);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_nat_dec_le(v___x_2928_, v___x_2928_);
if (v___x_2932_ == 0)
{
if (v___x_2929_ == 0)
{
lean_object* v___x_2933_; 
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2899_);
v___x_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2933_, 0, v_a_2926_);
return v___x_2933_;
}
else
{
size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = ((size_t)0ULL);
v___x_2935_ = lean_usize_of_nat(v___x_2928_);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2927_, v___x_2934_, v___x_2935_, v___x_2931_, v_a_2899_);
lean_dec(v_a_2927_);
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
lean_ctor_set(v___x_2938_, 0, v_a_2926_);
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2926_);
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
lean_dec(v_a_2926_);
return v___x_2936_;
}
}
}
else
{
size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_of_nat(v___x_2928_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2927_, v___x_2945_, v___x_2946_, v___x_2931_, v_a_2899_);
lean_dec(v_a_2927_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v___x_2947_, 0);
lean_dec(v_unused_2955_);
v___x_2949_ = v___x_2947_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_dec(v___x_2947_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v_a_2926_);
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2926_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
lean_dec(v_a_2926_);
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2925_, 1);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2925_);
v___x_2957_ = lean_array_get_size(v_a_2956_);
v___x_2958_ = lean_nat_dec_lt(v___x_2923_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2899_);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
else
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_nat_dec_le(v___x_2957_, v___x_2957_);
if (v___x_2962_ == 0)
{
if (v___x_2958_ == 0)
{
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2899_);
goto v___jp_2901_;
}
else
{
size_t v___x_2963_; size_t v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((size_t)0ULL);
v___x_2964_ = lean_usize_of_nat(v___x_2957_);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2956_, v___x_2963_, v___x_2964_, v___x_2961_, v_a_2899_);
lean_dec(v_a_2956_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_dec_ref(v___x_2965_);
goto v___jp_2901_;
}
else
{
return v___x_2965_;
}
}
}
else
{
size_t v___x_2966_; size_t v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = ((size_t)0ULL);
v___x_2967_ = lean_usize_of_nat(v___x_2957_);
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_2956_, v___x_2966_, v___x_2967_, v___x_2961_, v_a_2899_);
lean_dec(v_a_2956_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_dec_ref(v___x_2968_);
goto v___jp_2901_;
}
else
{
return v___x_2968_;
}
}
}
}
}
v___jp_2969_:
{
lean_object* v_s_2971_; 
v_s_2971_ = lean_ctor_get(v_scope_2897_, 0);
lean_inc_ref(v_s_2971_);
lean_dec_ref(v_scope_2897_);
v___y_2908_ = v___y_2970_;
v___y_2909_ = v_s_2971_;
goto v___jp_2907_;
}
v___jp_2972_:
{
if (v_a_2974_ == 0)
{
v___y_2970_ = v___y_2973_;
goto v___jp_2969_;
}
else
{
if (v_force_2898_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec_ref(v___y_2973_);
lean_dec_ref(v_url_2906_);
lean_dec_ref(v_a_2899_);
lean_dec_ref(v_scope_2897_);
v___x_2975_ = lean_box(0);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
else
{
v___y_2970_ = v___y_2973_;
goto v___jp_2969_;
}
}
}
v___jp_2979_:
{
lean_object* v_path_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_path_2981_ = l_System_FilePath_join(v___x_2978_, v___y_2980_);
v___x_2982_ = l_System_FilePath_pathExists(v_path_2981_);
v___x_2983_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_2984_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_2984_ == 0)
{
v___y_2973_ = v_path_2981_;
v_a_2974_ = v___x_2982_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_2986_ == 0)
{
if (v___x_2984_ == 0)
{
v___y_2973_ = v_path_2981_;
v_a_2974_ = v___x_2982_;
goto v___jp_2972_;
}
else
{
size_t v___x_2987_; size_t v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_2899_);
v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_2983_, v___x_2987_, v___x_2988_, v___x_2985_, v_a_2899_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_dec_ref(v___x_2989_);
v___y_2973_ = v_path_2981_;
v_a_2974_ = v___x_2982_;
goto v___jp_2972_;
}
else
{
lean_dec_ref(v_path_2981_);
lean_dec_ref(v_url_2906_);
lean_dec_ref(v_a_2899_);
lean_dec_ref(v_scope_2897_);
return v___x_2989_;
}
}
}
else
{
size_t v___x_2990_; size_t v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = ((size_t)0ULL);
v___x_2991_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_2899_);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_2983_, v___x_2990_, v___x_2991_, v___x_2985_, v_a_2899_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref(v___x_2992_);
v___y_2973_ = v_path_2981_;
v_a_2974_ = v___x_2982_;
goto v___jp_2972_;
}
else
{
lean_dec_ref(v_path_2981_);
lean_dec_ref(v_url_2906_);
lean_dec_ref(v_a_2899_);
lean_dec_ref(v_scope_2897_);
return v___x_2992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3001_, lean_object* v_cache_3002_, lean_object* v_service_3003_, lean_object* v_scope_3004_, lean_object* v_force_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
uint8_t v_force_boxed_3008_; lean_object* v_res_3009_; 
v_force_boxed_3008_ = lean_unbox(v_force_3005_);
v_res_3009_ = l_Lake_CacheService_downloadArtifact(v_descr_3001_, v_cache_3002_, v_service_3003_, v_scope_3004_, v_force_boxed_3008_, v_a_3006_);
lean_dec_ref(v_descr_3001_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object* v___y_3010_, lean_object* v_descr_3011_, lean_object* v_cache_3012_, lean_object* v_service_3013_, lean_object* v_scope_3014_, uint8_t v_force_3015_){
_start:
{
uint64_t v_hash_3020_; lean_object* v_ext_3021_; lean_object* v_url_3022_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3086_; lean_object* v___y_3089_; uint8_t v_a_3090_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___y_3096_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_hash_3020_ = lean_ctor_get_uint64(v_descr_3011_, sizeof(void*)*1);
v_ext_3021_ = lean_ctor_get(v_descr_3011_, 0);
lean_inc_ref(v_scope_3014_);
v_url_3022_ = l_Lake_CacheService_artifactUrl(v_hash_3020_, v_service_3013_, v_scope_3014_);
v___x_3093_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3094_ = l_System_FilePath_join(v_cache_3012_, v___x_3093_);
v___x_3109_ = lean_string_utf8_byte_size(v_ext_3021_);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_nat_dec_eq(v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3112_ = l_Lake_Hash_hex(v_hash_3020_);
v___x_3113_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3114_ = lean_string_append(v___x_3112_, v___x_3113_);
v___x_3115_ = lean_string_append(v___x_3114_, v_ext_3021_);
v___y_3096_ = v___x_3115_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lake_Hash_hex(v_hash_3020_);
v___y_3096_ = v___x_3116_;
goto v___jp_3095_;
}
v___jp_3017_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
v___jp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3026_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3027_ = lean_string_append(v___y_3025_, v___x_3026_);
v___x_3028_ = l_Lake_Hash_hex(v_hash_3020_);
v___x_3029_ = lean_string_append(v___x_3027_, v___x_3028_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3031_ = lean_string_append(v___x_3029_, v___x_3030_);
v___x_3032_ = lean_string_append(v___x_3031_, v___y_3024_);
v___x_3033_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3034_ = lean_string_append(v___x_3032_, v___x_3033_);
v___x_3035_ = lean_string_append(v___x_3034_, v_url_3022_);
v___x_3036_ = 1;
v___x_3037_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*1, v___x_3036_);
lean_inc_ref(v___y_3010_);
v___x_3038_ = lean_apply_2(v___y_3010_, v___x_3037_, lean_box(0));
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3041_ = l_Lake_downloadArtifactCore(v_hash_3020_, v_url_3022_, v___y_3024_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v_a_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
v_a_3043_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3041_);
v___x_3044_ = lean_array_get_size(v_a_3043_);
v___x_3045_ = lean_nat_dec_lt(v___x_3039_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
lean_dec(v_a_3043_);
lean_dec_ref(v___y_3010_);
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_a_3042_);
return v___x_3046_;
}
else
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = lean_box(0);
v___x_3048_ = lean_nat_dec_le(v___x_3044_, v___x_3044_);
if (v___x_3048_ == 0)
{
if (v___x_3045_ == 0)
{
lean_object* v___x_3049_; 
lean_dec(v_a_3043_);
lean_dec_ref(v___y_3010_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_a_3042_);
return v___x_3049_;
}
else
{
size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = lean_usize_of_nat(v___x_3044_);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3043_, v___x_3050_, v___x_3051_, v___x_3047_, v___y_3010_);
lean_dec(v_a_3043_);
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
lean_ctor_set(v___x_3054_, 0, v_a_3042_);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3042_);
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
lean_dec(v_a_3042_);
return v___x_3052_;
}
}
}
else
{
size_t v___x_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((size_t)0ULL);
v___x_3062_ = lean_usize_of_nat(v___x_3044_);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3043_, v___x_3061_, v___x_3062_, v___x_3047_, v___y_3010_);
lean_dec(v_a_3043_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_3063_, 0);
lean_dec(v_unused_3071_);
v___x_3065_ = v___x_3063_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v___x_3063_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v_a_3042_);
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3042_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
else
{
lean_dec(v_a_3042_);
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v_a_3072_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_a_3072_);
lean_dec_ref(v___x_3041_);
v___x_3073_ = lean_array_get_size(v_a_3072_);
v___x_3074_ = lean_nat_dec_lt(v___x_3039_, v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec(v_a_3072_);
lean_dec_ref(v___y_3010_);
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_nat_dec_le(v___x_3073_, v___x_3073_);
if (v___x_3078_ == 0)
{
if (v___x_3074_ == 0)
{
lean_dec(v_a_3072_);
lean_dec_ref(v___y_3010_);
goto v___jp_3017_;
}
else
{
size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = lean_usize_of_nat(v___x_3073_);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3072_, v___x_3079_, v___x_3080_, v___x_3077_, v___y_3010_);
lean_dec(v_a_3072_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_dec_ref(v___x_3081_);
goto v___jp_3017_;
}
else
{
return v___x_3081_;
}
}
}
else
{
size_t v___x_3082_; size_t v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = lean_usize_of_nat(v___x_3073_);
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3072_, v___x_3082_, v___x_3083_, v___x_3077_, v___y_3010_);
lean_dec(v_a_3072_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref(v___x_3084_);
goto v___jp_3017_;
}
else
{
return v___x_3084_;
}
}
}
}
}
v___jp_3085_:
{
lean_object* v_s_3087_; 
v_s_3087_ = lean_ctor_get(v_scope_3014_, 0);
lean_inc_ref(v_s_3087_);
lean_dec_ref(v_scope_3014_);
v___y_3024_ = v___y_3086_;
v___y_3025_ = v_s_3087_;
goto v___jp_3023_;
}
v___jp_3088_:
{
if (v_a_3090_ == 0)
{
v___y_3086_ = v___y_3089_;
goto v___jp_3085_;
}
else
{
if (v_force_3015_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec_ref(v___y_3089_);
lean_dec_ref(v_url_3022_);
lean_dec_ref(v_scope_3014_);
lean_dec_ref(v___y_3010_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
return v___x_3092_;
}
else
{
v___y_3086_ = v___y_3089_;
goto v___jp_3085_;
}
}
}
v___jp_3095_:
{
lean_object* v_path_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_path_3097_ = l_System_FilePath_join(v___x_3094_, v___y_3096_);
v___x_3098_ = l_System_FilePath_pathExists(v_path_3097_);
v___x_3099_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3100_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3100_ == 0)
{
v___y_3089_ = v_path_3097_;
v_a_3090_ = v___x_3098_;
goto v___jp_3088_;
}
else
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3102_ == 0)
{
if (v___x_3100_ == 0)
{
v___y_3089_ = v_path_3097_;
v_a_3090_ = v___x_3098_;
goto v___jp_3088_;
}
else
{
size_t v___x_3103_; size_t v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((size_t)0ULL);
v___x_3104_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v___y_3010_);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3099_, v___x_3103_, v___x_3104_, v___x_3101_, v___y_3010_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec_ref(v___x_3105_);
v___y_3089_ = v_path_3097_;
v_a_3090_ = v___x_3098_;
goto v___jp_3088_;
}
else
{
lean_dec_ref(v_path_3097_);
lean_dec_ref(v_url_3022_);
lean_dec_ref(v_scope_3014_);
lean_dec_ref(v___y_3010_);
return v___x_3105_;
}
}
}
else
{
size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = ((size_t)0ULL);
v___x_3107_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v___y_3010_);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_3099_, v___x_3106_, v___x_3107_, v___x_3101_, v___y_3010_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_dec_ref(v___x_3108_);
v___y_3089_ = v_path_3097_;
v_a_3090_ = v___x_3098_;
goto v___jp_3088_;
}
else
{
lean_dec_ref(v_path_3097_);
lean_dec_ref(v_url_3022_);
lean_dec_ref(v_scope_3014_);
lean_dec_ref(v___y_3010_);
return v___x_3108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object* v___y_3117_, lean_object* v_descr_3118_, lean_object* v_cache_3119_, lean_object* v_service_3120_, lean_object* v_scope_3121_, lean_object* v_force_3122_, lean_object* v_a_3123_){
_start:
{
uint8_t v_force_boxed_3124_; lean_object* v_res_3125_; 
v_force_boxed_3124_ = lean_unbox(v_force_3122_);
v_res_3125_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3117_, v_descr_3118_, v_cache_3119_, v_service_3120_, v_scope_3121_, v_force_boxed_3124_);
lean_dec_ref(v_descr_3118_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object* v_cache_3126_, lean_object* v_service_3127_, lean_object* v_scope_3128_, uint8_t v_force_3129_, uint8_t v_ok_3130_, lean_object* v_descr_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3132_, v_descr_3131_, v_cache_3126_, v_service_3127_, v_scope_3128_, v_force_3129_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3142_; 
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; 
v_unused_3143_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3143_);
v___x_3136_ = v___x_3134_;
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
else
{
lean_dec(v___x_3134_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3138_ = lean_box(v_ok_3130_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3138_);
v___x_3140_ = v___x_3136_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
else
{
lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3152_; 
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3153_);
v___x_3145_ = v___x_3134_;
v_isShared_3146_ = v_isSharedCheck_3152_;
goto v_resetjp_3144_;
}
else
{
lean_dec(v___x_3134_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3152_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3147_ = 0;
v___x_3148_ = lean_box(v___x_3147_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3148_);
v___x_3150_ = v___x_3145_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object* v_cache_3154_, lean_object* v_service_3155_, lean_object* v_scope_3156_, lean_object* v_force_3157_, lean_object* v_ok_3158_, lean_object* v_descr_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v_force_boxed_3162_; uint8_t v_ok_boxed_3163_; lean_object* v_res_3164_; 
v_force_boxed_3162_ = lean_unbox(v_force_3157_);
v_ok_boxed_3163_ = lean_unbox(v_ok_3158_);
v_res_3164_ = l_Lake_CacheService_downloadArtifacts___elam__0(v_cache_3154_, v_service_3155_, v_scope_3156_, v_force_boxed_3162_, v_ok_boxed_3163_, v_descr_3159_, v___y_3160_);
lean_dec_ref(v_descr_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(lean_object* v___y_3165_, lean_object* v_cache_3166_, lean_object* v_service_3167_, lean_object* v_scope_3168_, uint8_t v_force_3169_, uint8_t v_ok_3170_, lean_object* v_descr_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(v___y_3165_, v_descr_3171_, v_cache_3166_, v_service_3167_, v_scope_3168_, v_force_3169_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3181_; 
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v___x_3173_, 0);
lean_dec(v_unused_3182_);
v___x_3175_ = v___x_3173_;
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3173_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3177_ = lean_box(v_ok_3170_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3177_);
v___x_3179_ = v___x_3175_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
else
{
lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3191_; 
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v___x_3173_, 0);
lean_dec(v_unused_3192_);
v___x_3184_ = v___x_3173_;
v_isShared_3185_ = v_isSharedCheck_3191_;
goto v_resetjp_3183_;
}
else
{
lean_dec(v___x_3173_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3191_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3186_ = 0;
v___x_3187_ = lean_box(v___x_3186_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3187_);
v___x_3189_ = v___x_3184_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2___boxed(lean_object* v___y_3193_, lean_object* v_cache_3194_, lean_object* v_service_3195_, lean_object* v_scope_3196_, lean_object* v_force_3197_, lean_object* v_ok_3198_, lean_object* v_descr_3199_, lean_object* v___y_3200_){
_start:
{
uint8_t v_force_boxed_3201_; uint8_t v_ok_boxed_3202_; lean_object* v_res_3203_; 
v_force_boxed_3201_ = lean_unbox(v_force_3197_);
v_ok_boxed_3202_ = lean_unbox(v_ok_3198_);
v_res_3203_ = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(v___y_3193_, v_cache_3194_, v_service_3195_, v_scope_3196_, v_force_boxed_3201_, v_ok_boxed_3202_, v_descr_3199_);
lean_dec_ref(v_descr_3199_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object* v_cache_3204_, lean_object* v_service_3205_, lean_object* v_scope_3206_, uint8_t v_force_3207_, lean_object* v_as_3208_, size_t v_i_3209_, size_t v_stop_3210_, uint8_t v_b_3211_, lean_object* v___y_3212_){
_start:
{
uint8_t v___x_3214_; 
v___x_3214_ = lean_usize_dec_eq(v_i_3209_, v_stop_3210_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_array_uget_borrowed(v_as_3208_, v_i_3209_);
lean_inc_ref(v_scope_3206_);
lean_inc_ref(v_service_3205_);
lean_inc_ref(v_cache_3204_);
lean_inc_ref(v___y_3212_);
v___x_3216_ = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2_spec__2(v___y_3212_, v_cache_3204_, v_service_3205_, v_scope_3206_, v_force_3207_, v_b_3211_, v___x_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; size_t v___x_3218_; size_t v___x_3219_; uint8_t v___x_3220_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref(v___x_3216_);
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_add(v_i_3209_, v___x_3218_);
v___x_3220_ = lean_unbox(v_a_3217_);
lean_dec(v_a_3217_);
v_i_3209_ = v___x_3219_;
v_b_3211_ = v___x_3220_;
goto _start;
}
else
{
lean_dec_ref(v___y_3212_);
lean_dec_ref(v_scope_3206_);
lean_dec_ref(v_service_3205_);
lean_dec_ref(v_cache_3204_);
return v___x_3216_;
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___y_3212_);
lean_dec_ref(v_scope_3206_);
lean_dec_ref(v_service_3205_);
lean_dec_ref(v_cache_3204_);
v___x_3222_ = lean_box(v_b_3211_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_cache_3224_, lean_object* v_service_3225_, lean_object* v_scope_3226_, lean_object* v_force_3227_, lean_object* v_as_3228_, lean_object* v_i_3229_, lean_object* v_stop_3230_, lean_object* v_b_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
uint8_t v_force_boxed_3234_; size_t v_i_boxed_3235_; size_t v_stop_boxed_3236_; uint8_t v_b_boxed_3237_; lean_object* v_res_3238_; 
v_force_boxed_3234_ = lean_unbox(v_force_3227_);
v_i_boxed_3235_ = lean_unbox_usize(v_i_3229_);
lean_dec(v_i_3229_);
v_stop_boxed_3236_ = lean_unbox_usize(v_stop_3230_);
lean_dec(v_stop_3230_);
v_b_boxed_3237_ = lean_unbox(v_b_3231_);
v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3224_, v_service_3225_, v_scope_3226_, v_force_boxed_3234_, v_as_3228_, v_i_boxed_3235_, v_stop_boxed_3236_, v_b_boxed_3237_, v___y_3232_);
lean_dec_ref(v_as_3228_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_3240_, lean_object* v_cache_3241_, lean_object* v_service_3242_, lean_object* v_scope_3243_, uint8_t v_force_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v___y_3251_; lean_object* v___y_3260_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = lean_array_get_size(v_descrs_3240_);
v___x_3274_ = lean_nat_dec_lt(v___x_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_dec_ref(v_a_3245_);
lean_dec_ref(v_scope_3243_);
lean_dec_ref(v_service_3242_);
lean_dec_ref(v_cache_3241_);
goto v___jp_3247_;
}
else
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_nat_dec_le(v___x_3273_, v___x_3273_);
if (v___x_3275_ == 0)
{
if (v___x_3274_ == 0)
{
lean_dec_ref(v_a_3245_);
lean_dec_ref(v_scope_3243_);
lean_dec_ref(v_service_3242_);
lean_dec_ref(v_cache_3241_);
goto v___jp_3247_;
}
else
{
size_t v___x_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = ((size_t)0ULL);
v___x_3277_ = lean_usize_of_nat(v___x_3273_);
lean_inc_ref(v_a_3245_);
lean_inc_ref(v_scope_3243_);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3241_, v_service_3242_, v_scope_3243_, v_force_3244_, v_descrs_3240_, v___x_3276_, v___x_3277_, v___x_3274_, v_a_3245_);
v___y_3260_ = v___x_3278_;
goto v___jp_3259_;
}
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = lean_usize_of_nat(v___x_3273_);
lean_inc_ref(v_a_3245_);
lean_inc_ref(v_scope_3243_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3241_, v_service_3242_, v_scope_3243_, v_force_3244_, v_descrs_3240_, v___x_3279_, v___x_3280_, v___x_3274_, v_a_3245_);
v___y_3260_ = v___x_3281_;
goto v___jp_3259_;
}
}
v___jp_3247_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_box(0);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
v___jp_3250_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3252_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_3253_ = lean_string_append(v___y_3251_, v___x_3252_);
v___x_3254_ = 3;
v___x_3255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*1, v___x_3254_);
v___x_3256_ = lean_apply_2(v_a_3245_, v___x_3255_, lean_box(0));
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
return v___x_3258_;
}
v___jp_3259_:
{
if (lean_obj_tag(v___y_3260_) == 0)
{
lean_object* v_a_3261_; uint8_t v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___y_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___y_3260_);
v___x_3262_ = lean_unbox(v_a_3261_);
lean_dec(v_a_3261_);
if (v___x_3262_ == 0)
{
lean_object* v_s_3263_; 
v_s_3263_ = lean_ctor_get(v_scope_3243_, 0);
lean_inc_ref(v_s_3263_);
lean_dec_ref(v_scope_3243_);
v___y_3251_ = v_s_3263_;
goto v___jp_3250_;
}
else
{
lean_dec_ref(v_a_3245_);
lean_dec_ref(v_scope_3243_);
goto v___jp_3247_;
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_a_3245_);
lean_dec_ref(v_scope_3243_);
v_a_3264_ = lean_ctor_get(v___y_3260_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___y_3260_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___y_3260_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___y_3260_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_3282_, lean_object* v_cache_3283_, lean_object* v_service_3284_, lean_object* v_scope_3285_, lean_object* v_force_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
uint8_t v_force_boxed_3289_; lean_object* v_res_3290_; 
v_force_boxed_3289_ = lean_unbox(v_force_3286_);
v_res_3290_ = l_Lake_CacheService_downloadArtifacts(v_descrs_3282_, v_cache_3283_, v_service_3284_, v_scope_3285_, v_force_boxed_3289_, v_a_3287_);
lean_dec_ref(v_descrs_3282_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_3291_, lean_object* v_descrs_3292_, lean_object* v_cache_3293_, lean_object* v_service_3294_, lean_object* v_scope_3295_, uint8_t v_force_3296_){
_start:
{
lean_object* v___y_3302_; lean_object* v___y_3311_; lean_object* v___x_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_array_get_size(v_descrs_3292_);
v___x_3325_ = lean_nat_dec_lt(v___x_3323_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_dec_ref(v_scope_3295_);
lean_dec_ref(v_service_3294_);
lean_dec_ref(v_cache_3293_);
lean_dec_ref(v_a_3291_);
goto v___jp_3298_;
}
else
{
uint8_t v___x_3326_; 
v___x_3326_ = lean_nat_dec_le(v___x_3324_, v___x_3324_);
if (v___x_3326_ == 0)
{
if (v___x_3325_ == 0)
{
lean_dec_ref(v_scope_3295_);
lean_dec_ref(v_service_3294_);
lean_dec_ref(v_cache_3293_);
lean_dec_ref(v_a_3291_);
goto v___jp_3298_;
}
else
{
size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = lean_usize_of_nat(v___x_3324_);
lean_inc_ref(v_a_3291_);
lean_inc_ref(v_scope_3295_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3293_, v_service_3294_, v_scope_3295_, v_force_3296_, v_descrs_3292_, v___x_3327_, v___x_3328_, v___x_3325_, v_a_3291_);
v___y_3311_ = v___x_3329_;
goto v___jp_3310_;
}
}
else
{
size_t v___x_3330_; size_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = lean_usize_of_nat(v___x_3324_);
lean_inc_ref(v_a_3291_);
lean_inc_ref(v_scope_3295_);
v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_3293_, v_service_3294_, v_scope_3295_, v_force_3296_, v_descrs_3292_, v___x_3330_, v___x_3331_, v___x_3325_, v_a_3291_);
v___y_3311_ = v___x_3332_;
goto v___jp_3310_;
}
}
v___jp_3298_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
v___jp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3303_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_3304_ = lean_string_append(v___y_3302_, v___x_3303_);
v___x_3305_ = 3;
v___x_3306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set_uint8(v___x_3306_, sizeof(void*)*1, v___x_3305_);
v___x_3307_ = lean_apply_2(v_a_3291_, v___x_3306_, lean_box(0));
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
v___jp_3310_:
{
if (lean_obj_tag(v___y_3311_) == 0)
{
lean_object* v_a_3312_; uint8_t v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___y_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___y_3311_);
v___x_3313_ = lean_unbox(v_a_3312_);
lean_dec(v_a_3312_);
if (v___x_3313_ == 0)
{
lean_object* v_s_3314_; 
v_s_3314_ = lean_ctor_get(v_scope_3295_, 0);
lean_inc_ref(v_s_3314_);
lean_dec_ref(v_scope_3295_);
v___y_3302_ = v_s_3314_;
goto v___jp_3301_;
}
else
{
lean_dec_ref(v_scope_3295_);
lean_dec_ref(v_a_3291_);
goto v___jp_3298_;
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v_scope_3295_);
lean_dec_ref(v_a_3291_);
v_a_3315_ = lean_ctor_get(v___y_3311_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___y_3311_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___y_3311_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___y_3311_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_3333_, lean_object* v_descrs_3334_, lean_object* v_cache_3335_, lean_object* v_service_3336_, lean_object* v_scope_3337_, lean_object* v_force_3338_, lean_object* v_a_3339_){
_start:
{
uint8_t v_force_boxed_3340_; lean_object* v_res_3341_; 
v_force_boxed_3340_ = lean_unbox(v_force_3338_);
v_res_3341_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3333_, v_descrs_3334_, v_cache_3335_, v_service_3336_, v_scope_3337_, v_force_boxed_3340_);
lean_dec_ref(v_descrs_3334_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_3342_, lean_object* v_cache_3343_, lean_object* v_service_3344_, lean_object* v_localScope_3345_, lean_object* v_remoteScope_3346_, uint8_t v_force_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_name_x3f_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_name_x3f_3353_ = lean_ctor_get(v_service_3344_, 0);
lean_inc_ref(v_remoteScope_3346_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_remoteScope_3346_);
lean_inc(v_name_x3f_3353_);
lean_inc_ref(v_cache_3343_);
v___x_3355_ = l_Lake_Cache_writeMap(v_cache_3343_, v_localScope_3345_, v_map_3342_, v_name_x3f_3353_, v___x_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3393_; 
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3355_, 0);
lean_dec(v_unused_3394_);
v___x_3357_ = v___x_3355_;
v_isShared_3358_ = v_isSharedCheck_3393_;
goto v_resetjp_3356_;
}
else
{
lean_dec(v___x_3355_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3393_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3361_ = l_Lake_CacheMap_collectOutputDescrs(v_map_3342_, v___x_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v_a_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
lean_del_object(v___x_3357_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
v_a_3363_ = lean_ctor_get(v___x_3361_, 1);
lean_inc(v_a_3363_);
lean_dec_ref(v___x_3361_);
v___x_3364_ = lean_array_get_size(v_a_3363_);
v___x_3365_ = lean_nat_dec_lt(v___x_3359_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; 
lean_dec(v_a_3363_);
v___x_3366_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3348_, v_a_3362_, v_cache_3343_, v_service_3344_, v_remoteScope_3346_, v_force_3347_);
lean_dec(v_a_3362_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_nat_dec_le(v___x_3364_, v___x_3364_);
if (v___x_3368_ == 0)
{
if (v___x_3365_ == 0)
{
lean_object* v___x_3369_; 
lean_dec(v_a_3363_);
v___x_3369_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3348_, v_a_3362_, v_cache_3343_, v_service_3344_, v_remoteScope_3346_, v_force_3347_);
lean_dec(v_a_3362_);
return v___x_3369_;
}
else
{
size_t v___x_3370_; size_t v___x_3371_; lean_object* v___x_3372_; 
v___x_3370_ = ((size_t)0ULL);
v___x_3371_ = lean_usize_of_nat(v___x_3364_);
lean_inc_ref(v_a_3348_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3363_, v___x_3370_, v___x_3371_, v___x_3367_, v_a_3348_);
lean_dec(v_a_3363_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3373_; 
lean_dec_ref(v___x_3372_);
v___x_3373_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3348_, v_a_3362_, v_cache_3343_, v_service_3344_, v_remoteScope_3346_, v_force_3347_);
lean_dec(v_a_3362_);
return v___x_3373_;
}
else
{
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3348_);
lean_dec_ref(v_remoteScope_3346_);
lean_dec_ref(v_service_3344_);
lean_dec_ref(v_cache_3343_);
return v___x_3372_;
}
}
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3364_);
lean_inc_ref(v_a_3348_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3363_, v___x_3374_, v___x_3375_, v___x_3367_, v_a_3348_);
lean_dec(v_a_3363_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; 
lean_dec_ref(v___x_3376_);
v___x_3377_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_3348_, v_a_3362_, v_cache_3343_, v_service_3344_, v_remoteScope_3346_, v_force_3347_);
lean_dec(v_a_3362_);
return v___x_3377_;
}
else
{
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3348_);
lean_dec_ref(v_remoteScope_3346_);
lean_dec_ref(v_service_3344_);
lean_dec_ref(v_cache_3343_);
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
lean_dec_ref(v_remoteScope_3346_);
lean_dec_ref(v_service_3344_);
lean_dec_ref(v_cache_3343_);
v_a_3378_ = lean_ctor_get(v___x_3361_, 1);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3361_);
v___x_3379_ = lean_array_get_size(v_a_3378_);
v___x_3380_ = lean_nat_dec_lt(v___x_3359_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3348_);
v___x_3381_ = lean_box(0);
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 1);
lean_ctor_set(v___x_3357_, 0, v___x_3381_);
v___x_3383_ = v___x_3357_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
else
{
lean_object* v___x_3385_; uint8_t v___x_3386_; 
lean_del_object(v___x_3357_);
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_nat_dec_le(v___x_3379_, v___x_3379_);
if (v___x_3386_ == 0)
{
if (v___x_3380_ == 0)
{
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3348_);
goto v___jp_3350_;
}
else
{
size_t v___x_3387_; size_t v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = lean_usize_of_nat(v___x_3379_);
v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3378_, v___x_3387_, v___x_3388_, v___x_3385_, v_a_3348_);
lean_dec(v_a_3378_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_dec_ref(v___x_3389_);
goto v___jp_3350_;
}
else
{
return v___x_3389_;
}
}
}
else
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = lean_usize_of_nat(v___x_3379_);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3378_, v___x_3390_, v___x_3391_, v___x_3385_, v_a_3348_);
lean_dec(v_a_3378_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_dec_ref(v___x_3392_);
goto v___jp_3350_;
}
else
{
return v___x_3392_;
}
}
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3407_; 
lean_dec_ref(v_remoteScope_3346_);
lean_dec_ref(v_service_3344_);
lean_dec_ref(v_cache_3343_);
lean_dec_ref(v_map_3342_);
v_a_3395_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3397_ = v___x_3355_;
v_isShared_3398_ = v_isSharedCheck_3407_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3355_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3407_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3399_ = lean_io_error_to_string(v_a_3395_);
v___x_3400_ = 3;
v___x_3401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*1, v___x_3400_);
v___x_3402_ = lean_apply_2(v_a_3348_, v___x_3401_, lean_box(0));
v___x_3403_ = lean_box(0);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3403_);
v___x_3405_ = v___x_3397_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
v___jp_3350_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = lean_box(0);
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_3408_, lean_object* v_cache_3409_, lean_object* v_service_3410_, lean_object* v_localScope_3411_, lean_object* v_remoteScope_3412_, lean_object* v_force_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
uint8_t v_force_boxed_3416_; lean_object* v_res_3417_; 
v_force_boxed_3416_ = lean_unbox(v_force_3413_);
v_res_3417_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_3408_, v_cache_3409_, v_service_3410_, v_localScope_3411_, v_remoteScope_3412_, v_force_boxed_3416_, v_a_3414_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3418_, lean_object* v_file_3419_, lean_object* v_contentType_3420_, lean_object* v_url_3421_, lean_object* v_key_3422_){
_start:
{
lean_object* v___y_3425_; lean_object* v_a_3426_; lean_object* v_stderr_3439_; lean_object* v___y_3448_; lean_object* v___y_3451_; lean_object* v_a_3452_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v_stderr_3491_; lean_object* v_a_3492_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3506_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3507_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3508_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3509_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3510_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3511_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3512_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3513_ = lean_string_append(v___x_3512_, v_contentType_3420_);
v___x_3514_ = lean_unsigned_to_nat(14u);
v___x_3515_ = lean_mk_empty_array_with_capacity(v___x_3514_);
lean_dec_ref(v___x_3515_);
v___x_3516_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3517_ = lean_array_push(v___x_3516_, v_key_3422_);
v___x_3518_ = lean_array_push(v___x_3517_, v___x_3508_);
v___x_3519_ = lean_array_push(v___x_3518_, v___x_3509_);
v___x_3520_ = lean_array_push(v___x_3519_, v___x_3510_);
v___x_3521_ = lean_array_push(v___x_3520_, v_file_3419_);
v___x_3522_ = lean_array_push(v___x_3521_, v_url_3421_);
v___x_3523_ = lean_array_push(v___x_3522_, v___x_3511_);
v___x_3524_ = lean_array_push(v___x_3523_, v___x_3513_);
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3528_ = 1;
v___x_3529_ = 0;
v___x_3530_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3530_, 0, v___x_3506_);
lean_ctor_set(v___x_3530_, 1, v___x_3507_);
lean_ctor_set(v___x_3530_, 2, v___x_3524_);
lean_ctor_set(v___x_3530_, 3, v___x_3525_);
lean_ctor_set(v___x_3530_, 4, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*5, v___x_3528_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*5 + 1, v___x_3529_);
v___x_3531_ = l_Lake_captureProc_x27(v___x_3530_, v___x_3527_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v_a_3533_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
v_a_3533_ = lean_ctor_get(v___x_3531_, 1);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3531_);
v___x_3547_ = lean_array_get_size(v_a_3533_);
v___x_3548_ = lean_nat_dec_lt(v___x_3526_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_dec(v_a_3533_);
goto v___jp_3534_;
}
else
{
lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3549_ = lean_box(0);
v___x_3550_ = lean_nat_dec_le(v___x_3547_, v___x_3547_);
if (v___x_3550_ == 0)
{
if (v___x_3548_ == 0)
{
lean_dec(v_a_3533_);
goto v___jp_3534_;
}
else
{
size_t v___x_3551_; size_t v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = ((size_t)0ULL);
v___x_3552_ = lean_usize_of_nat(v___x_3547_);
lean_inc_ref(v_a_3418_);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3533_, v___x_3551_, v___x_3552_, v___x_3549_, v_a_3418_);
lean_dec(v_a_3533_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_dec_ref(v___x_3553_);
goto v___jp_3534_;
}
else
{
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3418_);
return v___x_3553_;
}
}
}
else
{
size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((size_t)0ULL);
v___x_3555_ = lean_usize_of_nat(v___x_3547_);
lean_inc_ref(v_a_3418_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3533_, v___x_3554_, v___x_3555_, v___x_3549_, v_a_3418_);
lean_dec(v_a_3533_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref(v___x_3556_);
goto v___jp_3534_;
}
else
{
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3418_);
return v___x_3556_;
}
}
}
v___jp_3534_:
{
lean_object* v_stderr_3535_; lean_object* v___x_3536_; 
v_stderr_3535_ = lean_ctor_get(v_a_3532_, 1);
lean_inc_ref(v_stderr_3535_);
v___x_3536_ = l_Lean_Json_parse(v_stderr_3535_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; 
lean_inc_ref(v_stderr_3535_);
lean_dec(v_a_3532_);
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref(v___x_3536_);
v_stderr_3491_ = v_stderr_3535_;
v_a_3492_ = v_a_3537_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3538_);
lean_dec_ref(v___x_3536_);
v___x_3539_ = l_Lean_Json_getObj_x3f(v_a_3538_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; 
lean_inc_ref(v_stderr_3535_);
lean_dec(v_a_3532_);
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3539_);
v_stderr_3491_ = v_stderr_3535_;
v_a_3492_ = v_a_3540_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v_a_3541_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3541_);
lean_dec_ref(v___x_3539_);
v___x_3542_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3543_ = l_Lake_JsonObject_getJson_x3f(v_a_3541_, v___x_3542_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_inc_ref(v_stderr_3535_);
lean_dec(v_a_3541_);
lean_dec(v_a_3532_);
v_stderr_3439_ = v_stderr_3535_;
goto v___jp_3438_;
}
else
{
lean_object* v_val_3544_; lean_object* v___x_3545_; 
v_val_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_val_3544_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3544_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_dec_ref(v___x_3545_);
v___y_3479_ = v_a_3532_;
v___y_3480_ = v_a_3541_;
goto v___jp_3478_;
}
else
{
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_dec_ref(v___x_3545_);
v___y_3479_ = v_a_3532_;
v___y_3480_ = v_a_3541_;
goto v___jp_3478_;
}
else
{
lean_object* v_a_3546_; 
lean_dec(v_a_3541_);
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v___x_3545_);
v___y_3451_ = v_a_3532_;
v_a_3452_ = v_a_3546_;
goto v___jp_3450_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_a_3557_ = lean_ctor_get(v___x_3531_, 1);
lean_inc(v_a_3557_);
lean_dec_ref(v___x_3531_);
v___x_3558_ = lean_array_get_size(v_a_3557_);
v___x_3559_ = lean_nat_dec_lt(v___x_3526_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3418_);
v___x_3560_ = lean_box(0);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_nat_dec_le(v___x_3558_, v___x_3558_);
if (v___x_3563_ == 0)
{
if (v___x_3559_ == 0)
{
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3418_);
goto v___jp_3503_;
}
else
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = lean_usize_of_nat(v___x_3558_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3557_, v___x_3564_, v___x_3565_, v___x_3562_, v_a_3418_);
lean_dec(v_a_3557_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_dec_ref(v___x_3566_);
goto v___jp_3503_;
}
else
{
return v___x_3566_;
}
}
}
else
{
size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((size_t)0ULL);
v___x_3568_ = lean_usize_of_nat(v___x_3558_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3557_, v___x_3567_, v___x_3568_, v___x_3562_, v_a_3418_);
lean_dec(v_a_3557_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_dec_ref(v___x_3569_);
goto v___jp_3503_;
}
else
{
return v___x_3569_;
}
}
}
}
v___jp_3424_:
{
lean_object* v_stderr_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_stderr_3427_ = lean_ctor_get(v___y_3425_, 1);
lean_inc_ref(v_stderr_3427_);
lean_dec_ref(v___y_3425_);
v___x_3428_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3429_ = lean_string_append(v___x_3428_, v_a_3426_);
lean_dec_ref(v_a_3426_);
v___x_3430_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3431_ = lean_string_append(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_string_append(v___x_3431_, v_stderr_3427_);
lean_dec_ref(v_stderr_3427_);
v___x_3433_ = 3;
v___x_3434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*1, v___x_3433_);
v___x_3435_ = lean_apply_2(v_a_3418_, v___x_3434_, lean_box(0));
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
v___jp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3440_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3441_ = lean_string_append(v___x_3440_, v_stderr_3439_);
lean_dec_ref(v_stderr_3439_);
v___x_3442_ = 3;
v___x_3443_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*1, v___x_3442_);
v___x_3444_ = lean_apply_2(v_a_3418_, v___x_3443_, lean_box(0));
v___x_3445_ = lean_box(0);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
v___jp_3447_:
{
lean_object* v_stderr_3449_; 
v_stderr_3449_ = lean_ctor_get(v___y_3448_, 1);
lean_inc_ref(v_stderr_3449_);
lean_dec_ref(v___y_3448_);
v_stderr_3439_ = v_stderr_3449_;
goto v___jp_3438_;
}
v___jp_3450_:
{
if (lean_obj_tag(v_a_3452_) == 0)
{
v___y_3448_ = v___y_3451_;
goto v___jp_3447_;
}
else
{
lean_object* v_val_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3477_; 
v_val_3453_ = lean_ctor_get(v_a_3452_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3455_ = v_a_3452_;
v_isShared_3456_ = v_isSharedCheck_3477_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_val_3453_);
lean_dec(v_a_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3477_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = lean_unsigned_to_nat(200u);
v___x_3458_ = lean_nat_dec_eq(v_val_3453_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_object* v_stdout_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v_stdout_3459_ = lean_ctor_get(v___y_3451_, 0);
lean_inc_ref(v_stdout_3459_);
lean_dec_ref(v___y_3451_);
v___x_3460_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3461_ = l_Nat_reprFast(v_val_3453_);
v___x_3462_ = lean_string_append(v___x_3460_, v___x_3461_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3464_ = lean_string_append(v___x_3462_, v___x_3463_);
v___x_3465_ = lean_string_append(v___x_3464_, v_stdout_3459_);
lean_dec_ref(v_stdout_3459_);
v___x_3466_ = 3;
v___x_3467_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set_uint8(v___x_3467_, sizeof(void*)*1, v___x_3466_);
v___x_3468_ = lean_apply_2(v_a_3418_, v___x_3467_, lean_box(0));
v___x_3469_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3469_);
v___x_3471_ = v___x_3455_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
lean_dec(v_val_3453_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v_a_3418_);
v___x_3473_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3473_);
v___x_3475_ = v___x_3455_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
v___jp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3482_ = l_Lake_JsonObject_getJson_x3f(v___y_3480_, v___x_3481_);
lean_dec(v___y_3480_);
if (lean_obj_tag(v___x_3482_) == 0)
{
v___y_3448_ = v___y_3479_;
goto v___jp_3447_;
}
else
{
lean_object* v_val_3483_; lean_object* v___x_3484_; 
v_val_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_val_3483_);
lean_dec_ref(v___x_3482_);
v___x_3484_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3483_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref(v___x_3484_);
v___x_3486_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3487_ = lean_string_append(v___x_3486_, v_a_3485_);
lean_dec(v_a_3485_);
v___y_3425_ = v___y_3479_;
v_a_3426_ = v___x_3487_;
goto v___jp_3424_;
}
else
{
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v___x_3484_);
v___y_3425_ = v___y_3479_;
v_a_3426_ = v_a_3488_;
goto v___jp_3424_;
}
else
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3484_);
v___y_3451_ = v___y_3479_;
v_a_3452_ = v_a_3489_;
goto v___jp_3450_;
}
}
}
}
v___jp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3493_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3494_ = lean_string_append(v___x_3493_, v_a_3492_);
lean_dec_ref(v_a_3492_);
v___x_3495_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
v___x_3497_ = lean_string_append(v___x_3496_, v_stderr_3491_);
lean_dec_ref(v_stderr_3491_);
v___x_3498_ = 3;
v___x_3499_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*1, v___x_3498_);
v___x_3500_ = lean_apply_2(v_a_3418_, v___x_3499_, lean_box(0));
v___x_3501_ = lean_box(0);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
v___jp_3503_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_box(0);
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3570_, lean_object* v_file_3571_, lean_object* v_contentType_3572_, lean_object* v_url_3573_, lean_object* v_key_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3570_, v_file_3571_, v_contentType_3572_, v_url_3573_, v_key_3574_);
lean_dec_ref(v_contentType_3572_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3578_, lean_object* v_art_3579_, lean_object* v_service_3580_, lean_object* v_scope_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_url_3584_; lean_object* v___y_3586_; lean_object* v_s_3603_; 
lean_inc_ref(v_scope_3581_);
lean_inc_ref(v_service_3580_);
v_url_3584_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3578_, v_service_3580_, v_scope_3581_);
v_s_3603_ = lean_ctor_get(v_scope_3581_, 0);
lean_inc_ref(v_s_3603_);
lean_dec_ref(v_scope_3581_);
v___y_3586_ = v_s_3603_;
goto v___jp_3585_;
v___jp_3585_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_key_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3587_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3588_ = lean_string_append(v___y_3586_, v___x_3587_);
v___x_3589_ = l_Lake_Hash_hex(v_contentHash_3578_);
v___x_3590_ = lean_string_append(v___x_3588_, v___x_3589_);
lean_dec_ref(v___x_3589_);
v___x_3591_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3592_ = lean_string_append(v___x_3590_, v___x_3591_);
v___x_3593_ = lean_string_append(v___x_3592_, v_art_3579_);
v___x_3594_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3595_ = lean_string_append(v___x_3593_, v___x_3594_);
v___x_3596_ = lean_string_append(v___x_3595_, v_url_3584_);
v___x_3597_ = 1;
v___x_3598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set_uint8(v___x_3598_, sizeof(void*)*1, v___x_3597_);
lean_inc_ref(v_a_3582_);
v___x_3599_ = lean_apply_2(v_a_3582_, v___x_3598_, lean_box(0));
v_key_3600_ = lean_ctor_get(v_service_3580_, 1);
lean_inc_ref(v_key_3600_);
lean_dec_ref(v_service_3580_);
v___x_3601_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3602_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3582_, v_art_3579_, v___x_3601_, v_url_3584_, v_key_3600_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3604_, lean_object* v_art_3605_, lean_object* v_service_3606_, lean_object* v_scope_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
uint64_t v_contentHash_boxed_3610_; lean_object* v_res_3611_; 
v_contentHash_boxed_3610_ = lean_unbox_uint64(v_contentHash_3604_);
lean_dec_ref(v_contentHash_3604_);
v_res_3611_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3610_, v_art_3605_, v_service_3606_, v_scope_3607_, v_a_3608_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object* v___y_3612_, uint64_t v_contentHash_3613_, lean_object* v_art_3614_, lean_object* v_service_3615_, lean_object* v_scope_3616_){
_start:
{
lean_object* v_url_3618_; lean_object* v___y_3620_; lean_object* v_s_3637_; 
lean_inc_ref(v_scope_3616_);
lean_inc_ref(v_service_3615_);
v_url_3618_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3613_, v_service_3615_, v_scope_3616_);
v_s_3637_ = lean_ctor_get(v_scope_3616_, 0);
lean_inc_ref(v_s_3637_);
lean_dec_ref(v_scope_3616_);
v___y_3620_ = v_s_3637_;
goto v___jp_3619_;
v___jp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_key_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3621_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3622_ = lean_string_append(v___y_3620_, v___x_3621_);
v___x_3623_ = l_Lake_Hash_hex(v_contentHash_3613_);
v___x_3624_ = lean_string_append(v___x_3622_, v___x_3623_);
lean_dec_ref(v___x_3623_);
v___x_3625_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3626_ = lean_string_append(v___x_3624_, v___x_3625_);
v___x_3627_ = lean_string_append(v___x_3626_, v_art_3614_);
v___x_3628_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3629_ = lean_string_append(v___x_3627_, v___x_3628_);
v___x_3630_ = lean_string_append(v___x_3629_, v_url_3618_);
v___x_3631_ = 1;
v___x_3632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3632_, 0, v___x_3630_);
lean_ctor_set_uint8(v___x_3632_, sizeof(void*)*1, v___x_3631_);
lean_inc_ref(v___y_3612_);
v___x_3633_ = lean_apply_2(v___y_3612_, v___x_3632_, lean_box(0));
v_key_3634_ = lean_ctor_get(v_service_3615_, 1);
lean_inc_ref(v_key_3634_);
lean_dec_ref(v_service_3615_);
v___x_3635_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3636_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v___y_3612_, v_art_3614_, v___x_3635_, v_url_3618_, v_key_3634_);
return v___x_3636_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object* v___y_3638_, lean_object* v_contentHash_3639_, lean_object* v_art_3640_, lean_object* v_service_3641_, lean_object* v_scope_3642_, lean_object* v_a_3643_){
_start:
{
uint64_t v_contentHash_boxed_3644_; lean_object* v_res_3645_; 
v_contentHash_boxed_3644_ = lean_unbox_uint64(v_contentHash_3639_);
lean_dec_ref(v_contentHash_3639_);
v_res_3645_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3638_, v_contentHash_boxed_3644_, v_art_3640_, v_service_3641_, v_scope_3642_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object* v_descrs_3646_, lean_object* v_paths_3647_, lean_object* v_service_3648_, lean_object* v_scope_3649_, lean_object* v_n_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; uint64_t v_hash_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3653_ = lean_array_fget_borrowed(v_descrs_3646_, v_n_3650_);
v_hash_3654_ = lean_ctor_get_uint64(v___x_3653_, sizeof(void*)*1);
v___x_3655_ = lean_array_fget_borrowed(v_paths_3647_, v_n_3650_);
lean_inc(v___x_3655_);
v___x_3656_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3651_, v_hash_3654_, v___x_3655_, v_service_3648_, v_scope_3649_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object* v_descrs_3657_, lean_object* v_paths_3658_, lean_object* v_service_3659_, lean_object* v_scope_3660_, lean_object* v_n_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(v_descrs_3657_, v_paths_3658_, v_service_3659_, v_scope_3660_, v_n_3661_, v___y_3662_);
lean_dec(v_n_3661_);
lean_dec_ref(v_paths_3658_);
lean_dec_ref(v_descrs_3657_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object* v_descrs_3665_, lean_object* v_paths_3666_, lean_object* v_service_3667_, lean_object* v_scope_3668_, lean_object* v_n_3669_, lean_object* v_h_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(v_descrs_3665_, v_paths_3666_, v_service_3667_, v_scope_3668_, v_n_3669_, v___y_3671_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object* v_descrs_3674_, lean_object* v_paths_3675_, lean_object* v_service_3676_, lean_object* v_scope_3677_, lean_object* v_n_3678_, lean_object* v_h_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lake_CacheService_uploadArtifacts___elam__0(v_descrs_3674_, v_paths_3675_, v_service_3676_, v_scope_3677_, v_n_3678_, v_h_3679_, v___y_3680_);
lean_dec(v_n_3678_);
lean_dec_ref(v_paths_3675_);
lean_dec_ref(v_descrs_3674_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(lean_object* v___y_3683_, lean_object* v_descrs_3684_, lean_object* v_paths_3685_, lean_object* v_service_3686_, lean_object* v_scope_3687_, lean_object* v_n_3688_){
_start:
{
lean_object* v___x_3690_; uint64_t v_hash_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3690_ = lean_array_fget_borrowed(v_descrs_3684_, v_n_3688_);
v_hash_3691_ = lean_ctor_get_uint64(v___x_3690_, sizeof(void*)*1);
v___x_3692_ = lean_array_fget_borrowed(v_paths_3685_, v_n_3688_);
lean_inc(v___x_3692_);
v___x_3693_ = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(v___y_3683_, v_hash_3691_, v___x_3692_, v_service_3686_, v_scope_3687_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg___boxed(lean_object* v___y_3694_, lean_object* v_descrs_3695_, lean_object* v_paths_3696_, lean_object* v_service_3697_, lean_object* v_scope_3698_, lean_object* v_n_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3694_, v_descrs_3695_, v_paths_3696_, v_service_3697_, v_scope_3698_, v_n_3699_);
lean_dec(v_n_3699_);
lean_dec_ref(v_paths_3696_);
lean_dec_ref(v_descrs_3695_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(lean_object* v_descrs_3702_, lean_object* v_paths_3703_, lean_object* v_service_3704_, lean_object* v_scope_3705_, lean_object* v_n_3706_, lean_object* v_i_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_zero_3710_; uint8_t v_isZero_3711_; 
v_zero_3710_ = lean_unsigned_to_nat(0u);
v_isZero_3711_ = lean_nat_dec_eq(v_i_3707_, v_zero_3710_);
if (v_isZero_3711_ == 1)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v___y_3708_);
lean_dec(v_i_3707_);
lean_dec_ref(v_scope_3705_);
lean_dec_ref(v_service_3704_);
v___x_3712_ = lean_box(0);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
else
{
lean_object* v_one_3714_; lean_object* v_n_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_one_3714_ = lean_unsigned_to_nat(1u);
v_n_3715_ = lean_nat_sub(v_i_3707_, v_one_3714_);
lean_dec(v_i_3707_);
v___x_3716_ = lean_nat_sub(v_n_3706_, v_n_3715_);
v___x_3717_ = lean_nat_sub(v___x_3716_, v_one_3714_);
lean_dec(v___x_3716_);
lean_inc_ref(v_scope_3705_);
lean_inc_ref(v_service_3704_);
lean_inc_ref(v___y_3708_);
v___x_3718_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3708_, v_descrs_3702_, v_paths_3703_, v_service_3704_, v_scope_3705_, v___x_3717_);
lean_dec(v___x_3717_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_dec_ref(v___x_3718_);
v_i_3707_ = v_n_3715_;
goto _start;
}
else
{
lean_dec(v_n_3715_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v_scope_3705_);
lean_dec_ref(v_service_3704_);
return v___x_3718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg___boxed(lean_object* v_descrs_3720_, lean_object* v_paths_3721_, lean_object* v_service_3722_, lean_object* v_scope_3723_, lean_object* v_n_3724_, lean_object* v_i_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3720_, v_paths_3721_, v_service_3722_, v_scope_3723_, v_n_3724_, v_i_3725_, v___y_3726_);
lean_dec(v_n_3724_);
lean_dec_ref(v_paths_3721_);
lean_dec_ref(v_descrs_3720_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_3729_, lean_object* v_descrs_3730_, lean_object* v_paths_3731_, lean_object* v_service_3732_, lean_object* v_scope_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v___x_3736_; 
lean_inc(v_n_3729_);
v___x_3736_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3730_, v_paths_3731_, v_service_3732_, v_scope_3733_, v_n_3729_, v_n_3729_, v_a_3734_);
lean_dec(v_n_3729_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_3737_, lean_object* v_descrs_3738_, lean_object* v_paths_3739_, lean_object* v_service_3740_, lean_object* v_scope_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lake_CacheService_uploadArtifacts(v_n_3737_, v_descrs_3738_, v_paths_3739_, v_service_3740_, v_scope_3741_, v_a_3742_);
lean_dec_ref(v_paths_3739_);
lean_dec_ref(v_descrs_3738_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(lean_object* v_descrs_3745_, lean_object* v_paths_3746_, lean_object* v_service_3747_, lean_object* v_scope_3748_, lean_object* v_n_3749_, lean_object* v_i_3750_, lean_object* v_a_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___redArg(v_descrs_3745_, v_paths_3746_, v_service_3747_, v_scope_3748_, v_n_3749_, v_i_3750_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2___boxed(lean_object* v_descrs_3755_, lean_object* v_paths_3756_, lean_object* v_service_3757_, lean_object* v_scope_3758_, lean_object* v_n_3759_, lean_object* v_i_3760_, lean_object* v_a_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2(v_descrs_3755_, v_paths_3756_, v_service_3757_, v_scope_3758_, v_n_3759_, v_i_3760_, v_a_3761_, v___y_3762_);
lean_dec(v_n_3759_);
lean_dec_ref(v_paths_3756_);
lean_dec_ref(v_descrs_3755_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(lean_object* v___y_3765_, lean_object* v_descrs_3766_, lean_object* v_paths_3767_, lean_object* v_service_3768_, lean_object* v_scope_3769_, lean_object* v_n_3770_, lean_object* v_h_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___redArg(v___y_3765_, v_descrs_3766_, v_paths_3767_, v_service_3768_, v_scope_3769_, v_n_3770_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2___boxed(lean_object* v___y_3774_, lean_object* v_descrs_3775_, lean_object* v_paths_3776_, lean_object* v_service_3777_, lean_object* v_scope_3778_, lean_object* v_n_3779_, lean_object* v_h_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__2_spec__2(v___y_3774_, v_descrs_3775_, v_paths_3776_, v_service_3777_, v_scope_3778_, v_n_3779_, v_h_3780_);
lean_dec(v_n_3779_);
lean_dec_ref(v_paths_3776_);
lean_dec_ref(v_descrs_3775_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_3787_, lean_object* v_service_3788_, lean_object* v_scope_3789_, lean_object* v_platform_3790_, lean_object* v_toolchain_3791_){
_start:
{
lean_object* v_url_3793_; lean_object* v_url_3800_; 
if (lean_obj_tag(v_scope_3789_) == 0)
{
lean_object* v_s_3809_; lean_object* v_revisionEndpoint_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec_ref(v_platform_3790_);
v_s_3809_ = lean_ctor_get(v_scope_3789_, 0);
lean_inc_ref(v_s_3809_);
lean_dec_ref(v_scope_3789_);
v_revisionEndpoint_3810_ = lean_ctor_get(v_service_3788_, 3);
lean_inc_ref(v_revisionEndpoint_3810_);
lean_dec_ref(v_service_3788_);
v___x_3811_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_3810_, v_s_3809_);
v___x_3812_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_3813_ = lean_string_append(v___x_3812_, v_rev_3787_);
v___x_3814_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_3815_ = lean_string_append(v___x_3813_, v___x_3814_);
v___x_3816_ = lean_string_append(v___x_3811_, v___x_3815_);
lean_dec_ref(v___x_3815_);
return v___x_3816_;
}
else
{
lean_object* v_s_3817_; lean_object* v_revisionEndpoint_3818_; lean_object* v_url_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v_s_3817_ = lean_ctor_get(v_scope_3789_, 0);
lean_inc_ref(v_s_3817_);
lean_dec_ref(v_scope_3789_);
v_revisionEndpoint_3818_ = lean_ctor_get(v_service_3788_, 3);
lean_inc_ref(v_revisionEndpoint_3818_);
lean_dec_ref(v_service_3788_);
v_url_3819_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_3818_, v_s_3817_);
v___x_3820_ = lean_string_utf8_byte_size(v_platform_3790_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = lean_nat_dec_eq(v___x_3820_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v_url_3825_; 
v___x_3823_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_3824_ = lean_string_append(v_url_3819_, v___x_3823_);
v_url_3825_ = l_Lake_uriEncode(v_platform_3790_, v___x_3824_);
v_url_3800_ = v_url_3825_;
goto v___jp_3799_;
}
else
{
lean_dec_ref(v_platform_3790_);
v_url_3800_ = v_url_3819_;
goto v___jp_3799_;
}
}
v___jp_3792_:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3794_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_3795_ = lean_string_append(v_url_3793_, v___x_3794_);
v___x_3796_ = lean_string_append(v___x_3795_, v_rev_3787_);
v___x_3797_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_3798_ = lean_string_append(v___x_3796_, v___x_3797_);
return v___x_3798_;
}
v___jp_3799_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v___x_3801_ = lean_string_utf8_byte_size(v_toolchain_3791_);
v___x_3802_ = lean_unsigned_to_nat(0u);
v___x_3803_ = lean_nat_dec_eq(v___x_3801_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v_url_3808_; 
v___x_3804_ = ((lean_object*)(l_Lake_CachePlatform_none___closed__0));
v___x_3805_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_3791_, v___x_3804_, v___x_3802_);
v___x_3806_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_3807_ = lean_string_append(v_url_3800_, v___x_3806_);
v_url_3808_ = l_Lake_uriEncode(v___x_3805_, v___x_3807_);
v_url_3793_ = v_url_3808_;
goto v___jp_3792_;
}
else
{
v_url_3793_ = v_url_3800_;
goto v___jp_3792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_3826_, lean_object* v_service_3827_, lean_object* v_scope_3828_, lean_object* v_platform_3829_, lean_object* v_toolchain_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_3826_, v_service_3827_, v_scope_3828_, v_platform_3829_, v_toolchain_3830_);
lean_dec_ref(v_toolchain_3830_);
lean_dec_ref(v_rev_3826_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_3835_, lean_object* v_service_3836_, lean_object* v_scope_3837_, lean_object* v_platform_3838_, lean_object* v_toolchain_3839_){
_start:
{
lean_object* v_url_3841_; lean_object* v___y_3849_; uint8_t v_isReservoir_3859_; 
v_isReservoir_3859_ = lean_ctor_get_uint8(v_service_3836_, sizeof(void*)*5);
if (v_isReservoir_3859_ == 0)
{
lean_object* v___x_3860_; 
v___x_3860_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_3835_, v_service_3836_, v_scope_3837_, v_platform_3838_, v_toolchain_3839_);
lean_dec_ref(v_toolchain_3839_);
return v___x_3860_;
}
else
{
if (lean_obj_tag(v_scope_3837_) == 0)
{
lean_object* v_apiEndpoint_3861_; lean_object* v_s_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_apiEndpoint_3861_ = lean_ctor_get(v_service_3836_, 4);
lean_inc_ref(v_apiEndpoint_3861_);
lean_dec_ref(v_service_3836_);
v_s_3862_ = lean_ctor_get(v_scope_3837_, 0);
lean_inc_ref(v_s_3862_);
lean_dec_ref(v_scope_3837_);
v___x_3863_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_3864_ = lean_string_append(v_apiEndpoint_3861_, v___x_3863_);
v___x_3865_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3864_, v_s_3862_);
v___y_3849_ = v___x_3865_;
goto v___jp_3848_;
}
else
{
lean_object* v_apiEndpoint_3866_; lean_object* v_s_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_apiEndpoint_3866_ = lean_ctor_get(v_service_3836_, 4);
lean_inc_ref(v_apiEndpoint_3866_);
lean_dec_ref(v_service_3836_);
v_s_3867_ = lean_ctor_get(v_scope_3837_, 0);
lean_inc_ref(v_s_3867_);
lean_dec_ref(v_scope_3837_);
v___x_3868_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3869_ = lean_string_append(v_apiEndpoint_3866_, v___x_3868_);
v___x_3870_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3869_, v_s_3867_);
v___y_3849_ = v___x_3870_;
goto v___jp_3848_;
}
}
v___jp_3840_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = lean_string_utf8_byte_size(v_toolchain_3839_);
v___x_3843_ = lean_unsigned_to_nat(0u);
v___x_3844_ = lean_nat_dec_eq(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_url_3847_; 
v___x_3845_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_3846_ = lean_string_append(v_url_3841_, v___x_3845_);
v_url_3847_ = l_Lake_uriEncode(v_toolchain_3839_, v___x_3846_);
return v_url_3847_;
}
else
{
lean_dec_ref(v_toolchain_3839_);
return v_url_3841_;
}
}
v___jp_3848_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v_url_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3850_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_3851_ = lean_string_append(v___y_3849_, v___x_3850_);
v_url_3852_ = lean_string_append(v___x_3851_, v_rev_3835_);
v___x_3853_ = lean_string_utf8_byte_size(v_platform_3838_);
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_nat_dec_eq(v___x_3853_, v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v_url_3858_; 
v___x_3856_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_3857_ = lean_string_append(v_url_3852_, v___x_3856_);
v_url_3858_ = l_Lake_uriEncode(v_platform_3838_, v___x_3857_);
v_url_3841_ = v_url_3858_;
goto v___jp_3840_;
}
else
{
lean_dec_ref(v_platform_3838_);
v_url_3841_ = v_url_3852_;
goto v___jp_3840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_3871_, lean_object* v_service_3872_, lean_object* v_scope_3873_, lean_object* v_platform_3874_, lean_object* v_toolchain_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lake_CacheService_revisionUrl(v_rev_3871_, v_service_3872_, v_scope_3873_, v_platform_3874_, v_toolchain_3875_);
lean_dec_ref(v_rev_3871_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_3881_, lean_object* v_cache_3882_, lean_object* v_service_3883_, lean_object* v_localScope_3884_, lean_object* v_remoteScope_3885_, lean_object* v_platform_3886_, lean_object* v_toolchain_3887_, uint8_t v_force_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_a_3895_; lean_object* v_a_3902_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v_a_3915_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v_path_3924_; lean_object* v_a_3926_; lean_object* v___y_4026_; lean_object* v___y_4027_; uint8_t v___x_4076_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_3919_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_3920_ = l_System_FilePath_join(v_cache_3882_, v___x_3919_);
lean_inc_ref(v_localScope_3884_);
v___x_3921_ = l_System_FilePath_join(v___x_3920_, v_localScope_3884_);
v___x_3922_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_3881_);
v___x_3923_ = lean_string_append(v_rev_3881_, v___x_3922_);
v_path_3924_ = l_System_FilePath_join(v___x_3921_, v___x_3923_);
v___x_4076_ = l_System_FilePath_pathExists(v_path_3924_);
v___x_4138_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4139_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_4139_ == 0)
{
goto v___jp_4077_;
}
else
{
lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4140_ = lean_box(0);
v___x_4141_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_4141_ == 0)
{
if (v___x_4139_ == 0)
{
goto v___jp_4077_;
}
else
{
size_t v___x_4142_; size_t v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = ((size_t)0ULL);
v___x_4143_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_3889_);
v___x_4144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_4138_, v___x_4142_, v___x_4143_, v___x_4140_, v_a_3889_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_dec_ref(v___x_4144_);
goto v___jp_4077_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v_path_3924_);
lean_dec_ref(v_a_3889_);
lean_dec_ref(v_toolchain_3887_);
lean_dec_ref(v_platform_3886_);
lean_dec_ref(v_remoteScope_3885_);
lean_dec_ref(v_localScope_3884_);
lean_dec_ref(v_service_3883_);
lean_dec_ref(v_rev_3881_);
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
else
{
size_t v___x_4153_; size_t v___x_4154_; lean_object* v___x_4155_; 
v___x_4153_ = ((size_t)0ULL);
v___x_4154_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
lean_inc_ref(v_a_3889_);
v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v___x_4138_, v___x_4153_, v___x_4154_, v___x_4140_, v_a_3889_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_dec_ref(v___x_4155_);
goto v___jp_4077_;
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v_path_3924_);
lean_dec_ref(v_a_3889_);
lean_dec_ref(v_toolchain_3887_);
lean_dec_ref(v_platform_3886_);
lean_dec_ref(v_remoteScope_3885_);
lean_dec_ref(v_localScope_3884_);
lean_dec_ref(v_service_3883_);
lean_dec_ref(v_rev_3881_);
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
v___jp_3891_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_box(0);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
return v___x_3893_;
}
v___jp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v_a_3895_);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
v___jp_3898_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_box(0);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
return v___x_3900_;
}
v___jp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_a_3902_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
v___jp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3908_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_3909_ = lean_string_append(v___y_3907_, v___x_3908_);
v___x_3910_ = 3;
v___x_3911_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set_uint8(v___x_3911_, sizeof(void*)*1, v___x_3910_);
v___x_3912_ = lean_apply_2(v_a_3889_, v___x_3911_, lean_box(0));
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___y_3906_);
return v___x_3913_;
}
v___jp_3914_:
{
lean_object* v_s_3916_; 
v_s_3916_ = lean_ctor_get(v_remoteScope_3885_, 0);
lean_inc_ref(v_s_3916_);
lean_dec_ref(v_remoteScope_3885_);
v___y_3906_ = v_a_3915_;
v___y_3907_ = v_s_3916_;
goto v___jp_3905_;
}
v___jp_3917_:
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_box(0);
v_a_3915_ = v___x_3918_;
goto v___jp_3914_;
}
v___jp_3925_:
{
if (lean_obj_tag(v_a_3926_) == 1)
{
lean_object* v_val_3927_; lean_object* v___x_3928_; 
v_val_3927_ = lean_ctor_get(v_a_3926_, 0);
lean_inc(v_val_3927_);
lean_dec_ref(v_a_3926_);
lean_inc_ref(v_path_3924_);
v___x_3928_ = l_Lake_createParentDirs(v_path_3924_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v___x_3929_; 
lean_dec_ref(v___x_3928_);
v___x_3929_ = l_IO_FS_writeFile(v_path_3924_, v_val_3927_);
lean_dec(v_val_3927_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3995_; 
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v___x_3929_, 0);
lean_dec(v_unused_3996_);
v___x_3931_ = v___x_3929_;
v_isShared_3932_ = v_isSharedCheck_3995_;
goto v_resetjp_3930_;
}
else
{
lean_dec(v___x_3929_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3995_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3935_ = l_Lake_CacheMap_load(v_path_3924_, v___x_3934_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v_a_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
lean_del_object(v___x_3931_);
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
v_a_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_a_3937_);
lean_dec_ref(v___x_3935_);
v___x_3938_ = lean_array_get_size(v_a_3937_);
v___x_3939_ = lean_nat_dec_lt(v___x_3933_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3889_);
v_a_3902_ = v_a_3936_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3940_; uint8_t v___x_3941_; 
v___x_3940_ = lean_box(0);
v___x_3941_ = lean_nat_dec_le(v___x_3938_, v___x_3938_);
if (v___x_3941_ == 0)
{
if (v___x_3939_ == 0)
{
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3889_);
v_a_3902_ = v_a_3936_;
goto v___jp_3901_;
}
else
{
size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = ((size_t)0ULL);
v___x_3943_ = lean_usize_of_nat(v___x_3938_);
v___x_3944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3937_, v___x_3942_, v___x_3943_, v___x_3940_, v_a_3889_);
lean_dec(v_a_3937_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_dec_ref(v___x_3944_);
v_a_3902_ = v_a_3936_;
goto v___jp_3901_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_a_3936_);
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
else
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = ((size_t)0ULL);
v___x_3954_ = lean_usize_of_nat(v___x_3938_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3937_, v___x_3953_, v___x_3954_, v___x_3940_, v_a_3889_);
lean_dec(v_a_3937_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_dec_ref(v___x_3955_);
v_a_3902_ = v_a_3936_;
goto v___jp_3901_;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_a_3936_);
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
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
else
{
lean_object* v_a_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v_a_3964_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3935_);
v___x_3965_ = lean_array_get_size(v_a_3964_);
v___x_3966_ = lean_nat_dec_lt(v___x_3933_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3889_);
v___x_3967_ = lean_box(0);
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 1);
lean_ctor_set(v___x_3931_, 0, v___x_3967_);
v___x_3969_ = v___x_3931_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
else
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
lean_del_object(v___x_3931_);
v___x_3971_ = lean_box(0);
v___x_3972_ = lean_nat_dec_le(v___x_3965_, v___x_3965_);
if (v___x_3972_ == 0)
{
if (v___x_3966_ == 0)
{
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3889_);
goto v___jp_3898_;
}
else
{
size_t v___x_3973_; size_t v___x_3974_; lean_object* v___x_3975_; 
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = lean_usize_of_nat(v___x_3965_);
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3964_, v___x_3973_, v___x_3974_, v___x_3971_, v_a_3889_);
lean_dec(v_a_3964_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_dec_ref(v___x_3975_);
goto v___jp_3898_;
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
else
{
size_t v___x_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = ((size_t)0ULL);
v___x_3985_ = lean_usize_of_nat(v___x_3965_);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_3964_, v___x_3984_, v___x_3985_, v___x_3971_, v_a_3889_);
lean_dec(v_a_3964_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_dec_ref(v___x_3986_);
goto v___jp_3898_;
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
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
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_path_3924_);
v_a_3997_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3999_ = v___x_3929_;
v_isShared_4000_ = v_isSharedCheck_4009_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3929_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4009_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; uint8_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_4001_ = lean_io_error_to_string(v_a_3997_);
v___x_4002_ = 3;
v___x_4003_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set_uint8(v___x_4003_, sizeof(void*)*1, v___x_4002_);
v___x_4004_ = lean_apply_2(v_a_3889_, v___x_4003_, lean_box(0));
v___x_4005_ = lean_box(0);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4005_);
v___x_4007_ = v___x_3999_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_val_3927_);
lean_dec_ref(v_path_3924_);
v_a_4010_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4012_ = v___x_3928_;
v_isShared_4013_ = v_isSharedCheck_4022_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3928_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4022_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4014_ = lean_io_error_to_string(v_a_4010_);
v___x_4015_ = 3;
v___x_4016_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4016_, 0, v___x_4014_);
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*1, v___x_4015_);
v___x_4017_ = lean_apply_2(v_a_3889_, v___x_4016_, lean_box(0));
v___x_4018_ = lean_box(0);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4018_);
v___x_4020_ = v___x_4012_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
lean_dec(v_a_3926_);
lean_dec_ref(v_path_3924_);
lean_dec_ref(v_a_3889_);
v___x_4023_ = lean_box(0);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
}
v___jp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4030_ = l_Lake_getUrl_x3f(v___y_4026_, v___y_4027_, v___x_4029_);
lean_dec_ref(v___y_4027_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v_a_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
v_a_4032_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_a_4032_);
lean_dec_ref(v___x_4030_);
v___x_4033_ = lean_array_get_size(v_a_4032_);
v___x_4034_ = lean_nat_dec_lt(v___x_4028_, v___x_4033_);
if (v___x_4034_ == 0)
{
lean_dec(v_a_4032_);
lean_dec_ref(v_remoteScope_3885_);
v_a_3926_ = v_a_4031_;
goto v___jp_3925_;
}
else
{
lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4035_ = lean_box(0);
v___x_4036_ = lean_nat_dec_le(v___x_4033_, v___x_4033_);
if (v___x_4036_ == 0)
{
if (v___x_4034_ == 0)
{
lean_dec(v_a_4032_);
lean_dec_ref(v_remoteScope_3885_);
v_a_3926_ = v_a_4031_;
goto v___jp_3925_;
}
else
{
size_t v___x_4037_; size_t v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = ((size_t)0ULL);
v___x_4038_ = lean_usize_of_nat(v___x_4033_);
lean_inc_ref(v_a_3889_);
v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4032_, v___x_4037_, v___x_4038_, v___x_4035_, v_a_3889_);
lean_dec(v_a_4032_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_dec_ref(v___x_4039_);
lean_dec_ref(v_remoteScope_3885_);
v_a_3926_ = v_a_4031_;
goto v___jp_3925_;
}
else
{
lean_object* v_a_4040_; 
lean_dec(v_a_4031_);
lean_dec_ref(v_path_3924_);
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
v_a_3915_ = v_a_4040_;
goto v___jp_3914_;
}
}
}
else
{
size_t v___x_4041_; size_t v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = ((size_t)0ULL);
v___x_4042_ = lean_usize_of_nat(v___x_4033_);
lean_inc_ref(v_a_3889_);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4032_, v___x_4041_, v___x_4042_, v___x_4035_, v_a_3889_);
lean_dec(v_a_4032_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_dec_ref(v___x_4043_);
lean_dec_ref(v_remoteScope_3885_);
v_a_3926_ = v_a_4031_;
goto v___jp_3925_;
}
else
{
lean_object* v_a_4044_; 
lean_dec(v_a_4031_);
lean_dec_ref(v_path_3924_);
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref(v___x_4043_);
v_a_3915_ = v_a_4044_;
goto v___jp_3914_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
lean_dec_ref(v_path_3924_);
v_a_4045_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_a_4045_);
lean_dec_ref(v___x_4030_);
v___x_4046_ = lean_array_get_size(v_a_4045_);
v___x_4047_ = lean_nat_dec_lt(v___x_4028_, v___x_4046_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; 
lean_dec(v_a_4045_);
v___x_4048_ = lean_box(0);
v_a_3915_ = v___x_4048_;
goto v___jp_3914_;
}
else
{
lean_object* v___x_4049_; uint8_t v___x_4050_; 
v___x_4049_ = lean_box(0);
v___x_4050_ = lean_nat_dec_le(v___x_4046_, v___x_4046_);
if (v___x_4050_ == 0)
{
if (v___x_4047_ == 0)
{
lean_dec(v_a_4045_);
goto v___jp_3917_;
}
else
{
size_t v___x_4051_; size_t v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = ((size_t)0ULL);
v___x_4052_ = lean_usize_of_nat(v___x_4046_);
lean_inc_ref(v_a_3889_);
v___x_4053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4045_, v___x_4051_, v___x_4052_, v___x_4049_, v_a_3889_);
lean_dec(v_a_4045_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_dec_ref(v___x_4053_);
goto v___jp_3917_;
}
else
{
lean_object* v_a_4054_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
v_a_3915_ = v_a_4054_;
goto v___jp_3914_;
}
}
}
else
{
size_t v___x_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = ((size_t)0ULL);
v___x_4056_ = lean_usize_of_nat(v___x_4046_);
lean_inc_ref(v_a_3889_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4045_, v___x_4055_, v___x_4056_, v___x_4049_, v_a_3889_);
lean_dec(v_a_4045_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_dec_ref(v___x_4057_);
goto v___jp_3917_;
}
else
{
lean_object* v_a_4058_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref(v___x_4057_);
v_a_3915_ = v_a_4058_;
goto v___jp_3914_;
}
}
}
}
}
v___jp_4059_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; uint8_t v_isReservoir_4073_; 
lean_inc_ref(v_remoteScope_3885_);
lean_inc_ref(v_service_3883_);
v___x_4060_ = l_Lake_CacheService_revisionUrl(v_rev_3881_, v_service_3883_, v_remoteScope_3885_, v_platform_3886_, v_toolchain_3887_);
v___x_4061_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_4062_ = lean_string_append(v_localScope_3884_, v___x_4061_);
v___x_4063_ = lean_string_append(v___x_4062_, v_rev_3881_);
lean_dec_ref(v_rev_3881_);
v___x_4064_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4065_ = lean_string_append(v___x_4063_, v___x_4064_);
v___x_4066_ = lean_string_append(v___x_4065_, v_path_3924_);
v___x_4067_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4068_ = lean_string_append(v___x_4066_, v___x_4067_);
v___x_4069_ = lean_string_append(v___x_4068_, v___x_4060_);
v___x_4070_ = 1;
v___x_4071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4071_, 0, v___x_4069_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*1, v___x_4070_);
lean_inc_ref(v_a_3889_);
v___x_4072_ = lean_apply_2(v_a_3889_, v___x_4071_, lean_box(0));
v_isReservoir_4073_ = lean_ctor_get_uint8(v_service_3883_, sizeof(void*)*5);
lean_dec_ref(v_service_3883_);
if (v_isReservoir_4073_ == 0)
{
lean_object* v___x_4074_; 
v___x_4074_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_4026_ = v___x_4060_;
v___y_4027_ = v___x_4074_;
goto v___jp_4025_;
}
else
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lake_Reservoir_lakeHeaders;
v___y_4026_ = v___x_4060_;
v___y_4027_ = v___x_4075_;
goto v___jp_4025_;
}
}
v___jp_4077_:
{
if (v___x_4076_ == 0)
{
goto v___jp_4059_;
}
else
{
if (v_force_3888_ == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_dec_ref(v_toolchain_3887_);
lean_dec_ref(v_platform_3886_);
lean_dec_ref(v_remoteScope_3885_);
lean_dec_ref(v_localScope_3884_);
lean_dec_ref(v_service_3883_);
lean_dec_ref(v_rev_3881_);
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4079_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_4080_ = l_Lake_CacheMap_load(v_path_3924_, v___x_4079_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v_a_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
v_a_4082_ = lean_ctor_get(v___x_4080_, 1);
lean_inc(v_a_4082_);
lean_dec_ref(v___x_4080_);
v___x_4083_ = lean_array_get_size(v_a_4082_);
v___x_4084_ = lean_nat_dec_lt(v___x_4078_, v___x_4083_);
if (v___x_4084_ == 0)
{
lean_dec(v_a_4082_);
lean_dec_ref(v_a_3889_);
v_a_3895_ = v_a_4081_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_4085_; uint8_t v___x_4086_; 
v___x_4085_ = lean_box(0);
v___x_4086_ = lean_nat_dec_le(v___x_4083_, v___x_4083_);
if (v___x_4086_ == 0)
{
if (v___x_4084_ == 0)
{
lean_dec(v_a_4082_);
lean_dec_ref(v_a_3889_);
v_a_3895_ = v_a_4081_;
goto v___jp_3894_;
}
else
{
size_t v___x_4087_; size_t v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = ((size_t)0ULL);
v___x_4088_ = lean_usize_of_nat(v___x_4083_);
v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4082_, v___x_4087_, v___x_4088_, v___x_4085_, v_a_3889_);
lean_dec(v_a_4082_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_dec_ref(v___x_4089_);
v_a_3895_ = v_a_4081_;
goto v___jp_3894_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_a_4081_);
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
else
{
size_t v___x_4098_; size_t v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = ((size_t)0ULL);
v___x_4099_ = lean_usize_of_nat(v___x_4083_);
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4082_, v___x_4098_, v___x_4099_, v___x_4085_, v_a_3889_);
lean_dec(v_a_4082_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_dec_ref(v___x_4100_);
v_a_3895_ = v_a_4081_;
goto v___jp_3894_;
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_a_4081_);
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v_a_4109_ = lean_ctor_get(v___x_4080_, 1);
lean_inc(v_a_4109_);
lean_dec_ref(v___x_4080_);
v___x_4110_ = lean_array_get_size(v_a_4109_);
v___x_4111_ = lean_nat_dec_lt(v___x_4078_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec(v_a_4109_);
lean_dec_ref(v_a_3889_);
v___x_4112_ = lean_box(0);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
else
{
lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = lean_box(0);
v___x_4115_ = lean_nat_dec_le(v___x_4110_, v___x_4110_);
if (v___x_4115_ == 0)
{
if (v___x_4111_ == 0)
{
lean_dec(v_a_4109_);
lean_dec_ref(v_a_3889_);
goto v___jp_3891_;
}
else
{
size_t v___x_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = ((size_t)0ULL);
v___x_4117_ = lean_usize_of_nat(v___x_4110_);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4109_, v___x_4116_, v___x_4117_, v___x_4114_, v_a_3889_);
lean_dec(v_a_4109_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_dec_ref(v___x_4118_);
goto v___jp_3891_;
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
else
{
size_t v___x_4127_; size_t v___x_4128_; lean_object* v___x_4129_; 
v___x_4127_ = ((size_t)0ULL);
v___x_4128_ = lean_usize_of_nat(v___x_4110_);
v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__1(v_a_4109_, v___x_4127_, v___x_4128_, v___x_4114_, v_a_3889_);
lean_dec(v_a_4109_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_dec_ref(v___x_4129_);
goto v___jp_3891_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4129_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4129_);
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
}
}
else
{
goto v___jp_4059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_4164_, lean_object* v_cache_4165_, lean_object* v_service_4166_, lean_object* v_localScope_4167_, lean_object* v_remoteScope_4168_, lean_object* v_platform_4169_, lean_object* v_toolchain_4170_, lean_object* v_force_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
uint8_t v_force_boxed_4174_; lean_object* v_res_4175_; 
v_force_boxed_4174_ = lean_unbox(v_force_4171_);
v_res_4175_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_4164_, v_cache_4165_, v_service_4166_, v_localScope_4167_, v_remoteScope_4168_, v_platform_4169_, v_toolchain_4170_, v_force_boxed_4174_, v_a_4172_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_4177_, lean_object* v_outputs_4178_, lean_object* v_service_4179_, lean_object* v_scope_4180_, lean_object* v_platform_4181_, lean_object* v_toolchain_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_url_4185_; lean_object* v___y_4187_; lean_object* v_s_4203_; 
lean_inc_ref(v_scope_4180_);
lean_inc_ref(v_service_4179_);
v_url_4185_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_4177_, v_service_4179_, v_scope_4180_, v_platform_4181_, v_toolchain_4182_);
v_s_4203_ = lean_ctor_get(v_scope_4180_, 0);
lean_inc_ref(v_s_4203_);
lean_dec_ref(v_scope_4180_);
v___y_4187_ = v_s_4203_;
goto v___jp_4186_;
v___jp_4186_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v_key_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4188_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_4189_ = lean_string_append(v___y_4187_, v___x_4188_);
v___x_4190_ = lean_string_append(v___x_4189_, v_rev_4177_);
v___x_4191_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_4192_ = lean_string_append(v___x_4190_, v___x_4191_);
v___x_4193_ = lean_string_append(v___x_4192_, v_outputs_4178_);
v___x_4194_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_4195_ = lean_string_append(v___x_4193_, v___x_4194_);
v___x_4196_ = lean_string_append(v___x_4195_, v_url_4185_);
v___x_4197_ = 1;
v___x_4198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set_uint8(v___x_4198_, sizeof(void*)*1, v___x_4197_);
lean_inc_ref(v_a_4183_);
v___x_4199_ = lean_apply_2(v_a_4183_, v___x_4198_, lean_box(0));
v_key_4200_ = lean_ctor_get(v_service_4179_, 1);
lean_inc_ref(v_key_4200_);
lean_dec_ref(v_service_4179_);
v___x_4201_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_4202_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_4183_, v_outputs_4178_, v___x_4201_, v_url_4185_, v_key_4200_);
return v___x_4202_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_4204_, lean_object* v_outputs_4205_, lean_object* v_service_4206_, lean_object* v_scope_4207_, lean_object* v_platform_4208_, lean_object* v_toolchain_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_4204_, v_outputs_4205_, v_service_4206_, v_scope_4207_, v_platform_4208_, v_toolchain_4209_, v_a_4210_);
lean_dec_ref(v_toolchain_4209_);
lean_dec_ref(v_rev_4204_);
return v_res_4212_;
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
