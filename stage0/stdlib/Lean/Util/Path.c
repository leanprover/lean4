// Lean compiler output
// Module: Lean.Util.Path
// Imports: public import Init.System.IO public import Init.Data.String.Compare import Init.Control.Do import Init.Data.ToString.Name import Init.Data.String.TakeDrop import Init.Data.List.Monadic import Init.Data.Option.BasicAux import Init.Data.ToString.Macro import Init.Data.String.Length
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
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_IO_Process_run(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_current_dir();
lean_object* l_System_SearchPath_parse(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_IO_appDir();
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_runtime_deep_copy(lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_value)}};
static const lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_forEachModuleInDir___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_forEachModuleInDir___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_forEachModuleInDir___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object*);
LEAN_EXPORT lean_object* l_Lean_realPathNormalized___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Util.Path"};
static const lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0 = (const lean_object*)&l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0_value;
static const lean_string_object l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Util.Path.0.Lean.modToFilePath.go"};
static const lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1 = (const lean_object*)&l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1_value;
static const lean_string_object l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ill-formed import"};
static const lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2 = (const lean_object*)&l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchPathRef;
static const lean_string_object l_Lean_getBuildDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_getBuildDir___closed__0 = (const lean_object*)&l_Lean_getBuildDir___closed__0_value;
static const lean_string_object l_Lean_getBuildDir___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_getBuildDir___closed__1 = (const lean_object*)&l_Lean_getBuildDir___closed__1_value;
static const lean_string_object l_Lean_getBuildDir___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_getBuildDir___closed__2 = (const lean_object*)&l_Lean_getBuildDir___closed__2_value;
static lean_once_cell_t l_Lean_getBuildDir___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getBuildDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_getBuildDir();
LEAN_EXPORT lean_object* l_Lean_getBuildDir___boxed(lean_object*);
static const lean_string_object l_Lean_getLibDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lean_getLibDir___closed__0 = (const lean_object*)&l_Lean_getLibDir___closed__0_value;
static lean_once_cell_t l_Lean_getLibDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_getLibDir___closed__1;
static const lean_string_object l_Lean_getLibDir___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_Lean_getLibDir___closed__2 = (const lean_object*)&l_Lean_getLibDir___closed__2_value;
static const lean_string_object l_Lean_getLibDir___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "stage1"};
static const lean_object* l_Lean_getLibDir___closed__3 = (const lean_object*)&l_Lean_getLibDir___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_getLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLibDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_addSearchPathFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lean_addSearchPathFromEnv___closed__0 = (const lean_object*)&l_Lean_addSearchPathFromEnv___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initSearchPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_init_search_path();
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_oleanRootCacheRef;
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_findOLean_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_findOLean_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_findOLean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_Lean_findOLean___closed__0 = (const lean_object*)&l_Lean_findOLean___closed__0_value;
static const lean_string_object l_Lean_findOLean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unknown module prefix '"};
static const lean_object* l_Lean_findOLean___closed__1 = (const lean_object*)&l_Lean_findOLean___closed__1_value;
static const lean_string_object l_Lean_findOLean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "'\n\nNo directory '"};
static const lean_object* l_Lean_findOLean___closed__2 = (const lean_object*)&l_Lean_findOLean___closed__2_value;
static const lean_string_object l_Lean_findOLean___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' or file '"};
static const lean_object* l_Lean_findOLean___closed__3 = (const lean_object*)&l_Lean_findOLean___closed__3_value;
static const lean_string_object l_Lean_findOLean___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ".olean' in the search path entries:\n"};
static const lean_object* l_Lean_findOLean___closed__4 = (const lean_object*)&l_Lean_findOLean___closed__4_value;
static const lean_string_object l_Lean_findOLean___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_findOLean___closed__5 = (const lean_object*)&l_Lean_findOLean___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_findLean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ".lean' in the search path entries:\n"};
static const lean_object* l_Lean_findLean___closed__0 = (const lean_object*)&l_Lean_findLean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getSrcSearchPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LEAN_SRC_PATH"};
static const lean_object* l_Lean_getSrcSearchPath___closed__0 = (const lean_object*)&l_Lean_getSrcSearchPath___closed__0_value;
static const lean_string_object l_Lean_getSrcSearchPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* l_Lean_getSrcSearchPath___closed__1 = (const lean_object*)&l_Lean_getSrcSearchPath___closed__1_value;
static const lean_string_object l_Lean_getSrcSearchPath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l_Lean_getSrcSearchPath___closed__2 = (const lean_object*)&l_Lean_getSrcSearchPath___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath();
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_moduleNameOfFileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "input file '"};
static const lean_object* l_Lean_moduleNameOfFileName___closed__0 = (const lean_object*)&l_Lean_moduleNameOfFileName___closed__0_value;
static const lean_string_object l_Lean_moduleNameOfFileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "' must be contained in root directory ("};
static const lean_object* l_Lean_moduleNameOfFileName___closed__1 = (const lean_object*)&l_Lean_moduleNameOfFileName___closed__1_value;
static const lean_string_object l_Lean_moduleNameOfFileName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_moduleNameOfFileName___closed__2 = (const lean_object*)&l_Lean_moduleNameOfFileName___closed__2_value;
static lean_once_cell_t l_Lean_moduleNameOfFileName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_moduleNameOfFileName___closed__3;
static lean_once_cell_t l_Lean_moduleNameOfFileName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_moduleNameOfFileName___closed__4;
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_findSysroot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lean_findSysroot___closed__0 = (const lean_object*)&l_Lean_findSysroot___closed__0_value;
static const lean_ctor_object l_Lean_findSysroot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_findSysroot___closed__1 = (const lean_object*)&l_Lean_findSysroot___closed__1_value;
static const lean_string_object l_Lean_findSysroot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "--print-prefix"};
static const lean_object* l_Lean_findSysroot___closed__2 = (const lean_object*)&l_Lean_findSysroot___closed__2_value;
static const lean_array_object l_Lean_findSysroot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_findSysroot___closed__2_value)}};
static const lean_object* l_Lean_findSysroot___closed__3 = (const lean_object*)&l_Lean_findSysroot___closed__3_value;
static const lean_array_object l_Lean_findSysroot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_findSysroot___closed__4 = (const lean_object*)&l_Lean_findSysroot___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____s_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__1(lean_object* v___x_5_, lean_object* v_toPure_6_, lean_object* v_r_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_5_);
v___x_9_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object* v___x_10_){
_start:
{
uint8_t v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = l_System_FilePath_isDir(v___x_10_);
v___x_13_ = lean_box(v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object* v___x_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_forEachModuleInDir___redArg___lam__3(v___x_15_);
lean_dec_ref(v___x_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object* v___x_18_, lean_object* v_f_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = l_Lean_Name_append(v___x_18_, v_x_20_);
v___x_22_ = lean_apply_1(v_f_19_, v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___f_28_; 
v___x_27_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_28_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_28_, 0, v___x_27_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object* v_toPure_29_, lean_object* v___f_30_, lean_object* v_f_31_, lean_object* v_toBind_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v___f_35_, lean_object* v_____do__lift_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___f_39_; size_t v_sz_40_; size_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_37_ = lean_box(0);
lean_inc(v_toPure_29_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__1), 3, 2);
lean_closure_set(v___f_38_, 0, v___x_37_);
lean_closure_set(v___f_38_, 1, v_toPure_29_);
lean_inc_ref(v_inst_33_);
lean_inc_ref(v___f_38_);
lean_inc(v_toBind_32_);
v___f_39_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__5), 12, 9);
lean_closure_set(v___f_39_, 0, v___f_30_);
lean_closure_set(v___f_39_, 1, v___x_37_);
lean_closure_set(v___f_39_, 2, v_toPure_29_);
lean_closure_set(v___f_39_, 3, v_f_31_);
lean_closure_set(v___f_39_, 4, v_toBind_32_);
lean_closure_set(v___f_39_, 5, v___f_38_);
lean_closure_set(v___f_39_, 6, v_inst_33_);
lean_closure_set(v___f_39_, 7, v_inst_34_);
lean_closure_set(v___f_39_, 8, v___f_38_);
v_sz_40_ = lean_array_size(v_____do__lift_36_);
v___x_41_ = ((size_t)0ULL);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_33_, v_____do__lift_36_, v___f_39_, v_sz_40_, v___x_41_, v___x_37_);
v___x_43_ = lean_apply_4(v_toBind_32_, lean_box(0), lean_box(0), v___x_42_, v___f_35_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_dir_46_, lean_object* v_f_47_){
_start:
{
lean_object* v_toApplicative_48_; lean_object* v_toBind_49_; lean_object* v_toPure_50_; lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___x_56_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_44_, 0);
v_toBind_49_ = lean_ctor_get(v_inst_44_, 1);
lean_inc_n(v_toBind_49_, 2);
v_toPure_50_ = lean_ctor_get(v_toApplicative_48_, 1);
lean_inc_n(v_toPure_50_, 2);
v___f_51_ = lean_obj_once(&l_Lean_forEachModuleInDir___redArg___closed__0, &l_Lean_forEachModuleInDir___redArg___closed__0_once, _init_l_Lean_forEachModuleInDir___redArg___closed__0);
v___x_52_ = lean_alloc_closure((void*)(l_System_FilePath_readDir___boxed), 2, 1);
lean_closure_set(v___x_52_, 0, v_dir_46_);
lean_inc(v_inst_45_);
v___x_53_ = lean_apply_2(v_inst_45_, lean_box(0), v___x_52_);
v___f_54_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__0), 2, 1);
lean_closure_set(v___f_54_, 0, v_toPure_50_);
v___f_55_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__6), 8, 7);
lean_closure_set(v___f_55_, 0, v_toPure_50_);
lean_closure_set(v___f_55_, 1, v___f_51_);
lean_closure_set(v___f_55_, 2, v_f_47_);
lean_closure_set(v___f_55_, 3, v_toBind_49_);
lean_closure_set(v___f_55_, 4, v_inst_44_);
lean_closure_set(v___f_55_, 5, v_inst_45_);
lean_closure_set(v___f_55_, 6, v___f_54_);
v___x_56_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v___x_53_, v___f_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object* v___x_57_, lean_object* v___f_58_, lean_object* v___x_59_, lean_object* v_toPure_60_, lean_object* v_a_61_, lean_object* v_f_62_, lean_object* v_toBind_63_, lean_object* v___f_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v___f_67_, uint8_t v_____do__lift_68_){
_start:
{
if (v_____do__lift_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
lean_dec(v___f_67_);
lean_dec(v_inst_66_);
lean_dec_ref(v_inst_65_);
v___x_69_ = l_System_FilePath_extension(v___x_57_);
v___x_70_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
v___x_71_ = l_instBEqOption_beq___redArg(v___f_58_, v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v___f_64_);
lean_dec(v_toBind_63_);
lean_dec(v_f_62_);
lean_dec_ref(v_a_61_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_59_);
v___x_73_ = lean_apply_2(v_toPure_60_, lean_box(0), v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_fileName_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_toPure_60_);
v_fileName_74_ = lean_ctor_get(v_a_61_, 1);
lean_inc_ref(v_fileName_74_);
lean_dec_ref(v_a_61_);
v___x_75_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2));
v___x_76_ = l_System_FilePath_withExtension(v_fileName_74_, v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = l_Lean_Name_str___override(v___x_77_, v___x_76_);
v___x_79_ = lean_apply_1(v_f_62_, v___x_78_);
v___x_80_ = lean_apply_4(v_toBind_63_, lean_box(0), lean_box(0), v___x_79_, v___f_64_);
return v___x_80_;
}
}
else
{
lean_object* v_fileName_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v___f_64_);
lean_dec(v_toPure_60_);
lean_dec_ref(v___f_58_);
v_fileName_81_ = lean_ctor_get(v_a_61_, 1);
lean_inc_ref(v_fileName_81_);
lean_dec_ref(v_a_61_);
v___x_82_ = lean_box(0);
v___x_83_ = l_Lean_Name_str___override(v___x_82_, v_fileName_81_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__2), 3, 2);
lean_closure_set(v___f_84_, 0, v___x_83_);
lean_closure_set(v___f_84_, 1, v_f_62_);
v___x_85_ = l_Lean_forEachModuleInDir___redArg(v_inst_65_, v_inst_66_, v___x_57_, v___f_84_);
v___x_86_ = lean_apply_4(v_toBind_63_, lean_box(0), lean_box(0), v___x_85_, v___f_67_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___boxed(lean_object* v___x_87_, lean_object* v___f_88_, lean_object* v___x_89_, lean_object* v_toPure_90_, lean_object* v_a_91_, lean_object* v_f_92_, lean_object* v_toBind_93_, lean_object* v___f_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v___f_97_, lean_object* v_____do__lift_98_){
_start:
{
uint8_t v_____do__lift_401__boxed_99_; lean_object* v_res_100_; 
v_____do__lift_401__boxed_99_ = lean_unbox(v_____do__lift_98_);
v_res_100_ = l_Lean_forEachModuleInDir___redArg___lam__4(v___x_87_, v___f_88_, v___x_89_, v_toPure_90_, v_a_91_, v_f_92_, v_toBind_93_, v___f_94_, v_inst_95_, v_inst_96_, v___f_97_, v_____do__lift_401__boxed_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object* v___f_101_, lean_object* v___x_102_, lean_object* v_toPure_103_, lean_object* v_f_104_, lean_object* v_toBind_105_, lean_object* v___f_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v___f_109_, lean_object* v_a_110_, lean_object* v_x_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref(v_a_110_);
v___x_113_ = l_IO_FS_DirEntry_path(v_a_110_);
lean_inc_ref(v___x_113_);
v___f_114_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_114_, 0, v___x_113_);
lean_inc(v_inst_108_);
lean_inc(v_toBind_105_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_115_, 0, v___x_113_);
lean_closure_set(v___f_115_, 1, v___f_101_);
lean_closure_set(v___f_115_, 2, v___x_102_);
lean_closure_set(v___f_115_, 3, v_toPure_103_);
lean_closure_set(v___f_115_, 4, v_a_110_);
lean_closure_set(v___f_115_, 5, v_f_104_);
lean_closure_set(v___f_115_, 6, v_toBind_105_);
lean_closure_set(v___f_115_, 7, v___f_106_);
lean_closure_set(v___f_115_, 8, v_inst_107_);
lean_closure_set(v___f_115_, 9, v_inst_108_);
lean_closure_set(v___f_115_, 10, v___f_109_);
v___x_116_ = lean_apply_2(v_inst_108_, lean_box(0), v___f_114_);
v___x_117_ = lean_apply_4(v_toBind_105_, lean_box(0), lean_box(0), v___x_116_, v___f_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object* v_m_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_dir_121_, lean_object* v_f_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_forEachModuleInDir___redArg(v_inst_119_, v_inst_120_, v_dir_121_, v_f_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object* v_p_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_io_realpath(v_p_124_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_135_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_135_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = l_System_FilePath_normalize(v_a_127_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_131_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized___boxed(lean_object* v_p_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_realPathNormalized(v_p_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object* v_msg_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2));
v___x_141_ = lean_panic_fn_borrowed(v___x_140_, v_msg_139_);
return v___x_141_;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2));
v___x_146_ = lean_unsigned_to_nat(20u);
v___x_147_ = lean_unsigned_to_nat(52u);
v___x_148_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1));
v___x_149_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0));
v___x_150_ = l_mkPanicMessageWithDecl(v___x_149_, v___x_148_, v___x_147_, v___x_146_, v___x_145_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object* v_base_151_, lean_object* v_a_152_){
_start:
{
switch(lean_obj_tag(v_a_152_))
{
case 0:
{
lean_inc_ref(v_base_151_);
return v_base_151_;
}
case 1:
{
lean_object* v_pre_153_; lean_object* v_str_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_pre_153_ = lean_ctor_get(v_a_152_, 0);
lean_inc(v_pre_153_);
v_str_154_ = lean_ctor_get(v_a_152_, 1);
lean_inc_ref(v_str_154_);
lean_dec_ref_known(v_a_152_, 2);
v___x_155_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_151_, v_pre_153_);
v___x_156_ = l_System_FilePath_join(v___x_155_, v_str_154_);
return v___x_156_;
}
default: 
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref_known(v_a_152_, 2);
v___x_157_ = lean_obj_once(&l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3, &l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3_once, _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3);
v___x_158_ = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object* v_base_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_159_, v_a_160_);
lean_dec_ref(v_base_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object* v_base_162_, lean_object* v_mod_163_, lean_object* v_ext_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_162_, v_mod_163_);
v___x_166_ = l_System_FilePath_addExtension(v___x_165_, v_ext_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object* v_base_167_, lean_object* v_mod_168_, lean_object* v_ext_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_modToFilePath(v_base_167_, v_mod_168_, v_ext_169_);
lean_dec_ref(v_ext_169_);
lean_dec_ref(v_base_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(lean_object* v_pkg_171_, lean_object* v_ext_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v_pkg_171_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_head_177_; lean_object* v_tail_178_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_head_177_ = lean_ctor_get(v_x_173_, 0);
lean_inc_n(v_head_177_, 2);
v_tail_178_ = lean_ctor_get(v_x_173_, 1);
lean_inc(v_tail_178_);
lean_dec_ref_known(v_x_173_, 2);
lean_inc_ref(v_pkg_171_);
v___x_182_ = l_System_FilePath_join(v_head_177_, v_pkg_171_);
v___x_183_ = l_System_FilePath_isDir(v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = l_System_FilePath_addExtension(v___x_182_, v_ext_172_);
v___x_185_ = l_System_FilePath_pathExists(v___x_184_);
lean_dec_ref(v___x_184_);
if (v___x_185_ == 0)
{
lean_dec(v_head_177_);
v_x_173_ = v_tail_178_;
goto _start;
}
else
{
lean_dec(v_tail_178_);
lean_dec_ref(v_pkg_171_);
goto v___jp_179_;
}
}
else
{
lean_dec_ref(v___x_182_);
lean_dec(v_tail_178_);
lean_dec_ref(v_pkg_171_);
goto v___jp_179_;
}
v___jp_179_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v_head_177_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0___boxed(lean_object* v_pkg_187_, lean_object* v_ext_188_, lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(v_pkg_187_, v_ext_188_, v_x_189_);
lean_dec_ref(v_ext_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt(lean_object* v_sp_192_, lean_object* v_ext_193_, lean_object* v_mod_194_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v_pkg_198_; lean_object* v___x_199_; 
v___x_196_ = l_Lean_Name_getRoot(v_mod_194_);
v___x_197_ = 0;
v_pkg_198_ = l_Lean_Name_toString(v___x_196_, v___x_197_);
v___x_199_ = l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(v_pkg_198_, v_ext_193_, v_sp_192_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt___boxed(lean_object* v_sp_200_, lean_object* v_ext_201_, lean_object* v_mod_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_SearchPath_findRootWithExt(v_sp_200_, v_ext_201_, v_mod_202_);
lean_dec(v_mod_202_);
lean_dec_ref(v_ext_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* v_sp_205_, lean_object* v_ext_206_, lean_object* v_mod_207_){
_start:
{
lean_object* v___x_209_; lean_object* v_a_210_; 
v___x_209_ = l_Lean_SearchPath_findRootWithExt(v_sp_205_, v_ext_206_, v_mod_207_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
if (lean_obj_tag(v_a_210_) == 0)
{
lean_dec(v_mod_207_);
return v___x_209_;
}
else
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_226_; 
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v___x_209_, 0);
lean_dec(v_unused_227_);
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_226_;
goto v_resetjp_211_;
}
else
{
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_226_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_225_; 
v_val_214_ = lean_ctor_get(v_a_210_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_210_);
if (v_isSharedCheck_225_ == 0)
{
v___x_216_ = v_a_210_;
v_isShared_217_ = v_isSharedCheck_225_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_dec(v_a_210_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_225_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = l_Lean_modToFilePath(v_val_214_, v_mod_207_, v_ext_206_);
lean_dec(v_val_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_220_);
v___x_222_ = v___x_212_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* v_sp_228_, lean_object* v_ext_229_, lean_object* v_mod_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_SearchPath_findWithExt(v_sp_228_, v_ext_229_, v_mod_230_);
lean_dec_ref(v_ext_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* v_sp_233_, lean_object* v_ext_234_, lean_object* v_mod_235_){
_start:
{
lean_object* v___x_240_; lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_250_; 
v___x_240_ = l_Lean_SearchPath_findWithExt(v_sp_233_, v_ext_234_, v_mod_235_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_250_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_250_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_250_;
goto v_resetjp_242_;
}
v___jp_237_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
v_resetjp_242_:
{
if (lean_obj_tag(v_a_241_) == 1)
{
lean_object* v_val_245_; uint8_t v___x_246_; 
v_val_245_ = lean_ctor_get(v_a_241_, 0);
v___x_246_ = l_System_FilePath_pathExists(v_val_245_);
if (v___x_246_ == 0)
{
lean_dec_ref_known(v_a_241_, 1);
lean_del_object(v___x_243_);
goto v___jp_237_;
}
else
{
lean_object* v___x_248_; 
if (v_isShared_244_ == 0)
{
v___x_248_ = v___x_243_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_241_);
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
lean_del_object(v___x_243_);
lean_dec(v_a_241_);
goto v___jp_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* v_sp_251_, lean_object* v_ext_252_, lean_object* v_mod_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_SearchPath_findModuleWithExt(v_sp_251_, v_ext_252_, v_mod_253_);
lean_dec_ref(v_ext_252_);
return v_res_255_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
if (lean_obj_tag(v_x_257_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 1;
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
else
{
if (lean_obj_tag(v_x_257_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v_val_262_; uint8_t v___x_263_; 
v_val_261_ = lean_ctor_get(v_x_256_, 0);
v_val_262_ = lean_ctor_get(v_x_257_, 0);
v___x_263_ = lean_string_dec_eq(v_val_261_, v_val_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v_x_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object* v_ext_268_, lean_object* v_as_269_, size_t v_i_270_, size_t v_stop_271_, lean_object* v_b_272_){
_start:
{
lean_object* v___y_274_; uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_eq(v_i_270_, v_stop_271_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_279_ = lean_array_uget_borrowed(v_as_269_, v_i_270_);
lean_inc(v___x_279_);
v___x_280_ = l_System_FilePath_extension(v___x_279_);
lean_inc_ref(v_ext_268_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_ext_268_);
v___x_282_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v___x_280_, v___x_281_);
lean_dec_ref_known(v___x_281_, 1);
lean_dec(v___x_280_);
if (v___x_282_ == 0)
{
v___y_274_ = v_b_272_;
goto v___jp_273_;
}
else
{
lean_object* v___x_283_; 
lean_inc(v___x_279_);
v___x_283_ = lean_array_push(v_b_272_, v___x_279_);
v___y_274_ = v___x_283_;
goto v___jp_273_;
}
}
else
{
lean_dec_ref(v_ext_268_);
return v_b_272_;
}
v___jp_273_:
{
size_t v___x_275_; size_t v___x_276_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_270_, v___x_275_);
v_i_270_ = v___x_276_;
v_b_272_ = v___y_274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object* v_ext_284_, lean_object* v_as_285_, lean_object* v_i_286_, lean_object* v_stop_287_, lean_object* v_b_288_){
_start:
{
size_t v_i_boxed_289_; size_t v_stop_boxed_290_; lean_object* v_res_291_; 
v_i_boxed_289_ = lean_unbox_usize(v_i_286_);
lean_dec(v_i_286_);
v_stop_boxed_290_ = lean_unbox_usize(v_stop_287_);
lean_dec(v_stop_287_);
v_res_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_284_, v_as_285_, v_i_boxed_289_, v_stop_boxed_290_, v_b_288_);
lean_dec_ref(v_as_285_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t v_val_292_, lean_object* v_x_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(v_val_292_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object* v_val_297_, lean_object* v_x_298_, lean_object* v___y_299_){
_start:
{
uint8_t v_val_911__boxed_300_; lean_object* v_res_301_; 
v_val_911__boxed_300_ = lean_unbox(v_val_297_);
v_res_301_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(v_val_911__boxed_300_, v_x_298_);
lean_dec_ref(v_x_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object* v_ext_304_, lean_object* v_as_x27_305_, lean_object* v_b_306_){
_start:
{
if (lean_obj_tag(v_as_x27_305_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref(v_ext_304_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v_b_306_);
return v___x_308_;
}
else
{
lean_object* v_head_309_; lean_object* v_tail_310_; uint8_t v___x_311_; 
v_head_309_ = lean_ctor_get(v_as_x27_305_, 0);
v_tail_310_ = lean_ctor_get(v_as_x27_305_, 1);
v___x_311_ = l_System_FilePath_isDir(v_head_309_);
if (v___x_311_ == 0)
{
v_as_x27_305_ = v_tail_310_;
goto _start;
}
else
{
lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v___x_313_ = lean_box(v___x_311_);
v___f_314_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_314_, 0, v___x_313_);
lean_inc(v_head_309_);
v___x_315_ = l_System_FilePath_walkDir(v_head_309_, v___f_314_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___y_318_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_array_get_size(v_a_316_);
v___x_323_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_324_ = lean_nat_dec_lt(v___x_321_, v___x_322_);
if (v___x_324_ == 0)
{
lean_dec(v_a_316_);
v___y_318_ = v___x_323_;
goto v___jp_317_;
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_322_);
lean_inc_ref(v_ext_304_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_304_, v_a_316_, v___x_325_, v___x_326_, v___x_323_);
lean_dec(v_a_316_);
v___y_318_ = v___x_327_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = l_Array_append___redArg(v_b_306_, v___y_318_);
lean_dec_ref(v___y_318_);
v_as_x27_305_ = v_tail_310_;
v_b_306_ = v___x_319_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_306_);
lean_dec_ref(v_ext_304_);
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(lean_object* v_ext_328_, lean_object* v_as_x27_329_, lean_object* v_b_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_328_, v_as_x27_329_, v_b_330_);
lean_dec(v_as_x27_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object* v_sp_333_, lean_object* v_ext_334_){
_start:
{
lean_object* v_paths_336_; lean_object* v___x_337_; 
v_paths_336_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_337_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_334_, v_sp_333_, v_paths_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt___boxed(lean_object* v_sp_338_, lean_object* v_ext_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_SearchPath_findAllWithExt(v_sp_338_, v_ext_339_);
lean_dec(v_sp_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(lean_object* v_ext_342_, lean_object* v_as_343_, lean_object* v_as_x27_344_, lean_object* v_b_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_342_, v_as_x27_344_, v_b_345_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(lean_object* v_ext_349_, lean_object* v_as_350_, lean_object* v_as_x27_351_, lean_object* v_b_352_, lean_object* v_a_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(v_ext_349_, v_as_350_, v_as_x27_351_, v_b_352_, v_a_353_);
lean_dec(v_as_x27_351_);
lean_dec(v_as_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_box(0);
v___x_358_ = lean_st_mk_ref(v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
return v_res_361_;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__3(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = ((lean_object*)(l_Lean_getBuildDir___closed__2));
v___x_366_ = lean_unsigned_to_nat(14u);
v___x_367_ = lean_unsigned_to_nat(22u);
v___x_368_ = ((lean_object*)(l_Lean_getBuildDir___closed__1));
v___x_369_ = ((lean_object*)(l_Lean_getBuildDir___closed__0));
v___x_370_ = l_mkPanicMessageWithDecl(v___x_369_, v___x_368_, v___x_367_, v___x_366_, v___x_365_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir(){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_IO_appDir();
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_387_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_387_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; 
v___x_377_ = l_System_FilePath_parent(v_a_373_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = lean_obj_once(&l_Lean_getBuildDir___closed__3, &l_Lean_getBuildDir___closed__3_once, _init_l_Lean_getBuildDir___closed__3);
v___x_379_ = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(v___x_378_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_379_);
v___x_381_ = v___x_375_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v_val_383_; lean_object* v___x_385_; 
v_val_383_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_377_, 1);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_val_383_);
v___x_385_ = v___x_375_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_val_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir___boxed(lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_getBuildDir();
return v_res_389_;
}
}
static uint8_t _init_l_Lean_getLibDir___closed__1(void){
_start:
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_box(0);
v___x_392_ = lean_internal_is_stage0(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir(lean_object* v_leanSysroot_395_){
_start:
{
lean_object* v_buildDir_398_; uint8_t v___x_404_; 
v___x_404_ = lean_uint8_once(&l_Lean_getLibDir___closed__1, &l_Lean_getLibDir___closed__1_once, _init_l_Lean_getLibDir___closed__1);
if (v___x_404_ == 0)
{
v_buildDir_398_ = v_leanSysroot_395_;
goto v___jp_397_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_buildDir_408_; 
v___x_405_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_406_ = l_System_FilePath_join(v_leanSysroot_395_, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_getLibDir___closed__3));
v_buildDir_408_ = l_System_FilePath_join(v___x_406_, v___x_407_);
v_buildDir_398_ = v_buildDir_408_;
goto v___jp_397_;
}
v___jp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_399_ = ((lean_object*)(l_Lean_getLibDir___closed__0));
v___x_400_ = l_System_FilePath_join(v_buildDir_398_, v___x_399_);
v___x_401_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__0));
v___x_402_ = l_System_FilePath_join(v___x_400_, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___boxed(lean_object* v_leanSysroot_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_getLibDir(v_leanSysroot_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object* v_leanSysroot_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_424_; 
v___x_414_ = l_Lean_getLibDir(v_leanSysroot_412_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_424_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v_a_415_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_420_);
v___x_422_ = v___x_417_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath___boxed(lean_object* v_leanSysroot_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object* v_sp_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_addSearchPathFromEnv___closed__0));
v___x_432_ = lean_io_getenv(v___x_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_sp_429_);
return v___x_433_;
}
else
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_443_; 
v_val_434_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_443_ == 0)
{
v___x_436_ = v___x_432_;
v_isShared_437_ = v_isSharedCheck_443_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v___x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_443_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = l_System_SearchPath_parse(v_val_434_);
v___x_439_ = l_List_appendTR___redArg(v___x_438_, v_sp_429_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 0);
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv___boxed(lean_object* v_sp_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_addSearchPathFromEnv(v_sp_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object* v_leanSysroot_447_, lean_object* v_sp_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_447_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_464_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = l_Lean_addSearchPathFromEnv(v_a_451_);
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_464_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_457_ = l_List_appendTR___redArg(v_sp_448_, v_a_453_);
v___x_458_ = l_Lean_searchPathRef;
v___x_459_ = lean_box(0);
v___x_460_ = lean_st_ref_swap(v___x_458_, v___x_457_);
lean_dec(v___x_460_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_sp_448_);
v_a_465_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_450_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_450_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath___boxed(lean_object* v_leanSysroot_473_, lean_object* v_sp_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_initSearchPath(v_leanSysroot_473_, v_sp_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* lean_init_search_path(){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v___x_480_ = lean_box(0);
v___x_481_ = l_Lean_initSearchPath(v_a_479_, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_478_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_478_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = lean_init_search_path();
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2_));
v___x_496_ = lean_st_mk_ref(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2____boxed(lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2_();
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___redArg(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_head_503_; lean_object* v_tail_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; uint8_t v___x_507_; 
v_head_503_ = lean_ctor_get(v_x_501_, 0);
v_tail_504_ = lean_ctor_get(v_x_501_, 1);
v_fst_505_ = lean_ctor_get(v_head_503_, 0);
v_snd_506_ = lean_ctor_get(v_head_503_, 1);
v___x_507_ = lean_name_eq(v_x_500_, v_fst_505_);
if (v___x_507_ == 0)
{
v_x_501_ = v_tail_504_;
goto _start;
}
else
{
lean_object* v___x_509_; 
lean_inc(v_snd_506_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_snd_506_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___redArg___boxed(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v_x_510_, v_x_511_);
lean_dec(v_x_511_);
lean_dec(v_x_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__1(lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
if (lean_obj_tag(v_a_513_) == 0)
{
lean_object* v___x_515_; 
v___x_515_ = l_List_reverse___redArg(v_a_514_);
return v___x_515_;
}
else
{
lean_object* v_head_516_; lean_object* v_tail_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_head_516_ = lean_ctor_get(v_a_513_, 0);
v_tail_517_ = lean_ctor_get(v_a_513_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v_a_513_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_tail_517_);
lean_inc(v_head_516_);
lean_dec(v_a_513_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_a_514_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_head_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_a_514_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v_a_513_ = v_tail_517_;
v_a_514_ = v___x_522_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_findOLean_spec__2(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 1;
return v___x_528_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = 0;
return v___x_529_;
}
}
else
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
else
{
lean_object* v_head_531_; lean_object* v_tail_532_; lean_object* v_head_533_; lean_object* v_tail_534_; uint8_t v___x_535_; 
v_head_531_ = lean_ctor_get(v_x_526_, 0);
v_tail_532_ = lean_ctor_get(v_x_526_, 1);
v_head_533_ = lean_ctor_get(v_x_527_, 0);
v_tail_534_ = lean_ctor_get(v_x_527_, 1);
v___x_535_ = lean_string_dec_eq(v_head_531_, v_head_533_);
if (v___x_535_ == 0)
{
return v___x_535_;
}
else
{
v_x_526_ = v_tail_532_;
v_x_527_ = v_tail_534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_findOLean_spec__2___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_List_beq___at___00Lean_findOLean_spec__2(v_x_537_, v_x_538_);
lean_dec(v_x_538_);
lean_dec(v_x_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object* v_mod_547_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___y_555_; lean_object* v_fst_618_; lean_object* v_snd_619_; uint8_t v___x_620_; 
v___x_549_ = l_Lean_searchPathRef;
v___x_550_ = lean_st_ref_get(v___x_549_);
v___x_551_ = l_Lean_Name_getRoot(v_mod_547_);
v___x_552_ = l___private_Lean_Util_Path_0__Lean_oleanRootCacheRef;
v___x_553_ = lean_st_ref_get(v___x_552_);
v_fst_618_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_fst_618_);
v_snd_619_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_619_);
lean_dec(v___x_553_);
v___x_620_ = l_List_beq___at___00Lean_findOLean_spec__2(v_fst_618_, v___x_550_);
lean_dec(v_fst_618_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_snd_619_);
v___x_621_ = lean_box(0);
v___y_555_ = v___x_621_;
goto v___jp_554_;
}
else
{
v___y_555_ = v_snd_619_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v___x_551_, v___y_555_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_566_; 
lean_dec(v___y_555_);
lean_dec(v___x_551_);
lean_dec(v___x_550_);
v_val_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_566_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_val_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = ((lean_object*)(l_Lean_findOLean___closed__0));
v___x_562_ = l_Lean_modToFilePath(v_val_557_, v_mod_547_, v___x_561_);
lean_dec(v_val_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
lean_ctor_set(v___x_559_, 0, v___x_562_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_617_; 
lean_dec(v___x_556_);
v___x_567_ = ((lean_object*)(l_Lean_findOLean___closed__0));
lean_inc(v___x_550_);
v___x_568_ = l_Lean_SearchPath_findRootWithExt(v___x_550_, v___x_567_, v_mod_547_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_617_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_617_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_617_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_574_; 
lean_del_object(v___x_571_);
v_val_573_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_a_569_, 1);
v___x_574_ = lean_runtime_deep_copy(v___x_551_);
lean_dec(v___x_551_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_587_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_587_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
lean_inc(v_val_573_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_575_);
lean_ctor_set(v___x_579_, 1, v_val_573_);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___y_555_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_550_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_st_ref_swap(v___x_552_, v___x_581_);
lean_dec(v___x_582_);
v___x_583_ = l_Lean_modToFilePath(v_val_573_, v_mod_547_, v___x_567_);
lean_dec(v_val_573_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_583_);
v___x_585_ = v___x_577_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
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
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_val_573_);
lean_dec(v___y_555_);
lean_dec(v___x_550_);
lean_dec(v_mod_547_);
v_a_588_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_574_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_574_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_a_569_);
lean_dec(v___y_555_);
lean_dec(v_mod_547_);
v___x_596_ = 0;
v___x_597_ = l_Lean_Name_toString(v___x_551_, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_599_ = lean_string_append(v___x_598_, v___x_597_);
v___x_600_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_601_ = lean_string_append(v___x_599_, v___x_600_);
v___x_602_ = lean_string_append(v___x_601_, v___x_597_);
v___x_603_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
v___x_605_ = lean_string_append(v___x_604_, v___x_597_);
lean_dec_ref(v___x_597_);
v___x_606_ = ((lean_object*)(l_Lean_findOLean___closed__4));
v___x_607_ = lean_string_append(v___x_605_, v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_609_ = lean_box(0);
v___x_610_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__1(v___x_550_, v___x_609_);
v___x_611_ = l_String_intercalate(v___x_608_, v___x_610_);
v___x_612_ = lean_string_append(v___x_607_, v___x_611_);
lean_dec_ref(v___x_611_);
v___x_613_ = lean_mk_io_user_error(v___x_612_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 1);
lean_ctor_set(v___x_571_, 0, v___x_613_);
v___x_615_ = v___x_571_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* v_mod_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_findOLean(v_mod_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0(lean_object* v_00_u03b2_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v_x_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___boxed(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_List_lookup___at___00Lean_findOLean_spec__0(v_00_u03b2_629_, v_x_630_, v_x_631_);
lean_dec(v_x_631_);
lean_dec(v_x_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object* v_sp_634_, lean_object* v_mod_635_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_669_; 
v___x_637_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__0));
lean_inc(v_mod_635_);
lean_inc(v_sp_634_);
v___x_638_ = l_Lean_SearchPath_findWithExt(v_sp_634_, v___x_637_, v_mod_635_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_669_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_669_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_669_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
if (lean_obj_tag(v_a_639_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_645_; 
lean_dec(v_mod_635_);
lean_dec(v_sp_634_);
v_val_643_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v_a_639_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_val_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_val_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_a_639_);
v___x_647_ = l_Lean_Name_getRoot(v_mod_635_);
lean_dec(v_mod_635_);
v___x_648_ = 0;
v___x_649_ = l_Lean_Name_toString(v___x_647_, v___x_648_);
v___x_650_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_651_ = lean_string_append(v___x_650_, v___x_649_);
v___x_652_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_653_ = lean_string_append(v___x_651_, v___x_652_);
v___x_654_ = lean_string_append(v___x_653_, v___x_649_);
v___x_655_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
v___x_657_ = lean_string_append(v___x_656_, v___x_649_);
lean_dec_ref(v___x_649_);
v___x_658_ = ((lean_object*)(l_Lean_findLean___closed__0));
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
v___x_660_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_661_ = lean_box(0);
v___x_662_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__1(v_sp_634_, v___x_661_);
v___x_663_ = l_String_intercalate(v___x_660_, v___x_662_);
v___x_664_ = lean_string_append(v___x_659_, v___x_663_);
lean_dec_ref(v___x_663_);
v___x_665_ = lean_mk_io_user_error(v___x_664_);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 1);
lean_ctor_set(v___x_641_, 0, v___x_665_);
v___x_667_ = v___x_641_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object* v_sp_670_, lean_object* v_mod_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_findLean(v_sp_670_, v_mod_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath(){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___y_681_; 
v___x_678_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__0));
v___x_679_ = lean_io_getenv(v___x_678_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_box(0);
v___y_681_ = v___x_711_;
goto v___jp_680_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_713_; 
v_val_712_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_val_712_);
lean_dec_ref_known(v___x_679_, 1);
v___x_713_ = l_System_SearchPath_parse(v_val_712_);
v___y_681_ = v___x_713_;
goto v___jp_680_;
}
v___jp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = l_IO_appDir();
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_702_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_702_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_702_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_702_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_687_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_688_ = l_System_FilePath_join(v_a_683_, v___x_687_);
v___x_689_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__1));
v___x_690_ = l_System_FilePath_join(v___x_688_, v___x_689_);
v___x_691_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__0));
v___x_692_ = l_System_FilePath_join(v___x_690_, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__2));
lean_inc_ref(v___x_692_);
v___x_694_ = l_System_FilePath_join(v___x_692_, v___x_693_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_692_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_694_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_List_appendTR___redArg(v___y_681_, v___x_697_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_698_);
v___x_700_ = v___x_685_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___y_681_);
v_a_703_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_682_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_682_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_getSrcSearchPath();
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_717_) == 0)
{
return v_x_716_;
}
else
{
lean_object* v_head_718_; lean_object* v_tail_719_; lean_object* v___x_720_; 
v_head_718_ = lean_ctor_get(v_x_717_, 0);
lean_inc(v_head_718_);
v_tail_719_ = lean_ctor_get(v_x_717_, 1);
lean_inc(v_tail_719_);
lean_dec_ref_known(v_x_717_, 2);
v___x_720_ = l_Lean_Name_str___override(v_x_716_, v_head_718_);
v_x_716_ = v___x_720_;
v_x_717_ = v_tail_719_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__3(void){
_start:
{
uint32_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = l_System_FilePath_pathSeparator;
v___x_726_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2));
v___x_727_ = lean_string_push(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__4(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_729_ = lean_string_utf8_byte_size(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object* v_fname_730_, lean_object* v_rootDir_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_io_realpath(v_fname_730_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_804_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_804_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_804_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_804_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___y_739_; lean_object* v_rootDir_752_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v_rootDir_775_; 
if (lean_obj_tag(v_rootDir_731_) == 0)
{
lean_object* v___x_793_; 
v___x_793_ = lean_io_current_dir();
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v_rootDir_775_ = v_a_794_;
goto v___jp_774_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_del_object(v___x_736_);
lean_dec(v_a_734_);
v_a_795_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_793_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_val_803_; 
v_val_803_ = lean_ctor_get(v_rootDir_731_, 0);
lean_inc(v_val_803_);
lean_dec_ref_known(v_rootDir_731_, 1);
v_rootDir_775_ = v_val_803_;
goto v___jp_774_;
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_740_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__0));
v___x_741_ = lean_string_append(v___x_740_, v_a_734_);
lean_dec(v_a_734_);
v___x_742_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__1));
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
v___x_744_ = lean_string_append(v___x_743_, v___y_739_);
lean_dec_ref(v___y_739_);
v___x_745_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__2));
v___x_746_ = lean_string_append(v___x_744_, v___x_745_);
v___x_747_ = lean_mk_io_user_error(v___x_746_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 1);
lean_ctor_set(v___x_736_, 0, v___x_747_);
v___x_749_ = v___x_736_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
lean_inc(v_a_734_);
v___x_753_ = l_System_FilePath_normalize(v_a_734_);
v___x_754_ = lean_string_utf8_byte_size(v___x_753_);
v___x_755_ = lean_string_utf8_byte_size(v_rootDir_752_);
v___x_756_ = lean_nat_dec_le(v___x_755_, v___x_754_);
if (v___x_756_ == 0)
{
lean_dec_ref(v___x_753_);
v___y_739_ = v_rootDir_752_;
goto v___jp_738_;
}
else
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_string_memcmp(v___x_753_, v_rootDir_752_, v___x_757_, v___x_757_, v___x_755_);
lean_dec_ref(v___x_753_);
if (v___x_758_ == 0)
{
v___y_739_ = v_rootDir_752_;
goto v___jp_738_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_del_object(v___x_736_);
v___x_759_ = lean_string_length(v_rootDir_752_);
lean_dec_ref(v_rootDir_752_);
v___x_760_ = lean_string_utf8_byte_size(v_a_734_);
lean_inc(v_a_734_);
v___x_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_761_, 0, v_a_734_);
lean_ctor_set(v___x_761_, 1, v___x_757_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
v___x_762_ = l_String_Slice_Pos_nextn(v___x_761_, v___x_757_, v___x_759_);
lean_dec_ref_known(v___x_761_, 3);
v___x_763_ = lean_string_utf8_extract_fast(v_a_734_, v___x_762_, v___x_760_);
lean_dec(v___x_762_);
lean_dec(v_a_734_);
v___x_764_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2));
v___x_765_ = l_System_FilePath_withExtension(v___x_763_, v___x_764_);
v___x_766_ = lean_box(0);
v___x_767_ = l_System_FilePath_components(v___x_765_);
v___x_768_ = l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(v___x_766_, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
}
v___jp_770_:
{
lean_object* v___x_773_; 
v___x_773_ = lean_string_append(v___y_771_, v___y_772_);
v_rootDir_752_ = v___x_773_;
goto v___jp_751_;
}
v___jp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_realPathNormalized(v_rootDir_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_779_ = lean_string_utf8_byte_size(v_a_777_);
v___x_780_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__4, &l_Lean_moduleNameOfFileName___closed__4_once, _init_l_Lean_moduleNameOfFileName___closed__4);
v___x_781_ = lean_nat_dec_le(v___x_780_, v___x_779_);
if (v___x_781_ == 0)
{
v___y_771_ = v_a_777_;
v___y_772_ = v___x_778_;
goto v___jp_770_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_nat_sub(v___x_779_, v___x_780_);
v___x_784_ = lean_string_memcmp(v_a_777_, v___x_778_, v___x_783_, v___x_782_, v___x_780_);
lean_dec(v___x_783_);
if (v___x_784_ == 0)
{
v___y_771_ = v_a_777_;
v___y_772_ = v___x_778_;
goto v___jp_770_;
}
else
{
v_rootDir_752_ = v_a_777_;
goto v___jp_751_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_del_object(v___x_736_);
lean_dec(v_a_734_);
v_a_785_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_776_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_776_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_rootDir_731_);
v_a_805_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_733_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_733_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object* v_fname_813_, lean_object* v_rootDir_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_moduleNameOfFileName(v_fname_813_, v_rootDir_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object* v_fname_820_, lean_object* v_as_x27_821_, lean_object* v_b_822_){
_start:
{
if (lean_obj_tag(v_as_x27_821_) == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v_fname_820_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v_b_822_);
return v___x_824_;
}
else
{
lean_object* v_head_825_; lean_object* v_tail_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v_b_822_);
v_head_825_ = lean_ctor_get(v_as_x27_821_, 0);
v_tail_826_ = lean_ctor_get(v_as_x27_821_, 1);
v___x_827_ = lean_box(0);
v___x_828_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
lean_inc(v_head_825_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_head_825_);
lean_inc_ref(v_fname_820_);
v___x_830_ = l_Lean_moduleNameOfFileName(v_fname_820_, v___x_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v_fname_820_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_841_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v_a_831_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_827_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_dec_ref_known(v___x_830_, 1);
v_as_x27_821_ = v_tail_826_;
v_b_822_ = v___x_828_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object* v_fname_843_, lean_object* v_as_x27_844_, lean_object* v_b_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_843_, v_as_x27_844_, v_b_845_);
lean_dec(v_as_x27_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object* v_fname_848_, lean_object* v_rootDirs_849_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_866_; 
v___x_851_ = lean_box(0);
v___x_852_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
v___x_853_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_848_, v_rootDirs_849_, v___x_852_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_866_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_866_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; 
v_fst_858_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_fst_858_);
lean_dec(v_a_854_);
if (lean_obj_tag(v_fst_858_) == 0)
{
lean_object* v___x_860_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_851_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_851_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v_val_862_; lean_object* v___x_864_; 
v_val_862_ = lean_ctor_get(v_fst_858_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_fst_858_, 1);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v_val_862_);
v___x_864_ = v___x_856_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_val_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object* v_fname_867_, lean_object* v_rootDirs_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_searchModuleNameOfFileName(v_fname_867_, v_rootDirs_868_);
lean_dec(v_rootDirs_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object* v_fname_871_, lean_object* v_as_872_, lean_object* v_as_x27_873_, lean_object* v_b_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_871_, v_as_x27_873_, v_b_874_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object* v_fname_878_, lean_object* v_as_879_, lean_object* v_as_x27_880_, lean_object* v_b_881_, lean_object* v_a_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(v_fname_878_, v_as_879_, v_as_x27_880_, v_b_881_, v_a_882_);
lean_dec(v_as_x27_880_);
lean_dec(v_as_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object* v_lean_895_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_findSysroot___closed__0));
v___x_898_ = lean_io_getenv(v___x_897_);
if (lean_obj_tag(v___x_898_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_lean_895_);
v_val_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_val_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 0);
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_val_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v___x_898_);
v___x_907_ = ((lean_object*)(l_Lean_findSysroot___closed__1));
v___x_908_ = ((lean_object*)(l_Lean_findSysroot___closed__3));
v___x_909_ = lean_box(0);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = ((lean_object*)(l_Lean_findSysroot___closed__4));
v___x_912_ = 1;
v___x_913_ = 0;
v___x_914_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_914_, 0, v___x_907_);
lean_ctor_set(v___x_914_, 1, v_lean_895_);
lean_ctor_set(v___x_914_, 2, v___x_908_);
lean_ctor_set(v___x_914_, 3, v___x_909_);
lean_ctor_set(v___x_914_, 4, v___x_911_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*5, v___x_912_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*5 + 1, v___x_913_);
v___x_915_ = l_IO_Process_run(v___x_914_, v___x_909_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_930_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_930_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_str_923_; lean_object* v_startInclusive_924_; lean_object* v_endExclusive_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_920_ = lean_string_utf8_byte_size(v_a_916_);
v___x_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_921_, 0, v_a_916_);
lean_ctor_set(v___x_921_, 1, v___x_910_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
v___x_922_ = l_String_Slice_trimAscii(v___x_921_);
v_str_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc_ref(v_str_923_);
v_startInclusive_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_startInclusive_924_);
v_endExclusive_925_ = lean_ctor_get(v___x_922_, 2);
lean_inc(v_endExclusive_925_);
lean_dec_ref(v___x_922_);
v___x_926_ = lean_string_utf8_extract_fast(v_str_923_, v_startInclusive_924_, v_endExclusive_925_);
lean_dec(v_endExclusive_925_);
lean_dec(v_startInclusive_924_);
lean_dec_ref(v_str_923_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_926_);
v___x_928_ = v___x_918_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_915_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_915_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object* v_lean_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_findSysroot(v_lean_939_);
return v_res_941_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
res = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_1261712593____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Util_Path_0__Lean_oleanRootCacheRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Util_Path_0__Lean_oleanRootCacheRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Path(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Path(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Path(builtin);
}
#ifdef __cplusplus
}
#endif
