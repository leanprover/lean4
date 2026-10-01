// Lean compiler output
// Module: Lean.Util.Path
// Imports: public import Init.System.IO import Init.Control.Do import Init.Data.ToString.Name import Init.Data.String.TakeDrop import Init.Data.List.Monadic import Init.Data.Option.BasicAux import Init.Data.ToString.Macro import Init.Data.String.Length
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
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__0;
static const lean_string_object l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value;
static const lean_ctor_object l_Lean_forEachModuleInDir___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value)}};
static const lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__2_value;
static const lean_string_object l_Lean_forEachModuleInDir___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_forEachModuleInDir___redArg___lam__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___f_24_; 
v___x_23_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_24_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_24_, 0, v___x_23_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object* v_toPure_29_, lean_object* v_f_30_, lean_object* v_toBind_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v___f_34_, lean_object* v_____do__lift_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___f_38_; size_t v_sz_39_; size_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_36_ = lean_box(0);
lean_inc(v_toPure_29_);
v___f_37_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__1), 3, 2);
lean_closure_set(v___f_37_, 0, v___x_36_);
lean_closure_set(v___f_37_, 1, v_toPure_29_);
lean_inc_ref(v_inst_32_);
lean_inc_ref(v___f_37_);
lean_inc(v_toBind_31_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__5), 11, 8);
lean_closure_set(v___f_38_, 0, v___x_36_);
lean_closure_set(v___f_38_, 1, v_toPure_29_);
lean_closure_set(v___f_38_, 2, v_f_30_);
lean_closure_set(v___f_38_, 3, v_toBind_31_);
lean_closure_set(v___f_38_, 4, v___f_37_);
lean_closure_set(v___f_38_, 5, v_inst_32_);
lean_closure_set(v___f_38_, 6, v_inst_33_);
lean_closure_set(v___f_38_, 7, v___f_37_);
v_sz_39_ = lean_array_size(v_____do__lift_35_);
v___x_40_ = ((size_t)0ULL);
v___x_41_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_32_, v_____do__lift_35_, v___f_38_, v_sz_39_, v___x_40_, v___x_36_);
v___x_42_ = lean_apply_4(v_toBind_31_, lean_box(0), lean_box(0), v___x_41_, v___f_34_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_dir_45_, lean_object* v_f_46_){
_start:
{
lean_object* v_toApplicative_47_; lean_object* v_toBind_48_; lean_object* v_toPure_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_toApplicative_47_ = lean_ctor_get(v_inst_43_, 0);
v_toBind_48_ = lean_ctor_get(v_inst_43_, 1);
lean_inc_n(v_toBind_48_, 2);
v_toPure_49_ = lean_ctor_get(v_toApplicative_47_, 1);
lean_inc_n(v_toPure_49_, 2);
v___x_50_ = lean_alloc_closure((void*)(l_System_FilePath_readDir___boxed), 2, 1);
lean_closure_set(v___x_50_, 0, v_dir_45_);
lean_inc(v_inst_44_);
v___x_51_ = lean_apply_2(v_inst_44_, lean_box(0), v___x_50_);
v___f_52_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__0), 2, 1);
lean_closure_set(v___f_52_, 0, v_toPure_49_);
v___f_53_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__6), 7, 6);
lean_closure_set(v___f_53_, 0, v_toPure_49_);
lean_closure_set(v___f_53_, 1, v_f_46_);
lean_closure_set(v___f_53_, 2, v_toBind_48_);
lean_closure_set(v___f_53_, 3, v_inst_43_);
lean_closure_set(v___f_53_, 4, v_inst_44_);
lean_closure_set(v___f_53_, 5, v___f_52_);
v___x_54_ = lean_apply_4(v_toBind_48_, lean_box(0), lean_box(0), v___x_51_, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object* v___x_55_, lean_object* v___x_56_, lean_object* v_toPure_57_, lean_object* v_a_58_, lean_object* v_f_59_, lean_object* v_toBind_60_, lean_object* v___f_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v___f_64_, uint8_t v_____do__lift_65_){
_start:
{
if (v_____do__lift_65_ == 0)
{
lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
lean_dec(v___f_64_);
lean_dec(v_inst_63_);
lean_dec_ref(v_inst_62_);
v___f_66_ = lean_obj_once(&l_Lean_forEachModuleInDir___redArg___lam__4___closed__0, &l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_once, _init_l_Lean_forEachModuleInDir___redArg___lam__4___closed__0);
v___x_67_ = l_System_FilePath_extension(v___x_55_);
v___x_68_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2));
v___x_69_ = l_instBEqOption_beq___redArg(v___f_66_, v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v___f_61_);
lean_dec(v_toBind_60_);
lean_dec(v_f_59_);
lean_dec_ref(v_a_58_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_56_);
v___x_71_ = lean_apply_2(v_toPure_57_, lean_box(0), v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_fileName_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_toPure_57_);
v_fileName_72_ = lean_ctor_get(v_a_58_, 1);
lean_inc_ref(v_fileName_72_);
lean_dec_ref(v_a_58_);
v___x_73_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_74_ = l_System_FilePath_withExtension(v_fileName_72_, v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Lean_Name_str___override(v___x_75_, v___x_74_);
v___x_77_ = lean_apply_1(v_f_59_, v___x_76_);
v___x_78_ = lean_apply_4(v_toBind_60_, lean_box(0), lean_box(0), v___x_77_, v___f_61_);
return v___x_78_;
}
}
else
{
lean_object* v_fileName_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v___f_61_);
lean_dec(v_toPure_57_);
v_fileName_79_ = lean_ctor_get(v_a_58_, 1);
lean_inc_ref(v_fileName_79_);
lean_dec_ref(v_a_58_);
v___x_80_ = lean_box(0);
v___x_81_ = l_Lean_Name_str___override(v___x_80_, v_fileName_79_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__2), 3, 2);
lean_closure_set(v___f_82_, 0, v___x_81_);
lean_closure_set(v___f_82_, 1, v_f_59_);
v___x_83_ = l_Lean_forEachModuleInDir___redArg(v_inst_62_, v_inst_63_, v___x_55_, v___f_82_);
v___x_84_ = lean_apply_4(v_toBind_60_, lean_box(0), lean_box(0), v___x_83_, v___f_64_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___boxed(lean_object* v___x_85_, lean_object* v___x_86_, lean_object* v_toPure_87_, lean_object* v_a_88_, lean_object* v_f_89_, lean_object* v_toBind_90_, lean_object* v___f_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v___f_94_, lean_object* v_____do__lift_95_){
_start:
{
uint8_t v_____do__lift_385__boxed_96_; lean_object* v_res_97_; 
v_____do__lift_385__boxed_96_ = lean_unbox(v_____do__lift_95_);
v_res_97_ = l_Lean_forEachModuleInDir___redArg___lam__4(v___x_85_, v___x_86_, v_toPure_87_, v_a_88_, v_f_89_, v_toBind_90_, v___f_91_, v_inst_92_, v_inst_93_, v___f_94_, v_____do__lift_385__boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object* v___x_98_, lean_object* v_toPure_99_, lean_object* v_f_100_, lean_object* v_toBind_101_, lean_object* v___f_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v___f_105_, lean_object* v_a_106_, lean_object* v_x_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
lean_inc_ref(v_a_106_);
v___x_109_ = l_IO_FS_DirEntry_path(v_a_106_);
lean_inc_ref(v___x_109_);
v___f_110_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_110_, 0, v___x_109_);
lean_inc(v_inst_104_);
lean_inc(v_toBind_101_);
v___f_111_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_111_, 0, v___x_109_);
lean_closure_set(v___f_111_, 1, v___x_98_);
lean_closure_set(v___f_111_, 2, v_toPure_99_);
lean_closure_set(v___f_111_, 3, v_a_106_);
lean_closure_set(v___f_111_, 4, v_f_100_);
lean_closure_set(v___f_111_, 5, v_toBind_101_);
lean_closure_set(v___f_111_, 6, v___f_102_);
lean_closure_set(v___f_111_, 7, v_inst_103_);
lean_closure_set(v___f_111_, 8, v_inst_104_);
lean_closure_set(v___f_111_, 9, v___f_105_);
v___x_112_ = lean_apply_2(v_inst_104_, lean_box(0), v___f_110_);
v___x_113_ = lean_apply_4(v_toBind_101_, lean_box(0), lean_box(0), v___x_112_, v___f_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object* v_m_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_dir_117_, lean_object* v_f_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_forEachModuleInDir___redArg(v_inst_115_, v_inst_116_, v_dir_117_, v_f_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object* v_p_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_io_realpath(v_p_120_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = l_System_FilePath_normalize(v_a_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized___boxed(lean_object* v_p_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_realPathNormalized(v_p_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object* v_msg_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_137_ = lean_panic_fn_borrowed(v___x_136_, v_msg_135_);
return v___x_137_;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2));
v___x_142_ = lean_unsigned_to_nat(20u);
v___x_143_ = lean_unsigned_to_nat(51u);
v___x_144_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1));
v___x_145_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0));
v___x_146_ = l_mkPanicMessageWithDecl(v___x_145_, v___x_144_, v___x_143_, v___x_142_, v___x_141_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object* v_base_147_, lean_object* v_a_148_){
_start:
{
switch(lean_obj_tag(v_a_148_))
{
case 0:
{
lean_inc_ref(v_base_147_);
return v_base_147_;
}
case 1:
{
lean_object* v_pre_149_; lean_object* v_str_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_pre_149_ = lean_ctor_get(v_a_148_, 0);
lean_inc(v_pre_149_);
v_str_150_ = lean_ctor_get(v_a_148_, 1);
lean_inc_ref(v_str_150_);
lean_dec_ref_known(v_a_148_, 2);
v___x_151_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_147_, v_pre_149_);
v___x_152_ = l_System_FilePath_join(v___x_151_, v_str_150_);
return v___x_152_;
}
default: 
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref_known(v_a_148_, 2);
v___x_153_ = lean_obj_once(&l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3, &l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3_once, _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3);
v___x_154_ = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(v___x_153_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object* v_base_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_155_, v_a_156_);
lean_dec_ref(v_base_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object* v_base_158_, lean_object* v_mod_159_, lean_object* v_ext_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_158_, v_mod_159_);
v___x_162_ = l_System_FilePath_addExtension(v___x_161_, v_ext_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object* v_base_163_, lean_object* v_mod_164_, lean_object* v_ext_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_modToFilePath(v_base_163_, v_mod_164_, v_ext_165_);
lean_dec_ref(v_ext_165_);
lean_dec_ref(v_base_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(lean_object* v_pkg_167_, lean_object* v_ext_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v_pkg_167_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_head_173_; lean_object* v_tail_174_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_head_173_ = lean_ctor_get(v_x_169_, 0);
lean_inc_n(v_head_173_, 2);
v_tail_174_ = lean_ctor_get(v_x_169_, 1);
lean_inc(v_tail_174_);
lean_dec_ref_known(v_x_169_, 2);
lean_inc_ref(v_pkg_167_);
v___x_178_ = l_System_FilePath_join(v_head_173_, v_pkg_167_);
v___x_179_ = l_System_FilePath_isDir(v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = l_System_FilePath_addExtension(v___x_178_, v_ext_168_);
v___x_181_ = l_System_FilePath_pathExists(v___x_180_);
lean_dec_ref(v___x_180_);
if (v___x_181_ == 0)
{
lean_dec(v_head_173_);
v_x_169_ = v_tail_174_;
goto _start;
}
else
{
lean_dec(v_tail_174_);
lean_dec_ref(v_pkg_167_);
goto v___jp_175_;
}
}
else
{
lean_dec_ref(v___x_178_);
lean_dec(v_tail_174_);
lean_dec_ref(v_pkg_167_);
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_head_173_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0___boxed(lean_object* v_pkg_183_, lean_object* v_ext_184_, lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(v_pkg_183_, v_ext_184_, v_x_185_);
lean_dec_ref(v_ext_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt(lean_object* v_sp_188_, lean_object* v_ext_189_, lean_object* v_mod_190_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v_pkg_194_; lean_object* v___x_195_; 
v___x_192_ = l_Lean_Name_getRoot(v_mod_190_);
v___x_193_ = 0;
v_pkg_194_ = l_Lean_Name_toString(v___x_192_, v___x_193_);
v___x_195_ = l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(v_pkg_194_, v_ext_189_, v_sp_188_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt___boxed(lean_object* v_sp_196_, lean_object* v_ext_197_, lean_object* v_mod_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_SearchPath_findRootWithExt(v_sp_196_, v_ext_197_, v_mod_198_);
lean_dec(v_mod_198_);
lean_dec_ref(v_ext_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* v_sp_201_, lean_object* v_ext_202_, lean_object* v_mod_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_a_206_; 
v___x_205_ = l_Lean_SearchPath_findRootWithExt(v_sp_201_, v_ext_202_, v_mod_203_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
if (lean_obj_tag(v_a_206_) == 0)
{
lean_dec(v_mod_203_);
return v___x_205_;
}
else
{
lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_222_; 
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v___x_205_, 0);
lean_dec(v_unused_223_);
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_222_;
goto v_resetjp_207_;
}
else
{
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_222_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_val_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_221_; 
v_val_210_ = lean_ctor_get(v_a_206_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_221_ == 0)
{
v___x_212_ = v_a_206_;
v_isShared_213_ = v_isSharedCheck_221_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_val_210_);
lean_dec(v_a_206_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_221_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = l_Lean_modToFilePath(v_val_210_, v_mod_203_, v_ext_202_);
lean_dec(v_val_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_216_);
v___x_218_ = v___x_208_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* v_sp_224_, lean_object* v_ext_225_, lean_object* v_mod_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_SearchPath_findWithExt(v_sp_224_, v_ext_225_, v_mod_226_);
lean_dec_ref(v_ext_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* v_sp_229_, lean_object* v_ext_230_, lean_object* v_mod_231_){
_start:
{
lean_object* v___x_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_246_; 
v___x_236_ = l_Lean_SearchPath_findWithExt(v_sp_229_, v_ext_230_, v_mod_231_);
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_246_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_246_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_246_;
goto v_resetjp_238_;
}
v___jp_233_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
v_resetjp_238_:
{
if (lean_obj_tag(v_a_237_) == 1)
{
lean_object* v_val_241_; uint8_t v___x_242_; 
v_val_241_ = lean_ctor_get(v_a_237_, 0);
v___x_242_ = l_System_FilePath_pathExists(v_val_241_);
if (v___x_242_ == 0)
{
lean_dec_ref_known(v_a_237_, 1);
lean_del_object(v___x_239_);
goto v___jp_233_;
}
else
{
lean_object* v___x_244_; 
if (v_isShared_240_ == 0)
{
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_237_);
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
lean_del_object(v___x_239_);
lean_dec(v_a_237_);
goto v___jp_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* v_sp_247_, lean_object* v_ext_248_, lean_object* v_mod_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_SearchPath_findModuleWithExt(v_sp_247_, v_ext_248_, v_mod_249_);
lean_dec_ref(v_ext_248_);
return v_res_251_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
if (lean_obj_tag(v_x_253_) == 0)
{
uint8_t v___x_254_; 
v___x_254_ = 1;
return v___x_254_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
}
else
{
if (lean_obj_tag(v_x_253_) == 0)
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
else
{
lean_object* v_val_257_; lean_object* v_val_258_; uint8_t v___x_259_; 
v_val_257_ = lean_ctor_get(v_x_252_, 0);
v_val_258_ = lean_ctor_get(v_x_253_, 0);
v___x_259_ = lean_string_dec_eq(v_val_257_, v_val_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v_x_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_x_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object* v_ext_264_, lean_object* v_as_265_, size_t v_i_266_, size_t v_stop_267_, lean_object* v_b_268_){
_start:
{
lean_object* v___y_270_; uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_eq(v_i_266_, v_stop_267_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_275_ = lean_array_uget_borrowed(v_as_265_, v_i_266_);
lean_inc(v___x_275_);
v___x_276_ = l_System_FilePath_extension(v___x_275_);
lean_inc_ref(v_ext_264_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_ext_264_);
v___x_278_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v___x_276_, v___x_277_);
lean_dec_ref_known(v___x_277_, 1);
lean_dec(v___x_276_);
if (v___x_278_ == 0)
{
v___y_270_ = v_b_268_;
goto v___jp_269_;
}
else
{
lean_object* v___x_279_; 
lean_inc(v___x_275_);
v___x_279_ = lean_array_push(v_b_268_, v___x_275_);
v___y_270_ = v___x_279_;
goto v___jp_269_;
}
}
else
{
lean_dec_ref(v_ext_264_);
return v_b_268_;
}
v___jp_269_:
{
size_t v___x_271_; size_t v___x_272_; 
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_266_, v___x_271_);
v_i_266_ = v___x_272_;
v_b_268_ = v___y_270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object* v_ext_280_, lean_object* v_as_281_, lean_object* v_i_282_, lean_object* v_stop_283_, lean_object* v_b_284_){
_start:
{
size_t v_i_boxed_285_; size_t v_stop_boxed_286_; lean_object* v_res_287_; 
v_i_boxed_285_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_stop_boxed_286_ = lean_unbox_usize(v_stop_283_);
lean_dec(v_stop_283_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_280_, v_as_281_, v_i_boxed_285_, v_stop_boxed_286_, v_b_284_);
lean_dec_ref(v_as_281_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t v_val_288_, lean_object* v_x_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_box(v_val_288_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object* v_val_293_, lean_object* v_x_294_, lean_object* v___y_295_){
_start:
{
uint8_t v_val_901__boxed_296_; lean_object* v_res_297_; 
v_val_901__boxed_296_ = lean_unbox(v_val_293_);
v_res_297_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(v_val_901__boxed_296_, v_x_294_);
lean_dec_ref(v_x_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object* v_ext_300_, lean_object* v_as_x27_301_, lean_object* v_b_302_){
_start:
{
if (lean_obj_tag(v_as_x27_301_) == 0)
{
lean_object* v___x_304_; 
lean_dec_ref(v_ext_300_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_b_302_);
return v___x_304_;
}
else
{
lean_object* v_head_305_; lean_object* v_tail_306_; uint8_t v___x_307_; 
v_head_305_ = lean_ctor_get(v_as_x27_301_, 0);
v_tail_306_ = lean_ctor_get(v_as_x27_301_, 1);
v___x_307_ = l_System_FilePath_isDir(v_head_305_);
if (v___x_307_ == 0)
{
v_as_x27_301_ = v_tail_306_;
goto _start;
}
else
{
lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(v___x_307_);
v___f_310_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_310_, 0, v___x_309_);
lean_inc(v_head_305_);
v___x_311_ = l_System_FilePath_walkDir(v_head_305_, v___f_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___y_314_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_array_get_size(v_a_312_);
v___x_319_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_320_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_320_ == 0)
{
lean_dec(v_a_312_);
v___y_314_ = v___x_319_;
goto v___jp_313_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = lean_nat_dec_le(v___x_318_, v___x_318_);
if (v___x_321_ == 0)
{
if (v___x_320_ == 0)
{
lean_dec(v_a_312_);
v___y_314_ = v___x_319_;
goto v___jp_313_;
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_318_);
lean_inc_ref(v_ext_300_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_300_, v_a_312_, v___x_322_, v___x_323_, v___x_319_);
lean_dec(v_a_312_);
v___y_314_ = v___x_324_;
goto v___jp_313_;
}
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_318_);
lean_inc_ref(v_ext_300_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_300_, v_a_312_, v___x_325_, v___x_326_, v___x_319_);
lean_dec(v_a_312_);
v___y_314_ = v___x_327_;
goto v___jp_313_;
}
}
v___jp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = l_Array_append___redArg(v_b_302_, v___y_314_);
lean_dec_ref(v___y_314_);
v_as_x27_301_ = v_tail_306_;
v_b_302_ = v___x_315_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_302_);
lean_dec_ref(v_ext_300_);
return v___x_311_;
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
v___x_401_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_));
v___x_496_ = lean_st_mk_ref(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2____boxed(lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_();
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
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___y_555_; lean_object* v_fst_604_; lean_object* v_snd_605_; uint8_t v___x_606_; 
v___x_549_ = l_Lean_searchPathRef;
v___x_550_ = lean_st_ref_get(v___x_549_);
v___x_551_ = l_Lean_Name_getRoot(v_mod_547_);
v___x_552_ = l___private_Lean_Util_Path_0__Lean_oleanRootCacheRef;
v___x_553_ = lean_st_ref_get(v___x_552_);
v_fst_604_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_605_);
lean_dec(v___x_553_);
v___x_606_ = l_List_beq___at___00Lean_findOLean_spec__2(v_fst_604_, v___x_550_);
lean_dec(v_fst_604_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_dec(v_snd_605_);
v___x_607_ = lean_box(0);
v___y_555_ = v___x_607_;
goto v___jp_554_;
}
else
{
v___y_555_ = v_snd_605_;
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
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_603_; 
lean_dec(v___x_556_);
v___x_567_ = ((lean_object*)(l_Lean_findOLean___closed__0));
lean_inc(v___x_550_);
v___x_568_ = l_Lean_SearchPath_findRootWithExt(v___x_550_, v___x_567_, v_mod_547_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_603_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_603_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_603_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v_val_573_ = lean_ctor_get(v_a_569_, 0);
lean_inc_n(v_val_573_, 2);
lean_dec_ref_known(v_a_569_, 1);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_551_);
lean_ctor_set(v___x_574_, 1, v_val_573_);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___y_555_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_550_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_st_ref_swap(v___x_552_, v___x_576_);
lean_dec(v___x_577_);
v___x_578_ = l_Lean_modToFilePath(v_val_573_, v_mod_547_, v___x_567_);
lean_dec(v_val_573_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_578_);
v___x_580_ = v___x_571_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
lean_dec(v_a_569_);
lean_dec(v___y_555_);
lean_dec(v_mod_547_);
v___x_582_ = 0;
v___x_583_ = l_Lean_Name_toString(v___x_551_, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_585_ = lean_string_append(v___x_584_, v___x_583_);
v___x_586_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
v___x_588_ = lean_string_append(v___x_587_, v___x_583_);
v___x_589_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
v___x_591_ = lean_string_append(v___x_590_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_592_ = ((lean_object*)(l_Lean_findOLean___closed__4));
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_595_ = lean_box(0);
v___x_596_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__1(v___x_550_, v___x_595_);
v___x_597_ = l_String_intercalate(v___x_594_, v___x_596_);
v___x_598_ = lean_string_append(v___x_593_, v___x_597_);
lean_dec_ref(v___x_597_);
v___x_599_ = lean_mk_io_user_error(v___x_598_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 1);
lean_ctor_set(v___x_571_, 0, v___x_599_);
v___x_601_ = v___x_571_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* v_mod_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_findOLean(v_mod_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___boxed(lean_object* v_00_u03b2_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_List_lookup___at___00Lean_findOLean_spec__0(v_00_u03b2_615_, v_x_616_, v_x_617_);
lean_dec(v_x_617_);
lean_dec(v_x_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object* v_sp_620_, lean_object* v_mod_621_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_655_; 
v___x_623_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
lean_inc(v_mod_621_);
lean_inc(v_sp_620_);
v___x_624_ = l_Lean_SearchPath_findWithExt(v_sp_620_, v___x_623_, v_mod_621_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_655_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
if (lean_obj_tag(v_a_625_) == 1)
{
lean_object* v_val_629_; lean_object* v___x_631_; 
lean_dec(v_mod_621_);
lean_dec(v_sp_620_);
v_val_629_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v_a_625_, 1);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v_val_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_val_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
lean_dec(v_a_625_);
v___x_633_ = l_Lean_Name_getRoot(v_mod_621_);
lean_dec(v_mod_621_);
v___x_634_ = 0;
v___x_635_ = l_Lean_Name_toString(v___x_633_, v___x_634_);
v___x_636_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_637_ = lean_string_append(v___x_636_, v___x_635_);
v___x_638_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___x_640_ = lean_string_append(v___x_639_, v___x_635_);
v___x_641_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = lean_string_append(v___x_642_, v___x_635_);
lean_dec_ref(v___x_635_);
v___x_644_ = ((lean_object*)(l_Lean_findLean___closed__0));
v___x_645_ = lean_string_append(v___x_643_, v___x_644_);
v___x_646_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_647_ = lean_box(0);
v___x_648_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__1(v_sp_620_, v___x_647_);
v___x_649_ = l_String_intercalate(v___x_646_, v___x_648_);
v___x_650_ = lean_string_append(v___x_645_, v___x_649_);
lean_dec_ref(v___x_649_);
v___x_651_ = lean_mk_io_user_error(v___x_650_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 1);
lean_ctor_set(v___x_627_, 0, v___x_651_);
v___x_653_ = v___x_627_;
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
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object* v_sp_656_, lean_object* v_mod_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_findLean(v_sp_656_, v_mod_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath(){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___y_667_; 
v___x_664_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__0));
v___x_665_ = lean_io_getenv(v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
v___y_667_ = v___x_697_;
goto v___jp_666_;
}
else
{
lean_object* v_val_698_; lean_object* v___x_699_; 
v_val_698_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v___x_665_, 1);
v___x_699_ = l_System_SearchPath_parse(v_val_698_);
v___y_667_ = v___x_699_;
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = l_IO_appDir();
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_688_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_688_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_688_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_688_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_673_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_674_ = l_System_FilePath_join(v_a_669_, v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__1));
v___x_676_ = l_System_FilePath_join(v___x_674_, v___x_675_);
v___x_677_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
v___x_678_ = l_System_FilePath_join(v___x_676_, v___x_677_);
v___x_679_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__2));
lean_inc_ref(v___x_678_);
v___x_680_ = l_System_FilePath_join(v___x_678_, v___x_679_);
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_678_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_List_appendTR___redArg(v___y_667_, v___x_683_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_684_);
v___x_686_ = v___x_671_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___y_667_);
v_a_689_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_668_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_668_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_getSrcSearchPath();
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
return v_x_702_;
}
else
{
lean_object* v_head_704_; lean_object* v_tail_705_; lean_object* v___x_706_; 
v_head_704_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_head_704_);
v_tail_705_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_tail_705_);
lean_dec_ref_known(v_x_703_, 2);
v___x_706_ = l_Lean_Name_str___override(v_x_702_, v_head_704_);
v_x_702_ = v___x_706_;
v_x_703_ = v_tail_705_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__3(void){
_start:
{
uint32_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = l_System_FilePath_pathSeparator;
v___x_712_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_713_ = lean_string_push(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__4(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_715_ = lean_string_utf8_byte_size(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object* v_fname_716_, lean_object* v_rootDir_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_io_realpath(v_fname_716_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_790_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_790_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_790_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_790_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___y_725_; lean_object* v_rootDir_738_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v_rootDir_761_; 
if (lean_obj_tag(v_rootDir_717_) == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_io_current_dir();
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v_rootDir_761_ = v_a_780_;
goto v___jp_760_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_del_object(v___x_722_);
lean_dec(v_a_720_);
v_a_781_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_779_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_val_789_; 
v_val_789_ = lean_ctor_get(v_rootDir_717_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_rootDir_717_, 1);
v_rootDir_761_ = v_val_789_;
goto v___jp_760_;
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_726_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__0));
v___x_727_ = lean_string_append(v___x_726_, v_a_720_);
lean_dec(v_a_720_);
v___x_728_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__1));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = lean_string_append(v___x_729_, v___y_725_);
lean_dec_ref(v___y_725_);
v___x_731_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__2));
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
v___x_733_ = lean_mk_io_user_error(v___x_732_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
lean_ctor_set(v___x_722_, 0, v___x_733_);
v___x_735_ = v___x_722_;
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
v___jp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
lean_inc(v_a_720_);
v___x_739_ = l_System_FilePath_normalize(v_a_720_);
v___x_740_ = lean_string_utf8_byte_size(v___x_739_);
v___x_741_ = lean_string_utf8_byte_size(v_rootDir_738_);
v___x_742_ = lean_nat_dec_le(v___x_741_, v___x_740_);
if (v___x_742_ == 0)
{
lean_dec_ref(v___x_739_);
v___y_725_ = v_rootDir_738_;
goto v___jp_724_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_string_memcmp(v___x_739_, v_rootDir_738_, v___x_743_, v___x_743_, v___x_741_);
lean_dec_ref(v___x_739_);
if (v___x_744_ == 0)
{
v___y_725_ = v_rootDir_738_;
goto v___jp_724_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_722_);
v___x_745_ = lean_string_length(v_rootDir_738_);
lean_dec_ref(v_rootDir_738_);
v___x_746_ = lean_string_utf8_byte_size(v_a_720_);
lean_inc(v_a_720_);
v___x_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_747_, 0, v_a_720_);
lean_ctor_set(v___x_747_, 1, v___x_743_);
lean_ctor_set(v___x_747_, 2, v___x_746_);
v___x_748_ = l_String_Slice_Pos_nextn(v___x_747_, v___x_743_, v___x_745_);
lean_dec_ref_known(v___x_747_, 3);
v___x_749_ = lean_string_utf8_extract_fast(v_a_720_, v___x_748_, v___x_746_);
lean_dec(v___x_748_);
lean_dec(v_a_720_);
v___x_750_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_751_ = l_System_FilePath_withExtension(v___x_749_, v___x_750_);
v___x_752_ = lean_box(0);
v___x_753_ = l_System_FilePath_components(v___x_751_);
v___x_754_ = l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(v___x_752_, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
v___jp_756_:
{
lean_object* v___x_759_; 
v___x_759_ = lean_string_append(v___y_758_, v___y_757_);
v_rootDir_738_ = v___x_759_;
goto v___jp_737_;
}
v___jp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_realPathNormalized(v_rootDir_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_765_ = lean_string_utf8_byte_size(v_a_763_);
v___x_766_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__4, &l_Lean_moduleNameOfFileName___closed__4_once, _init_l_Lean_moduleNameOfFileName___closed__4);
v___x_767_ = lean_nat_dec_le(v___x_766_, v___x_765_);
if (v___x_767_ == 0)
{
v___y_757_ = v___x_764_;
v___y_758_ = v_a_763_;
goto v___jp_756_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_nat_sub(v___x_765_, v___x_766_);
v___x_770_ = lean_string_memcmp(v_a_763_, v___x_764_, v___x_769_, v___x_768_, v___x_766_);
lean_dec(v___x_769_);
if (v___x_770_ == 0)
{
v___y_757_ = v___x_764_;
v___y_758_ = v_a_763_;
goto v___jp_756_;
}
else
{
v_rootDir_738_ = v_a_763_;
goto v___jp_737_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_722_);
lean_dec(v_a_720_);
v_a_771_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_762_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_762_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_rootDir_717_);
v_a_791_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_719_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_719_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object* v_fname_799_, lean_object* v_rootDir_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_moduleNameOfFileName(v_fname_799_, v_rootDir_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object* v_fname_806_, lean_object* v_as_x27_807_, lean_object* v_b_808_){
_start:
{
if (lean_obj_tag(v_as_x27_807_) == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v_fname_806_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_b_808_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref(v_b_808_);
v_head_811_ = lean_ctor_get(v_as_x27_807_, 0);
v_tail_812_ = lean_ctor_get(v_as_x27_807_, 1);
v___x_813_ = lean_box(0);
v___x_814_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
lean_inc(v_head_811_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_head_811_);
lean_inc_ref(v_fname_806_);
v___x_816_ = l_Lean_moduleNameOfFileName(v_fname_806_, v___x_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_fname_806_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_827_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_827_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_a_817_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_813_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_dec_ref_known(v___x_816_, 1);
v_as_x27_807_ = v_tail_812_;
v_b_808_ = v___x_814_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object* v_fname_829_, lean_object* v_as_x27_830_, lean_object* v_b_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_829_, v_as_x27_830_, v_b_831_);
lean_dec(v_as_x27_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object* v_fname_834_, lean_object* v_rootDirs_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v___x_837_ = lean_box(0);
v___x_838_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
v___x_839_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_834_, v_rootDirs_835_, v___x_838_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_fst_844_; 
v_fst_844_ = lean_ctor_get(v_a_840_, 0);
lean_inc(v_fst_844_);
lean_dec(v_a_840_);
if (lean_obj_tag(v_fst_844_) == 0)
{
lean_object* v___x_846_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_837_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_837_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v_val_848_; lean_object* v___x_850_; 
v_val_848_ = lean_ctor_get(v_fst_844_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_fst_844_, 1);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v_val_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_val_848_);
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
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object* v_fname_853_, lean_object* v_rootDirs_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_searchModuleNameOfFileName(v_fname_853_, v_rootDirs_854_);
lean_dec(v_rootDirs_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object* v_fname_857_, lean_object* v_as_858_, lean_object* v_as_x27_859_, lean_object* v_b_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_857_, v_as_x27_859_, v_b_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object* v_fname_864_, lean_object* v_as_865_, lean_object* v_as_x27_866_, lean_object* v_b_867_, lean_object* v_a_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(v_fname_864_, v_as_865_, v_as_x27_866_, v_b_867_, v_a_868_);
lean_dec(v_as_x27_866_);
lean_dec(v_as_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object* v_lean_881_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_findSysroot___closed__0));
v___x_884_ = lean_io_getenv(v___x_883_);
if (lean_obj_tag(v___x_884_) == 1)
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v_lean_881_);
v_val_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 0);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_val_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v___x_884_);
v___x_893_ = ((lean_object*)(l_Lean_findSysroot___closed__1));
v___x_894_ = ((lean_object*)(l_Lean_findSysroot___closed__3));
v___x_895_ = lean_box(0);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = ((lean_object*)(l_Lean_findSysroot___closed__4));
v___x_898_ = 1;
v___x_899_ = 0;
v___x_900_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_900_, 0, v___x_893_);
lean_ctor_set(v___x_900_, 1, v_lean_881_);
lean_ctor_set(v___x_900_, 2, v___x_894_);
lean_ctor_set(v___x_900_, 3, v___x_895_);
lean_ctor_set(v___x_900_, 4, v___x_897_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*5, v___x_898_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*5 + 1, v___x_899_);
v___x_901_ = l_IO_Process_run(v___x_900_, v___x_895_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_916_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_916_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_916_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_916_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_str_909_; lean_object* v_startInclusive_910_; lean_object* v_endExclusive_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_906_ = lean_string_utf8_byte_size(v_a_902_);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v_a_902_);
lean_ctor_set(v___x_907_, 1, v___x_896_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
v___x_908_ = l_String_Slice_trimAscii(v___x_907_);
v_str_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_str_909_);
v_startInclusive_910_ = lean_ctor_get(v___x_908_, 1);
lean_inc(v_startInclusive_910_);
v_endExclusive_911_ = lean_ctor_get(v___x_908_, 2);
lean_inc(v_endExclusive_911_);
lean_dec_ref(v___x_908_);
v___x_912_ = lean_string_utf8_extract_fast(v_str_909_, v_startInclusive_910_, v_endExclusive_911_);
lean_dec(v_endExclusive_911_);
lean_dec(v_startInclusive_910_);
lean_dec_ref(v_str_909_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_912_);
v___x_914_ = v___x_904_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
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
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_901_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_901_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object* v_lean_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_findSysroot(v_lean_925_);
return v_res_927_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
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
res = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_();
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
