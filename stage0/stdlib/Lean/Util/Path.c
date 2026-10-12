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
lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object* v___x_10_){
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
LEAN_EXPORT void l_Lean_forEachModuleInDir___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_10_ = stack[0].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_forEachModuleInDir___redArg___lam__3(v___x_10_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object* v___x_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_forEachModuleInDir___redArg___lam__3(v___x_16_);
lean_dec_ref(v___x_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object* v___x_19_, lean_object* v_f_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_Name_append(v___x_19_, v_x_21_);
v___x_23_ = lean_apply_1(v_f_20_, v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__4___closed__0(void){
_start:
{
lean_object* v___x_24_; lean_object* v___f_25_; 
v___x_24_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_25_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_25_, 0, v___x_24_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object* v_toPure_30_, lean_object* v_f_31_, lean_object* v_toBind_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v___f_35_, lean_object* v_____do__lift_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___f_39_; size_t v_sz_40_; size_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_37_ = lean_box(0);
lean_inc(v_toPure_30_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__1), 3, 2);
lean_closure_set(v___f_38_, 0, v___x_37_);
lean_closure_set(v___f_38_, 1, v_toPure_30_);
lean_inc_ref(v_inst_33_);
lean_inc_ref(v___f_38_);
lean_inc(v_toBind_32_);
v___f_39_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__5), 11, 8);
lean_closure_set(v___f_39_, 0, v___x_37_);
lean_closure_set(v___f_39_, 1, v_toPure_30_);
lean_closure_set(v___f_39_, 2, v_f_31_);
lean_closure_set(v___f_39_, 3, v_toBind_32_);
lean_closure_set(v___f_39_, 4, v___f_38_);
lean_closure_set(v___f_39_, 5, v_inst_33_);
lean_closure_set(v___f_39_, 6, v_inst_34_);
lean_closure_set(v___f_39_, 7, v___f_38_);
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
lean_object* v_toApplicative_48_; lean_object* v_toBind_49_; lean_object* v_toPure_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_44_, 0);
v_toBind_49_ = lean_ctor_get(v_inst_44_, 1);
lean_inc_n(v_toBind_49_, 2);
v_toPure_50_ = lean_ctor_get(v_toApplicative_48_, 1);
lean_inc_n(v_toPure_50_, 2);
v___x_51_ = lean_alloc_closure((void*)(l_System_FilePath_readDir___boxed), 2, 1);
lean_closure_set(v___x_51_, 0, v_dir_46_);
lean_inc(v_inst_45_);
v___x_52_ = lean_apply_2(v_inst_45_, lean_box(0), v___x_51_);
v___f_53_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__0), 2, 1);
lean_closure_set(v___f_53_, 0, v_toPure_50_);
v___f_54_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__6), 7, 6);
lean_closure_set(v___f_54_, 0, v_toPure_50_);
lean_closure_set(v___f_54_, 1, v_f_47_);
lean_closure_set(v___f_54_, 2, v_toBind_49_);
lean_closure_set(v___f_54_, 3, v_inst_44_);
lean_closure_set(v___f_54_, 4, v_inst_45_);
lean_closure_set(v___f_54_, 5, v___f_53_);
v___x_55_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v___x_52_, v___f_54_);
return v___x_55_;
}
}
lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object* v___x_56_, lean_object* v___x_57_, lean_object* v_toPure_58_, lean_object* v_a_59_, lean_object* v_f_60_, lean_object* v_toBind_61_, lean_object* v___f_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v___f_65_, uint8_t v_____do__lift_66_){
_start:
{
if (v_____do__lift_66_ == 0)
{
lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
lean_dec(v___f_65_);
lean_dec(v_inst_64_);
lean_dec_ref(v_inst_63_);
v___f_67_ = lean_obj_once(&l_Lean_forEachModuleInDir___redArg___lam__4___closed__0, &l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_once, _init_l_Lean_forEachModuleInDir___redArg___lam__4___closed__0);
v___x_68_ = l_System_FilePath_extension(v___x_56_);
v___x_69_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2));
v___x_70_ = l_instBEqOption_beq___redArg(v___f_67_, v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v___f_62_);
lean_dec(v_toBind_61_);
lean_dec(v_f_60_);
lean_dec_ref(v_a_59_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_57_);
v___x_72_ = lean_apply_2(v_toPure_58_, lean_box(0), v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_fileName_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_toPure_58_);
v_fileName_73_ = lean_ctor_get(v_a_59_, 1);
lean_inc_ref(v_fileName_73_);
lean_dec_ref(v_a_59_);
v___x_74_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_75_ = l_System_FilePath_withExtension(v_fileName_73_, v___x_74_);
v___x_76_ = lean_box(0);
v___x_77_ = l_Lean_Name_str___override(v___x_76_, v___x_75_);
v___x_78_ = lean_apply_1(v_f_60_, v___x_77_);
v___x_79_ = lean_apply_4(v_toBind_61_, lean_box(0), lean_box(0), v___x_78_, v___f_62_);
return v___x_79_;
}
}
else
{
lean_object* v_fileName_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v___f_62_);
lean_dec(v_toPure_58_);
v_fileName_80_ = lean_ctor_get(v_a_59_, 1);
lean_inc_ref(v_fileName_80_);
lean_dec_ref(v_a_59_);
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_Name_str___override(v___x_81_, v_fileName_80_);
v___f_83_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__2), 3, 2);
lean_closure_set(v___f_83_, 0, v___x_82_);
lean_closure_set(v___f_83_, 1, v_f_60_);
v___x_84_ = l_Lean_forEachModuleInDir___redArg(v_inst_63_, v_inst_64_, v___x_56_, v___f_83_);
v___x_85_ = lean_apply_4(v_toBind_61_, lean_box(0), lean_box(0), v___x_84_, v___f_65_);
return v___x_85_;
}
}
}
LEAN_EXPORT void l_Lean_forEachModuleInDir___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_56_ = stack[0].m_obj;
lean_object* v___x_57_ = stack[1].m_obj;
lean_object* v_toPure_58_ = stack[2].m_obj;
lean_object* v_a_59_ = stack[3].m_obj;
lean_object* v_f_60_ = stack[4].m_obj;
lean_object* v_toBind_61_ = stack[5].m_obj;
lean_object* v___f_62_ = stack[6].m_obj;
lean_object* v_inst_63_ = stack[7].m_obj;
lean_object* v_inst_64_ = stack[8].m_obj;
lean_object* v___f_65_ = stack[9].m_obj;
uint8_t v_____do__lift_66_ = stack[10].m_num;
lean_object* v_res_86_;
v_res_86_ = l_Lean_forEachModuleInDir___redArg___lam__4(v___x_56_, v___x_57_, v_toPure_58_, v_a_59_, v_f_60_, v_toBind_61_, v___f_62_, v_inst_63_, v_inst_64_, v___f_65_, v_____do__lift_66_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4___boxed(lean_object* v___x_87_, lean_object* v___x_88_, lean_object* v_toPure_89_, lean_object* v_a_90_, lean_object* v_f_91_, lean_object* v_toBind_92_, lean_object* v___f_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v___f_96_, lean_object* v_____do__lift_97_){
_start:
{
uint8_t v_____do__lift_403__boxed_98_; lean_object* v_res_99_; 
v_____do__lift_403__boxed_98_ = lean_unbox(v_____do__lift_97_);
v_res_99_ = l_Lean_forEachModuleInDir___redArg___lam__4(v___x_87_, v___x_88_, v_toPure_89_, v_a_90_, v_f_91_, v_toBind_92_, v___f_93_, v_inst_94_, v_inst_95_, v___f_96_, v_____do__lift_403__boxed_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object* v___x_100_, lean_object* v_toPure_101_, lean_object* v_f_102_, lean_object* v_toBind_103_, lean_object* v___f_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v___f_107_, lean_object* v_a_108_, lean_object* v_x_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
lean_inc_ref(v_a_108_);
v___x_111_ = l_IO_FS_DirEntry_path(v_a_108_);
lean_inc_ref(v___x_111_);
v___f_112_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
lean_inc(v_inst_106_);
lean_inc(v_toBind_103_);
v___f_113_ = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_113_, 0, v___x_111_);
lean_closure_set(v___f_113_, 1, v___x_100_);
lean_closure_set(v___f_113_, 2, v_toPure_101_);
lean_closure_set(v___f_113_, 3, v_a_108_);
lean_closure_set(v___f_113_, 4, v_f_102_);
lean_closure_set(v___f_113_, 5, v_toBind_103_);
lean_closure_set(v___f_113_, 6, v___f_104_);
lean_closure_set(v___f_113_, 7, v_inst_105_);
lean_closure_set(v___f_113_, 8, v_inst_106_);
lean_closure_set(v___f_113_, 9, v___f_107_);
v___x_114_ = lean_apply_2(v_inst_106_, lean_box(0), v___f_112_);
v___x_115_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v___x_114_, v___f_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object* v_m_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_dir_119_, lean_object* v_f_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_forEachModuleInDir___redArg(v_inst_117_, v_inst_118_, v_dir_119_, v_f_120_);
return v___x_121_;
}
}
lean_object* l_Lean_realPathNormalized(lean_object* v_p_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_io_realpath(v_p_122_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_133_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_133_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = l_System_FilePath_normalize(v_a_125_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
return v___x_124_;
}
}
}
LEAN_EXPORT void l_Lean_realPathNormalized_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_122_ = stack[0].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_realPathNormalized(v_p_122_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized___boxed(lean_object* v_p_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_realPathNormalized(v_p_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object* v_msg_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_140_ = lean_panic_fn_borrowed(v___x_139_, v_msg_138_);
return v___x_140_;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2));
v___x_145_ = lean_unsigned_to_nat(20u);
v___x_146_ = lean_unsigned_to_nat(51u);
v___x_147_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1));
v___x_148_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0));
v___x_149_ = l_mkPanicMessageWithDecl(v___x_148_, v___x_147_, v___x_146_, v___x_145_, v___x_144_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object* v_base_150_, lean_object* v_a_151_){
_start:
{
switch(lean_obj_tag(v_a_151_))
{
case 0:
{
lean_inc_ref(v_base_150_);
return v_base_150_;
}
case 1:
{
lean_object* v_pre_152_; lean_object* v_str_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_pre_152_ = lean_ctor_get(v_a_151_, 0);
lean_inc(v_pre_152_);
v_str_153_ = lean_ctor_get(v_a_151_, 1);
lean_inc_ref(v_str_153_);
lean_dec_ref_known(v_a_151_, 2);
v___x_154_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_150_, v_pre_152_);
v___x_155_ = l_System_FilePath_join(v___x_154_, v_str_153_);
return v___x_155_;
}
default: 
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref_known(v_a_151_, 2);
v___x_156_ = lean_obj_once(&l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3, &l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3_once, _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3);
v___x_157_ = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object* v_base_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_158_, v_a_159_);
lean_dec_ref(v_base_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object* v_base_161_, lean_object* v_mod_162_, lean_object* v_ext_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_161_, v_mod_162_);
v___x_165_ = l_System_FilePath_addExtension(v___x_164_, v_ext_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object* v_base_166_, lean_object* v_mod_167_, lean_object* v_ext_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_modToFilePath(v_base_166_, v_mod_167_, v_ext_168_);
lean_dec_ref(v_ext_168_);
lean_dec_ref(v_base_166_);
return v_res_169_;
}
}
lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(lean_object* v_pkg_170_, lean_object* v_ext_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec_ref(v_pkg_170_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_head_176_ = lean_ctor_get(v_x_172_, 0);
lean_inc_n(v_head_176_, 2);
v_tail_177_ = lean_ctor_get(v_x_172_, 1);
lean_inc(v_tail_177_);
lean_dec_ref_known(v_x_172_, 2);
lean_inc_ref(v_pkg_170_);
v___x_181_ = l_System_FilePath_join(v_head_176_, v_pkg_170_);
v___x_182_ = l_System_FilePath_isDir(v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = l_System_FilePath_addExtension(v___x_181_, v_ext_171_);
v___x_184_ = l_System_FilePath_pathExists(v___x_183_);
lean_dec_ref(v___x_183_);
if (v___x_184_ == 0)
{
lean_dec(v_head_176_);
v_x_172_ = v_tail_177_;
goto _start;
}
else
{
lean_dec(v_tail_177_);
lean_dec_ref(v_pkg_170_);
goto v___jp_178_;
}
}
else
{
lean_dec_ref(v___x_181_);
lean_dec(v_tail_177_);
lean_dec_ref(v_pkg_170_);
goto v___jp_178_;
}
v___jp_178_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_head_176_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT void l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_170_ = stack[0].m_obj;
lean_object* v_ext_171_ = stack[1].m_obj;
lean_object* v_x_172_ = stack[2].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_List_findM_x3f___at___00Lean_SearchPath_findRootWithExt_spec__0(v_pkg_170_, v_ext_171_, v_x_172_);
stack->m_obj
 = v_res_186_;
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
lean_object* l_Lean_SearchPath_findRootWithExt(lean_object* v_sp_192_, lean_object* v_ext_193_, lean_object* v_mod_194_){
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
LEAN_EXPORT void l_Lean_SearchPath_findRootWithExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_192_ = stack[0].m_obj;
lean_object* v_ext_193_ = stack[1].m_obj;
lean_object* v_mod_194_ = stack[2].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_SearchPath_findRootWithExt(v_sp_192_, v_ext_193_, v_mod_194_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRootWithExt___boxed(lean_object* v_sp_201_, lean_object* v_ext_202_, lean_object* v_mod_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_SearchPath_findRootWithExt(v_sp_201_, v_ext_202_, v_mod_203_);
lean_dec(v_mod_203_);
lean_dec_ref(v_ext_202_);
return v_res_205_;
}
}
lean_object* l_Lean_SearchPath_findWithExt(lean_object* v_sp_206_, lean_object* v_ext_207_, lean_object* v_mod_208_){
_start:
{
lean_object* v___x_210_; lean_object* v_a_211_; 
v___x_210_ = l_Lean_SearchPath_findRootWithExt(v_sp_206_, v_ext_207_, v_mod_208_);
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
if (lean_obj_tag(v_a_211_) == 0)
{
lean_dec(v_mod_208_);
return v___x_210_;
}
else
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_227_; 
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_228_);
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_227_;
goto v_resetjp_212_;
}
else
{
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_227_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_val_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_226_; 
v_val_215_ = lean_ctor_get(v_a_211_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_211_);
if (v_isSharedCheck_226_ == 0)
{
v___x_217_ = v_a_211_;
v_isShared_218_ = v_isSharedCheck_226_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_val_215_);
lean_dec(v_a_211_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_226_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = l_Lean_modToFilePath(v_val_215_, v_mod_208_, v_ext_207_);
lean_dec(v_val_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_221_);
v___x_223_ = v___x_213_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_SearchPath_findWithExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_206_ = stack[0].m_obj;
lean_object* v_ext_207_ = stack[1].m_obj;
lean_object* v_mod_208_ = stack[2].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_SearchPath_findWithExt(v_sp_206_, v_ext_207_, v_mod_208_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* v_sp_230_, lean_object* v_ext_231_, lean_object* v_mod_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_SearchPath_findWithExt(v_sp_230_, v_ext_231_, v_mod_232_);
lean_dec_ref(v_ext_231_);
return v_res_234_;
}
}
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* v_sp_235_, lean_object* v_ext_236_, lean_object* v_mod_237_){
_start:
{
lean_object* v___x_242_; lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
v___x_242_ = l_Lean_SearchPath_findWithExt(v_sp_235_, v_ext_236_, v_mod_237_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_252_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v___jp_239_:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
v_resetjp_244_:
{
if (lean_obj_tag(v_a_243_) == 1)
{
lean_object* v_val_247_; uint8_t v___x_248_; 
v_val_247_ = lean_ctor_get(v_a_243_, 0);
v___x_248_ = l_System_FilePath_pathExists(v_val_247_);
if (v___x_248_ == 0)
{
lean_dec_ref_known(v_a_243_, 1);
lean_del_object(v___x_245_);
goto v___jp_239_;
}
else
{
lean_object* v___x_250_; 
if (v_isShared_246_ == 0)
{
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_243_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_del_object(v___x_245_);
lean_dec(v_a_243_);
goto v___jp_239_;
}
}
}
}
LEAN_EXPORT void l_Lean_SearchPath_findModuleWithExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_235_ = stack[0].m_obj;
lean_object* v_ext_236_ = stack[1].m_obj;
lean_object* v_mod_237_ = stack[2].m_obj;
lean_object* v_res_253_;
v_res_253_ = l_Lean_SearchPath_findModuleWithExt(v_sp_235_, v_ext_236_, v_mod_237_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* v_sp_254_, lean_object* v_ext_255_, lean_object* v_mod_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_SearchPath_findModuleWithExt(v_sp_254_, v_ext_255_, v_mod_256_);
lean_dec_ref(v_ext_255_);
return v_res_258_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
if (lean_obj_tag(v_x_260_) == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 1;
return v___x_261_;
}
else
{
uint8_t v___x_262_; 
v___x_262_ = 0;
return v___x_262_;
}
}
else
{
if (lean_obj_tag(v_x_260_) == 0)
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v_val_265_; uint8_t v___x_266_; 
v_val_264_ = lean_ctor_get(v_x_259_, 0);
v_val_265_ = lean_ctor_get(v_x_260_, 0);
v___x_266_ = lean_string_dec_eq(v_val_264_, v_val_265_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_259_ = stack[0].m_obj;
lean_object* v_x_260_ = stack[1].m_obj;
uint8_t v_res_267_;
v_res_267_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v_x_259_, v_x_260_);
stack->m_num = v_res_267_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v_x_268_, v_x_269_);
lean_dec(v_x_269_);
lean_dec(v_x_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object* v_ext_272_, lean_object* v_as_273_, size_t v_i_274_, size_t v_stop_275_, lean_object* v_b_276_){
_start:
{
lean_object* v___y_278_; uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_eq(v_i_274_, v_stop_275_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_283_ = lean_array_uget_borrowed(v_as_273_, v_i_274_);
lean_inc(v___x_283_);
v___x_284_ = l_System_FilePath_extension(v___x_283_);
lean_inc_ref(v_ext_272_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_ext_272_);
v___x_286_ = l_instBEqOption_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v___x_284_, v___x_285_);
lean_dec_ref_known(v___x_285_, 1);
lean_dec(v___x_284_);
if (v___x_286_ == 0)
{
v___y_278_ = v_b_276_;
goto v___jp_277_;
}
else
{
lean_object* v___x_287_; 
lean_inc(v___x_283_);
v___x_287_ = lean_array_push(v_b_276_, v___x_283_);
v___y_278_ = v___x_287_;
goto v___jp_277_;
}
}
else
{
lean_dec_ref(v_ext_272_);
return v_b_276_;
}
v___jp_277_:
{
size_t v___x_279_; size_t v___x_280_; 
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_274_, v___x_279_);
v_i_274_ = v___x_280_;
v_b_276_ = v___y_278_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_272_ = stack[0].m_obj;
lean_object* v_as_273_ = stack[1].m_obj;
size_t v_i_274_ = stack[2].m_num;
size_t v_stop_275_ = stack[3].m_num;
lean_object* v_b_276_ = stack[4].m_obj;
lean_object* v_res_288_;
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_272_, v_as_273_, v_i_274_, v_stop_275_, v_b_276_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object* v_ext_289_, lean_object* v_as_290_, lean_object* v_i_291_, lean_object* v_stop_292_, lean_object* v_b_293_){
_start:
{
size_t v_i_boxed_294_; size_t v_stop_boxed_295_; lean_object* v_res_296_; 
v_i_boxed_294_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_stop_boxed_295_ = lean_unbox_usize(v_stop_292_);
lean_dec(v_stop_292_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_289_, v_as_290_, v_i_boxed_294_, v_stop_boxed_295_, v_b_293_);
lean_dec_ref(v_as_290_);
return v_res_296_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t v_val_297_, lean_object* v_x_298_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(v_val_297_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_297_ = stack[0].m_num;
lean_object* v_x_298_ = stack[1].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(v_val_297_, v_x_298_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object* v_val_303_, lean_object* v_x_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_val_922__boxed_306_; lean_object* v_res_307_; 
v_val_922__boxed_306_ = lean_unbox(v_val_303_);
v_res_307_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(v_val_922__boxed_306_, v_x_304_);
lean_dec_ref(v_x_304_);
return v_res_307_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object* v_ext_310_, lean_object* v_as_x27_311_, lean_object* v_b_312_){
_start:
{
if (lean_obj_tag(v_as_x27_311_) == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v_ext_310_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_b_312_);
return v___x_314_;
}
else
{
lean_object* v_head_315_; lean_object* v_tail_316_; uint8_t v___x_317_; 
v_head_315_ = lean_ctor_get(v_as_x27_311_, 0);
v_tail_316_ = lean_ctor_get(v_as_x27_311_, 1);
v___x_317_ = l_System_FilePath_isDir(v_head_315_);
if (v___x_317_ == 0)
{
v_as_x27_311_ = v_tail_316_;
goto _start;
}
else
{
lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(v___x_317_);
v___f_320_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_320_, 0, v___x_319_);
lean_inc(v_head_315_);
v___x_321_ = l_System_FilePath_walkDir(v_head_315_, v___f_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___y_324_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get_size(v_a_322_);
v___x_329_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_330_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_330_ == 0)
{
lean_dec(v_a_322_);
v___y_324_ = v___x_329_;
goto v___jp_323_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_le(v___x_328_, v___x_328_);
if (v___x_331_ == 0)
{
if (v___x_330_ == 0)
{
lean_dec(v_a_322_);
v___y_324_ = v___x_329_;
goto v___jp_323_;
}
else
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_328_);
lean_inc_ref(v_ext_310_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_310_, v_a_322_, v___x_332_, v___x_333_, v___x_329_);
lean_dec(v_a_322_);
v___y_324_ = v___x_334_;
goto v___jp_323_;
}
}
else
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((size_t)0ULL);
v___x_336_ = lean_usize_of_nat(v___x_328_);
lean_inc_ref(v_ext_310_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_310_, v_a_322_, v___x_335_, v___x_336_, v___x_329_);
lean_dec(v_a_322_);
v___y_324_ = v___x_337_;
goto v___jp_323_;
}
}
v___jp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Array_append___redArg(v_b_312_, v___y_324_);
lean_dec_ref(v___y_324_);
v_as_x27_311_ = v_tail_316_;
v_b_312_ = v___x_325_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_312_);
lean_dec_ref(v_ext_310_);
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_310_ = stack[0].m_obj;
lean_object* v_as_x27_311_ = stack[1].m_obj;
lean_object* v_b_312_ = stack[2].m_obj;
lean_object* v_res_338_;
v_res_338_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_310_, v_as_x27_311_, v_b_312_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(lean_object* v_ext_339_, lean_object* v_as_x27_340_, lean_object* v_b_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_339_, v_as_x27_340_, v_b_341_);
lean_dec(v_as_x27_340_);
return v_res_343_;
}
}
lean_object* l_Lean_SearchPath_findAllWithExt(lean_object* v_sp_344_, lean_object* v_ext_345_){
_start:
{
lean_object* v_paths_347_; lean_object* v___x_348_; 
v_paths_347_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_348_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_345_, v_sp_344_, v_paths_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_SearchPath_findAllWithExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_344_ = stack[0].m_obj;
lean_object* v_ext_345_ = stack[1].m_obj;
lean_object* v_res_349_;
v_res_349_ = l_Lean_SearchPath_findAllWithExt(v_sp_344_, v_ext_345_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt___boxed(lean_object* v_sp_350_, lean_object* v_ext_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_SearchPath_findAllWithExt(v_sp_350_, v_ext_351_);
lean_dec(v_sp_350_);
return v_res_353_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(lean_object* v_ext_354_, lean_object* v_as_355_, lean_object* v_as_x27_356_, lean_object* v_b_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_354_, v_as_x27_356_, v_b_357_);
return v___x_360_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_354_ = stack[0].m_obj;
lean_object* v_as_355_ = stack[1].m_obj;
lean_object* v_as_x27_356_ = stack[2].m_obj;
lean_object* v_b_357_ = stack[3].m_obj;
lean_object* v_res_361_;
v_res_361_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(v_ext_354_, v_as_355_, v_as_x27_356_, v_b_357_, lean_box(0));
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(lean_object* v_ext_362_, lean_object* v_as_363_, lean_object* v_as_x27_364_, lean_object* v_b_365_, lean_object* v_a_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(v_ext_362_, v_as_363_, v_as_x27_364_, v_b_365_, v_a_366_);
lean_dec(v_as_x27_364_);
lean_dec(v_as_363_);
return v_res_368_;
}
}
lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_box(0);
v___x_371_ = lean_st_mk_ref(v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_373_;
v_res_373_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
stack->m_obj
 = v_res_373_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
return v_res_375_;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__3(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_379_ = ((lean_object*)(l_Lean_getBuildDir___closed__2));
v___x_380_ = lean_unsigned_to_nat(14u);
v___x_381_ = lean_unsigned_to_nat(22u);
v___x_382_ = ((lean_object*)(l_Lean_getBuildDir___closed__1));
v___x_383_ = ((lean_object*)(l_Lean_getBuildDir___closed__0));
v___x_384_ = l_mkPanicMessageWithDecl(v___x_383_, v___x_382_, v___x_381_, v___x_380_, v___x_379_);
return v___x_384_;
}
}
lean_object* l_Lean_getBuildDir(){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_IO_appDir();
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_401_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_401_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; 
v___x_391_ = l_System_FilePath_parent(v_a_387_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = lean_obj_once(&l_Lean_getBuildDir___closed__3, &l_Lean_getBuildDir___closed__3_once, _init_l_Lean_getBuildDir___closed__3);
v___x_393_ = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(v___x_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_393_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
else
{
lean_object* v_val_397_; lean_object* v___x_399_; 
v_val_397_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_391_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_val_397_);
v___x_399_ = v___x_389_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_val_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
return v___x_386_;
}
}
}
LEAN_EXPORT void l_Lean_getBuildDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_402_;
v_res_402_ = l_Lean_getBuildDir();
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir___boxed(lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_getBuildDir();
return v_res_404_;
}
}
static uint8_t _init_l_Lean_getLibDir___closed__1(void){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_box(0);
v___x_407_ = lean_internal_is_stage0(v___x_406_);
return v___x_407_;
}
}
lean_object* l_Lean_getLibDir(lean_object* v_leanSysroot_410_){
_start:
{
lean_object* v_buildDir_413_; uint8_t v___x_419_; 
v___x_419_ = lean_uint8_once(&l_Lean_getLibDir___closed__1, &l_Lean_getLibDir___closed__1_once, _init_l_Lean_getLibDir___closed__1);
if (v___x_419_ == 0)
{
v_buildDir_413_ = v_leanSysroot_410_;
goto v___jp_412_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_buildDir_423_; 
v___x_420_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_421_ = l_System_FilePath_join(v_leanSysroot_410_, v___x_420_);
v___x_422_ = ((lean_object*)(l_Lean_getLibDir___closed__3));
v_buildDir_423_ = l_System_FilePath_join(v___x_421_, v___x_422_);
v_buildDir_413_ = v_buildDir_423_;
goto v___jp_412_;
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_414_ = ((lean_object*)(l_Lean_getLibDir___closed__0));
v___x_415_ = l_System_FilePath_join(v_buildDir_413_, v___x_414_);
v___x_416_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
v___x_417_ = l_System_FilePath_join(v___x_415_, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT void l_Lean_getLibDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanSysroot_410_ = stack[0].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_Lean_getLibDir(v_leanSysroot_410_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___boxed(lean_object* v_leanSysroot_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_getLibDir(v_leanSysroot_425_);
return v_res_427_;
}
}
lean_object* l_Lean_getBuiltinSearchPath(lean_object* v_leanSysroot_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_440_; 
v___x_430_ = l_Lean_getLibDir(v_leanSysroot_428_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_440_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_440_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_440_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_a_431_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
LEAN_EXPORT void l_Lean_getBuiltinSearchPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanSysroot_428_ = stack[0].m_obj;
lean_object* v_res_441_;
v_res_441_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_428_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath___boxed(lean_object* v_leanSysroot_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_442_);
return v_res_444_;
}
}
lean_object* l_Lean_addSearchPathFromEnv(lean_object* v_sp_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_addSearchPathFromEnv___closed__0));
v___x_449_ = lean_io_getenv(v___x_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_sp_446_);
return v___x_450_;
}
else
{
lean_object* v_val_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_460_; 
v_val_451_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_460_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_val_451_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = l_System_SearchPath_parse(v_val_451_);
v___x_456_ = l_List_appendTR___redArg(v___x_455_, v_sp_446_);
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 0);
lean_ctor_set(v___x_453_, 0, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addSearchPathFromEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_446_ = stack[0].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_addSearchPathFromEnv(v_sp_446_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv___boxed(lean_object* v_sp_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_addSearchPathFromEnv(v_sp_462_);
return v_res_464_;
}
}
lean_object* l_Lean_initSearchPath(lean_object* v_leanSysroot_465_, lean_object* v_sp_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_482_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = l_Lean_addSearchPathFromEnv(v_a_469_);
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_482_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_475_ = l_List_appendTR___redArg(v_sp_466_, v_a_471_);
v___x_476_ = l_Lean_searchPathRef;
v___x_477_ = lean_box(0);
v___x_478_ = lean_st_ref_swap(v___x_476_, v___x_475_);
lean_dec(v___x_478_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_477_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_477_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_sp_466_);
v_a_483_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_468_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_468_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_initSearchPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanSysroot_465_ = stack[0].m_obj;
lean_object* v_sp_466_ = stack[1].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_initSearchPath(v_leanSysroot_465_, v_sp_466_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath___boxed(lean_object* v_leanSysroot_492_, lean_object* v_sp_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_initSearchPath(v_leanSysroot_492_, v_sp_493_);
return v_res_495_;
}
}
lean_object* lean_init_search_path(){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = lean_box(0);
v___x_500_ = l_Lean_initSearchPath(v_a_498_, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_a_501_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_497_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
LEAN_EXPORT void lean_init_search_path_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_509_;
v_res_509_ = lean_init_search_path();
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = lean_init_search_path();
return v_res_511_;
}
}
lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((lean_object*)(l___private_Lean_Util_Path_0__Lean_initFn___closed__0_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_));
v___x_516_ = lean_st_mk_ref(v___x_515_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_518_;
v_res_518_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_();
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2____boxed(lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_182869876____hygCtx___hyg_2_();
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___redArg(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_head_524_; lean_object* v_tail_525_; lean_object* v_fst_526_; lean_object* v_snd_527_; uint8_t v___x_528_; 
v_head_524_ = lean_ctor_get(v_x_522_, 0);
v_tail_525_ = lean_ctor_get(v_x_522_, 1);
v_fst_526_ = lean_ctor_get(v_head_524_, 0);
v_snd_527_ = lean_ctor_get(v_head_524_, 1);
v___x_528_ = lean_name_eq(v_x_521_, v_fst_526_);
if (v___x_528_ == 0)
{
v_x_522_ = v_tail_525_;
goto _start;
}
else
{
lean_object* v___x_530_; 
lean_inc(v_snd_527_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_snd_527_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___redArg___boxed(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v_x_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_x_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__1(lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v___x_536_; 
v___x_536_ = l_List_reverse___redArg(v_a_535_);
return v___x_536_;
}
else
{
lean_object* v_head_537_; lean_object* v_tail_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
v_head_537_ = lean_ctor_get(v_a_534_, 0);
v_tail_538_ = lean_ctor_get(v_a_534_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v_a_534_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_tail_538_);
lean_inc(v_head_537_);
lean_dec(v_a_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_a_535_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_head_537_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_a_535_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
v_a_534_ = v_tail_538_;
v_a_535_ = v___x_543_;
goto _start;
}
}
}
}
}
uint8_t l_List_beq___at___00Lean_findOLean_spec__2(lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
if (lean_obj_tag(v_x_548_) == 0)
{
uint8_t v___x_549_; 
v___x_549_ = 1;
return v___x_549_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
}
else
{
if (lean_obj_tag(v_x_548_) == 0)
{
uint8_t v___x_551_; 
v___x_551_ = 0;
return v___x_551_;
}
else
{
lean_object* v_head_552_; lean_object* v_tail_553_; lean_object* v_head_554_; lean_object* v_tail_555_; uint8_t v___x_556_; 
v_head_552_ = lean_ctor_get(v_x_547_, 0);
v_tail_553_ = lean_ctor_get(v_x_547_, 1);
v_head_554_ = lean_ctor_get(v_x_548_, 0);
v_tail_555_ = lean_ctor_get(v_x_548_, 1);
v___x_556_ = lean_string_dec_eq(v_head_552_, v_head_554_);
if (v___x_556_ == 0)
{
return v___x_556_;
}
else
{
v_x_547_ = v_tail_553_;
v_x_548_ = v_tail_555_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_findOLean_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_547_ = stack[0].m_obj;
lean_object* v_x_548_ = stack[1].m_obj;
uint8_t v_res_558_;
v_res_558_ = l_List_beq___at___00Lean_findOLean_spec__2(v_x_547_, v_x_548_);
stack->m_num = v_res_558_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_findOLean_spec__2___boxed(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_List_beq___at___00Lean_findOLean_spec__2(v_x_559_, v_x_560_);
lean_dec(v_x_560_);
lean_dec(v_x_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
lean_object* l_Lean_findOLean(lean_object* v_mod_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___y_577_; lean_object* v_fst_626_; lean_object* v_snd_627_; uint8_t v___x_628_; 
v___x_571_ = l_Lean_searchPathRef;
v___x_572_ = lean_st_ref_get(v___x_571_);
v___x_573_ = l_Lean_Name_getRoot(v_mod_569_);
v___x_574_ = l___private_Lean_Util_Path_0__Lean_oleanRootCacheRef;
v___x_575_ = lean_st_ref_get(v___x_574_);
v_fst_626_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_fst_626_);
v_snd_627_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_snd_627_);
lean_dec(v___x_575_);
v___x_628_ = l_List_beq___at___00Lean_findOLean_spec__2(v_fst_626_, v___x_572_);
lean_dec(v_fst_626_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec(v_snd_627_);
v___x_629_ = lean_box(0);
v___y_577_ = v___x_629_;
goto v___jp_576_;
}
else
{
v___y_577_ = v_snd_627_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v___x_573_, v___y_577_);
if (lean_obj_tag(v___x_578_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_588_; 
lean_dec(v___y_577_);
lean_dec(v___x_573_);
lean_dec(v___x_572_);
v_val_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_588_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = ((lean_object*)(l_Lean_findOLean___closed__0));
v___x_584_ = l_Lean_modToFilePath(v_val_579_, v_mod_569_, v___x_583_);
lean_dec(v_val_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
lean_ctor_set(v___x_581_, 0, v___x_584_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_625_; 
lean_dec(v___x_578_);
v___x_589_ = ((lean_object*)(l_Lean_findOLean___closed__0));
lean_inc(v___x_572_);
v___x_590_ = l_Lean_SearchPath_findRootWithExt(v___x_572_, v___x_589_, v_mod_569_);
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_625_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_625_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_625_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
if (lean_obj_tag(v_a_591_) == 1)
{
lean_object* v_val_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v_val_595_ = lean_ctor_get(v_a_591_, 0);
lean_inc_n(v_val_595_, 2);
lean_dec_ref_known(v_a_591_, 1);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_573_);
lean_ctor_set(v___x_596_, 1, v_val_595_);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___y_577_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_572_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_st_ref_swap(v___x_574_, v___x_598_);
lean_dec(v___x_599_);
v___x_600_ = l_Lean_modToFilePath(v_val_595_, v_mod_569_, v___x_589_);
lean_dec(v_val_595_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_600_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec(v_a_591_);
lean_dec(v___y_577_);
lean_dec(v_mod_569_);
v___x_604_ = 0;
v___x_605_ = l_Lean_Name_toString(v___x_573_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_607_ = lean_string_append(v___x_606_, v___x_605_);
v___x_608_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_609_ = lean_string_append(v___x_607_, v___x_608_);
v___x_610_ = lean_string_append(v___x_609_, v___x_605_);
v___x_611_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = lean_string_append(v___x_612_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_614_ = ((lean_object*)(l_Lean_findOLean___closed__4));
v___x_615_ = lean_string_append(v___x_613_, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_617_ = lean_box(0);
v___x_618_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__1(v___x_572_, v___x_617_);
v___x_619_ = l_String_intercalate(v___x_616_, v___x_618_);
v___x_620_ = lean_string_append(v___x_615_, v___x_619_);
lean_dec_ref(v___x_619_);
v___x_621_ = lean_mk_io_user_error(v___x_620_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 1);
lean_ctor_set(v___x_593_, 0, v___x_621_);
v___x_623_ = v___x_593_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_findOLean_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_569_ = stack[0].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_findOLean(v_mod_569_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* v_mod_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_findOLean(v_mod_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0(lean_object* v_00_u03b2_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_List_lookup___at___00Lean_findOLean_spec__0___redArg(v_x_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00Lean_findOLean_spec__0___boxed(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_List_lookup___at___00Lean_findOLean_spec__0(v_00_u03b2_638_, v_x_639_, v_x_640_);
lean_dec(v_x_640_);
lean_dec(v_x_639_);
return v_res_641_;
}
}
lean_object* l_Lean_findLean(lean_object* v_sp_643_, lean_object* v_mod_644_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_678_; 
v___x_646_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
lean_inc(v_mod_644_);
lean_inc(v_sp_643_);
v___x_647_ = l_Lean_SearchPath_findWithExt(v_sp_643_, v___x_646_, v_mod_644_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_678_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_678_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_678_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
if (lean_obj_tag(v_a_648_) == 1)
{
lean_object* v_val_652_; lean_object* v___x_654_; 
lean_dec(v_mod_644_);
lean_dec(v_sp_643_);
v_val_652_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v_a_648_, 1);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v_val_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_val_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
lean_dec(v_a_648_);
v___x_656_ = l_Lean_Name_getRoot(v_mod_644_);
lean_dec(v_mod_644_);
v___x_657_ = 0;
v___x_658_ = l_Lean_Name_toString(v___x_656_, v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_660_ = lean_string_append(v___x_659_, v___x_658_);
v___x_661_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
v___x_663_ = lean_string_append(v___x_662_, v___x_658_);
v___x_664_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_665_ = lean_string_append(v___x_663_, v___x_664_);
v___x_666_ = lean_string_append(v___x_665_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_667_ = ((lean_object*)(l_Lean_findLean___closed__0));
v___x_668_ = lean_string_append(v___x_666_, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_670_ = lean_box(0);
v___x_671_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__1(v_sp_643_, v___x_670_);
v___x_672_ = l_String_intercalate(v___x_669_, v___x_671_);
v___x_673_ = lean_string_append(v___x_668_, v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = lean_mk_io_user_error(v___x_673_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 1);
lean_ctor_set(v___x_650_, 0, v___x_674_);
v___x_676_ = v___x_650_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findLean_0interp(lean_interpreter_value* stack)
{
lean_object* v_sp_643_ = stack[0].m_obj;
lean_object* v_mod_644_ = stack[1].m_obj;
lean_object* v_res_679_;
v_res_679_ = l_Lean_findLean(v_sp_643_, v_mod_644_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object* v_sp_680_, lean_object* v_mod_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_findLean(v_sp_680_, v_mod_681_);
return v_res_683_;
}
}
lean_object* l_Lean_getSrcSearchPath(){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___y_691_; 
v___x_688_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__0));
v___x_689_ = lean_io_getenv(v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(0);
v___y_691_ = v___x_721_;
goto v___jp_690_;
}
else
{
lean_object* v_val_722_; lean_object* v___x_723_; 
v_val_722_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_722_);
lean_dec_ref_known(v___x_689_, 1);
v___x_723_ = l_System_SearchPath_parse(v_val_722_);
v___y_691_ = v___x_723_;
goto v___jp_690_;
}
v___jp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = l_IO_appDir();
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_712_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_712_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_712_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_712_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_697_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_698_ = l_System_FilePath_join(v_a_693_, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__1));
v___x_700_ = l_System_FilePath_join(v___x_698_, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
v___x_702_ = l_System_FilePath_join(v___x_700_, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__2));
lean_inc_ref(v___x_702_);
v___x_704_ = l_System_FilePath_join(v___x_702_, v___x_703_);
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_702_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l_List_appendTR___redArg(v___y_691_, v___x_707_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_708_);
v___x_710_ = v___x_695_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v___y_691_);
v_a_713_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_692_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_692_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_getSrcSearchPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_724_;
v_res_724_ = l_Lean_getSrcSearchPath();
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_getSrcSearchPath();
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
return v_x_727_;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v___x_731_; 
v_head_729_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_head_729_);
v_tail_730_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_tail_730_);
lean_dec_ref_known(v_x_728_, 2);
v___x_731_ = l_Lean_Name_str___override(v_x_727_, v_head_729_);
v_x_727_ = v___x_731_;
v_x_728_ = v_tail_730_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__3(void){
_start:
{
uint32_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = l_System_FilePath_pathSeparator;
v___x_737_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_738_ = lean_string_push(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__4(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_740_ = lean_string_utf8_byte_size(v___x_739_);
return v___x_740_;
}
}
lean_object* l_Lean_moduleNameOfFileName(lean_object* v_fname_741_, lean_object* v_rootDir_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_io_realpath(v_fname_741_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_815_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_815_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_815_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_815_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___y_750_; lean_object* v_rootDir_763_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v_rootDir_786_; 
if (lean_obj_tag(v_rootDir_742_) == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_io_current_dir();
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v_rootDir_786_ = v_a_805_;
goto v___jp_785_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_del_object(v___x_747_);
lean_dec(v_a_745_);
v_a_806_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_804_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_val_814_; 
v_val_814_ = lean_ctor_get(v_rootDir_742_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v_rootDir_742_, 1);
v_rootDir_786_ = v_val_814_;
goto v___jp_785_;
}
v___jp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_751_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__0));
v___x_752_ = lean_string_append(v___x_751_, v_a_745_);
lean_dec(v_a_745_);
v___x_753_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__1));
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
v___x_755_ = lean_string_append(v___x_754_, v___y_750_);
lean_dec_ref(v___y_750_);
v___x_756_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__2));
v___x_757_ = lean_string_append(v___x_755_, v___x_756_);
v___x_758_ = lean_mk_io_user_error(v___x_757_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 1);
lean_ctor_set(v___x_747_, 0, v___x_758_);
v___x_760_ = v___x_747_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
lean_inc(v_a_745_);
v___x_764_ = l_System_FilePath_normalize(v_a_745_);
v___x_765_ = lean_string_utf8_byte_size(v___x_764_);
v___x_766_ = lean_string_utf8_byte_size(v_rootDir_763_);
v___x_767_ = lean_nat_dec_le(v___x_766_, v___x_765_);
if (v___x_767_ == 0)
{
lean_dec_ref(v___x_764_);
v___y_750_ = v_rootDir_763_;
goto v___jp_749_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_string_memcmp(v___x_764_, v_rootDir_763_, v___x_768_, v___x_768_, v___x_766_);
lean_dec_ref(v___x_764_);
if (v___x_769_ == 0)
{
v___y_750_ = v_rootDir_763_;
goto v___jp_749_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_747_);
v___x_770_ = lean_string_length(v_rootDir_763_);
lean_dec_ref(v_rootDir_763_);
v___x_771_ = lean_string_utf8_byte_size(v_a_745_);
lean_inc(v_a_745_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v_a_745_);
lean_ctor_set(v___x_772_, 1, v___x_768_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = l_String_Slice_Pos_nextn(v___x_772_, v___x_768_, v___x_770_);
lean_dec_ref_known(v___x_772_, 3);
v___x_774_ = lean_string_utf8_extract_fast(v_a_745_, v___x_773_, v___x_771_);
lean_dec(v___x_773_);
lean_dec(v_a_745_);
v___x_775_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_776_ = l_System_FilePath_withExtension(v___x_774_, v___x_775_);
v___x_777_ = lean_box(0);
v___x_778_ = l_System_FilePath_components(v___x_776_);
v___x_779_ = l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(v___x_777_, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
v___jp_781_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_string_append(v___y_782_, v___y_783_);
v_rootDir_763_ = v___x_784_;
goto v___jp_762_;
}
v___jp_785_:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_realPathNormalized(v_rootDir_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_790_ = lean_string_utf8_byte_size(v_a_788_);
v___x_791_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__4, &l_Lean_moduleNameOfFileName___closed__4_once, _init_l_Lean_moduleNameOfFileName___closed__4);
v___x_792_ = lean_nat_dec_le(v___x_791_, v___x_790_);
if (v___x_792_ == 0)
{
v___y_782_ = v_a_788_;
v___y_783_ = v___x_789_;
goto v___jp_781_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_nat_sub(v___x_790_, v___x_791_);
v___x_795_ = lean_string_memcmp(v_a_788_, v___x_789_, v___x_794_, v___x_793_, v___x_791_);
lean_dec(v___x_794_);
if (v___x_795_ == 0)
{
v___y_782_ = v_a_788_;
v___y_783_ = v___x_789_;
goto v___jp_781_;
}
else
{
v_rootDir_763_ = v_a_788_;
goto v___jp_762_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_del_object(v___x_747_);
lean_dec(v_a_745_);
v_a_796_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_787_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_787_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_rootDir_742_);
v_a_816_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_744_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_744_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_moduleNameOfFileName_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_741_ = stack[0].m_obj;
lean_object* v_rootDir_742_ = stack[1].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_Lean_moduleNameOfFileName(v_fname_741_, v_rootDir_742_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object* v_fname_825_, lean_object* v_rootDir_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_moduleNameOfFileName(v_fname_825_, v_rootDir_826_);
return v_res_828_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object* v_fname_832_, lean_object* v_as_x27_833_, lean_object* v_b_834_){
_start:
{
if (lean_obj_tag(v_as_x27_833_) == 0)
{
lean_object* v___x_836_; 
lean_dec_ref(v_fname_832_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_834_);
return v___x_836_;
}
else
{
lean_object* v_head_837_; lean_object* v_tail_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v_b_834_);
v_head_837_ = lean_ctor_get(v_as_x27_833_, 0);
v_tail_838_ = lean_ctor_get(v_as_x27_833_, 1);
v___x_839_ = lean_box(0);
v___x_840_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
lean_inc(v_head_837_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_head_837_);
lean_inc_ref(v_fname_832_);
v___x_842_ = l_Lean_moduleNameOfFileName(v_fname_832_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v_fname_832_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_853_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v_a_843_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_839_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_849_);
v___x_851_ = v___x_845_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec_ref_known(v___x_842_, 1);
v_as_x27_833_ = v_tail_838_;
v_b_834_ = v___x_840_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_832_ = stack[0].m_obj;
lean_object* v_as_x27_833_ = stack[1].m_obj;
lean_object* v_b_834_ = stack[2].m_obj;
lean_object* v_res_855_;
v_res_855_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_832_, v_as_x27_833_, v_b_834_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object* v_fname_856_, lean_object* v_as_x27_857_, lean_object* v_b_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_856_, v_as_x27_857_, v_b_858_);
lean_dec(v_as_x27_857_);
return v_res_860_;
}
}
lean_object* l_Lean_searchModuleNameOfFileName(lean_object* v_fname_861_, lean_object* v_rootDirs_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_879_; 
v___x_864_ = lean_box(0);
v___x_865_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
v___x_866_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_861_, v_rootDirs_862_, v___x_865_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_879_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_879_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_879_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_fst_871_; 
v_fst_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_fst_871_);
lean_dec(v_a_867_);
if (lean_obj_tag(v_fst_871_) == 0)
{
lean_object* v___x_873_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_864_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_864_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v_val_875_; lean_object* v___x_877_; 
v_val_875_ = lean_ctor_get(v_fst_871_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v_fst_871_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_val_875_);
v___x_877_ = v___x_869_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_val_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_searchModuleNameOfFileName_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_861_ = stack[0].m_obj;
lean_object* v_rootDirs_862_ = stack[1].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_searchModuleNameOfFileName(v_fname_861_, v_rootDirs_862_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object* v_fname_881_, lean_object* v_rootDirs_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_searchModuleNameOfFileName(v_fname_881_, v_rootDirs_882_);
lean_dec(v_rootDirs_882_);
return v_res_884_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object* v_fname_885_, lean_object* v_as_886_, lean_object* v_as_x27_887_, lean_object* v_b_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_885_, v_as_x27_887_, v_b_888_);
return v___x_891_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_885_ = stack[0].m_obj;
lean_object* v_as_886_ = stack[1].m_obj;
lean_object* v_as_x27_887_ = stack[2].m_obj;
lean_object* v_b_888_ = stack[3].m_obj;
lean_object* v_res_892_;
v_res_892_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(v_fname_885_, v_as_886_, v_as_x27_887_, v_b_888_, lean_box(0));
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object* v_fname_893_, lean_object* v_as_894_, lean_object* v_as_x27_895_, lean_object* v_b_896_, lean_object* v_a_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(v_fname_893_, v_as_894_, v_as_x27_895_, v_b_896_, v_a_897_);
lean_dec(v_as_x27_895_);
lean_dec(v_as_894_);
return v_res_899_;
}
}
lean_object* l_Lean_findSysroot(lean_object* v_lean_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_findSysroot___closed__0));
v___x_913_ = lean_io_getenv(v___x_912_);
if (lean_obj_tag(v___x_913_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v_lean_910_);
v_val_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_val_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 0);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_val_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v___x_913_);
v___x_922_ = ((lean_object*)(l_Lean_findSysroot___closed__1));
v___x_923_ = ((lean_object*)(l_Lean_findSysroot___closed__3));
v___x_924_ = lean_box(0);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = ((lean_object*)(l_Lean_findSysroot___closed__4));
v___x_927_ = 1;
v___x_928_ = 0;
v___x_929_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_929_, 0, v___x_922_);
lean_ctor_set(v___x_929_, 1, v_lean_910_);
lean_ctor_set(v___x_929_, 2, v___x_923_);
lean_ctor_set(v___x_929_, 3, v___x_924_);
lean_ctor_set(v___x_929_, 4, v___x_926_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*5, v___x_927_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*5 + 1, v___x_928_);
v___x_930_ = l_IO_Process_run(v___x_929_, v___x_924_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_945_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_945_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_str_938_; lean_object* v_startInclusive_939_; lean_object* v_endExclusive_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_935_ = lean_string_utf8_byte_size(v_a_931_);
v___x_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_936_, 0, v_a_931_);
lean_ctor_set(v___x_936_, 1, v___x_925_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
v___x_937_ = l_String_Slice_trimAscii(v___x_936_);
v_str_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_str_938_);
v_startInclusive_939_ = lean_ctor_get(v___x_937_, 1);
lean_inc(v_startInclusive_939_);
v_endExclusive_940_ = lean_ctor_get(v___x_937_, 2);
lean_inc(v_endExclusive_940_);
lean_dec_ref(v___x_937_);
v___x_941_ = lean_string_utf8_extract_fast(v_str_938_, v_startInclusive_939_, v_endExclusive_940_);
lean_dec(v_endExclusive_940_);
lean_dec(v_startInclusive_939_);
lean_dec_ref(v_str_938_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_941_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_a_946_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_930_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_930_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_findSysroot_0interp(lean_interpreter_value* stack)
{
lean_object* v_lean_910_ = stack[0].m_obj;
lean_object* v_res_954_;
v_res_954_ = l_Lean_findSysroot(v_lean_910_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object* v_lean_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_findSysroot(v_lean_955_);
return v_res_957_;
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
