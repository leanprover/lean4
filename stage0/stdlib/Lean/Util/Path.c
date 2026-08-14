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
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__0(lean_object*, lean_object*);
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
v___x_69_ = l_Option_instBEq_beq___redArg(v___f_66_, v___x_67_, v___x_68_);
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
uint8_t v_____do__lift_528__boxed_96_; lean_object* v_res_97_; 
v_____do__lift_528__boxed_96_ = lean_unbox(v_____do__lift_95_);
v_res_97_ = l_Lean_forEachModuleInDir___redArg___lam__4(v___x_85_, v___x_86_, v_toPure_87_, v_a_88_, v_f_89_, v_toBind_90_, v___f_91_, v_inst_92_, v_inst_93_, v___f_94_, v_____do__lift_528__boxed_96_);
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
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(lean_object* v_pkg_167_, lean_object* v_ext_168_, lean_object* v_x_169_){
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
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0___boxed(lean_object* v_pkg_183_, lean_object* v_ext_184_, lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(v_pkg_183_, v_ext_184_, v_x_185_);
lean_dec_ref(v_ext_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* v_sp_188_, lean_object* v_ext_189_, lean_object* v_mod_190_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v_pkg_194_; lean_object* v___x_195_; lean_object* v_a_196_; 
v___x_192_ = l_Lean_Name_getRoot(v_mod_190_);
v___x_193_ = 0;
v_pkg_194_ = l_Lean_Name_toString(v___x_192_, v___x_193_);
v___x_195_ = l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(v_pkg_194_, v_ext_189_, v_sp_188_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
if (lean_obj_tag(v_a_196_) == 0)
{
lean_dec(v_mod_190_);
return v___x_195_;
}
else
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_212_; 
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___x_195_, 0);
lean_dec(v_unused_213_);
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_212_;
goto v_resetjp_197_;
}
else
{
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_212_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_211_; 
v_val_200_ = lean_ctor_get(v_a_196_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_a_196_);
if (v_isSharedCheck_211_ == 0)
{
v___x_202_ = v_a_196_;
v_isShared_203_ = v_isSharedCheck_211_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v_a_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_211_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = l_Lean_modToFilePath(v_val_200_, v_mod_190_, v_ext_189_);
lean_dec(v_val_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_210_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_206_);
v___x_208_ = v___x_198_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* v_sp_214_, lean_object* v_ext_215_, lean_object* v_mod_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_SearchPath_findWithExt(v_sp_214_, v_ext_215_, v_mod_216_);
lean_dec_ref(v_ext_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* v_sp_219_, lean_object* v_ext_220_, lean_object* v_mod_221_){
_start:
{
lean_object* v___x_226_; lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_236_; 
v___x_226_ = l_Lean_SearchPath_findWithExt(v_sp_219_, v_ext_220_, v_mod_221_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_236_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_236_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_236_;
goto v_resetjp_228_;
}
v___jp_223_:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
v_resetjp_228_:
{
if (lean_obj_tag(v_a_227_) == 1)
{
lean_object* v_val_231_; uint8_t v___x_232_; 
v_val_231_ = lean_ctor_get(v_a_227_, 0);
v___x_232_ = l_System_FilePath_pathExists(v_val_231_);
if (v___x_232_ == 0)
{
lean_dec_ref_known(v_a_227_, 1);
lean_del_object(v___x_229_);
goto v___jp_223_;
}
else
{
lean_object* v___x_234_; 
if (v_isShared_230_ == 0)
{
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_227_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_del_object(v___x_229_);
lean_dec(v_a_227_);
goto v___jp_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* v_sp_237_, lean_object* v_ext_238_, lean_object* v_mod_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_SearchPath_findModuleWithExt(v_sp_237_, v_ext_238_, v_mod_239_);
lean_dec_ref(v_ext_238_);
return v_res_241_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 1;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
else
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
else
{
lean_object* v_val_247_; lean_object* v_val_248_; uint8_t v___x_249_; 
v_val_247_ = lean_ctor_get(v_x_242_, 0);
v_val_248_ = lean_ctor_get(v_x_243_, 0);
v___x_249_ = lean_string_dec_eq(v_val_247_, v_val_248_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v_x_250_, v_x_251_);
lean_dec(v_x_251_);
lean_dec(v_x_250_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object* v_ext_254_, lean_object* v_as_255_, size_t v_i_256_, size_t v_stop_257_, lean_object* v_b_258_){
_start:
{
lean_object* v___y_260_; uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_eq(v_i_256_, v_stop_257_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_array_uget_borrowed(v_as_255_, v_i_256_);
lean_inc(v___x_265_);
v___x_266_ = l_System_FilePath_extension(v___x_265_);
lean_inc_ref(v_ext_254_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_ext_254_);
v___x_268_ = l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v___x_266_, v___x_267_);
lean_dec_ref_known(v___x_267_, 1);
lean_dec(v___x_266_);
if (v___x_268_ == 0)
{
v___y_260_ = v_b_258_;
goto v___jp_259_;
}
else
{
lean_object* v___x_269_; 
lean_inc(v___x_265_);
v___x_269_ = lean_array_push(v_b_258_, v___x_265_);
v___y_260_ = v___x_269_;
goto v___jp_259_;
}
}
else
{
lean_dec_ref(v_ext_254_);
return v_b_258_;
}
v___jp_259_:
{
size_t v___x_261_; size_t v___x_262_; 
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_add(v_i_256_, v___x_261_);
v_i_256_ = v___x_262_;
v_b_258_ = v___y_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object* v_ext_270_, lean_object* v_as_271_, lean_object* v_i_272_, lean_object* v_stop_273_, lean_object* v_b_274_){
_start:
{
size_t v_i_boxed_275_; size_t v_stop_boxed_276_; lean_object* v_res_277_; 
v_i_boxed_275_ = lean_unbox_usize(v_i_272_);
lean_dec(v_i_272_);
v_stop_boxed_276_ = lean_unbox_usize(v_stop_273_);
lean_dec(v_stop_273_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_270_, v_as_271_, v_i_boxed_275_, v_stop_boxed_276_, v_b_274_);
lean_dec_ref(v_as_271_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t v_val_278_, lean_object* v_x_279_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_box(v_val_278_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object* v_val_283_, lean_object* v_x_284_, lean_object* v___y_285_){
_start:
{
uint8_t v_val_1031__boxed_286_; lean_object* v_res_287_; 
v_val_1031__boxed_286_ = lean_unbox(v_val_283_);
v_res_287_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(v_val_1031__boxed_286_, v_x_284_);
lean_dec_ref(v_x_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object* v_ext_290_, lean_object* v_as_x27_291_, lean_object* v_b_292_){
_start:
{
if (lean_obj_tag(v_as_x27_291_) == 0)
{
lean_object* v___x_294_; 
lean_dec_ref(v_ext_290_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v_b_292_);
return v___x_294_;
}
else
{
lean_object* v_head_295_; lean_object* v_tail_296_; uint8_t v___x_297_; 
v_head_295_ = lean_ctor_get(v_as_x27_291_, 0);
v_tail_296_ = lean_ctor_get(v_as_x27_291_, 1);
v___x_297_ = l_System_FilePath_isDir(v_head_295_);
if (v___x_297_ == 0)
{
v_as_x27_291_ = v_tail_296_;
goto _start;
}
else
{
lean_object* v___x_299_; lean_object* v___f_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(v___x_297_);
v___f_300_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_300_, 0, v___x_299_);
lean_inc(v_head_295_);
v___x_301_ = l_System_FilePath_walkDir(v_head_295_, v___f_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___y_304_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_array_get_size(v_a_302_);
v___x_309_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_310_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_310_ == 0)
{
lean_dec(v_a_302_);
v___y_304_ = v___x_309_;
goto v___jp_303_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_le(v___x_308_, v___x_308_);
if (v___x_311_ == 0)
{
if (v___x_310_ == 0)
{
lean_dec(v_a_302_);
v___y_304_ = v___x_309_;
goto v___jp_303_;
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_308_);
lean_inc_ref(v_ext_290_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_290_, v_a_302_, v___x_312_, v___x_313_, v___x_309_);
lean_dec(v_a_302_);
v___y_304_ = v___x_314_;
goto v___jp_303_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_308_);
lean_inc_ref(v_ext_290_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_290_, v_a_302_, v___x_315_, v___x_316_, v___x_309_);
lean_dec(v_a_302_);
v___y_304_ = v___x_317_;
goto v___jp_303_;
}
}
v___jp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = l_Array_append___redArg(v_b_292_, v___y_304_);
lean_dec_ref(v___y_304_);
v_as_x27_291_ = v_tail_296_;
v_b_292_ = v___x_305_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_292_);
lean_dec_ref(v_ext_290_);
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(lean_object* v_ext_318_, lean_object* v_as_x27_319_, lean_object* v_b_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_318_, v_as_x27_319_, v_b_320_);
lean_dec(v_as_x27_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object* v_sp_323_, lean_object* v_ext_324_){
_start:
{
lean_object* v_paths_326_; lean_object* v___x_327_; 
v_paths_326_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0));
v___x_327_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_324_, v_sp_323_, v_paths_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt___boxed(lean_object* v_sp_328_, lean_object* v_ext_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_SearchPath_findAllWithExt(v_sp_328_, v_ext_329_);
lean_dec(v_sp_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(lean_object* v_ext_332_, lean_object* v_as_333_, lean_object* v_as_x27_334_, lean_object* v_b_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(v_ext_332_, v_as_x27_334_, v_b_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(lean_object* v_ext_339_, lean_object* v_as_340_, lean_object* v_as_x27_341_, lean_object* v_b_342_, lean_object* v_a_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(v_ext_339_, v_as_340_, v_as_x27_341_, v_b_342_, v_a_343_);
lean_dec(v_as_x27_341_);
lean_dec(v_as_340_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_box(0);
v___x_348_ = lean_st_mk_ref(v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
return v_res_351_;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = ((lean_object*)(l_Lean_getBuildDir___closed__2));
v___x_356_ = lean_unsigned_to_nat(14u);
v___x_357_ = lean_unsigned_to_nat(22u);
v___x_358_ = ((lean_object*)(l_Lean_getBuildDir___closed__1));
v___x_359_ = ((lean_object*)(l_Lean_getBuildDir___closed__0));
v___x_360_ = l_mkPanicMessageWithDecl(v___x_359_, v___x_358_, v___x_357_, v___x_356_, v___x_355_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir(){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_IO_appDir();
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_377_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_377_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; 
v___x_367_ = l_System_FilePath_parent(v_a_363_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_obj_once(&l_Lean_getBuildDir___closed__3, &l_Lean_getBuildDir___closed__3_once, _init_l_Lean_getBuildDir___closed__3);
v___x_369_ = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(v___x_368_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_369_);
v___x_371_ = v___x_365_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v_val_373_; lean_object* v___x_375_; 
v_val_373_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_367_, 1);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v_val_373_);
v___x_375_ = v___x_365_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_val_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir___boxed(lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_getBuildDir();
return v_res_379_;
}
}
static uint8_t _init_l_Lean_getLibDir___closed__1(void){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_box(0);
v___x_382_ = lean_internal_is_stage0(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir(lean_object* v_leanSysroot_385_){
_start:
{
lean_object* v_buildDir_388_; uint8_t v___x_394_; 
v___x_394_ = lean_uint8_once(&l_Lean_getLibDir___closed__1, &l_Lean_getLibDir___closed__1_once, _init_l_Lean_getLibDir___closed__1);
if (v___x_394_ == 0)
{
v_buildDir_388_ = v_leanSysroot_385_;
goto v___jp_387_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_buildDir_398_; 
v___x_395_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_396_ = l_System_FilePath_join(v_leanSysroot_385_, v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_getLibDir___closed__3));
v_buildDir_398_ = l_System_FilePath_join(v___x_396_, v___x_397_);
v_buildDir_388_ = v_buildDir_398_;
goto v___jp_387_;
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_389_ = ((lean_object*)(l_Lean_getLibDir___closed__0));
v___x_390_ = l_System_FilePath_join(v_buildDir_388_, v___x_389_);
v___x_391_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
v___x_392_ = l_System_FilePath_join(v___x_390_, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___boxed(lean_object* v_leanSysroot_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_getLibDir(v_leanSysroot_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object* v_leanSysroot_402_){
_start:
{
lean_object* v___x_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_414_; 
v___x_404_ = l_Lean_getLibDir(v_leanSysroot_402_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_414_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v_a_405_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath___boxed(lean_object* v_leanSysroot_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object* v_sp_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_addSearchPathFromEnv___closed__0));
v___x_422_ = lean_io_getenv(v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_sp_419_);
return v___x_423_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_val_424_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v___x_422_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v___x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = l_System_SearchPath_parse(v_val_424_);
v___x_429_ = l_List_appendTR___redArg(v___x_428_, v_sp_419_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 0);
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
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
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv___boxed(lean_object* v_sp_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_addSearchPathFromEnv(v_sp_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object* v_leanSysroot_437_, lean_object* v_sp_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_454_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = l_Lean_addSearchPathFromEnv(v_a_441_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_454_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_454_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_454_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_447_ = l_List_appendTR___redArg(v_sp_438_, v_a_443_);
v___x_448_ = l_Lean_searchPathRef;
v___x_449_ = lean_st_ref_swap(v___x_448_, v___x_447_);
lean_dec(v___x_449_);
v___x_450_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_450_);
v___x_452_ = v___x_445_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_sp_438_);
v_a_455_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_440_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_440_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath___boxed(lean_object* v_leanSysroot_463_, lean_object* v_sp_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_initSearchPath(v_leanSysroot_463_, v_sp_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* lean_init_search_path(){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = lean_box(0);
v___x_471_ = l_Lean_initSearchPath(v_a_469_, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_a_472_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_468_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = lean_init_search_path();
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__0(lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
if (lean_obj_tag(v_a_482_) == 0)
{
lean_object* v___x_484_; 
v___x_484_ = l_List_reverse___redArg(v_a_483_);
return v___x_484_;
}
else
{
lean_object* v_head_485_; lean_object* v_tail_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
v_head_485_ = lean_ctor_get(v_a_482_, 0);
v_tail_486_ = lean_ctor_get(v_a_482_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_482_);
if (v_isSharedCheck_494_ == 0)
{
v___x_488_ = v_a_482_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_tail_486_);
lean_inc(v_head_485_);
lean_dec(v_a_482_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v_a_483_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_head_485_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_483_);
v___x_491_ = v_reuseFailAlloc_493_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v_a_482_ = v_tail_486_;
v_a_483_ = v___x_491_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object* v_mod_501_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_537_; 
v___x_503_ = l_Lean_searchPathRef;
v___x_504_ = lean_st_ref_get(v___x_503_);
v___x_505_ = ((lean_object*)(l_Lean_findOLean___closed__0));
lean_inc(v_mod_501_);
lean_inc(v___x_504_);
v___x_506_ = l_Lean_SearchPath_findWithExt(v___x_504_, v___x_505_, v_mod_501_);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_537_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_537_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_537_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
if (lean_obj_tag(v_a_507_) == 1)
{
lean_object* v_val_511_; lean_object* v___x_513_; 
lean_dec(v___x_504_);
lean_dec(v_mod_501_);
v_val_511_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_a_507_, 1);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_val_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_val_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
lean_dec(v_a_507_);
v___x_515_ = l_Lean_Name_getRoot(v_mod_501_);
lean_dec(v_mod_501_);
v___x_516_ = 0;
v___x_517_ = l_Lean_Name_toString(v___x_515_, v___x_516_);
v___x_518_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_519_ = lean_string_append(v___x_518_, v___x_517_);
v___x_520_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = lean_string_append(v___x_521_, v___x_517_);
v___x_523_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
v___x_525_ = lean_string_append(v___x_524_, v___x_517_);
lean_dec_ref(v___x_517_);
v___x_526_ = ((lean_object*)(l_Lean_findOLean___closed__4));
v___x_527_ = lean_string_append(v___x_525_, v___x_526_);
v___x_528_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_529_ = lean_box(0);
v___x_530_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__0(v___x_504_, v___x_529_);
v___x_531_ = l_String_intercalate(v___x_528_, v___x_530_);
v___x_532_ = lean_string_append(v___x_527_, v___x_531_);
lean_dec_ref(v___x_531_);
v___x_533_ = lean_mk_io_user_error(v___x_532_);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
lean_ctor_set(v___x_509_, 0, v___x_533_);
v___x_535_ = v___x_509_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* v_mod_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_findOLean(v_mod_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object* v_sp_542_, lean_object* v_mod_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_577_; 
v___x_545_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
lean_inc(v_mod_543_);
lean_inc(v_sp_542_);
v___x_546_ = l_Lean_SearchPath_findWithExt(v_sp_542_, v___x_545_, v_mod_543_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_577_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_577_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_577_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
if (lean_obj_tag(v_a_547_) == 1)
{
lean_object* v_val_551_; lean_object* v___x_553_; 
lean_dec(v_mod_543_);
lean_dec(v_sp_542_);
v_val_551_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_a_547_, 1);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_val_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec(v_a_547_);
v___x_555_ = l_Lean_Name_getRoot(v_mod_543_);
lean_dec(v_mod_543_);
v___x_556_ = 0;
v___x_557_ = l_Lean_Name_toString(v___x_555_, v___x_556_);
v___x_558_ = ((lean_object*)(l_Lean_findOLean___closed__1));
v___x_559_ = lean_string_append(v___x_558_, v___x_557_);
v___x_560_ = ((lean_object*)(l_Lean_findOLean___closed__2));
v___x_561_ = lean_string_append(v___x_559_, v___x_560_);
v___x_562_ = lean_string_append(v___x_561_, v___x_557_);
v___x_563_ = ((lean_object*)(l_Lean_findOLean___closed__3));
v___x_564_ = lean_string_append(v___x_562_, v___x_563_);
v___x_565_ = lean_string_append(v___x_564_, v___x_557_);
lean_dec_ref(v___x_557_);
v___x_566_ = ((lean_object*)(l_Lean_findLean___closed__0));
v___x_567_ = lean_string_append(v___x_565_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_findOLean___closed__5));
v___x_569_ = lean_box(0);
v___x_570_ = l_List_mapTR_loop___at___00Lean_findOLean_spec__0(v_sp_542_, v___x_569_);
v___x_571_ = l_String_intercalate(v___x_568_, v___x_570_);
v___x_572_ = lean_string_append(v___x_567_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = lean_mk_io_user_error(v___x_572_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 0, v___x_573_);
v___x_575_ = v___x_549_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object* v_sp_578_, lean_object* v_mod_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_findLean(v_sp_578_, v_mod_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath(){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___y_589_; 
v___x_586_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__0));
v___x_587_ = lean_io_getenv(v___x_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_box(0);
v___y_589_ = v___x_619_;
goto v___jp_588_;
}
else
{
lean_object* v_val_620_; lean_object* v___x_621_; 
v_val_620_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v___x_587_, 1);
v___x_621_ = l_System_SearchPath_parse(v_val_620_);
v___y_589_ = v___x_621_;
goto v___jp_588_;
}
v___jp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_IO_appDir();
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_610_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_610_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_610_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_610_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_595_ = ((lean_object*)(l_Lean_getLibDir___closed__2));
v___x_596_ = l_System_FilePath_join(v_a_591_, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__1));
v___x_598_ = l_System_FilePath_join(v___x_596_, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1));
v___x_600_ = l_System_FilePath_join(v___x_598_, v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_getSrcSearchPath___closed__2));
lean_inc_ref(v___x_600_);
v___x_602_ = l_System_FilePath_join(v___x_600_, v___x_601_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_List_appendTR___redArg(v___y_589_, v___x_605_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_606_);
v___x_608_ = v___x_593_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v___y_589_);
v_a_611_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_590_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_590_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_getSrcSearchPath();
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
return v_x_624_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; 
v_head_626_ = lean_ctor_get(v_x_625_, 0);
lean_inc(v_head_626_);
v_tail_627_ = lean_ctor_get(v_x_625_, 1);
lean_inc(v_tail_627_);
lean_dec_ref_known(v_x_625_, 2);
v___x_628_ = l_Lean_Name_str___override(v_x_624_, v_head_626_);
v_x_624_ = v___x_628_;
v_x_625_ = v_tail_627_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__3(void){
_start:
{
uint32_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = l_System_FilePath_pathSeparator;
v___x_634_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_635_ = lean_string_push(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__4(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_637_ = lean_string_utf8_byte_size(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object* v_fname_638_, lean_object* v_rootDir_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_io_realpath(v_fname_638_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_712_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_712_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_712_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_712_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___y_647_; lean_object* v_rootDir_660_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v_rootDir_683_; 
if (lean_obj_tag(v_rootDir_639_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_io_current_dir();
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v_rootDir_683_ = v_a_702_;
goto v___jp_682_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_del_object(v___x_644_);
lean_dec(v_a_642_);
v_a_703_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_701_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_701_);
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
else
{
lean_object* v_val_711_; 
v_val_711_ = lean_ctor_get(v_rootDir_639_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v_rootDir_639_, 1);
v_rootDir_683_ = v_val_711_;
goto v___jp_682_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_648_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__0));
v___x_649_ = lean_string_append(v___x_648_, v_a_642_);
lean_dec(v_a_642_);
v___x_650_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__1));
v___x_651_ = lean_string_append(v___x_649_, v___x_650_);
v___x_652_ = lean_string_append(v___x_651_, v___y_647_);
lean_dec_ref(v___y_647_);
v___x_653_ = ((lean_object*)(l_Lean_moduleNameOfFileName___closed__2));
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
v___x_655_ = lean_mk_io_user_error(v___x_654_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
lean_ctor_set(v___x_644_, 0, v___x_655_);
v___x_657_ = v___x_644_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
lean_inc(v_a_642_);
v___x_661_ = l_System_FilePath_normalize(v_a_642_);
v___x_662_ = lean_string_utf8_byte_size(v___x_661_);
v___x_663_ = lean_string_utf8_byte_size(v_rootDir_660_);
v___x_664_ = lean_nat_dec_le(v___x_663_, v___x_662_);
if (v___x_664_ == 0)
{
lean_dec_ref(v___x_661_);
v___y_647_ = v_rootDir_660_;
goto v___jp_646_;
}
else
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_string_memcmp(v___x_661_, v_rootDir_660_, v___x_665_, v___x_665_, v___x_663_);
lean_dec_ref(v___x_661_);
if (v___x_666_ == 0)
{
v___y_647_ = v_rootDir_660_;
goto v___jp_646_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_del_object(v___x_644_);
v___x_667_ = lean_string_length(v_rootDir_660_);
lean_dec_ref(v_rootDir_660_);
v___x_668_ = lean_string_utf8_byte_size(v_a_642_);
lean_inc(v_a_642_);
v___x_669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_669_, 0, v_a_642_);
lean_ctor_set(v___x_669_, 1, v___x_665_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
v___x_670_ = l_String_Slice_Pos_nextn(v___x_669_, v___x_665_, v___x_667_);
lean_dec_ref_known(v___x_669_, 3);
v___x_671_ = lean_string_utf8_extract_fast(v_a_642_, v___x_670_, v___x_668_);
lean_dec(v___x_670_);
lean_dec(v_a_642_);
v___x_672_ = ((lean_object*)(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3));
v___x_673_ = l_System_FilePath_withExtension(v___x_671_, v___x_672_);
v___x_674_ = lean_box(0);
v___x_675_ = l_System_FilePath_components(v___x_673_);
v___x_676_ = l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(v___x_674_, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
v___jp_678_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_string_append(v___y_679_, v___y_680_);
v_rootDir_660_ = v___x_681_;
goto v___jp_659_;
}
v___jp_682_:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_realPathNormalized(v_rootDir_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__3, &l_Lean_moduleNameOfFileName___closed__3_once, _init_l_Lean_moduleNameOfFileName___closed__3);
v___x_687_ = lean_string_utf8_byte_size(v_a_685_);
v___x_688_ = lean_obj_once(&l_Lean_moduleNameOfFileName___closed__4, &l_Lean_moduleNameOfFileName___closed__4_once, _init_l_Lean_moduleNameOfFileName___closed__4);
v___x_689_ = lean_nat_dec_le(v___x_688_, v___x_687_);
if (v___x_689_ == 0)
{
v___y_679_ = v_a_685_;
v___y_680_ = v___x_686_;
goto v___jp_678_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_nat_sub(v___x_687_, v___x_688_);
v___x_692_ = lean_string_memcmp(v_a_685_, v___x_686_, v___x_691_, v___x_690_, v___x_688_);
lean_dec(v___x_691_);
if (v___x_692_ == 0)
{
v___y_679_ = v_a_685_;
v___y_680_ = v___x_686_;
goto v___jp_678_;
}
else
{
v_rootDir_660_ = v_a_685_;
goto v___jp_659_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_644_);
lean_dec(v_a_642_);
v_a_693_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_684_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_684_);
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
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_rootDir_639_);
v_a_713_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_641_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_641_);
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
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object* v_fname_721_, lean_object* v_rootDir_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_moduleNameOfFileName(v_fname_721_, v_rootDir_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object* v_fname_728_, lean_object* v_as_x27_729_, lean_object* v_b_730_){
_start:
{
if (lean_obj_tag(v_as_x27_729_) == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v_fname_728_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_730_);
return v___x_732_;
}
else
{
lean_object* v_head_733_; lean_object* v_tail_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_b_730_);
v_head_733_ = lean_ctor_get(v_as_x27_729_, 0);
v_tail_734_ = lean_ctor_get(v_as_x27_729_, 1);
v___x_735_ = lean_box(0);
lean_inc(v_head_733_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_head_733_);
lean_inc_ref(v_fname_728_);
v___x_737_ = l_Lean_moduleNameOfFileName(v_fname_728_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v_fname_728_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_748_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_738_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_735_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v___x_749_; 
lean_dec_ref_known(v___x_737_, 1);
v___x_749_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
v_as_x27_729_ = v_tail_734_;
v_b_730_ = v___x_749_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object* v_fname_751_, lean_object* v_as_x27_752_, lean_object* v_b_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_751_, v_as_x27_752_, v_b_753_);
lean_dec(v_as_x27_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object* v_fname_756_, lean_object* v_rootDirs_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_774_; 
v___x_759_ = lean_box(0);
v___x_760_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0));
v___x_761_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_756_, v_rootDirs_757_, v___x_760_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_fst_766_; 
v_fst_766_ = lean_ctor_get(v_a_762_, 0);
lean_inc(v_fst_766_);
lean_dec(v_a_762_);
if (lean_obj_tag(v_fst_766_) == 0)
{
lean_object* v___x_768_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_759_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_759_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v_val_770_; lean_object* v___x_772_; 
v_val_770_ = lean_ctor_get(v_fst_766_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_fst_766_, 1);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_val_770_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_val_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object* v_fname_775_, lean_object* v_rootDirs_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_searchModuleNameOfFileName(v_fname_775_, v_rootDirs_776_);
lean_dec(v_rootDirs_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object* v_fname_779_, lean_object* v_as_780_, lean_object* v_as_x27_781_, lean_object* v_b_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(v_fname_779_, v_as_x27_781_, v_b_782_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object* v_fname_786_, lean_object* v_as_787_, lean_object* v_as_x27_788_, lean_object* v_b_789_, lean_object* v_a_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(v_fname_786_, v_as_787_, v_as_x27_788_, v_b_789_, v_a_790_);
lean_dec(v_as_x27_788_);
lean_dec(v_as_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object* v_lean_803_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_findSysroot___closed__0));
v___x_806_ = lean_io_getenv(v___x_805_);
if (lean_obj_tag(v___x_806_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_lean_803_);
v_val_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 0);
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_val_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v___x_806_);
v___x_815_ = ((lean_object*)(l_Lean_findSysroot___closed__1));
v___x_816_ = ((lean_object*)(l_Lean_findSysroot___closed__3));
v___x_817_ = lean_box(0);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = ((lean_object*)(l_Lean_findSysroot___closed__4));
v___x_820_ = 1;
v___x_821_ = 0;
v___x_822_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_822_, 0, v___x_815_);
lean_ctor_set(v___x_822_, 1, v_lean_803_);
lean_ctor_set(v___x_822_, 2, v___x_816_);
lean_ctor_set(v___x_822_, 3, v___x_817_);
lean_ctor_set(v___x_822_, 4, v___x_819_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*5, v___x_820_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*5 + 1, v___x_821_);
v___x_823_ = l_IO_Process_run(v___x_822_, v___x_817_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_838_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_838_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_str_831_; lean_object* v_startInclusive_832_; lean_object* v_endExclusive_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_828_ = lean_string_utf8_byte_size(v_a_824_);
v___x_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_829_, 0, v_a_824_);
lean_ctor_set(v___x_829_, 1, v___x_818_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
v___x_830_ = l_String_Slice_trimAscii(v___x_829_);
v_str_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_str_831_);
v_startInclusive_832_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_startInclusive_832_);
v_endExclusive_833_ = lean_ctor_get(v___x_830_, 2);
lean_inc(v_endExclusive_833_);
lean_dec_ref(v___x_830_);
v___x_834_ = lean_string_utf8_extract_fast(v_str_831_, v_startInclusive_832_, v_endExclusive_833_);
lean_dec(v_endExclusive_833_);
lean_dec(v_startInclusive_832_);
lean_dec_ref(v_str_831_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_834_);
v___x_836_ = v___x_826_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_823_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_823_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object* v_lean_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_findSysroot(v_lean_847_);
return v_res_849_;
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
