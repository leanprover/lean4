// Lean compiler output
// Module: Lake.Config.Module
// Imports: public import Lake.Config.LeanLib
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lake_OrdHashSet_empty___redArg();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_Package_id_x3f(lean_object*);
lean_object* l_Lean_mkModuleInitializationStem(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_LeanOptions_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
uint8_t l_Lake_instOrdBuildType_ord(uint8_t, uint8_t);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_BuildType_leanArgs___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_internal_has_llvm_backend(lean_object*);
lean_object* l_Lake_BuildType_leancArgs(uint8_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_relPathFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_keyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_keyName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonModule___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToJsonModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToJsonModule___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonModule___closed__0 = (const lean_object*)&l_Lake_instToJsonModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonModule = (const lean_object*)&l_Lake_instToJsonModule___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToStringModule___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToStringModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToStringModule___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToStringModule___closed__0 = (const lean_object*)&l_Lake_instToStringModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringModule = (const lean_object*)&l_Lake_instToStringModule___closed__0_value;
LEAN_EXPORT uint64_t l_Lake_instHashableModule___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableModule___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instHashableModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instHashableModule___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instHashableModule___closed__0 = (const lean_object*)&l_Lake_instHashableModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instHashableModule = (const lean_object*)&l_Lake_instHashableModule___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instBEqModule___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqModule___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instBEqModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instBEqModule___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instBEqModule___closed__0 = (const lean_object*)&l_Lake_instBEqModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instBEqModule = (const lean_object*)&l_Lake_instBEqModule___closed__0_value;
static lean_once_cell_t l_Lake_ModuleSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ModuleSet_empty___closed__0;
static lean_once_cell_t l_Lake_ModuleSet_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ModuleSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Lake_ModuleSet_empty;
static lean_once_cell_t l_Lake_OrdModuleSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdModuleSet_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_OrdModuleSet_empty;
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lean"};
static const lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0 = (const lean_object*)&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1;
static lean_once_cell_t l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModuleBySrc_x3f(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Package_findModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_findModule_x3f___closed__0 = (const lean_object*)&l_Lake_Package_findModule_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanLib_getModuleArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanLib_getModuleArray___closed__0 = (const lean_object*)&l_Lake_LeanLib_getModuleArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object*);
static const lean_string_object l_Lake_Module_oleanFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_Lake_Module_oleanFile___closed__0 = (const lean_object*)&l_Lake_Module_oleanFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object*);
static const lean_string_object l_Lake_Module_oleanServerFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "olean.server"};
static const lean_object* l_Lake_Module_oleanServerFile___closed__0 = (const lean_object*)&l_Lake_Module_oleanServerFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object*);
static const lean_string_object l_Lake_Module_oleanPrivateFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "olean.private"};
static const lean_object* l_Lake_Module_oleanPrivateFile___closed__0 = (const lean_object*)&l_Lake_Module_oleanPrivateFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object*);
static const lean_string_object l_Lake_Module_ileanFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ilean"};
static const lean_object* l_Lake_Module_ileanFile___closed__0 = (const lean_object*)&l_Lake_Module_ileanFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object*);
static const lean_string_object l_Lake_Module_irSigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ir.sig"};
static const lean_object* l_Lake_Module_irSigFile___closed__0 = (const lean_object*)&l_Lake_Module_irSigFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object*);
static const lean_string_object l_Lake_Module_irFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lake_Module_irFile___closed__0 = (const lean_object*)&l_Lake_Module_irFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object*);
static const lean_string_object l_Lake_Module_traceFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lake_Module_traceFile___closed__0 = (const lean_object*)&l_Lake_Module_traceFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object*);
static const lean_string_object l_Lake_Module_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setup.json"};
static const lean_object* l_Lake_Module_setupFile___closed__0 = (const lean_object*)&l_Lake_Module_setupFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object*);
static const lean_string_object l_Lake_Module_cFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lake_Module_cFile___closed__0 = (const lean_object*)&l_Lake_Module_cFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object*);
static const lean_string_object l_Lake_Module_coExportFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "c.o.export"};
static const lean_object* l_Lake_Module_coExportFile___closed__0 = (const lean_object*)&l_Lake_Module_coExportFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object*);
static const lean_string_object l_Lake_Module_coNoExportFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "c.o.noexport"};
static const lean_object* l_Lake_Module_coNoExportFile___closed__0 = (const lean_object*)&l_Lake_Module_coNoExportFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object*);
static const lean_string_object l_Lake_Module_bcFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bc"};
static const lean_object* l_Lake_Module_bcFile___closed__0 = (const lean_object*)&l_Lake_Module_bcFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object*);
static lean_once_cell_t l_Lake_Module_bcFile_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Module_bcFile_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object*);
static const lean_string_object l_Lake_Module_bcoFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bc.o"};
static const lean_object* l_Lake_Module_bcoFile___closed__0 = (const lean_object*)&l_Lake_Module_bcoFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object*);
static const lean_string_object l_Lake_Module_ltarFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ltar"};
static const lean_object* l_Lake_Module_ltarFile___closed__0 = (const lean_object*)&l_Lake_Module_ltarFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object*);
static const lean_string_object l_Lake_Module_dynlibSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-1"};
static const lean_object* l_Lake_Module_dynlibSuffix___closed__0 = (const lean_object*)&l_Lake_Module_dynlibSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Module_dynlibSuffix = (const lean_object*)&l_Lake_Module_dynlibSuffix___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object*);
static const lean_string_object l_Lake_Module_dynlibFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Module_dynlibFile___closed__0 = (const lean_object*)&l_Lake_Module_dynlibFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_requiresModuleSystem(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_allowNonModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object*);
static lean_once_cell_t l_Lake_Module_leanArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Module_leanArgs___closed__0;
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object*);
static const lean_string_object l_Lake_Module_leanIncludeDir_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lake_Module_leanIncludeDir_x3f___closed__0 = (const lean_object*)&l_Lake_Module_leanIncludeDir_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompileImports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompileImports___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_keyName(lean_object* v_self_1_){
_start:
{
lean_object* v_name_2_; 
v_name_2_ = lean_ctor_get(v_self_1_, 1);
lean_inc(v_name_2_);
return v_name_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_keyName___boxed(lean_object* v_self_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_Module_keyName(v_self_3_);
lean_dec_ref(v_self_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonModule___lam__0(lean_object* v_x_5_){
_start:
{
lean_object* v_name_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_name_6_ = lean_ctor_get(v_x_5_, 1);
lean_inc(v_name_6_);
lean_dec_ref(v_x_5_);
v___x_7_ = 1;
v___x_8_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_6_, v___x_7_);
v___x_9_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringModule___lam__0(lean_object* v_x_12_){
_start:
{
lean_object* v_name_13_; uint8_t v___x_14_; lean_object* v___x_15_; 
v_name_13_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_name_13_);
lean_dec_ref(v_x_12_);
v___x_14_ = 1;
v___x_15_ = l_Lean_Name_toString(v_name_13_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashableModule___lam__0(lean_object* v_m_18_){
_start:
{
lean_object* v_name_19_; 
v_name_19_ = lean_ctor_get(v_m_18_, 1);
if (lean_obj_tag(v_name_19_) == 0)
{
uint64_t v___x_20_; 
v___x_20_ = 1723ULL;
return v___x_20_;
}
else
{
uint64_t v_hash_21_; 
v_hash_21_ = lean_ctor_get_uint64(v_name_19_, sizeof(void*)*2);
return v_hash_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableModule___lam__0___boxed(lean_object* v_m_22_){
_start:
{
uint64_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Lake_instHashableModule___lam__0(v_m_22_);
lean_dec_ref(v_m_22_);
v_r_24_ = lean_box_uint64(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqModule___lam__0(lean_object* v_m_27_, lean_object* v_n_28_){
_start:
{
lean_object* v_name_29_; lean_object* v_name_30_; uint8_t v___x_31_; 
v_name_29_ = lean_ctor_get(v_m_27_, 1);
v_name_30_ = lean_ctor_get(v_n_28_, 1);
v___x_31_ = lean_name_eq(v_name_29_, v_name_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqModule___lam__0___boxed(lean_object* v_m_32_, lean_object* v_n_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Lake_instBEqModule___lam__0(v_m_32_, v_n_33_);
lean_dec_ref(v_n_33_);
lean_dec_ref(v_m_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = lean_unsigned_to_nat(16u);
v___x_40_ = lean_mk_array(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Lake_ModuleSet_empty___closed__0, &l_Lake_ModuleSet_empty___closed__0_once, _init_l_Lake_ModuleSet_empty___closed__0);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Lake_ModuleSet_empty___closed__1, &l_Lake_ModuleSet_empty___closed__1_once, _init_l_Lake_ModuleSet_empty___closed__1);
return v___x_44_;
}
}
static lean_object* _init_l_Lake_OrdModuleSet_empty___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lake_OrdHashSet_empty___redArg();
return v___x_45_;
}
}
static lean_object* _init_l_Lake_OrdModuleSet_empty(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Lake_OrdModuleSet_empty___closed__0, &l_Lake_OrdModuleSet_empty___closed__0_once, _init_l_Lake_OrdModuleSet_empty___closed__0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty___redArg(){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(1);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty___redArg___boxed(lean_object* v___dummy_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_ModuleMap_empty___redArg();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty(lean_object* v_00_u03b1_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(1);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModule_x3f(lean_object* v_mod_53_, lean_object* v_self_54_){
_start:
{
lean_object* v_config_55_; uint8_t v___x_56_; 
v_config_55_ = lean_ctor_get(v_self_54_, 2);
v___x_56_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_53_, v_config_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v_self_54_);
lean_dec(v_mod_53_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v_self_54_);
lean_ctor_set(v___x_58_, 1, v_mod_53_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(lean_object* v___x_60_, lean_object* v_s_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_string_utf8_byte_size(v_s_61_);
v___x_63_ = lean_string_utf8_byte_size(v___x_60_);
v___x_64_ = lean_nat_dec_le(v___x_63_, v___x_62_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_dec_ref(v_s_61_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_string_memcmp(v_s_61_, v___x_60_, v___x_66_, v___x_66_, v___x_63_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_s_61_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_inc_ref(v_s_61_);
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_s_61_);
lean_ctor_set(v___x_69_, 1, v___x_66_);
lean_ctor_set(v___x_69_, 2, v___x_62_);
v___x_70_ = l_String_Slice_pos_x21(v___x_69_, v___x_63_);
lean_dec_ref_known(v___x_69_, 3);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v_s_61_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
lean_ctor_set(v___x_71_, 2, v___x_62_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object* v___x_73_, lean_object* v_s_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_73_, v_s_74_);
lean_dec_ref(v___x_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(lean_object* v___x_76_, lean_object* v_s_77_, lean_object* v_pat_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_76_, v_s_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___boxed(lean_object* v___x_80_, lean_object* v_s_81_, lean_object* v_pat_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(v___x_80_, v_s_81_, v_pat_82_);
lean_dec_ref(v_pat_82_);
lean_dec_ref(v___x_80_);
return v_res_83_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0));
v___x_86_ = lean_string_utf8_byte_size(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(lean_object* v_s_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0));
v___x_89_ = lean_string_utf8_byte_size(v_s_87_);
v___x_90_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1);
v___x_91_ = lean_nat_dec_le(v___x_90_, v___x_89_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v_s_87_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_nat_sub(v___x_89_, v___x_90_);
v___x_95_ = lean_string_memcmp(v_s_87_, v___x_88_, v___x_94_, v___x_93_, v___x_90_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec(v___x_94_);
lean_dec_ref(v_s_87_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
lean_inc_ref(v_s_87_);
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v_s_87_);
lean_ctor_set(v___x_97_, 1, v___x_93_);
lean_ctor_set(v___x_97_, 2, v___x_89_);
v___x_98_ = l_String_Slice_pos_x21(v___x_97_, v___x_94_);
lean_dec(v___x_94_);
lean_dec_ref_known(v___x_97_, 3);
v___x_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_99_, 0, v_s_87_);
lean_ctor_set(v___x_99_, 1, v___x_93_);
lean_ctor_set(v___x_99_, 2, v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(lean_object* v_s_101_, lean_object* v_pat_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v_s_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___boxed(lean_object* v_s_104_, lean_object* v_pat_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(v_s_104_, v_pat_105_);
lean_dec_ref(v_pat_105_);
return v_res_106_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1(void){
_start:
{
uint32_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = l_System_FilePath_pathSeparator;
v___x_109_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_110_ = lean_string_push(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
v___x_112_ = lean_string_utf8_byte_size(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(lean_object* v_s_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_114_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
v___x_115_ = lean_string_utf8_byte_size(v_s_113_);
v___x_116_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2);
v___x_117_ = lean_nat_dec_le(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v_s_113_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_sub(v___x_115_, v___x_116_);
v___x_121_ = lean_string_memcmp(v_s_113_, v___x_114_, v___x_120_, v___x_119_, v___x_116_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v___x_120_);
lean_dec_ref(v_s_113_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
lean_inc_ref(v_s_113_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_s_113_);
lean_ctor_set(v___x_123_, 1, v___x_119_);
lean_ctor_set(v___x_123_, 2, v___x_115_);
v___x_124_ = l_String_Slice_pos_x21(v___x_123_, v___x_120_);
lean_dec(v___x_120_);
lean_dec_ref_known(v___x_123_, 3);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v_s_113_);
lean_ctor_set(v___x_125_, 1, v___x_119_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(lean_object* v_s_127_, lean_object* v_pat_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v_s_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___boxed(lean_object* v_s_130_, lean_object* v_pat_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(v_s_130_, v_pat_131_);
lean_dec_ref(v_pat_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
return v_x_133_;
}
else
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v___x_137_; 
v_head_135_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_head_135_);
v_tail_136_ = lean_ctor_get(v_x_134_, 1);
lean_inc(v_tail_136_);
lean_dec_ref_known(v_x_134_, 2);
v___x_137_ = l_Lean_Name_str___override(v_x_133_, v_head_135_);
v_x_133_ = v___x_137_;
v_x_134_ = v_tail_136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModuleBySrc_x3f(lean_object* v_path_139_, lean_object* v_self_140_){
_start:
{
lean_object* v___y_142_; lean_object* v_pkg_150_; lean_object* v_config_151_; lean_object* v_config_152_; lean_object* v_dir_153_; lean_object* v_srcDir_154_; lean_object* v_srcDir_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_pkg_150_ = lean_ctor_get(v_self_140_, 0);
v_config_151_ = lean_ctor_get(v_pkg_150_, 6);
v_config_152_ = lean_ctor_get(v_self_140_, 2);
v_dir_153_ = lean_ctor_get(v_pkg_150_, 4);
v_srcDir_154_ = lean_ctor_get(v_config_151_, 4);
v_srcDir_155_ = lean_ctor_get(v_config_152_, 1);
lean_inc_ref(v_srcDir_154_);
v___x_156_ = l_System_FilePath_normalize(v_srcDir_154_);
lean_inc_ref(v_dir_153_);
v___x_157_ = l_Lake_joinRelative(v_dir_153_, v___x_156_);
lean_inc_ref(v_srcDir_155_);
v___x_158_ = l_System_FilePath_normalize(v_srcDir_155_);
v___x_159_ = l_Lake_joinRelative(v___x_157_, v___x_158_);
v___x_160_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_159_, v_path_139_);
lean_dec_ref(v___x_159_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v_self_140_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v_str_163_; lean_object* v_startInclusive_164_; lean_object* v_endExclusive_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_179_; 
v_val_162_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_160_, 1);
v_str_163_ = lean_ctor_get(v_val_162_, 0);
lean_inc_ref(v_str_163_);
v_startInclusive_164_ = lean_ctor_get(v_val_162_, 1);
lean_inc(v_startInclusive_164_);
v_endExclusive_165_ = lean_ctor_get(v_val_162_, 2);
lean_inc(v_endExclusive_165_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_String_Slice_Pos_nextn(v_val_162_, v___x_167_, v___x_166_);
v_isSharedCheck_179_ = !lean_is_exclusive(v_val_162_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; 
v_unused_180_ = lean_ctor_get(v_val_162_, 2);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_val_162_, 1);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_val_162_, 0);
lean_dec(v_unused_182_);
v___x_170_ = v_val_162_;
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_val_162_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_nat_add(v_startInclusive_164_, v___x_168_);
lean_dec(v___x_168_);
lean_dec(v_startInclusive_164_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_str_163_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_endExclusive_165_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_String_Slice_toString(v___x_174_);
lean_dec_ref(v___x_174_);
lean_inc_ref(v___x_175_);
v___x_176_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v___x_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; 
v___x_177_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v___x_175_);
v___y_142_ = v___x_177_;
goto v___jp_141_;
}
else
{
lean_dec_ref(v___x_175_);
v___y_142_ = v___x_176_;
goto v___jp_141_;
}
}
}
}
v___jp_141_:
{
if (lean_obj_tag(v___y_142_) == 0)
{
lean_object* v___x_143_; 
lean_dec_ref(v_self_140_);
v___x_143_ = lean_box(0);
return v___x_143_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_val_144_ = lean_ctor_get(v___y_142_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___y_142_, 1);
v___x_145_ = lean_box(0);
v___x_146_ = l_String_Slice_toString(v_val_144_);
lean_dec(v_val_144_);
v___x_147_ = l_System_FilePath_components(v___x_146_);
v___x_148_ = l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(v___x_145_, v___x_147_);
v___x_149_ = l_Lake_LeanLib_findModule_x3f(v___x_148_, v_self_140_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(lean_object* v_self_186_, lean_object* v_as_187_, size_t v_i_188_, size_t v_stop_189_, lean_object* v_b_190_){
_start:
{
lean_object* v___y_192_; uint8_t v___x_196_; 
v___x_196_ = lean_usize_dec_eq(v_i_188_, v_stop_189_);
if (v___x_196_ == 0)
{
lean_object* v_toConfigDecl_197_; lean_object* v_name_198_; lean_object* v_kind_199_; lean_object* v_config_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_toConfigDecl_197_ = lean_array_uget_borrowed(v_as_187_, v_i_188_);
v_name_198_ = lean_ctor_get(v_toConfigDecl_197_, 1);
v_kind_199_ = lean_ctor_get(v_toConfigDecl_197_, 2);
v_config_200_ = lean_ctor_get(v_toConfigDecl_197_, 3);
v___x_201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1));
v___x_202_ = lean_name_eq(v_kind_199_, v___x_201_);
if (v___x_202_ == 0)
{
v___y_192_ = v_b_190_;
goto v___jp_191_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc(v_config_200_);
lean_inc(v_name_198_);
lean_inc_ref(v_self_186_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v_self_186_);
lean_ctor_set(v___x_203_, 1, v_name_198_);
lean_ctor_set(v___x_203_, 2, v_config_200_);
v___x_204_ = lean_array_push(v_b_190_, v___x_203_);
v___y_192_ = v___x_204_;
goto v___jp_191_;
}
}
else
{
lean_dec_ref(v_self_186_);
return v_b_190_;
}
v___jp_191_:
{
size_t v___x_193_; size_t v___x_194_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_188_, v___x_193_);
v_i_188_ = v___x_194_;
v_b_190_ = v___y_192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___boxed(lean_object* v_self_205_, lean_object* v_as_206_, lean_object* v_i_207_, lean_object* v_stop_208_, lean_object* v_b_209_){
_start:
{
size_t v_i_boxed_210_; size_t v_stop_boxed_211_; lean_object* v_res_212_; 
v_i_boxed_210_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_stop_boxed_211_ = lean_unbox_usize(v_stop_208_);
lean_dec(v_stop_208_);
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_205_, v_as_206_, v_i_boxed_210_, v_stop_boxed_211_, v_b_209_);
lean_dec_ref(v_as_206_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(lean_object* v_mod_213_, lean_object* v_as_214_, lean_object* v_i_215_){
_start:
{
lean_object* v_zero_216_; uint8_t v_isZero_217_; 
v_zero_216_ = lean_unsigned_to_nat(0u);
v_isZero_217_ = lean_nat_dec_eq(v_i_215_, v_zero_216_);
if (v_isZero_217_ == 1)
{
lean_object* v___x_218_; 
lean_dec(v_i_215_);
lean_dec(v_mod_213_);
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_one_219_; lean_object* v_n_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_one_219_ = lean_unsigned_to_nat(1u);
v_n_220_ = lean_nat_sub(v_i_215_, v_one_219_);
lean_dec(v_i_215_);
v___x_221_ = lean_array_fget_borrowed(v_as_214_, v_n_220_);
lean_inc(v___x_221_);
lean_inc(v_mod_213_);
v___x_222_ = l_Lake_LeanLib_findModule_x3f(v_mod_213_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
v_i_215_ = v_n_220_;
goto _start;
}
else
{
lean_dec(v_n_220_);
lean_dec(v_mod_213_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_224_, lean_object* v_as_225_, lean_object* v_i_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_224_, v_as_225_, v_i_226_);
lean_dec_ref(v_as_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object* v_mod_230_, lean_object* v_self_231_){
_start:
{
lean_object* v___y_233_; lean_object* v_targetDecls_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_targetDecls_236_ = lean_ctor_get(v_self_231_, 15);
lean_inc_ref(v_targetDecls_236_);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = ((lean_object*)(l_Lake_Package_findModule_x3f___closed__0));
v___x_239_ = lean_array_get_size(v_targetDecls_236_);
v___x_240_ = lean_nat_dec_lt(v___x_237_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec_ref(v_targetDecls_236_);
lean_dec_ref(v_self_231_);
v___y_233_ = v___x_238_;
goto v___jp_232_;
}
else
{
size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; 
v___x_241_ = ((size_t)0ULL);
v___x_242_ = lean_usize_of_nat(v___x_239_);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_231_, v_targetDecls_236_, v___x_241_, v___x_242_, v___x_238_);
lean_dec_ref(v_targetDecls_236_);
v___y_233_ = v___x_243_;
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_array_get_size(v___y_233_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_230_, v___y_233_, v___x_234_);
lean_dec_ref(v___y_233_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(lean_object* v_mod_244_, lean_object* v_as_245_, lean_object* v_i_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_244_, v_as_245_, v_i_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(lean_object* v_mod_249_, lean_object* v_as_250_, lean_object* v_i_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_249_, v_as_250_, v_i_251_, v_a_252_);
lean_dec_ref(v_as_250_);
return v_res_253_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
if (lean_obj_tag(v_x_255_) == 0)
{
uint8_t v___x_256_; 
v___x_256_ = 1;
return v___x_256_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
else
{
if (lean_obj_tag(v_x_255_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v_val_260_; uint8_t v___x_261_; 
v_val_259_ = lean_ctor_get(v_x_254_, 0);
v_val_260_ = lean_ctor_get(v_x_255_, 0);
v___x_261_ = lean_string_dec_eq(v_val_259_, v_val_260_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_262_, v_x_263_);
lean_dec(v_x_263_);
lean_dec(v_x_262_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object* v___x_266_, lean_object* v_f_267_, lean_object* v_x_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = l_Lean_Name_append(v___x_266_, v_x_268_);
v___x_272_ = lean_apply_3(v_f_267_, v___x_271_, v___y_269_, lean_box(0));
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object* v___x_273_, lean_object* v_f_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_273_, v_f_274_, v_x_275_, v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object* v_f_282_, lean_object* v_as_283_, size_t v_sz_284_, size_t v_i_285_, lean_object* v_b_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_a_290_; lean_object* v_snd_291_; uint8_t v___x_295_; 
v___x_295_ = lean_usize_dec_lt(v_i_285_, v_sz_284_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref(v_f_282_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_b_286_);
lean_ctor_set(v___x_296_, 1, v___y_287_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_298_ = lean_box(0);
v_a_299_ = lean_array_uget_borrowed(v_as_283_, v_i_285_);
lean_inc(v_a_299_);
v___x_300_ = l_IO_FS_DirEntry_path(v_a_299_);
v___x_301_ = l_System_FilePath_isDir(v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = l_System_FilePath_extension(v___x_300_);
v___x_303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1));
v___x_304_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
if (v___x_304_ == 0)
{
v_a_290_ = v___x_298_;
v_snd_291_ = v___y_287_;
goto v___jp_289_;
}
else
{
lean_object* v_fileName_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_fileName_305_ = lean_ctor_get(v_a_299_, 1);
v___x_306_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc_ref(v_fileName_305_);
v___x_307_ = l_System_FilePath_withExtension(v_fileName_305_, v___x_306_);
v___x_308_ = lean_box(0);
v___x_309_ = l_Lean_Name_str___override(v___x_308_, v___x_307_);
lean_inc_ref(v_f_282_);
v___x_310_ = lean_apply_3(v_f_282_, v___x_309_, v___y_287_, lean_box(0));
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v_snd_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v_snd_312_ = lean_ctor_get(v_a_311_, 1);
lean_inc(v_snd_312_);
lean_dec(v_a_311_);
v_a_290_ = v___x_298_;
v_snd_291_ = v_snd_312_;
goto v___jp_289_;
}
else
{
lean_dec_ref(v_f_282_);
return v___x_310_;
}
}
}
else
{
lean_object* v_fileName_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___f_316_; lean_object* v___x_317_; 
v_fileName_313_ = lean_ctor_get(v_a_299_, 1);
v___x_314_ = lean_box(0);
lean_inc_ref(v_fileName_313_);
v___x_315_ = l_Lean_Name_str___override(v___x_314_, v_fileName_313_);
lean_inc_ref(v_f_282_);
v___f_316_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_316_, 0, v___x_315_);
lean_closure_set(v___f_316_, 1, v_f_282_);
v___x_317_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_300_, v___f_316_, v___y_287_);
lean_dec_ref(v___x_300_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v_snd_319_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_snd_319_ = lean_ctor_get(v_a_318_, 1);
lean_inc(v_snd_319_);
lean_dec(v_a_318_);
v_a_290_ = v___x_298_;
v_snd_291_ = v_snd_319_;
goto v___jp_289_;
}
else
{
lean_dec_ref(v_f_282_);
return v___x_317_;
}
}
}
v___jp_289_:
{
size_t v___x_292_; size_t v___x_293_; 
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_add(v_i_285_, v___x_292_);
v_i_285_ = v___x_293_;
v_b_286_ = v_a_290_;
v___y_287_ = v_snd_291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object* v_dir_320_, lean_object* v_f_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_io_read_dir(v_dir_320_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; size_t v_sz_327_; size_t v___x_328_; lean_object* v___x_329_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_box(0);
v_sz_327_ = lean_array_size(v_a_325_);
v___x_328_ = ((size_t)0ULL);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_321_, v_a_325_, v_sz_327_, v___x_328_, v___x_326_, v___y_322_);
lean_dec(v_a_325_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_346_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_346_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_346_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_346_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_snd_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_344_; 
v_snd_334_ = lean_ctor_get(v_a_330_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v_a_330_, 0);
lean_dec(v_unused_345_);
v___x_336_ = v_a_330_;
v_isShared_337_ = v_isSharedCheck_344_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_334_);
lean_dec(v_a_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_344_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_326_);
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_snd_334_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_339_);
v___x_341_ = v___x_332_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
return v___x_329_;
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___y_322_);
lean_dec_ref(v_f_321_);
v_a_347_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_324_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_324_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object* v_dir_355_, lean_object* v_f_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_355_, v_f_356_, v___y_357_);
lean_dec_ref(v_dir_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object* v_f_360_, lean_object* v_as_361_, lean_object* v_sz_362_, lean_object* v_i_363_, lean_object* v_b_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
size_t v_sz_boxed_367_; size_t v_i_boxed_368_; lean_object* v_res_369_; 
v_sz_boxed_367_ = lean_unbox_usize(v_sz_362_);
lean_dec(v_sz_362_);
v_i_boxed_368_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_360_, v_as_361_, v_sz_boxed_367_, v_i_boxed_368_, v_b_364_, v___y_365_);
lean_dec_ref(v_as_361_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object* v_self_370_, lean_object* v_mod_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_374_ = lean_box(0);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_self_370_);
lean_ctor_set(v___x_375_, 1, v_mod_371_);
v___x_376_ = lean_array_push(v___y_372_, v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object* v_self_379_, lean_object* v_mod_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_379_, v_mod_380_, v___y_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object* v_a_384_, lean_object* v___f_385_, lean_object* v_x_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = l_Lean_Name_append(v_a_384_, v_x_386_);
v___x_390_ = lean_apply_3(v___f_385_, v___x_389_, v___y_387_, lean_box(0));
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object* v_a_391_, lean_object* v___f_392_, lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_391_, v___f_392_, v_x_393_, v___y_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object* v_self_397_, lean_object* v_as_398_, size_t v_i_399_, size_t v_stop_400_, lean_object* v_b_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___y_405_; uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_eq(v_i_399_, v_stop_400_);
if (v___x_412_ == 0)
{
lean_object* v_pkg_413_; lean_object* v_config_414_; lean_object* v_config_415_; lean_object* v_dir_416_; lean_object* v_srcDir_417_; lean_object* v_srcDir_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_pkg_413_ = lean_ctor_get(v_self_397_, 0);
v_config_414_ = lean_ctor_get(v_pkg_413_, 6);
v_config_415_ = lean_ctor_get(v_self_397_, 2);
v_dir_416_ = lean_ctor_get(v_pkg_413_, 4);
v_srcDir_417_ = lean_ctor_get(v_config_414_, 4);
v_srcDir_418_ = lean_ctor_get(v_config_415_, 1);
lean_inc_ref(v_self_397_);
v___f_419_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(v___f_419_, 0, v_self_397_);
v___x_420_ = lean_array_uget_borrowed(v_as_398_, v_i_399_);
lean_inc_ref(v_srcDir_417_);
v___x_421_ = l_System_FilePath_normalize(v_srcDir_417_);
lean_inc_ref(v_dir_416_);
v___x_422_ = l_Lake_joinRelative(v_dir_416_, v___x_421_);
lean_inc_ref(v_srcDir_418_);
v___x_423_ = l_System_FilePath_normalize(v_srcDir_418_);
v___x_424_ = l_Lake_joinRelative(v___x_422_, v___x_423_);
switch(lean_obj_tag(v___x_420_))
{
case 0:
{
lean_object* v_a_425_; lean_object* v___x_426_; 
lean_dec_ref(v___x_424_);
lean_dec_ref(v___f_419_);
v_a_425_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_425_);
lean_inc_ref(v_self_397_);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_397_, v_a_425_, v___y_402_);
v___y_405_ = v___x_426_;
goto v___jp_404_;
}
case 1:
{
lean_object* v_a_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_a_427_ = lean_ctor_get(v___x_420_, 0);
lean_inc_n(v_a_427_, 2);
v___f_428_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_428_, 0, v_a_427_);
lean_closure_set(v___f_428_, 1, v___f_419_);
v___x_429_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_430_ = l_Lean_modToFilePath(v___x_424_, v_a_427_, v___x_429_);
lean_dec_ref(v___x_424_);
v___x_431_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_430_, v___f_428_, v___y_402_);
lean_dec_ref(v___x_430_);
v___y_405_ = v___x_431_;
goto v___jp_404_;
}
default: 
{
lean_object* v_a_432_; lean_object* v___f_433_; lean_object* v___x_434_; 
v_a_432_ = lean_ctor_get(v___x_420_, 0);
lean_inc_n(v_a_432_, 2);
v___f_433_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_433_, 0, v_a_432_);
lean_closure_set(v___f_433_, 1, v___f_419_);
lean_inc_ref(v_self_397_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_397_, v_a_432_, v___y_402_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v_snd_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v_snd_436_ = lean_ctor_get(v_a_435_, 1);
lean_inc(v_snd_436_);
lean_dec(v_a_435_);
v___x_437_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc(v_a_432_);
v___x_438_ = l_Lean_modToFilePath(v___x_424_, v_a_432_, v___x_437_);
lean_dec_ref(v___x_424_);
v___x_439_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_438_, v___f_433_, v_snd_436_);
lean_dec_ref(v___x_438_);
v___y_405_ = v___x_439_;
goto v___jp_404_;
}
else
{
lean_dec_ref(v___f_433_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v_self_397_);
return v___x_434_;
}
}
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref(v_self_397_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_b_401_);
lean_ctor_set(v___x_440_, 1, v___y_402_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
v___jp_404_:
{
if (lean_obj_tag(v___y_405_) == 0)
{
lean_object* v_a_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; size_t v___x_409_; size_t v___x_410_; 
v_a_406_ = lean_ctor_get(v___y_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___y_405_, 1);
v_fst_407_ = lean_ctor_get(v_a_406_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v_a_406_, 1);
lean_inc(v_snd_408_);
lean_dec(v_a_406_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_add(v_i_399_, v___x_409_);
v_i_399_ = v___x_410_;
v_b_401_ = v_fst_407_;
v___y_402_ = v_snd_408_;
goto _start;
}
else
{
lean_dec_ref(v_self_397_);
return v___y_405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object* v_self_442_, lean_object* v_as_443_, lean_object* v_i_444_, lean_object* v_stop_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
size_t v_i_boxed_449_; size_t v_stop_boxed_450_; lean_object* v_res_451_; 
v_i_boxed_449_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_stop_boxed_450_ = lean_unbox_usize(v_stop_445_);
lean_dec(v_stop_445_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_442_, v_as_443_, v_i_boxed_449_, v_stop_boxed_450_, v_b_446_, v___y_447_);
lean_dec_ref(v_as_443_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object* v_self_454_){
_start:
{
lean_object* v___y_457_; lean_object* v_config_475_; lean_object* v_globs_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_config_475_ = lean_ctor_get(v_self_454_, 2);
v_globs_476_ = lean_ctor_get(v_config_475_, 3);
lean_inc_ref(v_globs_476_);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_array_get_size(v_globs_476_);
v___x_479_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_480_ = lean_nat_dec_lt(v___x_477_, v___x_478_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v_globs_476_);
lean_dec_ref(v_self_454_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_box(0);
v___x_483_ = lean_nat_dec_le(v___x_478_, v___x_478_);
if (v___x_483_ == 0)
{
if (v___x_480_ == 0)
{
lean_object* v___x_484_; 
lean_dec_ref(v_globs_476_);
lean_dec_ref(v_self_454_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_479_);
return v___x_484_;
}
else
{
size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((size_t)0ULL);
v___x_486_ = lean_usize_of_nat(v___x_478_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_454_, v_globs_476_, v___x_485_, v___x_486_, v___x_482_, v___x_479_);
lean_dec_ref(v_globs_476_);
v___y_457_ = v___x_487_;
goto v___jp_456_;
}
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((size_t)0ULL);
v___x_489_ = lean_usize_of_nat(v___x_478_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_454_, v_globs_476_, v___x_488_, v___x_489_, v___x_482_, v___x_479_);
lean_dec_ref(v_globs_476_);
v___y_457_ = v___x_490_;
goto v___jp_456_;
}
}
v___jp_456_:
{
if (lean_obj_tag(v___y_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_458_ = lean_ctor_get(v___y_457_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___y_457_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___y_457_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___y_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_snd_462_; lean_object* v___x_464_; 
v_snd_462_ = lean_ctor_get(v_a_458_, 1);
lean_inc(v_snd_462_);
lean_dec(v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v_snd_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_snd_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_a_467_ = lean_ctor_get(v___y_457_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___y_457_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___y_457_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___y_457_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object* v_self_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lake_LeanLib_getModuleArray(v_self_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object* v_self_494_, lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_){
_start:
{
lean_object* v___y_500_; uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
lean_inc_ref(v_self_494_);
lean_inc(v___x_505_);
v___x_506_ = l_Lake_LeanLib_findModule_x3f(v___x_505_, v_self_494_);
if (lean_obj_tag(v___x_506_) == 0)
{
v___y_500_ = v_b_498_;
goto v___jp_499_;
}
else
{
lean_object* v_val_507_; lean_object* v___x_508_; 
v_val_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_array_push(v_b_498_, v_val_507_);
v___y_500_ = v___x_508_;
goto v___jp_499_;
}
}
else
{
lean_dec_ref(v_self_494_);
return v_b_498_;
}
v___jp_499_:
{
size_t v___x_501_; size_t v___x_502_; 
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_496_, v___x_501_);
v_i_496_ = v___x_502_;
v_b_498_ = v___y_500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object* v_self_509_, lean_object* v_as_510_, lean_object* v_i_511_, lean_object* v_stop_512_, lean_object* v_b_513_){
_start:
{
size_t v_i_boxed_514_; size_t v_stop_boxed_515_; lean_object* v_res_516_; 
v_i_boxed_514_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_stop_boxed_515_ = lean_unbox_usize(v_stop_512_);
lean_dec(v_stop_512_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_509_, v_as_510_, v_i_boxed_514_, v_stop_boxed_515_, v_b_513_);
lean_dec_ref(v_as_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object* v_self_517_, lean_object* v_as_518_, lean_object* v_start_519_, lean_object* v_stop_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_522_ = lean_nat_dec_lt(v_start_519_, v_stop_520_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_self_517_);
return v___x_521_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_array_get_size(v_as_518_);
v___x_524_ = lean_nat_dec_le(v_stop_520_, v___x_523_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; 
v___x_525_ = lean_nat_dec_lt(v_start_519_, v___x_523_);
if (v___x_525_ == 0)
{
lean_dec_ref(v_self_517_);
return v___x_521_;
}
else
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_usize_of_nat(v_start_519_);
v___x_527_ = lean_usize_of_nat(v___x_523_);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_517_, v_as_518_, v___x_526_, v___x_527_, v___x_521_);
return v___x_528_;
}
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_usize_of_nat(v_start_519_);
v___x_530_ = lean_usize_of_nat(v_stop_520_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_517_, v_as_518_, v___x_529_, v___x_530_, v___x_521_);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object* v_self_532_, lean_object* v_as_533_, lean_object* v_start_534_, lean_object* v_stop_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_532_, v_as_533_, v_start_534_, v_stop_535_);
lean_dec(v_stop_535_);
lean_dec(v_start_534_);
lean_dec_ref(v_as_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* v_self_537_){
_start:
{
lean_object* v_config_538_; lean_object* v_roots_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_config_538_ = lean_ctor_get(v_self_537_, 2);
v_roots_539_ = lean_ctor_get(v_config_538_, 2);
lean_inc_ref(v_roots_539_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_array_get_size(v_roots_539_);
v___x_542_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_537_, v_roots_539_, v___x_540_, v___x_541_);
lean_dec_ref(v_roots_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* v_self_543_){
_start:
{
lean_object* v_lib_544_; lean_object* v_pkg_545_; 
v_lib_544_ = lean_ctor_get(v_self_543_, 0);
v_pkg_545_ = lean_ctor_get(v_lib_544_, 0);
lean_inc_ref(v_pkg_545_);
return v_pkg_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* v_self_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lake_Module_pkg(v_self_546_);
lean_dec_ref(v_self_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* v_self_548_){
_start:
{
lean_object* v_lib_549_; lean_object* v_pkg_550_; lean_object* v_config_551_; lean_object* v_config_552_; lean_object* v_dir_553_; lean_object* v_srcDir_554_; lean_object* v_srcDir_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_lib_549_ = lean_ctor_get(v_self_548_, 0);
lean_inc_ref(v_lib_549_);
lean_dec_ref(v_self_548_);
v_pkg_550_ = lean_ctor_get(v_lib_549_, 0);
lean_inc_ref(v_pkg_550_);
v_config_551_ = lean_ctor_get(v_pkg_550_, 6);
lean_inc_ref(v_config_551_);
v_config_552_ = lean_ctor_get(v_lib_549_, 2);
lean_inc(v_config_552_);
lean_dec_ref(v_lib_549_);
v_dir_553_ = lean_ctor_get(v_pkg_550_, 4);
lean_inc_ref(v_dir_553_);
lean_dec_ref(v_pkg_550_);
v_srcDir_554_ = lean_ctor_get(v_config_551_, 4);
lean_inc_ref(v_srcDir_554_);
lean_dec_ref(v_config_551_);
v_srcDir_555_ = lean_ctor_get(v_config_552_, 1);
lean_inc_ref(v_srcDir_555_);
lean_dec(v_config_552_);
v___x_556_ = l_System_FilePath_normalize(v_srcDir_554_);
v___x_557_ = l_Lake_joinRelative(v_dir_553_, v___x_556_);
v___x_558_ = l_System_FilePath_normalize(v_srcDir_555_);
v___x_559_ = l_Lake_joinRelative(v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object* v_ext_560_, lean_object* v_self_561_){
_start:
{
lean_object* v_name_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_name_562_ = lean_ctor_get(v_self_561_, 1);
v___x_563_ = l_Lean_Name_getString_x21(v_name_562_);
v___x_564_ = l_System_FilePath_addExtension(v___x_563_, v_ext_560_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object* v_ext_565_, lean_object* v_self_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lake_Module_fileName(v_ext_565_, v_self_566_);
lean_dec_ref(v_self_566_);
lean_dec_ref(v_ext_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_568_, lean_object* v_ext_569_, lean_object* v_self_570_){
_start:
{
lean_object* v_name_571_; lean_object* v___x_572_; 
v_name_571_ = lean_ctor_get(v_self_570_, 1);
lean_inc(v_name_571_);
lean_dec_ref(v_self_570_);
v___x_572_ = l_Lean_modToFilePath(v_dir_568_, v_name_571_, v_ext_569_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_573_, lean_object* v_ext_574_, lean_object* v_self_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lake_Module_filePath(v_dir_573_, v_ext_574_, v_self_575_);
lean_dec_ref(v_ext_574_);
lean_dec_ref(v_dir_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_577_, lean_object* v_self_578_){
_start:
{
lean_object* v_lib_579_; lean_object* v_pkg_580_; lean_object* v_config_581_; lean_object* v_config_582_; lean_object* v_name_583_; lean_object* v_dir_584_; lean_object* v_srcDir_585_; lean_object* v_srcDir_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_lib_579_ = lean_ctor_get(v_self_578_, 0);
v_pkg_580_ = lean_ctor_get(v_lib_579_, 0);
lean_inc_ref(v_pkg_580_);
v_config_581_ = lean_ctor_get(v_pkg_580_, 6);
lean_inc_ref(v_config_581_);
v_config_582_ = lean_ctor_get(v_lib_579_, 2);
lean_inc(v_config_582_);
v_name_583_ = lean_ctor_get(v_self_578_, 1);
lean_inc(v_name_583_);
lean_dec_ref(v_self_578_);
v_dir_584_ = lean_ctor_get(v_pkg_580_, 4);
lean_inc_ref(v_dir_584_);
lean_dec_ref(v_pkg_580_);
v_srcDir_585_ = lean_ctor_get(v_config_581_, 4);
lean_inc_ref(v_srcDir_585_);
lean_dec_ref(v_config_581_);
v_srcDir_586_ = lean_ctor_get(v_config_582_, 1);
lean_inc_ref(v_srcDir_586_);
lean_dec(v_config_582_);
v___x_587_ = l_System_FilePath_normalize(v_srcDir_585_);
v___x_588_ = l_Lake_joinRelative(v_dir_584_, v___x_587_);
v___x_589_ = l_System_FilePath_normalize(v_srcDir_586_);
v___x_590_ = l_Lake_joinRelative(v___x_588_, v___x_589_);
v___x_591_ = l_Lean_modToFilePath(v___x_590_, v_name_583_, v_ext_577_);
lean_dec_ref(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_592_, lean_object* v_self_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lake_Module_srcPath(v_ext_592_, v_self_593_);
lean_dec_ref(v_ext_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_595_){
_start:
{
lean_object* v_lib_596_; lean_object* v_pkg_597_; lean_object* v_config_598_; lean_object* v_config_599_; lean_object* v_name_600_; lean_object* v_dir_601_; lean_object* v_srcDir_602_; lean_object* v_srcDir_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_lib_596_ = lean_ctor_get(v_self_595_, 0);
v_pkg_597_ = lean_ctor_get(v_lib_596_, 0);
lean_inc_ref(v_pkg_597_);
v_config_598_ = lean_ctor_get(v_pkg_597_, 6);
lean_inc_ref(v_config_598_);
v_config_599_ = lean_ctor_get(v_lib_596_, 2);
lean_inc(v_config_599_);
v_name_600_ = lean_ctor_get(v_self_595_, 1);
lean_inc(v_name_600_);
lean_dec_ref(v_self_595_);
v_dir_601_ = lean_ctor_get(v_pkg_597_, 4);
lean_inc_ref(v_dir_601_);
lean_dec_ref(v_pkg_597_);
v_srcDir_602_ = lean_ctor_get(v_config_598_, 4);
lean_inc_ref(v_srcDir_602_);
lean_dec_ref(v_config_598_);
v_srcDir_603_ = lean_ctor_get(v_config_599_, 1);
lean_inc_ref(v_srcDir_603_);
lean_dec(v_config_599_);
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_605_ = l_System_FilePath_normalize(v_srcDir_602_);
v___x_606_ = l_Lake_joinRelative(v_dir_601_, v___x_605_);
v___x_607_ = l_System_FilePath_normalize(v_srcDir_603_);
v___x_608_ = l_Lake_joinRelative(v___x_606_, v___x_607_);
v___x_609_ = l_Lean_modToFilePath(v___x_608_, v_name_600_, v___x_604_);
lean_dec_ref(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_610_){
_start:
{
lean_object* v_lib_611_; lean_object* v_pkg_612_; lean_object* v_config_613_; lean_object* v_config_614_; lean_object* v_name_615_; lean_object* v_dir_616_; lean_object* v_srcDir_617_; lean_object* v_srcDir_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_lib_611_ = lean_ctor_get(v_self_610_, 0);
v_pkg_612_ = lean_ctor_get(v_lib_611_, 0);
lean_inc_ref(v_pkg_612_);
v_config_613_ = lean_ctor_get(v_pkg_612_, 6);
lean_inc_ref(v_config_613_);
v_config_614_ = lean_ctor_get(v_lib_611_, 2);
lean_inc(v_config_614_);
v_name_615_ = lean_ctor_get(v_self_610_, 1);
lean_inc(v_name_615_);
lean_dec_ref(v_self_610_);
v_dir_616_ = lean_ctor_get(v_pkg_612_, 4);
lean_inc_ref_n(v_dir_616_, 2);
lean_dec_ref(v_pkg_612_);
v_srcDir_617_ = lean_ctor_get(v_config_613_, 4);
lean_inc_ref(v_srcDir_617_);
lean_dec_ref(v_config_613_);
v_srcDir_618_ = lean_ctor_get(v_config_614_, 1);
lean_inc_ref(v_srcDir_618_);
lean_dec(v_config_614_);
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_620_ = l_System_FilePath_normalize(v_srcDir_617_);
v___x_621_ = l_Lake_joinRelative(v_dir_616_, v___x_620_);
v___x_622_ = l_System_FilePath_normalize(v_srcDir_618_);
v___x_623_ = l_Lake_joinRelative(v___x_621_, v___x_622_);
v___x_624_ = l_Lean_modToFilePath(v___x_623_, v_name_615_, v___x_619_);
lean_dec_ref(v___x_623_);
v___x_625_ = l_Lake_relPathFrom(v_dir_616_, v___x_624_);
lean_dec_ref(v_dir_616_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_626_, lean_object* v_self_627_){
_start:
{
lean_object* v_lib_628_; lean_object* v_pkg_629_; lean_object* v_config_630_; lean_object* v_name_631_; lean_object* v_dir_632_; lean_object* v_buildDir_633_; lean_object* v_leanLibDir_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_lib_628_ = lean_ctor_get(v_self_627_, 0);
v_pkg_629_ = lean_ctor_get(v_lib_628_, 0);
lean_inc_ref(v_pkg_629_);
v_config_630_ = lean_ctor_get(v_pkg_629_, 6);
lean_inc_ref(v_config_630_);
v_name_631_ = lean_ctor_get(v_self_627_, 1);
lean_inc(v_name_631_);
lean_dec_ref(v_self_627_);
v_dir_632_ = lean_ctor_get(v_pkg_629_, 4);
lean_inc_ref(v_dir_632_);
lean_dec_ref(v_pkg_629_);
v_buildDir_633_ = lean_ctor_get(v_config_630_, 5);
lean_inc_ref(v_buildDir_633_);
v_leanLibDir_634_ = lean_ctor_get(v_config_630_, 6);
lean_inc_ref(v_leanLibDir_634_);
lean_dec_ref(v_config_630_);
v___x_635_ = l_System_FilePath_normalize(v_buildDir_633_);
v___x_636_ = l_Lake_joinRelative(v_dir_632_, v___x_635_);
v___x_637_ = l_System_FilePath_normalize(v_leanLibDir_634_);
v___x_638_ = l_Lake_joinRelative(v___x_636_, v___x_637_);
v___x_639_ = l_Lean_modToFilePath(v___x_638_, v_name_631_, v_ext_626_);
lean_dec_ref(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_640_, lean_object* v_self_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lake_Module_leanLibPath(v_ext_640_, v_self_641_);
lean_dec_ref(v_ext_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object* v_self_643_){
_start:
{
lean_object* v_lib_644_; lean_object* v_pkg_645_; lean_object* v_config_646_; lean_object* v_name_647_; lean_object* v_dir_648_; lean_object* v_buildDir_649_; lean_object* v_leanLibDir_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_lib_644_ = lean_ctor_get(v_self_643_, 0);
v_pkg_645_ = lean_ctor_get(v_lib_644_, 0);
lean_inc_ref(v_pkg_645_);
v_config_646_ = lean_ctor_get(v_pkg_645_, 6);
lean_inc_ref(v_config_646_);
v_name_647_ = lean_ctor_get(v_self_643_, 1);
lean_inc(v_name_647_);
lean_dec_ref(v_self_643_);
v_dir_648_ = lean_ctor_get(v_pkg_645_, 4);
lean_inc_ref(v_dir_648_);
lean_dec_ref(v_pkg_645_);
v_buildDir_649_ = lean_ctor_get(v_config_646_, 5);
lean_inc_ref(v_buildDir_649_);
v_leanLibDir_650_ = lean_ctor_get(v_config_646_, 6);
lean_inc_ref(v_leanLibDir_650_);
lean_dec_ref(v_config_646_);
v___x_651_ = l_System_FilePath_normalize(v_buildDir_649_);
v___x_652_ = l_Lake_joinRelative(v_dir_648_, v___x_651_);
v___x_653_ = l_System_FilePath_normalize(v_leanLibDir_650_);
v___x_654_ = l_Lake_joinRelative(v___x_652_, v___x_653_);
v___x_655_ = l_Lean_Name_getPrefix(v_name_647_);
lean_dec(v_name_647_);
v___x_656_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_657_ = l_Lean_modToFilePath(v___x_654_, v___x_655_, v___x_656_);
lean_dec_ref(v___x_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_659_){
_start:
{
lean_object* v_lib_660_; lean_object* v_pkg_661_; lean_object* v_config_662_; lean_object* v_name_663_; lean_object* v_dir_664_; lean_object* v_buildDir_665_; lean_object* v_leanLibDir_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_lib_660_ = lean_ctor_get(v_self_659_, 0);
v_pkg_661_ = lean_ctor_get(v_lib_660_, 0);
lean_inc_ref(v_pkg_661_);
v_config_662_ = lean_ctor_get(v_pkg_661_, 6);
lean_inc_ref(v_config_662_);
v_name_663_ = lean_ctor_get(v_self_659_, 1);
lean_inc(v_name_663_);
lean_dec_ref(v_self_659_);
v_dir_664_ = lean_ctor_get(v_pkg_661_, 4);
lean_inc_ref(v_dir_664_);
lean_dec_ref(v_pkg_661_);
v_buildDir_665_ = lean_ctor_get(v_config_662_, 5);
lean_inc_ref(v_buildDir_665_);
v_leanLibDir_666_ = lean_ctor_get(v_config_662_, 6);
lean_inc_ref(v_leanLibDir_666_);
lean_dec_ref(v_config_662_);
v___x_667_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_668_ = l_System_FilePath_normalize(v_buildDir_665_);
v___x_669_ = l_Lake_joinRelative(v_dir_664_, v___x_668_);
v___x_670_ = l_System_FilePath_normalize(v_leanLibDir_666_);
v___x_671_ = l_Lake_joinRelative(v___x_669_, v___x_670_);
v___x_672_ = l_Lean_modToFilePath(v___x_671_, v_name_663_, v___x_667_);
lean_dec_ref(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_674_){
_start:
{
lean_object* v_lib_675_; lean_object* v_pkg_676_; lean_object* v_config_677_; lean_object* v_name_678_; lean_object* v_dir_679_; lean_object* v_buildDir_680_; lean_object* v_leanLibDir_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_lib_675_ = lean_ctor_get(v_self_674_, 0);
v_pkg_676_ = lean_ctor_get(v_lib_675_, 0);
lean_inc_ref(v_pkg_676_);
v_config_677_ = lean_ctor_get(v_pkg_676_, 6);
lean_inc_ref(v_config_677_);
v_name_678_ = lean_ctor_get(v_self_674_, 1);
lean_inc(v_name_678_);
lean_dec_ref(v_self_674_);
v_dir_679_ = lean_ctor_get(v_pkg_676_, 4);
lean_inc_ref(v_dir_679_);
lean_dec_ref(v_pkg_676_);
v_buildDir_680_ = lean_ctor_get(v_config_677_, 5);
lean_inc_ref(v_buildDir_680_);
v_leanLibDir_681_ = lean_ctor_get(v_config_677_, 6);
lean_inc_ref(v_leanLibDir_681_);
lean_dec_ref(v_config_677_);
v___x_682_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_683_ = l_System_FilePath_normalize(v_buildDir_680_);
v___x_684_ = l_Lake_joinRelative(v_dir_679_, v___x_683_);
v___x_685_ = l_System_FilePath_normalize(v_leanLibDir_681_);
v___x_686_ = l_Lake_joinRelative(v___x_684_, v___x_685_);
v___x_687_ = l_Lean_modToFilePath(v___x_686_, v_name_678_, v___x_682_);
lean_dec_ref(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_689_){
_start:
{
lean_object* v_lib_690_; lean_object* v_pkg_691_; lean_object* v_config_692_; lean_object* v_name_693_; lean_object* v_dir_694_; lean_object* v_buildDir_695_; lean_object* v_leanLibDir_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_lib_690_ = lean_ctor_get(v_self_689_, 0);
v_pkg_691_ = lean_ctor_get(v_lib_690_, 0);
lean_inc_ref(v_pkg_691_);
v_config_692_ = lean_ctor_get(v_pkg_691_, 6);
lean_inc_ref(v_config_692_);
v_name_693_ = lean_ctor_get(v_self_689_, 1);
lean_inc(v_name_693_);
lean_dec_ref(v_self_689_);
v_dir_694_ = lean_ctor_get(v_pkg_691_, 4);
lean_inc_ref(v_dir_694_);
lean_dec_ref(v_pkg_691_);
v_buildDir_695_ = lean_ctor_get(v_config_692_, 5);
lean_inc_ref(v_buildDir_695_);
v_leanLibDir_696_ = lean_ctor_get(v_config_692_, 6);
lean_inc_ref(v_leanLibDir_696_);
lean_dec_ref(v_config_692_);
v___x_697_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_698_ = l_System_FilePath_normalize(v_buildDir_695_);
v___x_699_ = l_Lake_joinRelative(v_dir_694_, v___x_698_);
v___x_700_ = l_System_FilePath_normalize(v_leanLibDir_696_);
v___x_701_ = l_Lake_joinRelative(v___x_699_, v___x_700_);
v___x_702_ = l_Lean_modToFilePath(v___x_701_, v_name_693_, v___x_697_);
lean_dec_ref(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_704_){
_start:
{
lean_object* v_lib_705_; lean_object* v_pkg_706_; lean_object* v_config_707_; lean_object* v_name_708_; lean_object* v_dir_709_; lean_object* v_buildDir_710_; lean_object* v_leanLibDir_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_lib_705_ = lean_ctor_get(v_self_704_, 0);
v_pkg_706_ = lean_ctor_get(v_lib_705_, 0);
lean_inc_ref(v_pkg_706_);
v_config_707_ = lean_ctor_get(v_pkg_706_, 6);
lean_inc_ref(v_config_707_);
v_name_708_ = lean_ctor_get(v_self_704_, 1);
lean_inc(v_name_708_);
lean_dec_ref(v_self_704_);
v_dir_709_ = lean_ctor_get(v_pkg_706_, 4);
lean_inc_ref(v_dir_709_);
lean_dec_ref(v_pkg_706_);
v_buildDir_710_ = lean_ctor_get(v_config_707_, 5);
lean_inc_ref(v_buildDir_710_);
v_leanLibDir_711_ = lean_ctor_get(v_config_707_, 6);
lean_inc_ref(v_leanLibDir_711_);
lean_dec_ref(v_config_707_);
v___x_712_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_713_ = l_System_FilePath_normalize(v_buildDir_710_);
v___x_714_ = l_Lake_joinRelative(v_dir_709_, v___x_713_);
v___x_715_ = l_System_FilePath_normalize(v_leanLibDir_711_);
v___x_716_ = l_Lake_joinRelative(v___x_714_, v___x_715_);
v___x_717_ = l_Lean_modToFilePath(v___x_716_, v_name_708_, v___x_712_);
lean_dec_ref(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object* v_self_719_){
_start:
{
lean_object* v_lib_720_; lean_object* v_pkg_721_; lean_object* v_config_722_; lean_object* v_name_723_; lean_object* v_dir_724_; lean_object* v_buildDir_725_; lean_object* v_leanLibDir_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_lib_720_ = lean_ctor_get(v_self_719_, 0);
v_pkg_721_ = lean_ctor_get(v_lib_720_, 0);
lean_inc_ref(v_pkg_721_);
v_config_722_ = lean_ctor_get(v_pkg_721_, 6);
lean_inc_ref(v_config_722_);
v_name_723_ = lean_ctor_get(v_self_719_, 1);
lean_inc(v_name_723_);
lean_dec_ref(v_self_719_);
v_dir_724_ = lean_ctor_get(v_pkg_721_, 4);
lean_inc_ref(v_dir_724_);
lean_dec_ref(v_pkg_721_);
v_buildDir_725_ = lean_ctor_get(v_config_722_, 5);
lean_inc_ref(v_buildDir_725_);
v_leanLibDir_726_ = lean_ctor_get(v_config_722_, 6);
lean_inc_ref(v_leanLibDir_726_);
lean_dec_ref(v_config_722_);
v___x_727_ = ((lean_object*)(l_Lake_Module_irSigFile___closed__0));
v___x_728_ = l_System_FilePath_normalize(v_buildDir_725_);
v___x_729_ = l_Lake_joinRelative(v_dir_724_, v___x_728_);
v___x_730_ = l_System_FilePath_normalize(v_leanLibDir_726_);
v___x_731_ = l_Lake_joinRelative(v___x_729_, v___x_730_);
v___x_732_ = l_Lean_modToFilePath(v___x_731_, v_name_723_, v___x_727_);
lean_dec_ref(v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_734_){
_start:
{
lean_object* v_lib_735_; lean_object* v_pkg_736_; lean_object* v_config_737_; lean_object* v_name_738_; lean_object* v_dir_739_; lean_object* v_buildDir_740_; lean_object* v_leanLibDir_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_lib_735_ = lean_ctor_get(v_self_734_, 0);
v_pkg_736_ = lean_ctor_get(v_lib_735_, 0);
lean_inc_ref(v_pkg_736_);
v_config_737_ = lean_ctor_get(v_pkg_736_, 6);
lean_inc_ref(v_config_737_);
v_name_738_ = lean_ctor_get(v_self_734_, 1);
lean_inc(v_name_738_);
lean_dec_ref(v_self_734_);
v_dir_739_ = lean_ctor_get(v_pkg_736_, 4);
lean_inc_ref(v_dir_739_);
lean_dec_ref(v_pkg_736_);
v_buildDir_740_ = lean_ctor_get(v_config_737_, 5);
lean_inc_ref(v_buildDir_740_);
v_leanLibDir_741_ = lean_ctor_get(v_config_737_, 6);
lean_inc_ref(v_leanLibDir_741_);
lean_dec_ref(v_config_737_);
v___x_742_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_743_ = l_System_FilePath_normalize(v_buildDir_740_);
v___x_744_ = l_Lake_joinRelative(v_dir_739_, v___x_743_);
v___x_745_ = l_System_FilePath_normalize(v_leanLibDir_741_);
v___x_746_ = l_Lake_joinRelative(v___x_744_, v___x_745_);
v___x_747_ = l_Lean_modToFilePath(v___x_746_, v_name_738_, v___x_742_);
lean_dec_ref(v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_749_){
_start:
{
lean_object* v_lib_750_; lean_object* v_pkg_751_; lean_object* v_config_752_; lean_object* v_name_753_; lean_object* v_dir_754_; lean_object* v_buildDir_755_; lean_object* v_leanLibDir_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_lib_750_ = lean_ctor_get(v_self_749_, 0);
v_pkg_751_ = lean_ctor_get(v_lib_750_, 0);
lean_inc_ref(v_pkg_751_);
v_config_752_ = lean_ctor_get(v_pkg_751_, 6);
lean_inc_ref(v_config_752_);
v_name_753_ = lean_ctor_get(v_self_749_, 1);
lean_inc(v_name_753_);
lean_dec_ref(v_self_749_);
v_dir_754_ = lean_ctor_get(v_pkg_751_, 4);
lean_inc_ref(v_dir_754_);
lean_dec_ref(v_pkg_751_);
v_buildDir_755_ = lean_ctor_get(v_config_752_, 5);
lean_inc_ref(v_buildDir_755_);
v_leanLibDir_756_ = lean_ctor_get(v_config_752_, 6);
lean_inc_ref(v_leanLibDir_756_);
lean_dec_ref(v_config_752_);
v___x_757_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_758_ = l_System_FilePath_normalize(v_buildDir_755_);
v___x_759_ = l_Lake_joinRelative(v_dir_754_, v___x_758_);
v___x_760_ = l_System_FilePath_normalize(v_leanLibDir_756_);
v___x_761_ = l_Lake_joinRelative(v___x_759_, v___x_760_);
v___x_762_ = l_Lean_modToFilePath(v___x_761_, v_name_753_, v___x_757_);
lean_dec_ref(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_763_, lean_object* v_self_764_){
_start:
{
lean_object* v_lib_765_; lean_object* v_pkg_766_; lean_object* v_config_767_; lean_object* v_name_768_; lean_object* v_dir_769_; lean_object* v_buildDir_770_; lean_object* v_irDir_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_lib_765_ = lean_ctor_get(v_self_764_, 0);
v_pkg_766_ = lean_ctor_get(v_lib_765_, 0);
lean_inc_ref(v_pkg_766_);
v_config_767_ = lean_ctor_get(v_pkg_766_, 6);
lean_inc_ref(v_config_767_);
v_name_768_ = lean_ctor_get(v_self_764_, 1);
lean_inc(v_name_768_);
lean_dec_ref(v_self_764_);
v_dir_769_ = lean_ctor_get(v_pkg_766_, 4);
lean_inc_ref(v_dir_769_);
lean_dec_ref(v_pkg_766_);
v_buildDir_770_ = lean_ctor_get(v_config_767_, 5);
lean_inc_ref(v_buildDir_770_);
v_irDir_771_ = lean_ctor_get(v_config_767_, 9);
lean_inc_ref(v_irDir_771_);
lean_dec_ref(v_config_767_);
v___x_772_ = l_System_FilePath_normalize(v_buildDir_770_);
v___x_773_ = l_Lake_joinRelative(v_dir_769_, v___x_772_);
v___x_774_ = l_System_FilePath_normalize(v_irDir_771_);
v___x_775_ = l_Lake_joinRelative(v___x_773_, v___x_774_);
v___x_776_ = l_Lean_modToFilePath(v___x_775_, v_name_768_, v_ext_763_);
lean_dec_ref(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_777_, lean_object* v_self_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_Module_irPath(v_ext_777_, v_self_778_);
lean_dec_ref(v_ext_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_780_){
_start:
{
lean_object* v_lib_781_; lean_object* v_pkg_782_; lean_object* v_config_783_; lean_object* v_name_784_; lean_object* v_dir_785_; lean_object* v_buildDir_786_; lean_object* v_irDir_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_lib_781_ = lean_ctor_get(v_self_780_, 0);
v_pkg_782_ = lean_ctor_get(v_lib_781_, 0);
lean_inc_ref(v_pkg_782_);
v_config_783_ = lean_ctor_get(v_pkg_782_, 6);
lean_inc_ref(v_config_783_);
v_name_784_ = lean_ctor_get(v_self_780_, 1);
lean_inc(v_name_784_);
lean_dec_ref(v_self_780_);
v_dir_785_ = lean_ctor_get(v_pkg_782_, 4);
lean_inc_ref(v_dir_785_);
lean_dec_ref(v_pkg_782_);
v_buildDir_786_ = lean_ctor_get(v_config_783_, 5);
lean_inc_ref(v_buildDir_786_);
v_irDir_787_ = lean_ctor_get(v_config_783_, 9);
lean_inc_ref(v_irDir_787_);
lean_dec_ref(v_config_783_);
v___x_788_ = l_System_FilePath_normalize(v_buildDir_786_);
v___x_789_ = l_Lake_joinRelative(v_dir_785_, v___x_788_);
v___x_790_ = l_System_FilePath_normalize(v_irDir_787_);
v___x_791_ = l_Lake_joinRelative(v___x_789_, v___x_790_);
v___x_792_ = l_Lean_Name_getPrefix(v_name_784_);
lean_dec(v_name_784_);
v___x_793_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_794_ = l_Lean_modToFilePath(v___x_791_, v___x_792_, v___x_793_);
lean_dec_ref(v___x_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_796_){
_start:
{
lean_object* v_lib_797_; lean_object* v_pkg_798_; lean_object* v_config_799_; lean_object* v_name_800_; lean_object* v_dir_801_; lean_object* v_buildDir_802_; lean_object* v_irDir_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_lib_797_ = lean_ctor_get(v_self_796_, 0);
v_pkg_798_ = lean_ctor_get(v_lib_797_, 0);
lean_inc_ref(v_pkg_798_);
v_config_799_ = lean_ctor_get(v_pkg_798_, 6);
lean_inc_ref(v_config_799_);
v_name_800_ = lean_ctor_get(v_self_796_, 1);
lean_inc(v_name_800_);
lean_dec_ref(v_self_796_);
v_dir_801_ = lean_ctor_get(v_pkg_798_, 4);
lean_inc_ref(v_dir_801_);
lean_dec_ref(v_pkg_798_);
v_buildDir_802_ = lean_ctor_get(v_config_799_, 5);
lean_inc_ref(v_buildDir_802_);
v_irDir_803_ = lean_ctor_get(v_config_799_, 9);
lean_inc_ref(v_irDir_803_);
lean_dec_ref(v_config_799_);
v___x_804_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_805_ = l_System_FilePath_normalize(v_buildDir_802_);
v___x_806_ = l_Lake_joinRelative(v_dir_801_, v___x_805_);
v___x_807_ = l_System_FilePath_normalize(v_irDir_803_);
v___x_808_ = l_Lake_joinRelative(v___x_806_, v___x_807_);
v___x_809_ = l_Lean_modToFilePath(v___x_808_, v_name_800_, v___x_804_);
lean_dec_ref(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_811_){
_start:
{
lean_object* v_lib_812_; lean_object* v_pkg_813_; lean_object* v_config_814_; lean_object* v_name_815_; lean_object* v_dir_816_; lean_object* v_buildDir_817_; lean_object* v_irDir_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_lib_812_ = lean_ctor_get(v_self_811_, 0);
v_pkg_813_ = lean_ctor_get(v_lib_812_, 0);
lean_inc_ref(v_pkg_813_);
v_config_814_ = lean_ctor_get(v_pkg_813_, 6);
lean_inc_ref(v_config_814_);
v_name_815_ = lean_ctor_get(v_self_811_, 1);
lean_inc(v_name_815_);
lean_dec_ref(v_self_811_);
v_dir_816_ = lean_ctor_get(v_pkg_813_, 4);
lean_inc_ref(v_dir_816_);
lean_dec_ref(v_pkg_813_);
v_buildDir_817_ = lean_ctor_get(v_config_814_, 5);
lean_inc_ref(v_buildDir_817_);
v_irDir_818_ = lean_ctor_get(v_config_814_, 9);
lean_inc_ref(v_irDir_818_);
lean_dec_ref(v_config_814_);
v___x_819_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_820_ = l_System_FilePath_normalize(v_buildDir_817_);
v___x_821_ = l_Lake_joinRelative(v_dir_816_, v___x_820_);
v___x_822_ = l_System_FilePath_normalize(v_irDir_818_);
v___x_823_ = l_Lake_joinRelative(v___x_821_, v___x_822_);
v___x_824_ = l_Lean_modToFilePath(v___x_823_, v_name_815_, v___x_819_);
lean_dec_ref(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_826_){
_start:
{
lean_object* v_lib_827_; lean_object* v_pkg_828_; lean_object* v_config_829_; lean_object* v_name_830_; lean_object* v_dir_831_; lean_object* v_buildDir_832_; lean_object* v_irDir_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_lib_827_ = lean_ctor_get(v_self_826_, 0);
v_pkg_828_ = lean_ctor_get(v_lib_827_, 0);
lean_inc_ref(v_pkg_828_);
v_config_829_ = lean_ctor_get(v_pkg_828_, 6);
lean_inc_ref(v_config_829_);
v_name_830_ = lean_ctor_get(v_self_826_, 1);
lean_inc(v_name_830_);
lean_dec_ref(v_self_826_);
v_dir_831_ = lean_ctor_get(v_pkg_828_, 4);
lean_inc_ref(v_dir_831_);
lean_dec_ref(v_pkg_828_);
v_buildDir_832_ = lean_ctor_get(v_config_829_, 5);
lean_inc_ref(v_buildDir_832_);
v_irDir_833_ = lean_ctor_get(v_config_829_, 9);
lean_inc_ref(v_irDir_833_);
lean_dec_ref(v_config_829_);
v___x_834_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_835_ = l_System_FilePath_normalize(v_buildDir_832_);
v___x_836_ = l_Lake_joinRelative(v_dir_831_, v___x_835_);
v___x_837_ = l_System_FilePath_normalize(v_irDir_833_);
v___x_838_ = l_Lake_joinRelative(v___x_836_, v___x_837_);
v___x_839_ = l_Lean_modToFilePath(v___x_838_, v_name_830_, v___x_834_);
lean_dec_ref(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_841_){
_start:
{
lean_object* v_lib_842_; lean_object* v_pkg_843_; lean_object* v_config_844_; lean_object* v_name_845_; lean_object* v_dir_846_; lean_object* v_buildDir_847_; lean_object* v_irDir_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_lib_842_ = lean_ctor_get(v_self_841_, 0);
v_pkg_843_ = lean_ctor_get(v_lib_842_, 0);
lean_inc_ref(v_pkg_843_);
v_config_844_ = lean_ctor_get(v_pkg_843_, 6);
lean_inc_ref(v_config_844_);
v_name_845_ = lean_ctor_get(v_self_841_, 1);
lean_inc(v_name_845_);
lean_dec_ref(v_self_841_);
v_dir_846_ = lean_ctor_get(v_pkg_843_, 4);
lean_inc_ref(v_dir_846_);
lean_dec_ref(v_pkg_843_);
v_buildDir_847_ = lean_ctor_get(v_config_844_, 5);
lean_inc_ref(v_buildDir_847_);
v_irDir_848_ = lean_ctor_get(v_config_844_, 9);
lean_inc_ref(v_irDir_848_);
lean_dec_ref(v_config_844_);
v___x_849_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_850_ = l_System_FilePath_normalize(v_buildDir_847_);
v___x_851_ = l_Lake_joinRelative(v_dir_846_, v___x_850_);
v___x_852_ = l_System_FilePath_normalize(v_irDir_848_);
v___x_853_ = l_Lake_joinRelative(v___x_851_, v___x_852_);
v___x_854_ = l_Lean_modToFilePath(v___x_853_, v_name_845_, v___x_849_);
lean_dec_ref(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_856_){
_start:
{
lean_object* v_lib_857_; lean_object* v_pkg_858_; lean_object* v_config_859_; lean_object* v_name_860_; lean_object* v_dir_861_; lean_object* v_buildDir_862_; lean_object* v_irDir_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_lib_857_ = lean_ctor_get(v_self_856_, 0);
v_pkg_858_ = lean_ctor_get(v_lib_857_, 0);
lean_inc_ref(v_pkg_858_);
v_config_859_ = lean_ctor_get(v_pkg_858_, 6);
lean_inc_ref(v_config_859_);
v_name_860_ = lean_ctor_get(v_self_856_, 1);
lean_inc(v_name_860_);
lean_dec_ref(v_self_856_);
v_dir_861_ = lean_ctor_get(v_pkg_858_, 4);
lean_inc_ref(v_dir_861_);
lean_dec_ref(v_pkg_858_);
v_buildDir_862_ = lean_ctor_get(v_config_859_, 5);
lean_inc_ref(v_buildDir_862_);
v_irDir_863_ = lean_ctor_get(v_config_859_, 9);
lean_inc_ref(v_irDir_863_);
lean_dec_ref(v_config_859_);
v___x_864_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_865_ = l_System_FilePath_normalize(v_buildDir_862_);
v___x_866_ = l_Lake_joinRelative(v_dir_861_, v___x_865_);
v___x_867_ = l_System_FilePath_normalize(v_irDir_863_);
v___x_868_ = l_Lake_joinRelative(v___x_866_, v___x_867_);
v___x_869_ = l_Lean_modToFilePath(v___x_868_, v_name_860_, v___x_864_);
lean_dec_ref(v___x_868_);
return v___x_869_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_box(0);
v___x_871_ = lean_internal_has_llvm_backend(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v_self_872_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
else
{
lean_object* v_lib_875_; lean_object* v_pkg_876_; lean_object* v_config_877_; lean_object* v_name_878_; lean_object* v_dir_879_; lean_object* v_buildDir_880_; lean_object* v_irDir_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_lib_875_ = lean_ctor_get(v_self_872_, 0);
v_pkg_876_ = lean_ctor_get(v_lib_875_, 0);
lean_inc_ref(v_pkg_876_);
v_config_877_ = lean_ctor_get(v_pkg_876_, 6);
lean_inc_ref(v_config_877_);
v_name_878_ = lean_ctor_get(v_self_872_, 1);
lean_inc(v_name_878_);
lean_dec_ref(v_self_872_);
v_dir_879_ = lean_ctor_get(v_pkg_876_, 4);
lean_inc_ref(v_dir_879_);
lean_dec_ref(v_pkg_876_);
v_buildDir_880_ = lean_ctor_get(v_config_877_, 5);
lean_inc_ref(v_buildDir_880_);
v_irDir_881_ = lean_ctor_get(v_config_877_, 9);
lean_inc_ref(v_irDir_881_);
lean_dec_ref(v_config_877_);
v___x_882_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_883_ = l_System_FilePath_normalize(v_buildDir_880_);
v___x_884_ = l_Lake_joinRelative(v_dir_879_, v___x_883_);
v___x_885_ = l_System_FilePath_normalize(v_irDir_881_);
v___x_886_ = l_Lake_joinRelative(v___x_884_, v___x_885_);
v___x_887_ = l_Lean_modToFilePath(v___x_886_, v_name_878_, v___x_882_);
lean_dec_ref(v___x_886_);
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_890_){
_start:
{
lean_object* v_lib_891_; lean_object* v_pkg_892_; lean_object* v_config_893_; lean_object* v_name_894_; lean_object* v_dir_895_; lean_object* v_buildDir_896_; lean_object* v_irDir_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_lib_891_ = lean_ctor_get(v_self_890_, 0);
v_pkg_892_ = lean_ctor_get(v_lib_891_, 0);
lean_inc_ref(v_pkg_892_);
v_config_893_ = lean_ctor_get(v_pkg_892_, 6);
lean_inc_ref(v_config_893_);
v_name_894_ = lean_ctor_get(v_self_890_, 1);
lean_inc(v_name_894_);
lean_dec_ref(v_self_890_);
v_dir_895_ = lean_ctor_get(v_pkg_892_, 4);
lean_inc_ref(v_dir_895_);
lean_dec_ref(v_pkg_892_);
v_buildDir_896_ = lean_ctor_get(v_config_893_, 5);
lean_inc_ref(v_buildDir_896_);
v_irDir_897_ = lean_ctor_get(v_config_893_, 9);
lean_inc_ref(v_irDir_897_);
lean_dec_ref(v_config_893_);
v___x_898_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_899_ = l_System_FilePath_normalize(v_buildDir_896_);
v___x_900_ = l_Lake_joinRelative(v_dir_895_, v___x_899_);
v___x_901_ = l_System_FilePath_normalize(v_irDir_897_);
v___x_902_ = l_Lake_joinRelative(v___x_900_, v___x_901_);
v___x_903_ = l_Lean_modToFilePath(v___x_902_, v_name_894_, v___x_898_);
lean_dec_ref(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_905_){
_start:
{
lean_object* v_lib_906_; lean_object* v_pkg_907_; lean_object* v_config_908_; lean_object* v_name_909_; lean_object* v_dir_910_; lean_object* v_buildDir_911_; lean_object* v_irDir_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_lib_906_ = lean_ctor_get(v_self_905_, 0);
v_pkg_907_ = lean_ctor_get(v_lib_906_, 0);
lean_inc_ref(v_pkg_907_);
v_config_908_ = lean_ctor_get(v_pkg_907_, 6);
lean_inc_ref(v_config_908_);
v_name_909_ = lean_ctor_get(v_self_905_, 1);
lean_inc(v_name_909_);
lean_dec_ref(v_self_905_);
v_dir_910_ = lean_ctor_get(v_pkg_907_, 4);
lean_inc_ref(v_dir_910_);
lean_dec_ref(v_pkg_907_);
v_buildDir_911_ = lean_ctor_get(v_config_908_, 5);
lean_inc_ref(v_buildDir_911_);
v_irDir_912_ = lean_ctor_get(v_config_908_, 9);
lean_inc_ref(v_irDir_912_);
lean_dec_ref(v_config_908_);
v___x_913_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_914_ = l_System_FilePath_normalize(v_buildDir_911_);
v___x_915_ = l_Lake_joinRelative(v_dir_910_, v___x_914_);
v___x_916_ = l_System_FilePath_normalize(v_irDir_912_);
v___x_917_ = l_Lake_joinRelative(v___x_915_, v___x_916_);
v___x_918_ = l_Lean_modToFilePath(v___x_917_, v_name_909_, v___x_913_);
lean_dec_ref(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_921_){
_start:
{
lean_object* v_lib_922_; lean_object* v_name_923_; lean_object* v_pkg_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_lib_922_ = lean_ctor_get(v_self_921_, 0);
lean_inc_ref(v_lib_922_);
v_name_923_ = lean_ctor_get(v_self_921_, 1);
lean_inc(v_name_923_);
lean_dec_ref(v_self_921_);
v_pkg_924_ = lean_ctor_get(v_lib_922_, 0);
lean_inc_ref(v_pkg_924_);
lean_dec_ref(v_lib_922_);
v___x_925_ = l_Lake_Package_id_x3f(v_pkg_924_);
v___x_926_ = l_Lean_mkModuleInitializationStem(v_name_923_, v___x_925_);
lean_dec(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_928_){
_start:
{
lean_object* v_lib_929_; lean_object* v_pkg_930_; lean_object* v_config_931_; lean_object* v_name_932_; lean_object* v_dir_933_; lean_object* v_buildDir_934_; lean_object* v_leanLibDir_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_lib_929_ = lean_ctor_get(v_self_928_, 0);
v_pkg_930_ = lean_ctor_get(v_lib_929_, 0);
lean_inc_ref(v_pkg_930_);
v_config_931_ = lean_ctor_get(v_pkg_930_, 6);
v_name_932_ = lean_ctor_get(v_self_928_, 1);
lean_inc(v_name_932_);
lean_dec_ref(v_self_928_);
v_dir_933_ = lean_ctor_get(v_pkg_930_, 4);
v_buildDir_934_ = lean_ctor_get(v_config_931_, 5);
v_leanLibDir_935_ = lean_ctor_get(v_config_931_, 6);
lean_inc_ref(v_buildDir_934_);
v___x_936_ = l_System_FilePath_normalize(v_buildDir_934_);
lean_inc_ref(v_dir_933_);
v___x_937_ = l_Lake_joinRelative(v_dir_933_, v___x_936_);
lean_inc_ref(v_leanLibDir_935_);
v___x_938_ = l_System_FilePath_normalize(v_leanLibDir_935_);
v___x_939_ = l_Lake_joinRelative(v___x_937_, v___x_938_);
v___x_940_ = l_Lake_Package_id_x3f(v_pkg_930_);
v___x_941_ = l_Lean_mkModuleInitializationStem(v_name_932_, v___x_940_);
lean_dec(v___x_940_);
v___x_942_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_943_ = lean_string_append(v___x_941_, v___x_942_);
v___x_944_ = l_Lake_sharedLibExt;
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
v___x_946_ = l_Lake_joinRelative(v___x_939_, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_947_){
_start:
{
lean_object* v_lib_948_; lean_object* v_pkg_949_; lean_object* v_config_950_; lean_object* v_toLeanConfig_951_; lean_object* v_config_952_; lean_object* v_toLeanConfig_953_; uint8_t v_buildType_954_; lean_object* v_leanOptions_955_; lean_object* v_moreServerOptions_956_; uint8_t v_buildType_957_; lean_object* v_leanOptions_958_; lean_object* v_moreServerOptions_959_; lean_object* v___x_960_; uint8_t v___y_962_; uint8_t v___x_970_; 
v_lib_948_ = lean_ctor_get(v_self_947_, 0);
v_pkg_949_ = lean_ctor_get(v_lib_948_, 0);
v_config_950_ = lean_ctor_get(v_pkg_949_, 6);
v_toLeanConfig_951_ = lean_ctor_get(v_config_950_, 1);
v_config_952_ = lean_ctor_get(v_lib_948_, 2);
v_toLeanConfig_953_ = lean_ctor_get(v_config_952_, 0);
v_buildType_954_ = lean_ctor_get_uint8(v_toLeanConfig_951_, sizeof(void*)*13);
v_leanOptions_955_ = lean_ctor_get(v_toLeanConfig_951_, 0);
v_moreServerOptions_956_ = lean_ctor_get(v_toLeanConfig_951_, 4);
v_buildType_957_ = lean_ctor_get_uint8(v_toLeanConfig_953_, sizeof(void*)*13);
v_leanOptions_958_ = lean_ctor_get(v_toLeanConfig_953_, 0);
v_moreServerOptions_959_ = lean_ctor_get(v_toLeanConfig_953_, 4);
v___x_960_ = lean_box(1);
v___x_970_ = l_Lake_instOrdBuildType_ord(v_buildType_954_, v_buildType_957_);
if (v___x_970_ == 2)
{
v___y_962_ = v_buildType_957_;
goto v___jp_961_;
}
else
{
v___y_962_ = v_buildType_954_;
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_963_ = l_Lake_BuildType_leanOptions(v___y_962_);
v___x_964_ = l_Lean_LeanOptions_append(v___x_960_, v___x_963_);
v___x_965_ = l_Lean_LeanOptions_ofArray(v_leanOptions_955_);
v___x_966_ = l_Lean_LeanOptions_appendArray(v___x_965_, v_moreServerOptions_956_);
v___x_967_ = l_Lean_LeanOptions_append(v___x_964_, v___x_966_);
v___x_968_ = l_Lean_LeanOptions_appendArray(v___x_967_, v_leanOptions_958_);
v___x_969_ = l_Lean_LeanOptions_appendArray(v___x_968_, v_moreServerOptions_959_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lake_Module_serverOptions(v_self_971_);
lean_dec_ref(v_self_971_);
return v_res_972_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_973_){
_start:
{
lean_object* v_lib_974_; lean_object* v_pkg_975_; lean_object* v_config_976_; lean_object* v_toLeanConfig_977_; lean_object* v_config_978_; lean_object* v_toLeanConfig_979_; uint8_t v_buildType_980_; uint8_t v_buildType_981_; uint8_t v___x_982_; 
v_lib_974_ = lean_ctor_get(v_self_973_, 0);
v_pkg_975_ = lean_ctor_get(v_lib_974_, 0);
v_config_976_ = lean_ctor_get(v_pkg_975_, 6);
v_toLeanConfig_977_ = lean_ctor_get(v_config_976_, 1);
v_config_978_ = lean_ctor_get(v_lib_974_, 2);
v_toLeanConfig_979_ = lean_ctor_get(v_config_978_, 0);
v_buildType_980_ = lean_ctor_get_uint8(v_toLeanConfig_977_, sizeof(void*)*13);
v_buildType_981_ = lean_ctor_get_uint8(v_toLeanConfig_979_, sizeof(void*)*13);
v___x_982_ = l_Lake_instOrdBuildType_ord(v_buildType_980_, v_buildType_981_);
if (v___x_982_ == 2)
{
return v_buildType_981_;
}
else
{
return v_buildType_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_983_){
_start:
{
uint8_t v_res_984_; lean_object* v_r_985_; 
v_res_984_ = l_Lake_Module_buildType(v_self_983_);
lean_dec_ref(v_self_983_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_986_){
_start:
{
lean_object* v_lib_987_; lean_object* v_config_988_; lean_object* v_toLeanConfig_989_; lean_object* v_pkg_990_; lean_object* v_config_991_; lean_object* v_toLeanConfig_992_; uint8_t v_backend_993_; uint8_t v_backend_994_; uint8_t v___x_995_; 
v_lib_987_ = lean_ctor_get(v_self_986_, 0);
v_config_988_ = lean_ctor_get(v_lib_987_, 2);
v_toLeanConfig_989_ = lean_ctor_get(v_config_988_, 0);
v_pkg_990_ = lean_ctor_get(v_lib_987_, 0);
v_config_991_ = lean_ctor_get(v_pkg_990_, 6);
v_toLeanConfig_992_ = lean_ctor_get(v_config_991_, 1);
v_backend_993_ = lean_ctor_get_uint8(v_toLeanConfig_989_, sizeof(void*)*13 + 1);
v_backend_994_ = lean_ctor_get_uint8(v_toLeanConfig_992_, sizeof(void*)*13 + 1);
v___x_995_ = l_Lake_Backend_orPreferLeft(v_backend_993_, v_backend_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = l_Lake_Module_backend(v_self_996_);
lean_dec_ref(v_self_996_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_999_){
_start:
{
lean_object* v_lib_1000_; lean_object* v_config_1001_; uint8_t v_allowImportAll_1002_; 
v_lib_1000_ = lean_ctor_get(v_self_999_, 0);
v_config_1001_ = lean_ctor_get(v_lib_1000_, 2);
v_allowImportAll_1002_ = lean_ctor_get_uint8(v_config_1001_, sizeof(void*)*9 + 3);
if (v_allowImportAll_1002_ == 0)
{
lean_object* v_pkg_1003_; lean_object* v_config_1004_; uint8_t v_allowImportAll_1005_; 
v_pkg_1003_ = lean_ctor_get(v_lib_1000_, 0);
v_config_1004_ = lean_ctor_get(v_pkg_1003_, 6);
v_allowImportAll_1005_ = lean_ctor_get_uint8(v_config_1004_, sizeof(void*)*28 + 5);
return v_allowImportAll_1005_;
}
else
{
return v_allowImportAll_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lake_Module_allowImportAll(v_self_1006_);
lean_dec_ref(v_self_1006_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_requiresModuleSystem(lean_object* v_self_1009_){
_start:
{
lean_object* v_lib_1010_; lean_object* v_config_1011_; lean_object* v_toLeanConfig_1012_; uint8_t v_requiresModuleSystem_1013_; 
v_lib_1010_ = lean_ctor_get(v_self_1009_, 0);
v_config_1011_ = lean_ctor_get(v_lib_1010_, 2);
v_toLeanConfig_1012_ = lean_ctor_get(v_config_1011_, 0);
v_requiresModuleSystem_1013_ = lean_ctor_get_uint8(v_toLeanConfig_1012_, sizeof(void*)*13 + 3);
if (v_requiresModuleSystem_1013_ == 0)
{
lean_object* v_pkg_1014_; lean_object* v_config_1015_; lean_object* v_toLeanConfig_1016_; uint8_t v_requiresModuleSystem_1017_; 
v_pkg_1014_ = lean_ctor_get(v_lib_1010_, 0);
v_config_1015_ = lean_ctor_get(v_pkg_1014_, 6);
v_toLeanConfig_1016_ = lean_ctor_get(v_config_1015_, 1);
v_requiresModuleSystem_1017_ = lean_ctor_get_uint8(v_toLeanConfig_1016_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_1017_;
}
else
{
return v_requiresModuleSystem_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object* v_self_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lake_Module_requiresModuleSystem(v_self_1018_);
lean_dec_ref(v_self_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowNonModules(lean_object* v_self_1021_){
_start:
{
lean_object* v_lib_1022_; lean_object* v_config_1023_; lean_object* v_toLeanConfig_1024_; uint8_t v_allowNonModules_1025_; 
v_lib_1022_ = lean_ctor_get(v_self_1021_, 0);
v_config_1023_ = lean_ctor_get(v_lib_1022_, 2);
v_toLeanConfig_1024_ = lean_ctor_get(v_config_1023_, 0);
v_allowNonModules_1025_ = lean_ctor_get_uint8(v_toLeanConfig_1024_, sizeof(void*)*13 + 4);
if (v_allowNonModules_1025_ == 0)
{
lean_object* v_pkg_1026_; lean_object* v_config_1027_; lean_object* v_toLeanConfig_1028_; uint8_t v_allowNonModules_1029_; 
v_pkg_1026_ = lean_ctor_get(v_lib_1022_, 0);
v_config_1027_ = lean_ctor_get(v_pkg_1026_, 6);
v_toLeanConfig_1028_ = lean_ctor_get(v_config_1027_, 1);
v_allowNonModules_1029_ = lean_ctor_get_uint8(v_toLeanConfig_1028_, sizeof(void*)*13 + 4);
return v_allowNonModules_1029_;
}
else
{
return v_allowNonModules_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object* v_self_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = l_Lake_Module_allowNonModules(v_self_1030_);
lean_dec_ref(v_self_1030_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_1033_){
_start:
{
lean_object* v_lib_1034_; lean_object* v_pkg_1035_; lean_object* v_config_1036_; lean_object* v_toLeanConfig_1037_; lean_object* v_config_1038_; lean_object* v_toLeanConfig_1039_; lean_object* v_dynlibs_1040_; lean_object* v_dynlibs_1041_; lean_object* v___x_1042_; 
v_lib_1034_ = lean_ctor_get(v_self_1033_, 0);
lean_inc_ref(v_lib_1034_);
lean_dec_ref(v_self_1033_);
v_pkg_1035_ = lean_ctor_get(v_lib_1034_, 0);
v_config_1036_ = lean_ctor_get(v_pkg_1035_, 6);
v_toLeanConfig_1037_ = lean_ctor_get(v_config_1036_, 1);
lean_inc_ref(v_toLeanConfig_1037_);
v_config_1038_ = lean_ctor_get(v_lib_1034_, 2);
lean_inc(v_config_1038_);
lean_dec_ref(v_lib_1034_);
v_toLeanConfig_1039_ = lean_ctor_get(v_config_1038_, 0);
lean_inc_ref(v_toLeanConfig_1039_);
lean_dec(v_config_1038_);
v_dynlibs_1040_ = lean_ctor_get(v_toLeanConfig_1037_, 11);
lean_inc_ref(v_dynlibs_1040_);
lean_dec_ref(v_toLeanConfig_1037_);
v_dynlibs_1041_ = lean_ctor_get(v_toLeanConfig_1039_, 11);
lean_inc_ref(v_dynlibs_1041_);
lean_dec_ref(v_toLeanConfig_1039_);
v___x_1042_ = l_Array_append___redArg(v_dynlibs_1040_, v_dynlibs_1041_);
lean_dec_ref(v_dynlibs_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1043_){
_start:
{
lean_object* v_lib_1044_; lean_object* v_pkg_1045_; lean_object* v_config_1046_; lean_object* v_toLeanConfig_1047_; lean_object* v_config_1048_; lean_object* v_toLeanConfig_1049_; lean_object* v_plugins_1050_; lean_object* v_plugins_1051_; lean_object* v___x_1052_; 
v_lib_1044_ = lean_ctor_get(v_self_1043_, 0);
lean_inc_ref(v_lib_1044_);
lean_dec_ref(v_self_1043_);
v_pkg_1045_ = lean_ctor_get(v_lib_1044_, 0);
v_config_1046_ = lean_ctor_get(v_pkg_1045_, 6);
v_toLeanConfig_1047_ = lean_ctor_get(v_config_1046_, 1);
lean_inc_ref(v_toLeanConfig_1047_);
v_config_1048_ = lean_ctor_get(v_lib_1044_, 2);
lean_inc(v_config_1048_);
lean_dec_ref(v_lib_1044_);
v_toLeanConfig_1049_ = lean_ctor_get(v_config_1048_, 0);
lean_inc_ref(v_toLeanConfig_1049_);
lean_dec(v_config_1048_);
v_plugins_1050_ = lean_ctor_get(v_toLeanConfig_1047_, 12);
lean_inc_ref(v_plugins_1050_);
lean_dec_ref(v_toLeanConfig_1047_);
v_plugins_1051_ = lean_ctor_get(v_toLeanConfig_1049_, 12);
lean_inc_ref(v_plugins_1051_);
lean_dec_ref(v_toLeanConfig_1049_);
v___x_1052_ = l_Array_append___redArg(v_plugins_1050_, v_plugins_1051_);
lean_dec_ref(v_plugins_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1053_){
_start:
{
lean_object* v_lib_1054_; lean_object* v_pkg_1055_; lean_object* v_config_1056_; lean_object* v_toLeanConfig_1057_; lean_object* v_config_1058_; lean_object* v_toLeanConfig_1059_; uint8_t v_buildType_1060_; lean_object* v_leanOptions_1061_; uint8_t v_buildType_1062_; lean_object* v_leanOptions_1063_; uint8_t v___y_1065_; uint8_t v___x_1070_; 
v_lib_1054_ = lean_ctor_get(v_self_1053_, 0);
v_pkg_1055_ = lean_ctor_get(v_lib_1054_, 0);
v_config_1056_ = lean_ctor_get(v_pkg_1055_, 6);
v_toLeanConfig_1057_ = lean_ctor_get(v_config_1056_, 1);
v_config_1058_ = lean_ctor_get(v_lib_1054_, 2);
v_toLeanConfig_1059_ = lean_ctor_get(v_config_1058_, 0);
v_buildType_1060_ = lean_ctor_get_uint8(v_toLeanConfig_1057_, sizeof(void*)*13);
v_leanOptions_1061_ = lean_ctor_get(v_toLeanConfig_1057_, 0);
v_buildType_1062_ = lean_ctor_get_uint8(v_toLeanConfig_1059_, sizeof(void*)*13);
v_leanOptions_1063_ = lean_ctor_get(v_toLeanConfig_1059_, 0);
v___x_1070_ = l_Lake_instOrdBuildType_ord(v_buildType_1060_, v_buildType_1062_);
if (v___x_1070_ == 2)
{
v___y_1065_ = v_buildType_1062_;
goto v___jp_1064_;
}
else
{
v___y_1065_ = v_buildType_1060_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = l_Lake_BuildType_leanOptions(v___y_1065_);
v___x_1067_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1061_);
v___x_1068_ = l_Lean_LeanOptions_append(v___x_1066_, v___x_1067_);
v___x_1069_ = l_Lean_LeanOptions_appendArray(v___x_1068_, v_leanOptions_1063_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lake_Module_leanOptions(v_self_1071_);
lean_dec_ref(v_self_1071_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lake_Module_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1074_){
_start:
{
lean_object* v_lib_1075_; lean_object* v_pkg_1076_; lean_object* v_config_1077_; lean_object* v_toLeanConfig_1078_; lean_object* v_config_1079_; lean_object* v_toLeanConfig_1080_; uint8_t v_buildType_1081_; lean_object* v_moreLeanArgs_1082_; uint8_t v_buildType_1083_; lean_object* v_moreLeanArgs_1084_; uint8_t v___x_1089_; 
v_lib_1075_ = lean_ctor_get(v_self_1074_, 0);
v_pkg_1076_ = lean_ctor_get(v_lib_1075_, 0);
v_config_1077_ = lean_ctor_get(v_pkg_1076_, 6);
v_toLeanConfig_1078_ = lean_ctor_get(v_config_1077_, 1);
v_config_1079_ = lean_ctor_get(v_lib_1075_, 2);
v_toLeanConfig_1080_ = lean_ctor_get(v_config_1079_, 0);
v_buildType_1081_ = lean_ctor_get_uint8(v_toLeanConfig_1078_, sizeof(void*)*13);
v_moreLeanArgs_1082_ = lean_ctor_get(v_toLeanConfig_1078_, 1);
v_buildType_1083_ = lean_ctor_get_uint8(v_toLeanConfig_1080_, sizeof(void*)*13);
v_moreLeanArgs_1084_ = lean_ctor_get(v_toLeanConfig_1080_, 1);
v___x_1089_ = l_Lake_instOrdBuildType_ord(v_buildType_1081_, v_buildType_1083_);
if (v___x_1089_ == 2)
{
goto v___jp_1085_;
}
else
{
goto v___jp_1085_;
}
v___jp_1085_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_obj_once(&l_Lake_Module_leanArgs___closed__0, &l_Lake_Module_leanArgs___closed__0_once, _init_l_Lake_Module_leanArgs___closed__0);
v___x_1087_ = l_Array_append___redArg(v___x_1086_, v_moreLeanArgs_1082_);
v___x_1088_ = l_Array_append___redArg(v___x_1087_, v_moreLeanArgs_1084_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lake_Module_leanArgs(v_self_1090_);
lean_dec_ref(v_self_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1092_){
_start:
{
lean_object* v_lib_1093_; lean_object* v_pkg_1094_; lean_object* v_config_1095_; lean_object* v_toLeanConfig_1096_; lean_object* v_config_1097_; lean_object* v_toLeanConfig_1098_; lean_object* v_weakLeanArgs_1099_; lean_object* v_weakLeanArgs_1100_; lean_object* v___x_1101_; 
v_lib_1093_ = lean_ctor_get(v_self_1092_, 0);
lean_inc_ref(v_lib_1093_);
lean_dec_ref(v_self_1092_);
v_pkg_1094_ = lean_ctor_get(v_lib_1093_, 0);
v_config_1095_ = lean_ctor_get(v_pkg_1094_, 6);
v_toLeanConfig_1096_ = lean_ctor_get(v_config_1095_, 1);
lean_inc_ref(v_toLeanConfig_1096_);
v_config_1097_ = lean_ctor_get(v_lib_1093_, 2);
lean_inc(v_config_1097_);
lean_dec_ref(v_lib_1093_);
v_toLeanConfig_1098_ = lean_ctor_get(v_config_1097_, 0);
lean_inc_ref(v_toLeanConfig_1098_);
lean_dec(v_config_1097_);
v_weakLeanArgs_1099_ = lean_ctor_get(v_toLeanConfig_1096_, 2);
lean_inc_ref(v_weakLeanArgs_1099_);
lean_dec_ref(v_toLeanConfig_1096_);
v_weakLeanArgs_1100_ = lean_ctor_get(v_toLeanConfig_1098_, 2);
lean_inc_ref(v_weakLeanArgs_1100_);
lean_dec_ref(v_toLeanConfig_1098_);
v___x_1101_ = l_Array_append___redArg(v_weakLeanArgs_1099_, v_weakLeanArgs_1100_);
lean_dec_ref(v_weakLeanArgs_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1102_){
_start:
{
lean_object* v_lib_1103_; lean_object* v_pkg_1104_; lean_object* v_config_1105_; lean_object* v_toLeanConfig_1106_; lean_object* v_config_1107_; lean_object* v_toLeanConfig_1108_; uint8_t v_buildType_1109_; lean_object* v_moreLeancArgs_1110_; uint8_t v_buildType_1111_; lean_object* v_moreLeancArgs_1112_; uint8_t v___y_1114_; uint8_t v___x_1118_; 
v_lib_1103_ = lean_ctor_get(v_self_1102_, 0);
v_pkg_1104_ = lean_ctor_get(v_lib_1103_, 0);
v_config_1105_ = lean_ctor_get(v_pkg_1104_, 6);
v_toLeanConfig_1106_ = lean_ctor_get(v_config_1105_, 1);
v_config_1107_ = lean_ctor_get(v_lib_1103_, 2);
v_toLeanConfig_1108_ = lean_ctor_get(v_config_1107_, 0);
v_buildType_1109_ = lean_ctor_get_uint8(v_toLeanConfig_1106_, sizeof(void*)*13);
v_moreLeancArgs_1110_ = lean_ctor_get(v_toLeanConfig_1106_, 3);
v_buildType_1111_ = lean_ctor_get_uint8(v_toLeanConfig_1108_, sizeof(void*)*13);
v_moreLeancArgs_1112_ = lean_ctor_get(v_toLeanConfig_1108_, 3);
v___x_1118_ = l_Lake_instOrdBuildType_ord(v_buildType_1109_, v_buildType_1111_);
if (v___x_1118_ == 2)
{
v___y_1114_ = v_buildType_1111_;
goto v___jp_1113_;
}
else
{
v___y_1114_ = v_buildType_1109_;
goto v___jp_1113_;
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = l_Lake_BuildType_leancArgs(v___y_1114_);
v___x_1116_ = l_Array_append___redArg(v___x_1115_, v_moreLeancArgs_1110_);
v___x_1117_ = l_Array_append___redArg(v___x_1116_, v_moreLeancArgs_1112_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lake_Module_leancArgs(v_self_1119_);
lean_dec_ref(v_self_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1121_){
_start:
{
lean_object* v_lib_1122_; lean_object* v_pkg_1123_; lean_object* v_config_1124_; lean_object* v_toLeanConfig_1125_; lean_object* v_config_1126_; lean_object* v_toLeanConfig_1127_; lean_object* v_weakLeancArgs_1128_; lean_object* v_weakLeancArgs_1129_; lean_object* v___x_1130_; 
v_lib_1122_ = lean_ctor_get(v_self_1121_, 0);
lean_inc_ref(v_lib_1122_);
lean_dec_ref(v_self_1121_);
v_pkg_1123_ = lean_ctor_get(v_lib_1122_, 0);
v_config_1124_ = lean_ctor_get(v_pkg_1123_, 6);
v_toLeanConfig_1125_ = lean_ctor_get(v_config_1124_, 1);
lean_inc_ref(v_toLeanConfig_1125_);
v_config_1126_ = lean_ctor_get(v_lib_1122_, 2);
lean_inc(v_config_1126_);
lean_dec_ref(v_lib_1122_);
v_toLeanConfig_1127_ = lean_ctor_get(v_config_1126_, 0);
lean_inc_ref(v_toLeanConfig_1127_);
lean_dec(v_config_1126_);
v_weakLeancArgs_1128_ = lean_ctor_get(v_toLeanConfig_1125_, 5);
lean_inc_ref(v_weakLeancArgs_1128_);
lean_dec_ref(v_toLeanConfig_1125_);
v_weakLeancArgs_1129_ = lean_ctor_get(v_toLeanConfig_1127_, 5);
lean_inc_ref(v_weakLeancArgs_1129_);
lean_dec_ref(v_toLeanConfig_1127_);
v___x_1130_ = l_Array_append___redArg(v_weakLeancArgs_1128_, v_weakLeancArgs_1129_);
lean_dec_ref(v_weakLeancArgs_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1131_){
_start:
{
lean_object* v_lib_1132_; lean_object* v_pkg_1133_; lean_object* v_config_1134_; lean_object* v_toLeanConfig_1135_; lean_object* v_config_1136_; lean_object* v_toLeanConfig_1137_; lean_object* v_moreLinkArgs_1138_; lean_object* v_moreLinkArgs_1139_; lean_object* v___x_1140_; 
v_lib_1132_ = lean_ctor_get(v_self_1131_, 0);
lean_inc_ref(v_lib_1132_);
lean_dec_ref(v_self_1131_);
v_pkg_1133_ = lean_ctor_get(v_lib_1132_, 0);
v_config_1134_ = lean_ctor_get(v_pkg_1133_, 6);
v_toLeanConfig_1135_ = lean_ctor_get(v_config_1134_, 1);
lean_inc_ref(v_toLeanConfig_1135_);
v_config_1136_ = lean_ctor_get(v_lib_1132_, 2);
lean_inc(v_config_1136_);
lean_dec_ref(v_lib_1132_);
v_toLeanConfig_1137_ = lean_ctor_get(v_config_1136_, 0);
lean_inc_ref(v_toLeanConfig_1137_);
lean_dec(v_config_1136_);
v_moreLinkArgs_1138_ = lean_ctor_get(v_toLeanConfig_1135_, 8);
lean_inc_ref(v_moreLinkArgs_1138_);
lean_dec_ref(v_toLeanConfig_1135_);
v_moreLinkArgs_1139_ = lean_ctor_get(v_toLeanConfig_1137_, 8);
lean_inc_ref(v_moreLinkArgs_1139_);
lean_dec_ref(v_toLeanConfig_1137_);
v___x_1140_ = l_Array_append___redArg(v_moreLinkArgs_1138_, v_moreLinkArgs_1139_);
lean_dec_ref(v_moreLinkArgs_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1141_){
_start:
{
lean_object* v_lib_1142_; lean_object* v_pkg_1143_; lean_object* v_config_1144_; lean_object* v_toLeanConfig_1145_; lean_object* v_config_1146_; lean_object* v_toLeanConfig_1147_; lean_object* v_weakLinkArgs_1148_; lean_object* v_weakLinkArgs_1149_; lean_object* v___x_1150_; 
v_lib_1142_ = lean_ctor_get(v_self_1141_, 0);
lean_inc_ref(v_lib_1142_);
lean_dec_ref(v_self_1141_);
v_pkg_1143_ = lean_ctor_get(v_lib_1142_, 0);
v_config_1144_ = lean_ctor_get(v_pkg_1143_, 6);
v_toLeanConfig_1145_ = lean_ctor_get(v_config_1144_, 1);
lean_inc_ref(v_toLeanConfig_1145_);
v_config_1146_ = lean_ctor_get(v_lib_1142_, 2);
lean_inc(v_config_1146_);
lean_dec_ref(v_lib_1142_);
v_toLeanConfig_1147_ = lean_ctor_get(v_config_1146_, 0);
lean_inc_ref(v_toLeanConfig_1147_);
lean_dec(v_config_1146_);
v_weakLinkArgs_1148_ = lean_ctor_get(v_toLeanConfig_1145_, 9);
lean_inc_ref(v_weakLinkArgs_1148_);
lean_dec_ref(v_toLeanConfig_1145_);
v_weakLinkArgs_1149_ = lean_ctor_get(v_toLeanConfig_1147_, 9);
lean_inc_ref(v_weakLinkArgs_1149_);
lean_dec_ref(v_toLeanConfig_1147_);
v___x_1150_ = l_Array_append___redArg(v_weakLinkArgs_1148_, v_weakLinkArgs_1149_);
lean_dec_ref(v_weakLinkArgs_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1152_){
_start:
{
lean_object* v_lib_1153_; lean_object* v_pkg_1154_; lean_object* v_config_1155_; uint8_t v_bootstrap_1156_; 
v_lib_1153_ = lean_ctor_get(v_self_1152_, 0);
lean_inc_ref(v_lib_1153_);
lean_dec_ref(v_self_1152_);
v_pkg_1154_ = lean_ctor_get(v_lib_1153_, 0);
lean_inc_ref(v_pkg_1154_);
lean_dec_ref(v_lib_1153_);
v_config_1155_ = lean_ctor_get(v_pkg_1154_, 6);
lean_inc_ref(v_config_1155_);
v_bootstrap_1156_ = lean_ctor_get_uint8(v_config_1155_, sizeof(void*)*28);
if (v_bootstrap_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v_config_1155_);
lean_dec_ref(v_pkg_1154_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
lean_object* v_dir_1158_; lean_object* v_buildDir_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_dir_1158_ = lean_ctor_get(v_pkg_1154_, 4);
lean_inc_ref(v_dir_1158_);
lean_dec_ref(v_pkg_1154_);
v_buildDir_1159_ = lean_ctor_get(v_config_1155_, 5);
lean_inc_ref(v_buildDir_1159_);
lean_dec_ref(v_config_1155_);
v___x_1160_ = l_System_FilePath_normalize(v_buildDir_1159_);
v___x_1161_ = l_Lake_joinRelative(v_dir_1158_, v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1163_ = l_Lake_joinRelative(v___x_1161_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1165_){
_start:
{
lean_object* v_lib_1166_; lean_object* v_config_1167_; lean_object* v_toLeanConfig_1168_; lean_object* v_platformIndependent_1169_; 
v_lib_1166_ = lean_ctor_get(v_self_1165_, 0);
v_config_1167_ = lean_ctor_get(v_lib_1166_, 2);
v_toLeanConfig_1168_ = lean_ctor_get(v_config_1167_, 0);
v_platformIndependent_1169_ = lean_ctor_get(v_toLeanConfig_1168_, 10);
if (lean_obj_tag(v_platformIndependent_1169_) == 0)
{
lean_object* v_pkg_1170_; lean_object* v_config_1171_; lean_object* v_toLeanConfig_1172_; lean_object* v_platformIndependent_1173_; 
v_pkg_1170_ = lean_ctor_get(v_lib_1166_, 0);
v_config_1171_ = lean_ctor_get(v_pkg_1170_, 6);
v_toLeanConfig_1172_ = lean_ctor_get(v_config_1171_, 1);
v_platformIndependent_1173_ = lean_ctor_get(v_toLeanConfig_1172_, 10);
lean_inc(v_platformIndependent_1173_);
return v_platformIndependent_1173_;
}
else
{
lean_inc_ref(v_platformIndependent_1169_);
return v_platformIndependent_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lake_Module_platformIndependent(v_self_1174_);
lean_dec_ref(v_self_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompileImports(lean_object* v_self_1176_){
_start:
{
lean_object* v_lib_1177_; lean_object* v_pkg_1178_; lean_object* v_config_1179_; uint8_t v_precompileModules_1180_; 
v_lib_1177_ = lean_ctor_get(v_self_1176_, 0);
v_pkg_1178_ = lean_ctor_get(v_lib_1177_, 0);
v_config_1179_ = lean_ctor_get(v_pkg_1178_, 6);
v_precompileModules_1180_ = lean_ctor_get_uint8(v_config_1179_, sizeof(void*)*28 + 1);
if (v_precompileModules_1180_ == 0)
{
lean_object* v_config_1181_; uint8_t v_precompileModules_1182_; 
v_config_1181_ = lean_ctor_get(v_lib_1177_, 2);
v_precompileModules_1182_ = lean_ctor_get_uint8(v_config_1181_, sizeof(void*)*9 + 2);
if (v_precompileModules_1182_ == 0)
{
lean_object* v_toLeanConfig_1183_; uint8_t v_precompileImports_1184_; 
v_toLeanConfig_1183_ = lean_ctor_get(v_config_1179_, 1);
v_precompileImports_1184_ = lean_ctor_get_uint8(v_toLeanConfig_1183_, sizeof(void*)*13 + 2);
if (v_precompileImports_1184_ == 0)
{
lean_object* v_toLeanConfig_1185_; uint8_t v_precompileImports_1186_; 
v_toLeanConfig_1185_ = lean_ctor_get(v_config_1181_, 0);
v_precompileImports_1186_ = lean_ctor_get_uint8(v_toLeanConfig_1185_, sizeof(void*)*13 + 2);
return v_precompileImports_1186_;
}
else
{
return v_precompileImports_1184_;
}
}
else
{
return v_precompileModules_1182_;
}
}
else
{
return v_precompileModules_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompileImports___boxed(lean_object* v_self_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Lake_Module_shouldPrecompileImports(v_self_1187_);
lean_dec_ref(v_self_1187_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1190_){
_start:
{
lean_object* v_lib_1191_; lean_object* v_pkg_1192_; lean_object* v_config_1193_; uint8_t v_precompileModules_1194_; 
v_lib_1191_ = lean_ctor_get(v_self_1190_, 0);
v_pkg_1192_ = lean_ctor_get(v_lib_1191_, 0);
v_config_1193_ = lean_ctor_get(v_pkg_1192_, 6);
v_precompileModules_1194_ = lean_ctor_get_uint8(v_config_1193_, sizeof(void*)*28 + 1);
if (v_precompileModules_1194_ == 0)
{
lean_object* v_config_1195_; uint8_t v_precompileModules_1196_; 
v_config_1195_ = lean_ctor_get(v_lib_1191_, 2);
v_precompileModules_1196_ = lean_ctor_get_uint8(v_config_1195_, sizeof(void*)*9 + 2);
return v_precompileModules_1196_;
}
else
{
return v_precompileModules_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_Lake_Module_shouldPrecompile(v_self_1197_);
lean_dec_ref(v_self_1197_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1200_, uint8_t v_shouldExport_1201_){
_start:
{
lean_object* v_lib_1202_; lean_object* v_config_1203_; lean_object* v_nativeFacets_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_lib_1202_ = lean_ctor_get(v_self_1200_, 0);
lean_inc_ref(v_lib_1202_);
lean_dec_ref(v_self_1200_);
v_config_1203_ = lean_ctor_get(v_lib_1202_, 2);
lean_inc(v_config_1203_);
lean_dec_ref(v_lib_1202_);
v_nativeFacets_1204_ = lean_ctor_get(v_config_1203_, 8);
lean_inc_ref(v_nativeFacets_1204_);
lean_dec(v_config_1203_);
v___x_1205_ = lean_box(v_shouldExport_1201_);
v___x_1206_ = lean_apply_1(v_nativeFacets_1204_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1207_, lean_object* v_shouldExport_1208_){
_start:
{
uint8_t v_shouldExport_boxed_1209_; lean_object* v_res_1210_; 
v_shouldExport_boxed_1209_ = lean_unbox(v_shouldExport_1208_);
v_res_1210_ = l_Lake_Module_nativeFacets(v_self_1207_, v_shouldExport_boxed_1209_);
return v_res_1210_;
}
}
lean_object* runtime_initialize_Lake_Config_LeanLib(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Module(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_LeanLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_ModuleSet_empty = _init_l_Lake_ModuleSet_empty();
lean_mark_persistent(l_Lake_ModuleSet_empty);
l_Lake_OrdModuleSet_empty = _init_l_Lake_OrdModuleSet_empty();
lean_mark_persistent(l_Lake_OrdModuleSet_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Module(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_LeanLib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_LeanLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Module(builtin);
}
#ifdef __cplusplus
}
#endif
