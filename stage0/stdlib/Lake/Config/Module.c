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
lean_object* l_Lake_OrdHashSet_empty(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_BuildType_leanArgs(uint8_t);
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
lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___x_47_; 
v___f_45_ = ((lean_object*)(l_Lake_instBEqModule___closed__0));
v___f_46_ = ((lean_object*)(l_Lake_instHashableModule___closed__0));
v___x_47_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_46_, v___f_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lake_OrdModuleSet_empty(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Lake_OrdModuleSet_empty___closed__0, &l_Lake_OrdModuleSet_empty___closed__0_once, _init_l_Lake_OrdModuleSet_empty___closed__0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty(lean_object* v_00_u03b1_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(1);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModule_x3f(lean_object* v_mod_51_, lean_object* v_self_52_){
_start:
{
lean_object* v_config_53_; uint8_t v___x_54_; 
v_config_53_ = lean_ctor_get(v_self_52_, 2);
v___x_54_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_51_, v_config_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec_ref(v_self_52_);
lean_dec(v_mod_51_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_self_52_);
lean_ctor_set(v___x_56_, 1, v_mod_51_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(lean_object* v___x_58_, lean_object* v_s_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_60_ = lean_string_utf8_byte_size(v_s_59_);
v___x_61_ = lean_string_utf8_byte_size(v___x_58_);
v___x_62_ = lean_nat_dec_le(v___x_61_, v___x_60_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v_s_59_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_string_memcmp(v_s_59_, v___x_58_, v___x_64_, v___x_64_, v___x_61_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
lean_dec_ref(v_s_59_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_inc_ref(v_s_59_);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v_s_59_);
lean_ctor_set(v___x_67_, 1, v___x_64_);
lean_ctor_set(v___x_67_, 2, v___x_60_);
v___x_68_ = l_String_Slice_pos_x21(v___x_67_, v___x_61_);
lean_dec_ref_known(v___x_67_, 3);
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_s_59_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
lean_ctor_set(v___x_69_, 2, v___x_60_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object* v___x_71_, lean_object* v_s_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_71_, v_s_72_);
lean_dec_ref(v___x_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(lean_object* v___x_74_, lean_object* v_s_75_, lean_object* v_pat_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_74_, v_s_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___boxed(lean_object* v___x_78_, lean_object* v_s_79_, lean_object* v_pat_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(v___x_78_, v_s_79_, v_pat_80_);
lean_dec_ref(v_pat_80_);
lean_dec_ref(v___x_78_);
return v_res_81_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0));
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(lean_object* v_s_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_86_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0));
v___x_87_ = lean_string_utf8_byte_size(v_s_85_);
v___x_88_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1);
v___x_89_ = lean_nat_dec_le(v___x_88_, v___x_87_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec_ref(v_s_85_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_nat_sub(v___x_87_, v___x_88_);
v___x_93_ = lean_string_memcmp(v_s_85_, v___x_86_, v___x_92_, v___x_91_, v___x_88_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v___x_92_);
lean_dec_ref(v_s_85_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_inc_ref(v_s_85_);
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v_s_85_);
lean_ctor_set(v___x_95_, 1, v___x_91_);
lean_ctor_set(v___x_95_, 2, v___x_87_);
v___x_96_ = l_String_Slice_pos_x21(v___x_95_, v___x_92_);
lean_dec(v___x_92_);
lean_dec_ref_known(v___x_95_, 3);
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v_s_85_);
lean_ctor_set(v___x_97_, 1, v___x_91_);
lean_ctor_set(v___x_97_, 2, v___x_96_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(lean_object* v_s_99_, lean_object* v_pat_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v_s_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___boxed(lean_object* v_s_102_, lean_object* v_pat_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(v_s_102_, v_pat_103_);
lean_dec_ref(v_pat_103_);
return v_res_104_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1(void){
_start:
{
uint32_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = l_System_FilePath_pathSeparator;
v___x_107_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_108_ = lean_string_push(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
v___x_110_ = lean_string_utf8_byte_size(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(lean_object* v_s_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_112_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
v___x_113_ = lean_string_utf8_byte_size(v_s_111_);
v___x_114_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2);
v___x_115_ = lean_nat_dec_le(v___x_114_, v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
lean_dec_ref(v_s_111_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_sub(v___x_113_, v___x_114_);
v___x_119_ = lean_string_memcmp(v_s_111_, v___x_112_, v___x_118_, v___x_117_, v___x_114_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec(v___x_118_);
lean_dec_ref(v_s_111_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_inc_ref(v_s_111_);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v_s_111_);
lean_ctor_set(v___x_121_, 1, v___x_117_);
lean_ctor_set(v___x_121_, 2, v___x_113_);
v___x_122_ = l_String_Slice_pos_x21(v___x_121_, v___x_118_);
lean_dec(v___x_118_);
lean_dec_ref_known(v___x_121_, 3);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_s_111_);
lean_ctor_set(v___x_123_, 1, v___x_117_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(lean_object* v_s_125_, lean_object* v_pat_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v_s_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___boxed(lean_object* v_s_128_, lean_object* v_pat_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(v_s_128_, v_pat_129_);
lean_dec_ref(v_pat_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
return v_x_131_;
}
else
{
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v___x_135_; 
v_head_133_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_head_133_);
v_tail_134_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_tail_134_);
lean_dec_ref_known(v_x_132_, 2);
v___x_135_ = l_Lean_Name_str___override(v_x_131_, v_head_133_);
v_x_131_ = v___x_135_;
v_x_132_ = v_tail_134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModuleBySrc_x3f(lean_object* v_path_137_, lean_object* v_self_138_){
_start:
{
lean_object* v___y_140_; lean_object* v_pkg_148_; lean_object* v_config_149_; lean_object* v_config_150_; lean_object* v_dir_151_; lean_object* v_srcDir_152_; lean_object* v_srcDir_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_pkg_148_ = lean_ctor_get(v_self_138_, 0);
v_config_149_ = lean_ctor_get(v_pkg_148_, 6);
v_config_150_ = lean_ctor_get(v_self_138_, 2);
v_dir_151_ = lean_ctor_get(v_pkg_148_, 4);
v_srcDir_152_ = lean_ctor_get(v_config_149_, 4);
v_srcDir_153_ = lean_ctor_get(v_config_150_, 1);
lean_inc_ref(v_srcDir_152_);
v___x_154_ = l_System_FilePath_normalize(v_srcDir_152_);
lean_inc_ref(v_dir_151_);
v___x_155_ = l_Lake_joinRelative(v_dir_151_, v___x_154_);
lean_inc_ref(v_srcDir_153_);
v___x_156_ = l_System_FilePath_normalize(v_srcDir_153_);
v___x_157_ = l_Lake_joinRelative(v___x_155_, v___x_156_);
v___x_158_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_157_, v_path_137_);
lean_dec_ref(v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v___x_159_; 
lean_dec_ref(v_self_138_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v_str_161_; lean_object* v_startInclusive_162_; lean_object* v_endExclusive_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
v_val_160_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v___x_158_, 1);
v_str_161_ = lean_ctor_get(v_val_160_, 0);
lean_inc_ref(v_str_161_);
v_startInclusive_162_ = lean_ctor_get(v_val_160_, 1);
lean_inc(v_startInclusive_162_);
v_endExclusive_163_ = lean_ctor_get(v_val_160_, 2);
lean_inc(v_endExclusive_163_);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_String_Slice_Pos_nextn(v_val_160_, v___x_165_, v___x_164_);
v_isSharedCheck_177_ = !lean_is_exclusive(v_val_160_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_178_ = lean_ctor_get(v_val_160_, 2);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_val_160_, 1);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_val_160_, 0);
lean_dec(v_unused_180_);
v___x_168_ = v_val_160_;
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_val_160_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_nat_add(v_startInclusive_162_, v___x_166_);
lean_dec(v___x_166_);
lean_dec(v_startInclusive_162_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_str_161_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_endExclusive_163_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_String_Slice_toString(v___x_172_);
lean_dec_ref(v___x_172_);
lean_inc_ref(v___x_173_);
v___x_174_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v___x_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v___x_173_);
v___y_140_ = v___x_175_;
goto v___jp_139_;
}
else
{
lean_dec_ref(v___x_173_);
v___y_140_ = v___x_174_;
goto v___jp_139_;
}
}
}
}
v___jp_139_:
{
if (lean_obj_tag(v___y_140_) == 0)
{
lean_object* v___x_141_; 
lean_dec_ref(v_self_138_);
v___x_141_ = lean_box(0);
return v___x_141_;
}
else
{
lean_object* v_val_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_val_142_ = lean_ctor_get(v___y_140_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v___y_140_, 1);
v___x_143_ = lean_box(0);
v___x_144_ = l_String_Slice_toString(v_val_142_);
lean_dec(v_val_142_);
v___x_145_ = l_System_FilePath_components(v___x_144_);
v___x_146_ = l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(v___x_143_, v___x_145_);
v___x_147_ = l_Lake_LeanLib_findModule_x3f(v___x_146_, v_self_138_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(lean_object* v_self_184_, lean_object* v_as_185_, size_t v_i_186_, size_t v_stop_187_, lean_object* v_b_188_){
_start:
{
lean_object* v___y_190_; uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_186_, v_stop_187_);
if (v___x_194_ == 0)
{
lean_object* v_toConfigDecl_195_; lean_object* v_name_196_; lean_object* v_kind_197_; lean_object* v_config_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_toConfigDecl_195_ = lean_array_uget_borrowed(v_as_185_, v_i_186_);
v_name_196_ = lean_ctor_get(v_toConfigDecl_195_, 1);
v_kind_197_ = lean_ctor_get(v_toConfigDecl_195_, 2);
v_config_198_ = lean_ctor_get(v_toConfigDecl_195_, 3);
v___x_199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1));
v___x_200_ = lean_name_eq(v_kind_197_, v___x_199_);
if (v___x_200_ == 0)
{
v___y_190_ = v_b_188_;
goto v___jp_189_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_inc(v_config_198_);
lean_inc(v_name_196_);
lean_inc_ref(v_self_184_);
v___x_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_201_, 0, v_self_184_);
lean_ctor_set(v___x_201_, 1, v_name_196_);
lean_ctor_set(v___x_201_, 2, v_config_198_);
v___x_202_ = lean_array_push(v_b_188_, v___x_201_);
v___y_190_ = v___x_202_;
goto v___jp_189_;
}
}
else
{
lean_dec_ref(v_self_184_);
return v_b_188_;
}
v___jp_189_:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_186_, v___x_191_);
v_i_186_ = v___x_192_;
v_b_188_ = v___y_190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___boxed(lean_object* v_self_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_, lean_object* v_b_207_){
_start:
{
size_t v_i_boxed_208_; size_t v_stop_boxed_209_; lean_object* v_res_210_; 
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_209_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_203_, v_as_204_, v_i_boxed_208_, v_stop_boxed_209_, v_b_207_);
lean_dec_ref(v_as_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(lean_object* v_mod_211_, lean_object* v_as_212_, lean_object* v_i_213_){
_start:
{
lean_object* v_zero_214_; uint8_t v_isZero_215_; 
v_zero_214_ = lean_unsigned_to_nat(0u);
v_isZero_215_ = lean_nat_dec_eq(v_i_213_, v_zero_214_);
if (v_isZero_215_ == 1)
{
lean_object* v___x_216_; 
lean_dec(v_i_213_);
lean_dec(v_mod_211_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v_one_217_; lean_object* v_n_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_one_217_ = lean_unsigned_to_nat(1u);
v_n_218_ = lean_nat_sub(v_i_213_, v_one_217_);
lean_dec(v_i_213_);
v___x_219_ = lean_array_fget_borrowed(v_as_212_, v_n_218_);
lean_inc(v___x_219_);
lean_inc(v_mod_211_);
v___x_220_ = l_Lake_LeanLib_findModule_x3f(v_mod_211_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
v_i_213_ = v_n_218_;
goto _start;
}
else
{
lean_dec(v_n_218_);
lean_dec(v_mod_211_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_222_, lean_object* v_as_223_, lean_object* v_i_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_222_, v_as_223_, v_i_224_);
lean_dec_ref(v_as_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object* v_mod_228_, lean_object* v_self_229_){
_start:
{
lean_object* v___y_231_; lean_object* v_targetDecls_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_targetDecls_234_ = lean_ctor_get(v_self_229_, 15);
lean_inc_ref(v_targetDecls_234_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = ((lean_object*)(l_Lake_Package_findModule_x3f___closed__0));
v___x_237_ = lean_array_get_size(v_targetDecls_234_);
v___x_238_ = lean_nat_dec_lt(v___x_235_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec_ref(v_targetDecls_234_);
lean_dec_ref(v_self_229_);
v___y_231_ = v___x_236_;
goto v___jp_230_;
}
else
{
uint8_t v___x_239_; 
v___x_239_ = lean_nat_dec_le(v___x_237_, v___x_237_);
if (v___x_239_ == 0)
{
if (v___x_238_ == 0)
{
lean_dec_ref(v_targetDecls_234_);
lean_dec_ref(v_self_229_);
v___y_231_ = v___x_236_;
goto v___jp_230_;
}
else
{
size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_usize_of_nat(v___x_237_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_229_, v_targetDecls_234_, v___x_240_, v___x_241_, v___x_236_);
lean_dec_ref(v_targetDecls_234_);
v___y_231_ = v___x_242_;
goto v___jp_230_;
}
}
else
{
size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((size_t)0ULL);
v___x_244_ = lean_usize_of_nat(v___x_237_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_229_, v_targetDecls_234_, v___x_243_, v___x_244_, v___x_236_);
lean_dec_ref(v_targetDecls_234_);
v___y_231_ = v___x_245_;
goto v___jp_230_;
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_array_get_size(v___y_231_);
v___x_233_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_228_, v___y_231_, v___x_232_);
lean_dec_ref(v___y_231_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(lean_object* v_mod_246_, lean_object* v_as_247_, lean_object* v_i_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_246_, v_as_247_, v_i_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(lean_object* v_mod_251_, lean_object* v_as_252_, lean_object* v_i_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_251_, v_as_252_, v_i_253_, v_a_254_);
lean_dec_ref(v_as_252_);
return v_res_255_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object* v_x_256_, lean_object* v_x_257_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object* v___x_268_, lean_object* v_f_269_, lean_object* v_x_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = l_Lean_Name_append(v___x_268_, v_x_270_);
v___x_274_ = lean_apply_3(v_f_269_, v___x_273_, v___y_271_, lean_box(0));
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object* v___x_275_, lean_object* v_f_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_275_, v_f_276_, v_x_277_, v___y_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object* v_f_284_, lean_object* v_as_285_, size_t v_sz_286_, size_t v_i_287_, lean_object* v_b_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_a_292_; lean_object* v_snd_293_; uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_lt(v_i_287_, v_sz_286_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_f_284_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_b_288_);
lean_ctor_set(v___x_298_, 1, v___y_289_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v_a_300_; lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; 
v_a_300_ = lean_array_uget_borrowed(v_as_285_, v_i_287_);
lean_inc(v_a_300_);
v___x_301_ = l_IO_FS_DirEntry_path(v_a_300_);
v___x_302_ = l_System_FilePath_isDir(v___x_301_);
v___x_303_ = lean_box(0);
if (v___x_302_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_System_FilePath_extension(v___x_301_);
v___x_305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1));
v___x_306_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_304_, v___x_305_);
lean_dec(v___x_304_);
if (v___x_306_ == 0)
{
v_a_292_ = v___x_303_;
v_snd_293_ = v___y_289_;
goto v___jp_291_;
}
else
{
lean_object* v_fileName_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_fileName_307_ = lean_ctor_get(v_a_300_, 1);
v___x_308_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc_ref(v_fileName_307_);
v___x_309_ = l_System_FilePath_withExtension(v_fileName_307_, v___x_308_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_Name_str___override(v___x_310_, v___x_309_);
lean_inc_ref(v_f_284_);
v___x_312_ = lean_apply_3(v_f_284_, v___x_311_, v___y_289_, lean_box(0));
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_snd_314_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v_snd_314_ = lean_ctor_get(v_a_313_, 1);
lean_inc(v_snd_314_);
lean_dec(v_a_313_);
v_a_292_ = v___x_303_;
v_snd_293_ = v_snd_314_;
goto v___jp_291_;
}
else
{
lean_dec_ref(v_f_284_);
return v___x_312_;
}
}
}
else
{
lean_object* v_fileName_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___f_318_; lean_object* v___x_319_; 
v_fileName_315_ = lean_ctor_get(v_a_300_, 1);
v___x_316_ = lean_box(0);
lean_inc_ref(v_fileName_315_);
v___x_317_ = l_Lean_Name_str___override(v___x_316_, v_fileName_315_);
lean_inc_ref(v_f_284_);
v___f_318_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_318_, 0, v___x_317_);
lean_closure_set(v___f_318_, 1, v_f_284_);
v___x_319_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_301_, v___f_318_, v___y_289_);
lean_dec_ref(v___x_301_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_snd_321_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v_snd_321_ = lean_ctor_get(v_a_320_, 1);
lean_inc(v_snd_321_);
lean_dec(v_a_320_);
v_a_292_ = v___x_303_;
v_snd_293_ = v_snd_321_;
goto v___jp_291_;
}
else
{
lean_dec_ref(v_f_284_);
return v___x_319_;
}
}
}
v___jp_291_:
{
size_t v___x_294_; size_t v___x_295_; 
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_add(v_i_287_, v___x_294_);
v_i_287_ = v___x_295_;
v_b_288_ = v_a_292_;
v___y_289_ = v_snd_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object* v_dir_322_, lean_object* v_f_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_io_read_dir(v_dir_322_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; size_t v_sz_329_; size_t v___x_330_; lean_object* v___x_331_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = lean_box(0);
v_sz_329_ = lean_array_size(v_a_327_);
v___x_330_ = ((size_t)0ULL);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_323_, v_a_327_, v_sz_329_, v___x_330_, v___x_328_, v___y_324_);
lean_dec(v_a_327_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_348_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_348_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_348_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_348_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_346_; 
v_snd_336_ = lean_ctor_get(v_a_332_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v_a_332_, 0);
lean_dec(v_unused_347_);
v___x_338_ = v_a_332_;
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_dec(v_a_332_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_328_);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_336_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_341_);
v___x_343_ = v___x_334_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
else
{
return v___x_331_;
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v___y_324_);
lean_dec_ref(v_f_323_);
v_a_349_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_326_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_326_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object* v_dir_357_, lean_object* v_f_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_357_, v_f_358_, v___y_359_);
lean_dec_ref(v_dir_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object* v_f_362_, lean_object* v_as_363_, lean_object* v_sz_364_, lean_object* v_i_365_, lean_object* v_b_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_364_);
lean_dec(v_sz_364_);
v_i_boxed_370_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_362_, v_as_363_, v_sz_boxed_369_, v_i_boxed_370_, v_b_366_, v___y_367_);
lean_dec_ref(v_as_363_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object* v_self_372_, lean_object* v_mod_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_self_372_);
lean_ctor_set(v___x_377_, 1, v_mod_373_);
v___x_378_ = lean_array_push(v___y_374_, v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object* v_self_381_, lean_object* v_mod_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_381_, v_mod_382_, v___y_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object* v_a_386_, lean_object* v___f_387_, lean_object* v_x_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Lean_Name_append(v_a_386_, v_x_388_);
v___x_392_ = lean_apply_3(v___f_387_, v___x_391_, v___y_389_, lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object* v_a_393_, lean_object* v___f_394_, lean_object* v_x_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_393_, v___f_394_, v_x_395_, v___y_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object* v_self_399_, lean_object* v_as_400_, size_t v_i_401_, size_t v_stop_402_, lean_object* v_b_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___y_407_; uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_eq(v_i_401_, v_stop_402_);
if (v___x_414_ == 0)
{
lean_object* v_pkg_415_; lean_object* v_config_416_; lean_object* v_config_417_; lean_object* v_dir_418_; lean_object* v_srcDir_419_; lean_object* v_srcDir_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_pkg_415_ = lean_ctor_get(v_self_399_, 0);
v_config_416_ = lean_ctor_get(v_pkg_415_, 6);
v_config_417_ = lean_ctor_get(v_self_399_, 2);
v_dir_418_ = lean_ctor_get(v_pkg_415_, 4);
v_srcDir_419_ = lean_ctor_get(v_config_416_, 4);
v_srcDir_420_ = lean_ctor_get(v_config_417_, 1);
lean_inc_ref(v_self_399_);
v___f_421_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(v___f_421_, 0, v_self_399_);
v___x_422_ = lean_array_uget_borrowed(v_as_400_, v_i_401_);
lean_inc_ref(v_srcDir_419_);
v___x_423_ = l_System_FilePath_normalize(v_srcDir_419_);
lean_inc_ref(v_dir_418_);
v___x_424_ = l_Lake_joinRelative(v_dir_418_, v___x_423_);
lean_inc_ref(v_srcDir_420_);
v___x_425_ = l_System_FilePath_normalize(v_srcDir_420_);
v___x_426_ = l_Lake_joinRelative(v___x_424_, v___x_425_);
switch(lean_obj_tag(v___x_422_))
{
case 0:
{
lean_object* v_a_427_; lean_object* v___x_428_; 
lean_dec_ref(v___x_426_);
lean_dec_ref(v___f_421_);
v_a_427_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_427_);
lean_inc_ref(v_self_399_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_399_, v_a_427_, v___y_404_);
v___y_407_ = v___x_428_;
goto v___jp_406_;
}
case 1:
{
lean_object* v_a_429_; lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_429_ = lean_ctor_get(v___x_422_, 0);
lean_inc_n(v_a_429_, 2);
v___f_430_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_430_, 0, v_a_429_);
lean_closure_set(v___f_430_, 1, v___f_421_);
v___x_431_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_432_ = l_Lean_modToFilePath(v___x_426_, v_a_429_, v___x_431_);
lean_dec_ref(v___x_426_);
v___x_433_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_432_, v___f_430_, v___y_404_);
lean_dec_ref(v___x_432_);
v___y_407_ = v___x_433_;
goto v___jp_406_;
}
default: 
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_434_);
lean_inc_ref(v_self_399_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_399_, v_a_434_, v___y_404_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_snd_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v_snd_437_ = lean_ctor_get(v_a_436_, 1);
lean_inc(v_snd_437_);
lean_dec(v_a_436_);
lean_inc_n(v_a_434_, 2);
v___f_438_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_438_, 0, v_a_434_);
lean_closure_set(v___f_438_, 1, v___f_421_);
v___x_439_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_440_ = l_Lean_modToFilePath(v___x_426_, v_a_434_, v___x_439_);
lean_dec_ref(v___x_426_);
v___x_441_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_440_, v___f_438_, v_snd_437_);
lean_dec_ref(v___x_440_);
v___y_407_ = v___x_441_;
goto v___jp_406_;
}
else
{
lean_dec_ref(v___x_426_);
lean_dec_ref(v___f_421_);
lean_dec_ref(v_self_399_);
return v___x_435_;
}
}
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v_self_399_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_b_403_);
lean_ctor_set(v___x_442_, 1, v___y_404_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
v___jp_406_:
{
if (lean_obj_tag(v___y_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_fst_409_; lean_object* v_snd_410_; size_t v___x_411_; size_t v___x_412_; 
v_a_408_ = lean_ctor_get(v___y_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___y_407_, 1);
v_fst_409_ = lean_ctor_get(v_a_408_, 0);
lean_inc(v_fst_409_);
v_snd_410_ = lean_ctor_get(v_a_408_, 1);
lean_inc(v_snd_410_);
lean_dec(v_a_408_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_401_, v___x_411_);
v_i_401_ = v___x_412_;
v_b_403_ = v_fst_409_;
v___y_404_ = v_snd_410_;
goto _start;
}
else
{
lean_dec_ref(v_self_399_);
return v___y_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object* v_self_444_, lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
size_t v_i_boxed_451_; size_t v_stop_boxed_452_; lean_object* v_res_453_; 
v_i_boxed_451_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_452_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_444_, v_as_445_, v_i_boxed_451_, v_stop_boxed_452_, v_b_448_, v___y_449_);
lean_dec_ref(v_as_445_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object* v_self_456_){
_start:
{
lean_object* v___y_459_; lean_object* v_config_477_; lean_object* v_globs_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_config_477_ = lean_ctor_get(v_self_456_, 2);
v_globs_478_ = lean_ctor_get(v_config_477_, 3);
lean_inc_ref(v_globs_478_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_array_get_size(v_globs_478_);
v___x_481_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_482_ = lean_nat_dec_lt(v___x_479_, v___x_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_globs_478_);
lean_dec_ref(v_self_456_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_box(0);
v___x_485_ = lean_nat_dec_le(v___x_480_, v___x_480_);
if (v___x_485_ == 0)
{
if (v___x_482_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_globs_478_);
lean_dec_ref(v_self_456_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_481_);
return v___x_486_;
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_480_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_456_, v_globs_478_, v___x_487_, v___x_488_, v___x_484_, v___x_481_);
lean_dec_ref(v_globs_478_);
v___y_459_ = v___x_489_;
goto v___jp_458_;
}
}
else
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((size_t)0ULL);
v___x_491_ = lean_usize_of_nat(v___x_480_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_456_, v_globs_478_, v___x_490_, v___x_491_, v___x_484_, v___x_481_);
lean_dec_ref(v_globs_478_);
v___y_459_ = v___x_492_;
goto v___jp_458_;
}
}
v___jp_458_:
{
if (lean_obj_tag(v___y_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_468_; 
v_a_460_ = lean_ctor_get(v___y_459_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___y_459_);
if (v_isSharedCheck_468_ == 0)
{
v___x_462_ = v___y_459_;
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___y_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_snd_464_; lean_object* v___x_466_; 
v_snd_464_ = lean_ctor_get(v_a_460_, 1);
lean_inc(v_snd_464_);
lean_dec(v_a_460_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v_snd_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_snd_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___y_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___y_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___y_459_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___y_459_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object* v_self_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lake_LeanLib_getModuleArray(v_self_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object* v_self_496_, lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_, lean_object* v_b_500_){
_start:
{
lean_object* v___y_502_; uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_eq(v_i_498_, v_stop_499_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_array_uget_borrowed(v_as_497_, v_i_498_);
lean_inc_ref(v_self_496_);
lean_inc(v___x_507_);
v___x_508_ = l_Lake_LeanLib_findModule_x3f(v___x_507_, v_self_496_);
if (lean_obj_tag(v___x_508_) == 0)
{
v___y_502_ = v_b_500_;
goto v___jp_501_;
}
else
{
lean_object* v_val_509_; lean_object* v___x_510_; 
v_val_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = lean_array_push(v_b_500_, v_val_509_);
v___y_502_ = v___x_510_;
goto v___jp_501_;
}
}
else
{
lean_dec_ref(v_self_496_);
return v_b_500_;
}
v___jp_501_:
{
size_t v___x_503_; size_t v___x_504_; 
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_498_, v___x_503_);
v_i_498_ = v___x_504_;
v_b_500_ = v___y_502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object* v_self_511_, lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_stop_514_, lean_object* v_b_515_){
_start:
{
size_t v_i_boxed_516_; size_t v_stop_boxed_517_; lean_object* v_res_518_; 
v_i_boxed_516_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_stop_boxed_517_ = lean_unbox_usize(v_stop_514_);
lean_dec(v_stop_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_511_, v_as_512_, v_i_boxed_516_, v_stop_boxed_517_, v_b_515_);
lean_dec_ref(v_as_512_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object* v_self_519_, lean_object* v_as_520_, lean_object* v_start_521_, lean_object* v_stop_522_){
_start:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_524_ = lean_nat_dec_lt(v_start_521_, v_stop_522_);
if (v___x_524_ == 0)
{
lean_dec_ref(v_self_519_);
return v___x_523_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_as_520_);
v___x_526_ = lean_nat_dec_le(v_stop_522_, v___x_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
v___x_527_ = lean_nat_dec_lt(v_start_521_, v___x_525_);
if (v___x_527_ == 0)
{
lean_dec_ref(v_self_519_);
return v___x_523_;
}
else
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_usize_of_nat(v_start_521_);
v___x_529_ = lean_usize_of_nat(v___x_525_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_519_, v_as_520_, v___x_528_, v___x_529_, v___x_523_);
return v___x_530_;
}
}
else
{
size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_usize_of_nat(v_start_521_);
v___x_532_ = lean_usize_of_nat(v_stop_522_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_519_, v_as_520_, v___x_531_, v___x_532_, v___x_523_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object* v_self_534_, lean_object* v_as_535_, lean_object* v_start_536_, lean_object* v_stop_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_534_, v_as_535_, v_start_536_, v_stop_537_);
lean_dec(v_stop_537_);
lean_dec(v_start_536_);
lean_dec_ref(v_as_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* v_self_539_){
_start:
{
lean_object* v_config_540_; lean_object* v_roots_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_config_540_ = lean_ctor_get(v_self_539_, 2);
v_roots_541_ = lean_ctor_get(v_config_540_, 2);
lean_inc_ref(v_roots_541_);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_array_get_size(v_roots_541_);
v___x_544_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_539_, v_roots_541_, v___x_542_, v___x_543_);
lean_dec_ref(v_roots_541_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* v_self_545_){
_start:
{
lean_object* v_lib_546_; lean_object* v_pkg_547_; 
v_lib_546_ = lean_ctor_get(v_self_545_, 0);
v_pkg_547_ = lean_ctor_get(v_lib_546_, 0);
lean_inc_ref(v_pkg_547_);
return v_pkg_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* v_self_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lake_Module_pkg(v_self_548_);
lean_dec_ref(v_self_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* v_self_550_){
_start:
{
lean_object* v_lib_551_; lean_object* v_pkg_552_; lean_object* v_config_553_; lean_object* v_config_554_; lean_object* v_dir_555_; lean_object* v_srcDir_556_; lean_object* v_srcDir_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_lib_551_ = lean_ctor_get(v_self_550_, 0);
lean_inc_ref(v_lib_551_);
lean_dec_ref(v_self_550_);
v_pkg_552_ = lean_ctor_get(v_lib_551_, 0);
lean_inc_ref(v_pkg_552_);
v_config_553_ = lean_ctor_get(v_pkg_552_, 6);
lean_inc_ref(v_config_553_);
v_config_554_ = lean_ctor_get(v_lib_551_, 2);
lean_inc(v_config_554_);
lean_dec_ref(v_lib_551_);
v_dir_555_ = lean_ctor_get(v_pkg_552_, 4);
lean_inc_ref(v_dir_555_);
lean_dec_ref(v_pkg_552_);
v_srcDir_556_ = lean_ctor_get(v_config_553_, 4);
lean_inc_ref(v_srcDir_556_);
lean_dec_ref(v_config_553_);
v_srcDir_557_ = lean_ctor_get(v_config_554_, 1);
lean_inc_ref(v_srcDir_557_);
lean_dec(v_config_554_);
v___x_558_ = l_System_FilePath_normalize(v_srcDir_556_);
v___x_559_ = l_Lake_joinRelative(v_dir_555_, v___x_558_);
v___x_560_ = l_System_FilePath_normalize(v_srcDir_557_);
v___x_561_ = l_Lake_joinRelative(v___x_559_, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object* v_ext_562_, lean_object* v_self_563_){
_start:
{
lean_object* v_name_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_name_564_ = lean_ctor_get(v_self_563_, 1);
v___x_565_ = l_Lean_Name_getString_x21(v_name_564_);
v___x_566_ = l_System_FilePath_addExtension(v___x_565_, v_ext_562_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object* v_ext_567_, lean_object* v_self_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lake_Module_fileName(v_ext_567_, v_self_568_);
lean_dec_ref(v_self_568_);
lean_dec_ref(v_ext_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_570_, lean_object* v_ext_571_, lean_object* v_self_572_){
_start:
{
lean_object* v_name_573_; lean_object* v___x_574_; 
v_name_573_ = lean_ctor_get(v_self_572_, 1);
lean_inc(v_name_573_);
lean_dec_ref(v_self_572_);
v___x_574_ = l_Lean_modToFilePath(v_dir_570_, v_name_573_, v_ext_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_575_, lean_object* v_ext_576_, lean_object* v_self_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lake_Module_filePath(v_dir_575_, v_ext_576_, v_self_577_);
lean_dec_ref(v_ext_576_);
lean_dec_ref(v_dir_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_579_, lean_object* v_self_580_){
_start:
{
lean_object* v_lib_581_; lean_object* v_pkg_582_; lean_object* v_config_583_; lean_object* v_config_584_; lean_object* v_name_585_; lean_object* v_dir_586_; lean_object* v_srcDir_587_; lean_object* v_srcDir_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_lib_581_ = lean_ctor_get(v_self_580_, 0);
v_pkg_582_ = lean_ctor_get(v_lib_581_, 0);
lean_inc_ref(v_pkg_582_);
v_config_583_ = lean_ctor_get(v_pkg_582_, 6);
lean_inc_ref(v_config_583_);
v_config_584_ = lean_ctor_get(v_lib_581_, 2);
lean_inc(v_config_584_);
v_name_585_ = lean_ctor_get(v_self_580_, 1);
lean_inc(v_name_585_);
lean_dec_ref(v_self_580_);
v_dir_586_ = lean_ctor_get(v_pkg_582_, 4);
lean_inc_ref(v_dir_586_);
lean_dec_ref(v_pkg_582_);
v_srcDir_587_ = lean_ctor_get(v_config_583_, 4);
lean_inc_ref(v_srcDir_587_);
lean_dec_ref(v_config_583_);
v_srcDir_588_ = lean_ctor_get(v_config_584_, 1);
lean_inc_ref(v_srcDir_588_);
lean_dec(v_config_584_);
v___x_589_ = l_System_FilePath_normalize(v_srcDir_587_);
v___x_590_ = l_Lake_joinRelative(v_dir_586_, v___x_589_);
v___x_591_ = l_System_FilePath_normalize(v_srcDir_588_);
v___x_592_ = l_Lake_joinRelative(v___x_590_, v___x_591_);
v___x_593_ = l_Lean_modToFilePath(v___x_592_, v_name_585_, v_ext_579_);
lean_dec_ref(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_594_, lean_object* v_self_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lake_Module_srcPath(v_ext_594_, v_self_595_);
lean_dec_ref(v_ext_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_597_){
_start:
{
lean_object* v_lib_598_; lean_object* v_pkg_599_; lean_object* v_config_600_; lean_object* v_config_601_; lean_object* v_name_602_; lean_object* v_dir_603_; lean_object* v_srcDir_604_; lean_object* v_srcDir_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_lib_598_ = lean_ctor_get(v_self_597_, 0);
v_pkg_599_ = lean_ctor_get(v_lib_598_, 0);
lean_inc_ref(v_pkg_599_);
v_config_600_ = lean_ctor_get(v_pkg_599_, 6);
lean_inc_ref(v_config_600_);
v_config_601_ = lean_ctor_get(v_lib_598_, 2);
lean_inc(v_config_601_);
v_name_602_ = lean_ctor_get(v_self_597_, 1);
lean_inc(v_name_602_);
lean_dec_ref(v_self_597_);
v_dir_603_ = lean_ctor_get(v_pkg_599_, 4);
lean_inc_ref(v_dir_603_);
lean_dec_ref(v_pkg_599_);
v_srcDir_604_ = lean_ctor_get(v_config_600_, 4);
lean_inc_ref(v_srcDir_604_);
lean_dec_ref(v_config_600_);
v_srcDir_605_ = lean_ctor_get(v_config_601_, 1);
lean_inc_ref(v_srcDir_605_);
lean_dec(v_config_601_);
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_607_ = l_System_FilePath_normalize(v_srcDir_604_);
v___x_608_ = l_Lake_joinRelative(v_dir_603_, v___x_607_);
v___x_609_ = l_System_FilePath_normalize(v_srcDir_605_);
v___x_610_ = l_Lake_joinRelative(v___x_608_, v___x_609_);
v___x_611_ = l_Lean_modToFilePath(v___x_610_, v_name_602_, v___x_606_);
lean_dec_ref(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_612_){
_start:
{
lean_object* v_lib_613_; lean_object* v_pkg_614_; lean_object* v_config_615_; lean_object* v_config_616_; lean_object* v_name_617_; lean_object* v_dir_618_; lean_object* v_srcDir_619_; lean_object* v_srcDir_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_lib_613_ = lean_ctor_get(v_self_612_, 0);
v_pkg_614_ = lean_ctor_get(v_lib_613_, 0);
lean_inc_ref(v_pkg_614_);
v_config_615_ = lean_ctor_get(v_pkg_614_, 6);
lean_inc_ref(v_config_615_);
v_config_616_ = lean_ctor_get(v_lib_613_, 2);
lean_inc(v_config_616_);
v_name_617_ = lean_ctor_get(v_self_612_, 1);
lean_inc(v_name_617_);
lean_dec_ref(v_self_612_);
v_dir_618_ = lean_ctor_get(v_pkg_614_, 4);
lean_inc_ref_n(v_dir_618_, 2);
lean_dec_ref(v_pkg_614_);
v_srcDir_619_ = lean_ctor_get(v_config_615_, 4);
lean_inc_ref(v_srcDir_619_);
lean_dec_ref(v_config_615_);
v_srcDir_620_ = lean_ctor_get(v_config_616_, 1);
lean_inc_ref(v_srcDir_620_);
lean_dec(v_config_616_);
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_622_ = l_System_FilePath_normalize(v_srcDir_619_);
v___x_623_ = l_Lake_joinRelative(v_dir_618_, v___x_622_);
v___x_624_ = l_System_FilePath_normalize(v_srcDir_620_);
v___x_625_ = l_Lake_joinRelative(v___x_623_, v___x_624_);
v___x_626_ = l_Lean_modToFilePath(v___x_625_, v_name_617_, v___x_621_);
lean_dec_ref(v___x_625_);
v___x_627_ = l_Lake_relPathFrom(v_dir_618_, v___x_626_);
lean_dec_ref(v_dir_618_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_628_, lean_object* v_self_629_){
_start:
{
lean_object* v_lib_630_; lean_object* v_pkg_631_; lean_object* v_config_632_; lean_object* v_name_633_; lean_object* v_dir_634_; lean_object* v_buildDir_635_; lean_object* v_leanLibDir_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_lib_630_ = lean_ctor_get(v_self_629_, 0);
v_pkg_631_ = lean_ctor_get(v_lib_630_, 0);
lean_inc_ref(v_pkg_631_);
v_config_632_ = lean_ctor_get(v_pkg_631_, 6);
lean_inc_ref(v_config_632_);
v_name_633_ = lean_ctor_get(v_self_629_, 1);
lean_inc(v_name_633_);
lean_dec_ref(v_self_629_);
v_dir_634_ = lean_ctor_get(v_pkg_631_, 4);
lean_inc_ref(v_dir_634_);
lean_dec_ref(v_pkg_631_);
v_buildDir_635_ = lean_ctor_get(v_config_632_, 5);
lean_inc_ref(v_buildDir_635_);
v_leanLibDir_636_ = lean_ctor_get(v_config_632_, 6);
lean_inc_ref(v_leanLibDir_636_);
lean_dec_ref(v_config_632_);
v___x_637_ = l_System_FilePath_normalize(v_buildDir_635_);
v___x_638_ = l_Lake_joinRelative(v_dir_634_, v___x_637_);
v___x_639_ = l_System_FilePath_normalize(v_leanLibDir_636_);
v___x_640_ = l_Lake_joinRelative(v___x_638_, v___x_639_);
v___x_641_ = l_Lean_modToFilePath(v___x_640_, v_name_633_, v_ext_628_);
lean_dec_ref(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_642_, lean_object* v_self_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lake_Module_leanLibPath(v_ext_642_, v_self_643_);
lean_dec_ref(v_ext_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object* v_self_645_){
_start:
{
lean_object* v_lib_646_; lean_object* v_pkg_647_; lean_object* v_config_648_; lean_object* v_name_649_; lean_object* v_dir_650_; lean_object* v_buildDir_651_; lean_object* v_leanLibDir_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_lib_646_ = lean_ctor_get(v_self_645_, 0);
v_pkg_647_ = lean_ctor_get(v_lib_646_, 0);
lean_inc_ref(v_pkg_647_);
v_config_648_ = lean_ctor_get(v_pkg_647_, 6);
lean_inc_ref(v_config_648_);
v_name_649_ = lean_ctor_get(v_self_645_, 1);
lean_inc(v_name_649_);
lean_dec_ref(v_self_645_);
v_dir_650_ = lean_ctor_get(v_pkg_647_, 4);
lean_inc_ref(v_dir_650_);
lean_dec_ref(v_pkg_647_);
v_buildDir_651_ = lean_ctor_get(v_config_648_, 5);
lean_inc_ref(v_buildDir_651_);
v_leanLibDir_652_ = lean_ctor_get(v_config_648_, 6);
lean_inc_ref(v_leanLibDir_652_);
lean_dec_ref(v_config_648_);
v___x_653_ = l_System_FilePath_normalize(v_buildDir_651_);
v___x_654_ = l_Lake_joinRelative(v_dir_650_, v___x_653_);
v___x_655_ = l_System_FilePath_normalize(v_leanLibDir_652_);
v___x_656_ = l_Lake_joinRelative(v___x_654_, v___x_655_);
v___x_657_ = l_Lean_Name_getPrefix(v_name_649_);
lean_dec(v_name_649_);
v___x_658_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_659_ = l_Lean_modToFilePath(v___x_656_, v___x_657_, v___x_658_);
lean_dec_ref(v___x_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_661_){
_start:
{
lean_object* v_lib_662_; lean_object* v_pkg_663_; lean_object* v_config_664_; lean_object* v_name_665_; lean_object* v_dir_666_; lean_object* v_buildDir_667_; lean_object* v_leanLibDir_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_lib_662_ = lean_ctor_get(v_self_661_, 0);
v_pkg_663_ = lean_ctor_get(v_lib_662_, 0);
lean_inc_ref(v_pkg_663_);
v_config_664_ = lean_ctor_get(v_pkg_663_, 6);
lean_inc_ref(v_config_664_);
v_name_665_ = lean_ctor_get(v_self_661_, 1);
lean_inc(v_name_665_);
lean_dec_ref(v_self_661_);
v_dir_666_ = lean_ctor_get(v_pkg_663_, 4);
lean_inc_ref(v_dir_666_);
lean_dec_ref(v_pkg_663_);
v_buildDir_667_ = lean_ctor_get(v_config_664_, 5);
lean_inc_ref(v_buildDir_667_);
v_leanLibDir_668_ = lean_ctor_get(v_config_664_, 6);
lean_inc_ref(v_leanLibDir_668_);
lean_dec_ref(v_config_664_);
v___x_669_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_670_ = l_System_FilePath_normalize(v_buildDir_667_);
v___x_671_ = l_Lake_joinRelative(v_dir_666_, v___x_670_);
v___x_672_ = l_System_FilePath_normalize(v_leanLibDir_668_);
v___x_673_ = l_Lake_joinRelative(v___x_671_, v___x_672_);
v___x_674_ = l_Lean_modToFilePath(v___x_673_, v_name_665_, v___x_669_);
lean_dec_ref(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_676_){
_start:
{
lean_object* v_lib_677_; lean_object* v_pkg_678_; lean_object* v_config_679_; lean_object* v_name_680_; lean_object* v_dir_681_; lean_object* v_buildDir_682_; lean_object* v_leanLibDir_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_lib_677_ = lean_ctor_get(v_self_676_, 0);
v_pkg_678_ = lean_ctor_get(v_lib_677_, 0);
lean_inc_ref(v_pkg_678_);
v_config_679_ = lean_ctor_get(v_pkg_678_, 6);
lean_inc_ref(v_config_679_);
v_name_680_ = lean_ctor_get(v_self_676_, 1);
lean_inc(v_name_680_);
lean_dec_ref(v_self_676_);
v_dir_681_ = lean_ctor_get(v_pkg_678_, 4);
lean_inc_ref(v_dir_681_);
lean_dec_ref(v_pkg_678_);
v_buildDir_682_ = lean_ctor_get(v_config_679_, 5);
lean_inc_ref(v_buildDir_682_);
v_leanLibDir_683_ = lean_ctor_get(v_config_679_, 6);
lean_inc_ref(v_leanLibDir_683_);
lean_dec_ref(v_config_679_);
v___x_684_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_685_ = l_System_FilePath_normalize(v_buildDir_682_);
v___x_686_ = l_Lake_joinRelative(v_dir_681_, v___x_685_);
v___x_687_ = l_System_FilePath_normalize(v_leanLibDir_683_);
v___x_688_ = l_Lake_joinRelative(v___x_686_, v___x_687_);
v___x_689_ = l_Lean_modToFilePath(v___x_688_, v_name_680_, v___x_684_);
lean_dec_ref(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_691_){
_start:
{
lean_object* v_lib_692_; lean_object* v_pkg_693_; lean_object* v_config_694_; lean_object* v_name_695_; lean_object* v_dir_696_; lean_object* v_buildDir_697_; lean_object* v_leanLibDir_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_lib_692_ = lean_ctor_get(v_self_691_, 0);
v_pkg_693_ = lean_ctor_get(v_lib_692_, 0);
lean_inc_ref(v_pkg_693_);
v_config_694_ = lean_ctor_get(v_pkg_693_, 6);
lean_inc_ref(v_config_694_);
v_name_695_ = lean_ctor_get(v_self_691_, 1);
lean_inc(v_name_695_);
lean_dec_ref(v_self_691_);
v_dir_696_ = lean_ctor_get(v_pkg_693_, 4);
lean_inc_ref(v_dir_696_);
lean_dec_ref(v_pkg_693_);
v_buildDir_697_ = lean_ctor_get(v_config_694_, 5);
lean_inc_ref(v_buildDir_697_);
v_leanLibDir_698_ = lean_ctor_get(v_config_694_, 6);
lean_inc_ref(v_leanLibDir_698_);
lean_dec_ref(v_config_694_);
v___x_699_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_700_ = l_System_FilePath_normalize(v_buildDir_697_);
v___x_701_ = l_Lake_joinRelative(v_dir_696_, v___x_700_);
v___x_702_ = l_System_FilePath_normalize(v_leanLibDir_698_);
v___x_703_ = l_Lake_joinRelative(v___x_701_, v___x_702_);
v___x_704_ = l_Lean_modToFilePath(v___x_703_, v_name_695_, v___x_699_);
lean_dec_ref(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_706_){
_start:
{
lean_object* v_lib_707_; lean_object* v_pkg_708_; lean_object* v_config_709_; lean_object* v_name_710_; lean_object* v_dir_711_; lean_object* v_buildDir_712_; lean_object* v_leanLibDir_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_lib_707_ = lean_ctor_get(v_self_706_, 0);
v_pkg_708_ = lean_ctor_get(v_lib_707_, 0);
lean_inc_ref(v_pkg_708_);
v_config_709_ = lean_ctor_get(v_pkg_708_, 6);
lean_inc_ref(v_config_709_);
v_name_710_ = lean_ctor_get(v_self_706_, 1);
lean_inc(v_name_710_);
lean_dec_ref(v_self_706_);
v_dir_711_ = lean_ctor_get(v_pkg_708_, 4);
lean_inc_ref(v_dir_711_);
lean_dec_ref(v_pkg_708_);
v_buildDir_712_ = lean_ctor_get(v_config_709_, 5);
lean_inc_ref(v_buildDir_712_);
v_leanLibDir_713_ = lean_ctor_get(v_config_709_, 6);
lean_inc_ref(v_leanLibDir_713_);
lean_dec_ref(v_config_709_);
v___x_714_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_715_ = l_System_FilePath_normalize(v_buildDir_712_);
v___x_716_ = l_Lake_joinRelative(v_dir_711_, v___x_715_);
v___x_717_ = l_System_FilePath_normalize(v_leanLibDir_713_);
v___x_718_ = l_Lake_joinRelative(v___x_716_, v___x_717_);
v___x_719_ = l_Lean_modToFilePath(v___x_718_, v_name_710_, v___x_714_);
lean_dec_ref(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object* v_self_721_){
_start:
{
lean_object* v_lib_722_; lean_object* v_pkg_723_; lean_object* v_config_724_; lean_object* v_name_725_; lean_object* v_dir_726_; lean_object* v_buildDir_727_; lean_object* v_leanLibDir_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_lib_722_ = lean_ctor_get(v_self_721_, 0);
v_pkg_723_ = lean_ctor_get(v_lib_722_, 0);
lean_inc_ref(v_pkg_723_);
v_config_724_ = lean_ctor_get(v_pkg_723_, 6);
lean_inc_ref(v_config_724_);
v_name_725_ = lean_ctor_get(v_self_721_, 1);
lean_inc(v_name_725_);
lean_dec_ref(v_self_721_);
v_dir_726_ = lean_ctor_get(v_pkg_723_, 4);
lean_inc_ref(v_dir_726_);
lean_dec_ref(v_pkg_723_);
v_buildDir_727_ = lean_ctor_get(v_config_724_, 5);
lean_inc_ref(v_buildDir_727_);
v_leanLibDir_728_ = lean_ctor_get(v_config_724_, 6);
lean_inc_ref(v_leanLibDir_728_);
lean_dec_ref(v_config_724_);
v___x_729_ = ((lean_object*)(l_Lake_Module_irSigFile___closed__0));
v___x_730_ = l_System_FilePath_normalize(v_buildDir_727_);
v___x_731_ = l_Lake_joinRelative(v_dir_726_, v___x_730_);
v___x_732_ = l_System_FilePath_normalize(v_leanLibDir_728_);
v___x_733_ = l_Lake_joinRelative(v___x_731_, v___x_732_);
v___x_734_ = l_Lean_modToFilePath(v___x_733_, v_name_725_, v___x_729_);
lean_dec_ref(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_736_){
_start:
{
lean_object* v_lib_737_; lean_object* v_pkg_738_; lean_object* v_config_739_; lean_object* v_name_740_; lean_object* v_dir_741_; lean_object* v_buildDir_742_; lean_object* v_leanLibDir_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_lib_737_ = lean_ctor_get(v_self_736_, 0);
v_pkg_738_ = lean_ctor_get(v_lib_737_, 0);
lean_inc_ref(v_pkg_738_);
v_config_739_ = lean_ctor_get(v_pkg_738_, 6);
lean_inc_ref(v_config_739_);
v_name_740_ = lean_ctor_get(v_self_736_, 1);
lean_inc(v_name_740_);
lean_dec_ref(v_self_736_);
v_dir_741_ = lean_ctor_get(v_pkg_738_, 4);
lean_inc_ref(v_dir_741_);
lean_dec_ref(v_pkg_738_);
v_buildDir_742_ = lean_ctor_get(v_config_739_, 5);
lean_inc_ref(v_buildDir_742_);
v_leanLibDir_743_ = lean_ctor_get(v_config_739_, 6);
lean_inc_ref(v_leanLibDir_743_);
lean_dec_ref(v_config_739_);
v___x_744_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_745_ = l_System_FilePath_normalize(v_buildDir_742_);
v___x_746_ = l_Lake_joinRelative(v_dir_741_, v___x_745_);
v___x_747_ = l_System_FilePath_normalize(v_leanLibDir_743_);
v___x_748_ = l_Lake_joinRelative(v___x_746_, v___x_747_);
v___x_749_ = l_Lean_modToFilePath(v___x_748_, v_name_740_, v___x_744_);
lean_dec_ref(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_751_){
_start:
{
lean_object* v_lib_752_; lean_object* v_pkg_753_; lean_object* v_config_754_; lean_object* v_name_755_; lean_object* v_dir_756_; lean_object* v_buildDir_757_; lean_object* v_leanLibDir_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_lib_752_ = lean_ctor_get(v_self_751_, 0);
v_pkg_753_ = lean_ctor_get(v_lib_752_, 0);
lean_inc_ref(v_pkg_753_);
v_config_754_ = lean_ctor_get(v_pkg_753_, 6);
lean_inc_ref(v_config_754_);
v_name_755_ = lean_ctor_get(v_self_751_, 1);
lean_inc(v_name_755_);
lean_dec_ref(v_self_751_);
v_dir_756_ = lean_ctor_get(v_pkg_753_, 4);
lean_inc_ref(v_dir_756_);
lean_dec_ref(v_pkg_753_);
v_buildDir_757_ = lean_ctor_get(v_config_754_, 5);
lean_inc_ref(v_buildDir_757_);
v_leanLibDir_758_ = lean_ctor_get(v_config_754_, 6);
lean_inc_ref(v_leanLibDir_758_);
lean_dec_ref(v_config_754_);
v___x_759_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_760_ = l_System_FilePath_normalize(v_buildDir_757_);
v___x_761_ = l_Lake_joinRelative(v_dir_756_, v___x_760_);
v___x_762_ = l_System_FilePath_normalize(v_leanLibDir_758_);
v___x_763_ = l_Lake_joinRelative(v___x_761_, v___x_762_);
v___x_764_ = l_Lean_modToFilePath(v___x_763_, v_name_755_, v___x_759_);
lean_dec_ref(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_765_, lean_object* v_self_766_){
_start:
{
lean_object* v_lib_767_; lean_object* v_pkg_768_; lean_object* v_config_769_; lean_object* v_name_770_; lean_object* v_dir_771_; lean_object* v_buildDir_772_; lean_object* v_irDir_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_lib_767_ = lean_ctor_get(v_self_766_, 0);
v_pkg_768_ = lean_ctor_get(v_lib_767_, 0);
lean_inc_ref(v_pkg_768_);
v_config_769_ = lean_ctor_get(v_pkg_768_, 6);
lean_inc_ref(v_config_769_);
v_name_770_ = lean_ctor_get(v_self_766_, 1);
lean_inc(v_name_770_);
lean_dec_ref(v_self_766_);
v_dir_771_ = lean_ctor_get(v_pkg_768_, 4);
lean_inc_ref(v_dir_771_);
lean_dec_ref(v_pkg_768_);
v_buildDir_772_ = lean_ctor_get(v_config_769_, 5);
lean_inc_ref(v_buildDir_772_);
v_irDir_773_ = lean_ctor_get(v_config_769_, 9);
lean_inc_ref(v_irDir_773_);
lean_dec_ref(v_config_769_);
v___x_774_ = l_System_FilePath_normalize(v_buildDir_772_);
v___x_775_ = l_Lake_joinRelative(v_dir_771_, v___x_774_);
v___x_776_ = l_System_FilePath_normalize(v_irDir_773_);
v___x_777_ = l_Lake_joinRelative(v___x_775_, v___x_776_);
v___x_778_ = l_Lean_modToFilePath(v___x_777_, v_name_770_, v_ext_765_);
lean_dec_ref(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_779_, lean_object* v_self_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lake_Module_irPath(v_ext_779_, v_self_780_);
lean_dec_ref(v_ext_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_782_){
_start:
{
lean_object* v_lib_783_; lean_object* v_pkg_784_; lean_object* v_config_785_; lean_object* v_name_786_; lean_object* v_dir_787_; lean_object* v_buildDir_788_; lean_object* v_irDir_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_lib_783_ = lean_ctor_get(v_self_782_, 0);
v_pkg_784_ = lean_ctor_get(v_lib_783_, 0);
lean_inc_ref(v_pkg_784_);
v_config_785_ = lean_ctor_get(v_pkg_784_, 6);
lean_inc_ref(v_config_785_);
v_name_786_ = lean_ctor_get(v_self_782_, 1);
lean_inc(v_name_786_);
lean_dec_ref(v_self_782_);
v_dir_787_ = lean_ctor_get(v_pkg_784_, 4);
lean_inc_ref(v_dir_787_);
lean_dec_ref(v_pkg_784_);
v_buildDir_788_ = lean_ctor_get(v_config_785_, 5);
lean_inc_ref(v_buildDir_788_);
v_irDir_789_ = lean_ctor_get(v_config_785_, 9);
lean_inc_ref(v_irDir_789_);
lean_dec_ref(v_config_785_);
v___x_790_ = l_System_FilePath_normalize(v_buildDir_788_);
v___x_791_ = l_Lake_joinRelative(v_dir_787_, v___x_790_);
v___x_792_ = l_System_FilePath_normalize(v_irDir_789_);
v___x_793_ = l_Lake_joinRelative(v___x_791_, v___x_792_);
v___x_794_ = l_Lean_Name_getPrefix(v_name_786_);
lean_dec(v_name_786_);
v___x_795_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_796_ = l_Lean_modToFilePath(v___x_793_, v___x_794_, v___x_795_);
lean_dec_ref(v___x_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_798_){
_start:
{
lean_object* v_lib_799_; lean_object* v_pkg_800_; lean_object* v_config_801_; lean_object* v_name_802_; lean_object* v_dir_803_; lean_object* v_buildDir_804_; lean_object* v_irDir_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_lib_799_ = lean_ctor_get(v_self_798_, 0);
v_pkg_800_ = lean_ctor_get(v_lib_799_, 0);
lean_inc_ref(v_pkg_800_);
v_config_801_ = lean_ctor_get(v_pkg_800_, 6);
lean_inc_ref(v_config_801_);
v_name_802_ = lean_ctor_get(v_self_798_, 1);
lean_inc(v_name_802_);
lean_dec_ref(v_self_798_);
v_dir_803_ = lean_ctor_get(v_pkg_800_, 4);
lean_inc_ref(v_dir_803_);
lean_dec_ref(v_pkg_800_);
v_buildDir_804_ = lean_ctor_get(v_config_801_, 5);
lean_inc_ref(v_buildDir_804_);
v_irDir_805_ = lean_ctor_get(v_config_801_, 9);
lean_inc_ref(v_irDir_805_);
lean_dec_ref(v_config_801_);
v___x_806_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_807_ = l_System_FilePath_normalize(v_buildDir_804_);
v___x_808_ = l_Lake_joinRelative(v_dir_803_, v___x_807_);
v___x_809_ = l_System_FilePath_normalize(v_irDir_805_);
v___x_810_ = l_Lake_joinRelative(v___x_808_, v___x_809_);
v___x_811_ = l_Lean_modToFilePath(v___x_810_, v_name_802_, v___x_806_);
lean_dec_ref(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_813_){
_start:
{
lean_object* v_lib_814_; lean_object* v_pkg_815_; lean_object* v_config_816_; lean_object* v_name_817_; lean_object* v_dir_818_; lean_object* v_buildDir_819_; lean_object* v_irDir_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_lib_814_ = lean_ctor_get(v_self_813_, 0);
v_pkg_815_ = lean_ctor_get(v_lib_814_, 0);
lean_inc_ref(v_pkg_815_);
v_config_816_ = lean_ctor_get(v_pkg_815_, 6);
lean_inc_ref(v_config_816_);
v_name_817_ = lean_ctor_get(v_self_813_, 1);
lean_inc(v_name_817_);
lean_dec_ref(v_self_813_);
v_dir_818_ = lean_ctor_get(v_pkg_815_, 4);
lean_inc_ref(v_dir_818_);
lean_dec_ref(v_pkg_815_);
v_buildDir_819_ = lean_ctor_get(v_config_816_, 5);
lean_inc_ref(v_buildDir_819_);
v_irDir_820_ = lean_ctor_get(v_config_816_, 9);
lean_inc_ref(v_irDir_820_);
lean_dec_ref(v_config_816_);
v___x_821_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_822_ = l_System_FilePath_normalize(v_buildDir_819_);
v___x_823_ = l_Lake_joinRelative(v_dir_818_, v___x_822_);
v___x_824_ = l_System_FilePath_normalize(v_irDir_820_);
v___x_825_ = l_Lake_joinRelative(v___x_823_, v___x_824_);
v___x_826_ = l_Lean_modToFilePath(v___x_825_, v_name_817_, v___x_821_);
lean_dec_ref(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_828_){
_start:
{
lean_object* v_lib_829_; lean_object* v_pkg_830_; lean_object* v_config_831_; lean_object* v_name_832_; lean_object* v_dir_833_; lean_object* v_buildDir_834_; lean_object* v_irDir_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_lib_829_ = lean_ctor_get(v_self_828_, 0);
v_pkg_830_ = lean_ctor_get(v_lib_829_, 0);
lean_inc_ref(v_pkg_830_);
v_config_831_ = lean_ctor_get(v_pkg_830_, 6);
lean_inc_ref(v_config_831_);
v_name_832_ = lean_ctor_get(v_self_828_, 1);
lean_inc(v_name_832_);
lean_dec_ref(v_self_828_);
v_dir_833_ = lean_ctor_get(v_pkg_830_, 4);
lean_inc_ref(v_dir_833_);
lean_dec_ref(v_pkg_830_);
v_buildDir_834_ = lean_ctor_get(v_config_831_, 5);
lean_inc_ref(v_buildDir_834_);
v_irDir_835_ = lean_ctor_get(v_config_831_, 9);
lean_inc_ref(v_irDir_835_);
lean_dec_ref(v_config_831_);
v___x_836_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_837_ = l_System_FilePath_normalize(v_buildDir_834_);
v___x_838_ = l_Lake_joinRelative(v_dir_833_, v___x_837_);
v___x_839_ = l_System_FilePath_normalize(v_irDir_835_);
v___x_840_ = l_Lake_joinRelative(v___x_838_, v___x_839_);
v___x_841_ = l_Lean_modToFilePath(v___x_840_, v_name_832_, v___x_836_);
lean_dec_ref(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_843_){
_start:
{
lean_object* v_lib_844_; lean_object* v_pkg_845_; lean_object* v_config_846_; lean_object* v_name_847_; lean_object* v_dir_848_; lean_object* v_buildDir_849_; lean_object* v_irDir_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_lib_844_ = lean_ctor_get(v_self_843_, 0);
v_pkg_845_ = lean_ctor_get(v_lib_844_, 0);
lean_inc_ref(v_pkg_845_);
v_config_846_ = lean_ctor_get(v_pkg_845_, 6);
lean_inc_ref(v_config_846_);
v_name_847_ = lean_ctor_get(v_self_843_, 1);
lean_inc(v_name_847_);
lean_dec_ref(v_self_843_);
v_dir_848_ = lean_ctor_get(v_pkg_845_, 4);
lean_inc_ref(v_dir_848_);
lean_dec_ref(v_pkg_845_);
v_buildDir_849_ = lean_ctor_get(v_config_846_, 5);
lean_inc_ref(v_buildDir_849_);
v_irDir_850_ = lean_ctor_get(v_config_846_, 9);
lean_inc_ref(v_irDir_850_);
lean_dec_ref(v_config_846_);
v___x_851_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_852_ = l_System_FilePath_normalize(v_buildDir_849_);
v___x_853_ = l_Lake_joinRelative(v_dir_848_, v___x_852_);
v___x_854_ = l_System_FilePath_normalize(v_irDir_850_);
v___x_855_ = l_Lake_joinRelative(v___x_853_, v___x_854_);
v___x_856_ = l_Lean_modToFilePath(v___x_855_, v_name_847_, v___x_851_);
lean_dec_ref(v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_858_){
_start:
{
lean_object* v_lib_859_; lean_object* v_pkg_860_; lean_object* v_config_861_; lean_object* v_name_862_; lean_object* v_dir_863_; lean_object* v_buildDir_864_; lean_object* v_irDir_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_lib_859_ = lean_ctor_get(v_self_858_, 0);
v_pkg_860_ = lean_ctor_get(v_lib_859_, 0);
lean_inc_ref(v_pkg_860_);
v_config_861_ = lean_ctor_get(v_pkg_860_, 6);
lean_inc_ref(v_config_861_);
v_name_862_ = lean_ctor_get(v_self_858_, 1);
lean_inc(v_name_862_);
lean_dec_ref(v_self_858_);
v_dir_863_ = lean_ctor_get(v_pkg_860_, 4);
lean_inc_ref(v_dir_863_);
lean_dec_ref(v_pkg_860_);
v_buildDir_864_ = lean_ctor_get(v_config_861_, 5);
lean_inc_ref(v_buildDir_864_);
v_irDir_865_ = lean_ctor_get(v_config_861_, 9);
lean_inc_ref(v_irDir_865_);
lean_dec_ref(v_config_861_);
v___x_866_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_867_ = l_System_FilePath_normalize(v_buildDir_864_);
v___x_868_ = l_Lake_joinRelative(v_dir_863_, v___x_867_);
v___x_869_ = l_System_FilePath_normalize(v_irDir_865_);
v___x_870_ = l_Lake_joinRelative(v___x_868_, v___x_869_);
v___x_871_ = l_Lean_modToFilePath(v___x_870_, v_name_862_, v___x_866_);
lean_dec_ref(v___x_870_);
return v___x_871_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_box(0);
v___x_873_ = lean_internal_has_llvm_backend(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref(v_self_874_);
v___x_876_ = lean_box(0);
return v___x_876_;
}
else
{
lean_object* v_lib_877_; lean_object* v_pkg_878_; lean_object* v_config_879_; lean_object* v_name_880_; lean_object* v_dir_881_; lean_object* v_buildDir_882_; lean_object* v_irDir_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_lib_877_ = lean_ctor_get(v_self_874_, 0);
v_pkg_878_ = lean_ctor_get(v_lib_877_, 0);
lean_inc_ref(v_pkg_878_);
v_config_879_ = lean_ctor_get(v_pkg_878_, 6);
lean_inc_ref(v_config_879_);
v_name_880_ = lean_ctor_get(v_self_874_, 1);
lean_inc(v_name_880_);
lean_dec_ref(v_self_874_);
v_dir_881_ = lean_ctor_get(v_pkg_878_, 4);
lean_inc_ref(v_dir_881_);
lean_dec_ref(v_pkg_878_);
v_buildDir_882_ = lean_ctor_get(v_config_879_, 5);
lean_inc_ref(v_buildDir_882_);
v_irDir_883_ = lean_ctor_get(v_config_879_, 9);
lean_inc_ref(v_irDir_883_);
lean_dec_ref(v_config_879_);
v___x_884_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_885_ = l_System_FilePath_normalize(v_buildDir_882_);
v___x_886_ = l_Lake_joinRelative(v_dir_881_, v___x_885_);
v___x_887_ = l_System_FilePath_normalize(v_irDir_883_);
v___x_888_ = l_Lake_joinRelative(v___x_886_, v___x_887_);
v___x_889_ = l_Lean_modToFilePath(v___x_888_, v_name_880_, v___x_884_);
lean_dec_ref(v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_892_){
_start:
{
lean_object* v_lib_893_; lean_object* v_pkg_894_; lean_object* v_config_895_; lean_object* v_name_896_; lean_object* v_dir_897_; lean_object* v_buildDir_898_; lean_object* v_irDir_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_lib_893_ = lean_ctor_get(v_self_892_, 0);
v_pkg_894_ = lean_ctor_get(v_lib_893_, 0);
lean_inc_ref(v_pkg_894_);
v_config_895_ = lean_ctor_get(v_pkg_894_, 6);
lean_inc_ref(v_config_895_);
v_name_896_ = lean_ctor_get(v_self_892_, 1);
lean_inc(v_name_896_);
lean_dec_ref(v_self_892_);
v_dir_897_ = lean_ctor_get(v_pkg_894_, 4);
lean_inc_ref(v_dir_897_);
lean_dec_ref(v_pkg_894_);
v_buildDir_898_ = lean_ctor_get(v_config_895_, 5);
lean_inc_ref(v_buildDir_898_);
v_irDir_899_ = lean_ctor_get(v_config_895_, 9);
lean_inc_ref(v_irDir_899_);
lean_dec_ref(v_config_895_);
v___x_900_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_901_ = l_System_FilePath_normalize(v_buildDir_898_);
v___x_902_ = l_Lake_joinRelative(v_dir_897_, v___x_901_);
v___x_903_ = l_System_FilePath_normalize(v_irDir_899_);
v___x_904_ = l_Lake_joinRelative(v___x_902_, v___x_903_);
v___x_905_ = l_Lean_modToFilePath(v___x_904_, v_name_896_, v___x_900_);
lean_dec_ref(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_907_){
_start:
{
lean_object* v_lib_908_; lean_object* v_pkg_909_; lean_object* v_config_910_; lean_object* v_name_911_; lean_object* v_dir_912_; lean_object* v_buildDir_913_; lean_object* v_irDir_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_lib_908_ = lean_ctor_get(v_self_907_, 0);
v_pkg_909_ = lean_ctor_get(v_lib_908_, 0);
lean_inc_ref(v_pkg_909_);
v_config_910_ = lean_ctor_get(v_pkg_909_, 6);
lean_inc_ref(v_config_910_);
v_name_911_ = lean_ctor_get(v_self_907_, 1);
lean_inc(v_name_911_);
lean_dec_ref(v_self_907_);
v_dir_912_ = lean_ctor_get(v_pkg_909_, 4);
lean_inc_ref(v_dir_912_);
lean_dec_ref(v_pkg_909_);
v_buildDir_913_ = lean_ctor_get(v_config_910_, 5);
lean_inc_ref(v_buildDir_913_);
v_irDir_914_ = lean_ctor_get(v_config_910_, 9);
lean_inc_ref(v_irDir_914_);
lean_dec_ref(v_config_910_);
v___x_915_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_916_ = l_System_FilePath_normalize(v_buildDir_913_);
v___x_917_ = l_Lake_joinRelative(v_dir_912_, v___x_916_);
v___x_918_ = l_System_FilePath_normalize(v_irDir_914_);
v___x_919_ = l_Lake_joinRelative(v___x_917_, v___x_918_);
v___x_920_ = l_Lean_modToFilePath(v___x_919_, v_name_911_, v___x_915_);
lean_dec_ref(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_923_){
_start:
{
lean_object* v_lib_924_; lean_object* v_name_925_; lean_object* v_pkg_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_lib_924_ = lean_ctor_get(v_self_923_, 0);
lean_inc_ref(v_lib_924_);
v_name_925_ = lean_ctor_get(v_self_923_, 1);
lean_inc(v_name_925_);
lean_dec_ref(v_self_923_);
v_pkg_926_ = lean_ctor_get(v_lib_924_, 0);
lean_inc_ref(v_pkg_926_);
lean_dec_ref(v_lib_924_);
v___x_927_ = l_Lake_Package_id_x3f(v_pkg_926_);
v___x_928_ = l_Lean_mkModuleInitializationStem(v_name_925_, v___x_927_);
lean_dec(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_930_){
_start:
{
lean_object* v_lib_931_; lean_object* v_pkg_932_; lean_object* v_config_933_; lean_object* v_name_934_; lean_object* v_dir_935_; lean_object* v_buildDir_936_; lean_object* v_leanLibDir_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_lib_931_ = lean_ctor_get(v_self_930_, 0);
v_pkg_932_ = lean_ctor_get(v_lib_931_, 0);
lean_inc_ref(v_pkg_932_);
v_config_933_ = lean_ctor_get(v_pkg_932_, 6);
v_name_934_ = lean_ctor_get(v_self_930_, 1);
lean_inc(v_name_934_);
lean_dec_ref(v_self_930_);
v_dir_935_ = lean_ctor_get(v_pkg_932_, 4);
v_buildDir_936_ = lean_ctor_get(v_config_933_, 5);
v_leanLibDir_937_ = lean_ctor_get(v_config_933_, 6);
lean_inc_ref(v_buildDir_936_);
v___x_938_ = l_System_FilePath_normalize(v_buildDir_936_);
lean_inc_ref(v_dir_935_);
v___x_939_ = l_Lake_joinRelative(v_dir_935_, v___x_938_);
lean_inc_ref(v_leanLibDir_937_);
v___x_940_ = l_System_FilePath_normalize(v_leanLibDir_937_);
v___x_941_ = l_Lake_joinRelative(v___x_939_, v___x_940_);
v___x_942_ = l_Lake_Package_id_x3f(v_pkg_932_);
v___x_943_ = l_Lean_mkModuleInitializationStem(v_name_934_, v___x_942_);
lean_dec(v___x_942_);
v___x_944_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
v___x_946_ = l_Lake_sharedLibExt;
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___x_948_ = l_Lake_joinRelative(v___x_941_, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_949_){
_start:
{
lean_object* v_lib_950_; lean_object* v_pkg_951_; lean_object* v_config_952_; lean_object* v_toLeanConfig_953_; lean_object* v_config_954_; lean_object* v_toLeanConfig_955_; uint8_t v_buildType_956_; lean_object* v_leanOptions_957_; lean_object* v_moreServerOptions_958_; uint8_t v_buildType_959_; lean_object* v_leanOptions_960_; lean_object* v_moreServerOptions_961_; lean_object* v___x_962_; uint8_t v___y_964_; uint8_t v___x_972_; 
v_lib_950_ = lean_ctor_get(v_self_949_, 0);
v_pkg_951_ = lean_ctor_get(v_lib_950_, 0);
v_config_952_ = lean_ctor_get(v_pkg_951_, 6);
v_toLeanConfig_953_ = lean_ctor_get(v_config_952_, 1);
v_config_954_ = lean_ctor_get(v_lib_950_, 2);
v_toLeanConfig_955_ = lean_ctor_get(v_config_954_, 0);
v_buildType_956_ = lean_ctor_get_uint8(v_toLeanConfig_953_, sizeof(void*)*13);
v_leanOptions_957_ = lean_ctor_get(v_toLeanConfig_953_, 0);
v_moreServerOptions_958_ = lean_ctor_get(v_toLeanConfig_953_, 4);
v_buildType_959_ = lean_ctor_get_uint8(v_toLeanConfig_955_, sizeof(void*)*13);
v_leanOptions_960_ = lean_ctor_get(v_toLeanConfig_955_, 0);
v_moreServerOptions_961_ = lean_ctor_get(v_toLeanConfig_955_, 4);
v___x_962_ = lean_box(1);
v___x_972_ = l_Lake_instOrdBuildType_ord(v_buildType_956_, v_buildType_959_);
if (v___x_972_ == 2)
{
v___y_964_ = v_buildType_959_;
goto v___jp_963_;
}
else
{
v___y_964_ = v_buildType_956_;
goto v___jp_963_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_965_ = l_Lake_BuildType_leanOptions(v___y_964_);
v___x_966_ = l_Lean_LeanOptions_append(v___x_962_, v___x_965_);
v___x_967_ = l_Lean_LeanOptions_ofArray(v_leanOptions_957_);
v___x_968_ = l_Lean_LeanOptions_appendArray(v___x_967_, v_moreServerOptions_958_);
v___x_969_ = l_Lean_LeanOptions_append(v___x_966_, v___x_968_);
v___x_970_ = l_Lean_LeanOptions_appendArray(v___x_969_, v_leanOptions_960_);
v___x_971_ = l_Lean_LeanOptions_appendArray(v___x_970_, v_moreServerOptions_961_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lake_Module_serverOptions(v_self_973_);
lean_dec_ref(v_self_973_);
return v_res_974_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_975_){
_start:
{
lean_object* v_lib_976_; lean_object* v_pkg_977_; lean_object* v_config_978_; lean_object* v_toLeanConfig_979_; lean_object* v_config_980_; lean_object* v_toLeanConfig_981_; uint8_t v_buildType_982_; uint8_t v_buildType_983_; uint8_t v___x_984_; 
v_lib_976_ = lean_ctor_get(v_self_975_, 0);
v_pkg_977_ = lean_ctor_get(v_lib_976_, 0);
v_config_978_ = lean_ctor_get(v_pkg_977_, 6);
v_toLeanConfig_979_ = lean_ctor_get(v_config_978_, 1);
v_config_980_ = lean_ctor_get(v_lib_976_, 2);
v_toLeanConfig_981_ = lean_ctor_get(v_config_980_, 0);
v_buildType_982_ = lean_ctor_get_uint8(v_toLeanConfig_979_, sizeof(void*)*13);
v_buildType_983_ = lean_ctor_get_uint8(v_toLeanConfig_981_, sizeof(void*)*13);
v___x_984_ = l_Lake_instOrdBuildType_ord(v_buildType_982_, v_buildType_983_);
if (v___x_984_ == 2)
{
return v_buildType_983_;
}
else
{
return v_buildType_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_985_){
_start:
{
uint8_t v_res_986_; lean_object* v_r_987_; 
v_res_986_ = l_Lake_Module_buildType(v_self_985_);
lean_dec_ref(v_self_985_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_988_){
_start:
{
lean_object* v_lib_989_; lean_object* v_config_990_; lean_object* v_toLeanConfig_991_; lean_object* v_pkg_992_; lean_object* v_config_993_; lean_object* v_toLeanConfig_994_; uint8_t v_backend_995_; uint8_t v_backend_996_; uint8_t v___x_997_; 
v_lib_989_ = lean_ctor_get(v_self_988_, 0);
v_config_990_ = lean_ctor_get(v_lib_989_, 2);
v_toLeanConfig_991_ = lean_ctor_get(v_config_990_, 0);
v_pkg_992_ = lean_ctor_get(v_lib_989_, 0);
v_config_993_ = lean_ctor_get(v_pkg_992_, 6);
v_toLeanConfig_994_ = lean_ctor_get(v_config_993_, 1);
v_backend_995_ = lean_ctor_get_uint8(v_toLeanConfig_991_, sizeof(void*)*13 + 1);
v_backend_996_ = lean_ctor_get_uint8(v_toLeanConfig_994_, sizeof(void*)*13 + 1);
v___x_997_ = l_Lake_Backend_orPreferLeft(v_backend_995_, v_backend_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l_Lake_Module_backend(v_self_998_);
lean_dec_ref(v_self_998_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_1001_){
_start:
{
lean_object* v_lib_1002_; lean_object* v_config_1003_; uint8_t v_allowImportAll_1004_; 
v_lib_1002_ = lean_ctor_get(v_self_1001_, 0);
v_config_1003_ = lean_ctor_get(v_lib_1002_, 2);
v_allowImportAll_1004_ = lean_ctor_get_uint8(v_config_1003_, sizeof(void*)*9 + 2);
if (v_allowImportAll_1004_ == 0)
{
lean_object* v_pkg_1005_; lean_object* v_config_1006_; uint8_t v_allowImportAll_1007_; 
v_pkg_1005_ = lean_ctor_get(v_lib_1002_, 0);
v_config_1006_ = lean_ctor_get(v_pkg_1005_, 6);
v_allowImportAll_1007_ = lean_ctor_get_uint8(v_config_1006_, sizeof(void*)*27 + 5);
return v_allowImportAll_1007_;
}
else
{
return v_allowImportAll_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lake_Module_allowImportAll(v_self_1008_);
lean_dec_ref(v_self_1008_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_requiresModuleSystem(lean_object* v_self_1011_){
_start:
{
lean_object* v_lib_1012_; lean_object* v_config_1013_; lean_object* v_toLeanConfig_1014_; uint8_t v_requiresModuleSystem_1015_; 
v_lib_1012_ = lean_ctor_get(v_self_1011_, 0);
v_config_1013_ = lean_ctor_get(v_lib_1012_, 2);
v_toLeanConfig_1014_ = lean_ctor_get(v_config_1013_, 0);
v_requiresModuleSystem_1015_ = lean_ctor_get_uint8(v_toLeanConfig_1014_, sizeof(void*)*13 + 2);
if (v_requiresModuleSystem_1015_ == 0)
{
lean_object* v_pkg_1016_; lean_object* v_config_1017_; lean_object* v_toLeanConfig_1018_; uint8_t v_requiresModuleSystem_1019_; 
v_pkg_1016_ = lean_ctor_get(v_lib_1012_, 0);
v_config_1017_ = lean_ctor_get(v_pkg_1016_, 6);
v_toLeanConfig_1018_ = lean_ctor_get(v_config_1017_, 1);
v_requiresModuleSystem_1019_ = lean_ctor_get_uint8(v_toLeanConfig_1018_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_1019_;
}
else
{
return v_requiresModuleSystem_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object* v_self_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lake_Module_requiresModuleSystem(v_self_1020_);
lean_dec_ref(v_self_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowNonModules(lean_object* v_self_1023_){
_start:
{
lean_object* v_lib_1024_; lean_object* v_config_1025_; lean_object* v_toLeanConfig_1026_; uint8_t v_allowNonModules_1027_; 
v_lib_1024_ = lean_ctor_get(v_self_1023_, 0);
v_config_1025_ = lean_ctor_get(v_lib_1024_, 2);
v_toLeanConfig_1026_ = lean_ctor_get(v_config_1025_, 0);
v_allowNonModules_1027_ = lean_ctor_get_uint8(v_toLeanConfig_1026_, sizeof(void*)*13 + 3);
if (v_allowNonModules_1027_ == 0)
{
lean_object* v_pkg_1028_; lean_object* v_config_1029_; lean_object* v_toLeanConfig_1030_; uint8_t v_allowNonModules_1031_; 
v_pkg_1028_ = lean_ctor_get(v_lib_1024_, 0);
v_config_1029_ = lean_ctor_get(v_pkg_1028_, 6);
v_toLeanConfig_1030_ = lean_ctor_get(v_config_1029_, 1);
v_allowNonModules_1031_ = lean_ctor_get_uint8(v_toLeanConfig_1030_, sizeof(void*)*13 + 3);
return v_allowNonModules_1031_;
}
else
{
return v_allowNonModules_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object* v_self_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lake_Module_allowNonModules(v_self_1032_);
lean_dec_ref(v_self_1032_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_1035_){
_start:
{
lean_object* v_lib_1036_; lean_object* v_pkg_1037_; lean_object* v_config_1038_; lean_object* v_toLeanConfig_1039_; lean_object* v_config_1040_; lean_object* v_toLeanConfig_1041_; lean_object* v_dynlibs_1042_; lean_object* v_dynlibs_1043_; lean_object* v___x_1044_; 
v_lib_1036_ = lean_ctor_get(v_self_1035_, 0);
lean_inc_ref(v_lib_1036_);
lean_dec_ref(v_self_1035_);
v_pkg_1037_ = lean_ctor_get(v_lib_1036_, 0);
v_config_1038_ = lean_ctor_get(v_pkg_1037_, 6);
v_toLeanConfig_1039_ = lean_ctor_get(v_config_1038_, 1);
lean_inc_ref(v_toLeanConfig_1039_);
v_config_1040_ = lean_ctor_get(v_lib_1036_, 2);
lean_inc(v_config_1040_);
lean_dec_ref(v_lib_1036_);
v_toLeanConfig_1041_ = lean_ctor_get(v_config_1040_, 0);
lean_inc_ref(v_toLeanConfig_1041_);
lean_dec(v_config_1040_);
v_dynlibs_1042_ = lean_ctor_get(v_toLeanConfig_1039_, 11);
lean_inc_ref(v_dynlibs_1042_);
lean_dec_ref(v_toLeanConfig_1039_);
v_dynlibs_1043_ = lean_ctor_get(v_toLeanConfig_1041_, 11);
lean_inc_ref(v_dynlibs_1043_);
lean_dec_ref(v_toLeanConfig_1041_);
v___x_1044_ = l_Array_append___redArg(v_dynlibs_1042_, v_dynlibs_1043_);
lean_dec_ref(v_dynlibs_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1045_){
_start:
{
lean_object* v_lib_1046_; lean_object* v_pkg_1047_; lean_object* v_config_1048_; lean_object* v_toLeanConfig_1049_; lean_object* v_config_1050_; lean_object* v_toLeanConfig_1051_; lean_object* v_plugins_1052_; lean_object* v_plugins_1053_; lean_object* v___x_1054_; 
v_lib_1046_ = lean_ctor_get(v_self_1045_, 0);
lean_inc_ref(v_lib_1046_);
lean_dec_ref(v_self_1045_);
v_pkg_1047_ = lean_ctor_get(v_lib_1046_, 0);
v_config_1048_ = lean_ctor_get(v_pkg_1047_, 6);
v_toLeanConfig_1049_ = lean_ctor_get(v_config_1048_, 1);
lean_inc_ref(v_toLeanConfig_1049_);
v_config_1050_ = lean_ctor_get(v_lib_1046_, 2);
lean_inc(v_config_1050_);
lean_dec_ref(v_lib_1046_);
v_toLeanConfig_1051_ = lean_ctor_get(v_config_1050_, 0);
lean_inc_ref(v_toLeanConfig_1051_);
lean_dec(v_config_1050_);
v_plugins_1052_ = lean_ctor_get(v_toLeanConfig_1049_, 12);
lean_inc_ref(v_plugins_1052_);
lean_dec_ref(v_toLeanConfig_1049_);
v_plugins_1053_ = lean_ctor_get(v_toLeanConfig_1051_, 12);
lean_inc_ref(v_plugins_1053_);
lean_dec_ref(v_toLeanConfig_1051_);
v___x_1054_ = l_Array_append___redArg(v_plugins_1052_, v_plugins_1053_);
lean_dec_ref(v_plugins_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1055_){
_start:
{
lean_object* v_lib_1056_; lean_object* v_pkg_1057_; lean_object* v_config_1058_; lean_object* v_toLeanConfig_1059_; lean_object* v_config_1060_; lean_object* v_toLeanConfig_1061_; uint8_t v_buildType_1062_; lean_object* v_leanOptions_1063_; uint8_t v_buildType_1064_; lean_object* v_leanOptions_1065_; uint8_t v___y_1067_; uint8_t v___x_1072_; 
v_lib_1056_ = lean_ctor_get(v_self_1055_, 0);
v_pkg_1057_ = lean_ctor_get(v_lib_1056_, 0);
v_config_1058_ = lean_ctor_get(v_pkg_1057_, 6);
v_toLeanConfig_1059_ = lean_ctor_get(v_config_1058_, 1);
v_config_1060_ = lean_ctor_get(v_lib_1056_, 2);
v_toLeanConfig_1061_ = lean_ctor_get(v_config_1060_, 0);
v_buildType_1062_ = lean_ctor_get_uint8(v_toLeanConfig_1059_, sizeof(void*)*13);
v_leanOptions_1063_ = lean_ctor_get(v_toLeanConfig_1059_, 0);
v_buildType_1064_ = lean_ctor_get_uint8(v_toLeanConfig_1061_, sizeof(void*)*13);
v_leanOptions_1065_ = lean_ctor_get(v_toLeanConfig_1061_, 0);
v___x_1072_ = l_Lake_instOrdBuildType_ord(v_buildType_1062_, v_buildType_1064_);
if (v___x_1072_ == 2)
{
v___y_1067_ = v_buildType_1064_;
goto v___jp_1066_;
}
else
{
v___y_1067_ = v_buildType_1062_;
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = l_Lake_BuildType_leanOptions(v___y_1067_);
v___x_1069_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1063_);
v___x_1070_ = l_Lean_LeanOptions_append(v___x_1068_, v___x_1069_);
v___x_1071_ = l_Lean_LeanOptions_appendArray(v___x_1070_, v_leanOptions_1065_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lake_Module_leanOptions(v_self_1073_);
lean_dec_ref(v_self_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1075_){
_start:
{
lean_object* v_lib_1076_; lean_object* v_pkg_1077_; lean_object* v_config_1078_; lean_object* v_toLeanConfig_1079_; lean_object* v_config_1080_; lean_object* v_toLeanConfig_1081_; uint8_t v_buildType_1082_; lean_object* v_moreLeanArgs_1083_; uint8_t v_buildType_1084_; lean_object* v_moreLeanArgs_1085_; uint8_t v___y_1087_; uint8_t v___x_1091_; 
v_lib_1076_ = lean_ctor_get(v_self_1075_, 0);
v_pkg_1077_ = lean_ctor_get(v_lib_1076_, 0);
v_config_1078_ = lean_ctor_get(v_pkg_1077_, 6);
v_toLeanConfig_1079_ = lean_ctor_get(v_config_1078_, 1);
v_config_1080_ = lean_ctor_get(v_lib_1076_, 2);
v_toLeanConfig_1081_ = lean_ctor_get(v_config_1080_, 0);
v_buildType_1082_ = lean_ctor_get_uint8(v_toLeanConfig_1079_, sizeof(void*)*13);
v_moreLeanArgs_1083_ = lean_ctor_get(v_toLeanConfig_1079_, 1);
v_buildType_1084_ = lean_ctor_get_uint8(v_toLeanConfig_1081_, sizeof(void*)*13);
v_moreLeanArgs_1085_ = lean_ctor_get(v_toLeanConfig_1081_, 1);
v___x_1091_ = l_Lake_instOrdBuildType_ord(v_buildType_1082_, v_buildType_1084_);
if (v___x_1091_ == 2)
{
v___y_1087_ = v_buildType_1084_;
goto v___jp_1086_;
}
else
{
v___y_1087_ = v_buildType_1082_;
goto v___jp_1086_;
}
v___jp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = l_Lake_BuildType_leanArgs(v___y_1087_);
v___x_1089_ = l_Array_append___redArg(v___x_1088_, v_moreLeanArgs_1083_);
v___x_1090_ = l_Array_append___redArg(v___x_1089_, v_moreLeanArgs_1085_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lake_Module_leanArgs(v_self_1092_);
lean_dec_ref(v_self_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1094_){
_start:
{
lean_object* v_lib_1095_; lean_object* v_pkg_1096_; lean_object* v_config_1097_; lean_object* v_toLeanConfig_1098_; lean_object* v_config_1099_; lean_object* v_toLeanConfig_1100_; lean_object* v_weakLeanArgs_1101_; lean_object* v_weakLeanArgs_1102_; lean_object* v___x_1103_; 
v_lib_1095_ = lean_ctor_get(v_self_1094_, 0);
lean_inc_ref(v_lib_1095_);
lean_dec_ref(v_self_1094_);
v_pkg_1096_ = lean_ctor_get(v_lib_1095_, 0);
v_config_1097_ = lean_ctor_get(v_pkg_1096_, 6);
v_toLeanConfig_1098_ = lean_ctor_get(v_config_1097_, 1);
lean_inc_ref(v_toLeanConfig_1098_);
v_config_1099_ = lean_ctor_get(v_lib_1095_, 2);
lean_inc(v_config_1099_);
lean_dec_ref(v_lib_1095_);
v_toLeanConfig_1100_ = lean_ctor_get(v_config_1099_, 0);
lean_inc_ref(v_toLeanConfig_1100_);
lean_dec(v_config_1099_);
v_weakLeanArgs_1101_ = lean_ctor_get(v_toLeanConfig_1098_, 2);
lean_inc_ref(v_weakLeanArgs_1101_);
lean_dec_ref(v_toLeanConfig_1098_);
v_weakLeanArgs_1102_ = lean_ctor_get(v_toLeanConfig_1100_, 2);
lean_inc_ref(v_weakLeanArgs_1102_);
lean_dec_ref(v_toLeanConfig_1100_);
v___x_1103_ = l_Array_append___redArg(v_weakLeanArgs_1101_, v_weakLeanArgs_1102_);
lean_dec_ref(v_weakLeanArgs_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1104_){
_start:
{
lean_object* v_lib_1105_; lean_object* v_pkg_1106_; lean_object* v_config_1107_; lean_object* v_toLeanConfig_1108_; lean_object* v_config_1109_; lean_object* v_toLeanConfig_1110_; uint8_t v_buildType_1111_; lean_object* v_moreLeancArgs_1112_; uint8_t v_buildType_1113_; lean_object* v_moreLeancArgs_1114_; uint8_t v___y_1116_; uint8_t v___x_1120_; 
v_lib_1105_ = lean_ctor_get(v_self_1104_, 0);
v_pkg_1106_ = lean_ctor_get(v_lib_1105_, 0);
v_config_1107_ = lean_ctor_get(v_pkg_1106_, 6);
v_toLeanConfig_1108_ = lean_ctor_get(v_config_1107_, 1);
v_config_1109_ = lean_ctor_get(v_lib_1105_, 2);
v_toLeanConfig_1110_ = lean_ctor_get(v_config_1109_, 0);
v_buildType_1111_ = lean_ctor_get_uint8(v_toLeanConfig_1108_, sizeof(void*)*13);
v_moreLeancArgs_1112_ = lean_ctor_get(v_toLeanConfig_1108_, 3);
v_buildType_1113_ = lean_ctor_get_uint8(v_toLeanConfig_1110_, sizeof(void*)*13);
v_moreLeancArgs_1114_ = lean_ctor_get(v_toLeanConfig_1110_, 3);
v___x_1120_ = l_Lake_instOrdBuildType_ord(v_buildType_1111_, v_buildType_1113_);
if (v___x_1120_ == 2)
{
v___y_1116_ = v_buildType_1113_;
goto v___jp_1115_;
}
else
{
v___y_1116_ = v_buildType_1111_;
goto v___jp_1115_;
}
v___jp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = l_Lake_BuildType_leancArgs(v___y_1116_);
v___x_1118_ = l_Array_append___redArg(v___x_1117_, v_moreLeancArgs_1112_);
v___x_1119_ = l_Array_append___redArg(v___x_1118_, v_moreLeancArgs_1114_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lake_Module_leancArgs(v_self_1121_);
lean_dec_ref(v_self_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1123_){
_start:
{
lean_object* v_lib_1124_; lean_object* v_pkg_1125_; lean_object* v_config_1126_; lean_object* v_toLeanConfig_1127_; lean_object* v_config_1128_; lean_object* v_toLeanConfig_1129_; lean_object* v_weakLeancArgs_1130_; lean_object* v_weakLeancArgs_1131_; lean_object* v___x_1132_; 
v_lib_1124_ = lean_ctor_get(v_self_1123_, 0);
lean_inc_ref(v_lib_1124_);
lean_dec_ref(v_self_1123_);
v_pkg_1125_ = lean_ctor_get(v_lib_1124_, 0);
v_config_1126_ = lean_ctor_get(v_pkg_1125_, 6);
v_toLeanConfig_1127_ = lean_ctor_get(v_config_1126_, 1);
lean_inc_ref(v_toLeanConfig_1127_);
v_config_1128_ = lean_ctor_get(v_lib_1124_, 2);
lean_inc(v_config_1128_);
lean_dec_ref(v_lib_1124_);
v_toLeanConfig_1129_ = lean_ctor_get(v_config_1128_, 0);
lean_inc_ref(v_toLeanConfig_1129_);
lean_dec(v_config_1128_);
v_weakLeancArgs_1130_ = lean_ctor_get(v_toLeanConfig_1127_, 5);
lean_inc_ref(v_weakLeancArgs_1130_);
lean_dec_ref(v_toLeanConfig_1127_);
v_weakLeancArgs_1131_ = lean_ctor_get(v_toLeanConfig_1129_, 5);
lean_inc_ref(v_weakLeancArgs_1131_);
lean_dec_ref(v_toLeanConfig_1129_);
v___x_1132_ = l_Array_append___redArg(v_weakLeancArgs_1130_, v_weakLeancArgs_1131_);
lean_dec_ref(v_weakLeancArgs_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1133_){
_start:
{
lean_object* v_lib_1134_; lean_object* v_pkg_1135_; lean_object* v_config_1136_; lean_object* v_toLeanConfig_1137_; lean_object* v_config_1138_; lean_object* v_toLeanConfig_1139_; lean_object* v_moreLinkArgs_1140_; lean_object* v_moreLinkArgs_1141_; lean_object* v___x_1142_; 
v_lib_1134_ = lean_ctor_get(v_self_1133_, 0);
lean_inc_ref(v_lib_1134_);
lean_dec_ref(v_self_1133_);
v_pkg_1135_ = lean_ctor_get(v_lib_1134_, 0);
v_config_1136_ = lean_ctor_get(v_pkg_1135_, 6);
v_toLeanConfig_1137_ = lean_ctor_get(v_config_1136_, 1);
lean_inc_ref(v_toLeanConfig_1137_);
v_config_1138_ = lean_ctor_get(v_lib_1134_, 2);
lean_inc(v_config_1138_);
lean_dec_ref(v_lib_1134_);
v_toLeanConfig_1139_ = lean_ctor_get(v_config_1138_, 0);
lean_inc_ref(v_toLeanConfig_1139_);
lean_dec(v_config_1138_);
v_moreLinkArgs_1140_ = lean_ctor_get(v_toLeanConfig_1137_, 8);
lean_inc_ref(v_moreLinkArgs_1140_);
lean_dec_ref(v_toLeanConfig_1137_);
v_moreLinkArgs_1141_ = lean_ctor_get(v_toLeanConfig_1139_, 8);
lean_inc_ref(v_moreLinkArgs_1141_);
lean_dec_ref(v_toLeanConfig_1139_);
v___x_1142_ = l_Array_append___redArg(v_moreLinkArgs_1140_, v_moreLinkArgs_1141_);
lean_dec_ref(v_moreLinkArgs_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1143_){
_start:
{
lean_object* v_lib_1144_; lean_object* v_pkg_1145_; lean_object* v_config_1146_; lean_object* v_toLeanConfig_1147_; lean_object* v_config_1148_; lean_object* v_toLeanConfig_1149_; lean_object* v_weakLinkArgs_1150_; lean_object* v_weakLinkArgs_1151_; lean_object* v___x_1152_; 
v_lib_1144_ = lean_ctor_get(v_self_1143_, 0);
lean_inc_ref(v_lib_1144_);
lean_dec_ref(v_self_1143_);
v_pkg_1145_ = lean_ctor_get(v_lib_1144_, 0);
v_config_1146_ = lean_ctor_get(v_pkg_1145_, 6);
v_toLeanConfig_1147_ = lean_ctor_get(v_config_1146_, 1);
lean_inc_ref(v_toLeanConfig_1147_);
v_config_1148_ = lean_ctor_get(v_lib_1144_, 2);
lean_inc(v_config_1148_);
lean_dec_ref(v_lib_1144_);
v_toLeanConfig_1149_ = lean_ctor_get(v_config_1148_, 0);
lean_inc_ref(v_toLeanConfig_1149_);
lean_dec(v_config_1148_);
v_weakLinkArgs_1150_ = lean_ctor_get(v_toLeanConfig_1147_, 9);
lean_inc_ref(v_weakLinkArgs_1150_);
lean_dec_ref(v_toLeanConfig_1147_);
v_weakLinkArgs_1151_ = lean_ctor_get(v_toLeanConfig_1149_, 9);
lean_inc_ref(v_weakLinkArgs_1151_);
lean_dec_ref(v_toLeanConfig_1149_);
v___x_1152_ = l_Array_append___redArg(v_weakLinkArgs_1150_, v_weakLinkArgs_1151_);
lean_dec_ref(v_weakLinkArgs_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1154_){
_start:
{
lean_object* v_lib_1155_; lean_object* v_pkg_1156_; lean_object* v_config_1157_; uint8_t v_bootstrap_1158_; 
v_lib_1155_ = lean_ctor_get(v_self_1154_, 0);
lean_inc_ref(v_lib_1155_);
lean_dec_ref(v_self_1154_);
v_pkg_1156_ = lean_ctor_get(v_lib_1155_, 0);
lean_inc_ref(v_pkg_1156_);
lean_dec_ref(v_lib_1155_);
v_config_1157_ = lean_ctor_get(v_pkg_1156_, 6);
lean_inc_ref(v_config_1157_);
v_bootstrap_1158_ = lean_ctor_get_uint8(v_config_1157_, sizeof(void*)*27);
if (v_bootstrap_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_config_1157_);
lean_dec_ref(v_pkg_1156_);
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
else
{
lean_object* v_dir_1160_; lean_object* v_buildDir_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_dir_1160_ = lean_ctor_get(v_pkg_1156_, 4);
lean_inc_ref(v_dir_1160_);
lean_dec_ref(v_pkg_1156_);
v_buildDir_1161_ = lean_ctor_get(v_config_1157_, 5);
lean_inc_ref(v_buildDir_1161_);
lean_dec_ref(v_config_1157_);
v___x_1162_ = l_System_FilePath_normalize(v_buildDir_1161_);
v___x_1163_ = l_Lake_joinRelative(v_dir_1160_, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1165_ = l_Lake_joinRelative(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1167_){
_start:
{
lean_object* v_lib_1168_; lean_object* v_config_1169_; lean_object* v_toLeanConfig_1170_; lean_object* v_platformIndependent_1171_; 
v_lib_1168_ = lean_ctor_get(v_self_1167_, 0);
v_config_1169_ = lean_ctor_get(v_lib_1168_, 2);
v_toLeanConfig_1170_ = lean_ctor_get(v_config_1169_, 0);
v_platformIndependent_1171_ = lean_ctor_get(v_toLeanConfig_1170_, 10);
if (lean_obj_tag(v_platformIndependent_1171_) == 0)
{
lean_object* v_pkg_1172_; lean_object* v_config_1173_; lean_object* v_toLeanConfig_1174_; lean_object* v_platformIndependent_1175_; 
v_pkg_1172_ = lean_ctor_get(v_lib_1168_, 0);
v_config_1173_ = lean_ctor_get(v_pkg_1172_, 6);
v_toLeanConfig_1174_ = lean_ctor_get(v_config_1173_, 1);
v_platformIndependent_1175_ = lean_ctor_get(v_toLeanConfig_1174_, 10);
lean_inc(v_platformIndependent_1175_);
return v_platformIndependent_1175_;
}
else
{
lean_inc_ref(v_platformIndependent_1171_);
return v_platformIndependent_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lake_Module_platformIndependent(v_self_1176_);
lean_dec_ref(v_self_1176_);
return v_res_1177_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1178_){
_start:
{
lean_object* v_lib_1179_; lean_object* v_pkg_1180_; lean_object* v_config_1181_; uint8_t v_precompileModules_1182_; 
v_lib_1179_ = lean_ctor_get(v_self_1178_, 0);
v_pkg_1180_ = lean_ctor_get(v_lib_1179_, 0);
v_config_1181_ = lean_ctor_get(v_pkg_1180_, 6);
v_precompileModules_1182_ = lean_ctor_get_uint8(v_config_1181_, sizeof(void*)*27 + 1);
if (v_precompileModules_1182_ == 0)
{
lean_object* v_config_1183_; uint8_t v_precompileModules_1184_; 
v_config_1183_ = lean_ctor_get(v_lib_1179_, 2);
v_precompileModules_1184_ = lean_ctor_get_uint8(v_config_1183_, sizeof(void*)*9 + 1);
return v_precompileModules_1184_;
}
else
{
return v_precompileModules_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1185_){
_start:
{
uint8_t v_res_1186_; lean_object* v_r_1187_; 
v_res_1186_ = l_Lake_Module_shouldPrecompile(v_self_1185_);
lean_dec_ref(v_self_1185_);
v_r_1187_ = lean_box(v_res_1186_);
return v_r_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1188_, uint8_t v_shouldExport_1189_){
_start:
{
lean_object* v_lib_1190_; lean_object* v_config_1191_; lean_object* v_nativeFacets_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_lib_1190_ = lean_ctor_get(v_self_1188_, 0);
lean_inc_ref(v_lib_1190_);
lean_dec_ref(v_self_1188_);
v_config_1191_ = lean_ctor_get(v_lib_1190_, 2);
lean_inc(v_config_1191_);
lean_dec_ref(v_lib_1190_);
v_nativeFacets_1192_ = lean_ctor_get(v_config_1191_, 8);
lean_inc_ref(v_nativeFacets_1192_);
lean_dec(v_config_1191_);
v___x_1193_ = lean_box(v_shouldExport_1189_);
v___x_1194_ = lean_apply_1(v_nativeFacets_1192_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1195_, lean_object* v_shouldExport_1196_){
_start:
{
uint8_t v_shouldExport_boxed_1197_; lean_object* v_res_1198_; 
v_shouldExport_boxed_1197_ = lean_unbox(v_shouldExport_1196_);
v_res_1198_ = l_Lake_Module_nativeFacets(v_self_1195_, v_shouldExport_boxed_1197_);
return v_res_1198_;
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
