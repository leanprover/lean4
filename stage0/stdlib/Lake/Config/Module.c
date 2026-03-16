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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Lake_instHashableModule___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_instHashableModule___lam__0___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Module_traceFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lake_Module_traceFile___closed__0 = (const lean_object*)&l_Lake_Module_traceFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Module_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setup.json"};
static const lean_object* l_Lake_Module_setupFile___closed__0 = (const lean_object*)&l_Lake_Module_setupFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object*);
static const lean_string_object l_Lake_Module_irFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lake_Module_irFile___closed__0 = (const lean_object*)&l_Lake_Module_irFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object*);
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
static uint64_t _init_l_Lake_instHashableModule___lam__0___closed__0(void){
_start:
{
lean_object* v___x_18_; uint64_t v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(1723u);
v___x_19_ = lean_uint64_of_nat(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashableModule___lam__0(lean_object* v_m_20_){
_start:
{
lean_object* v_name_21_; 
v_name_21_ = lean_ctor_get(v_m_20_, 1);
if (lean_obj_tag(v_name_21_) == 0)
{
uint64_t v___x_22_; 
v___x_22_ = lean_uint64_once(&l_Lake_instHashableModule___lam__0___closed__0, &l_Lake_instHashableModule___lam__0___closed__0_once, _init_l_Lake_instHashableModule___lam__0___closed__0);
return v___x_22_;
}
else
{
uint64_t v_hash_23_; 
v_hash_23_ = lean_ctor_get_uint64(v_name_21_, sizeof(void*)*2);
return v_hash_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableModule___lam__0___boxed(lean_object* v_m_24_){
_start:
{
uint64_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lake_instHashableModule___lam__0(v_m_24_);
lean_dec_ref(v_m_24_);
v_r_26_ = lean_box_uint64(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqModule___lam__0(lean_object* v_m_29_, lean_object* v_n_30_){
_start:
{
lean_object* v_name_31_; lean_object* v_name_32_; uint8_t v___x_33_; 
v_name_31_ = lean_ctor_get(v_m_29_, 1);
v_name_32_ = lean_ctor_get(v_n_30_, 1);
v___x_33_ = lean_name_eq(v_name_31_, v_name_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqModule___lam__0___boxed(lean_object* v_m_34_, lean_object* v_n_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lake_instBEqModule___lam__0(v_m_34_, v_n_35_);
lean_dec_ref(v_n_35_);
lean_dec_ref(v_m_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__0(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_box(0);
v___x_41_ = lean_unsigned_to_nat(16u);
v___x_42_ = lean_mk_array(v___x_41_, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty___closed__1(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lake_ModuleSet_empty___closed__0, &l_Lake_ModuleSet_empty___closed__0_once, _init_l_Lake_ModuleSet_empty___closed__0);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Lake_ModuleSet_empty(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Lake_ModuleSet_empty___closed__1, &l_Lake_ModuleSet_empty___closed__1_once, _init_l_Lake_ModuleSet_empty___closed__1);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_OrdModuleSet_empty___closed__0(void){
_start:
{
lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_Lake_instBEqModule___closed__0));
v___f_48_ = ((lean_object*)(l_Lake_instHashableModule___closed__0));
v___x_49_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_48_, v___f_47_);
return v___x_49_;
}
}
static lean_object* _init_l_Lake_OrdModuleSet_empty(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Lake_OrdModuleSet_empty___closed__0, &l_Lake_OrdModuleSet_empty___closed__0_once, _init_l_Lake_OrdModuleSet_empty___closed__0);
return v___x_50_;
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
lean_dec_ref(v___x_69_);
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
lean_dec_ref(v___x_97_);
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
lean_dec_ref(v___x_123_);
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
lean_dec_ref(v_x_134_);
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
v_srcDir_154_ = lean_ctor_get(v_config_151_, 5);
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
lean_dec_ref(v___x_160_);
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
lean_dec_ref(v___y_142_);
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
v_targetDecls_236_ = lean_ctor_get(v_self_231_, 13);
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
uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_le(v___x_239_, v___x_239_);
if (v___x_241_ == 0)
{
if (v___x_240_ == 0)
{
lean_dec_ref(v_targetDecls_236_);
lean_dec_ref(v_self_231_);
v___y_233_ = v___x_238_;
goto v___jp_232_;
}
else
{
size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; 
v___x_242_ = ((size_t)0ULL);
v___x_243_ = lean_usize_of_nat(v___x_239_);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_231_, v_targetDecls_236_, v___x_242_, v___x_243_, v___x_238_);
lean_dec_ref(v_targetDecls_236_);
v___y_233_ = v___x_244_;
goto v___jp_232_;
}
}
else
{
size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((size_t)0ULL);
v___x_246_ = lean_usize_of_nat(v___x_239_);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_231_, v_targetDecls_236_, v___x_245_, v___x_246_, v___x_238_);
lean_dec_ref(v_targetDecls_236_);
v___y_233_ = v___x_247_;
goto v___jp_232_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(lean_object* v_mod_248_, lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_248_, v_as_249_, v_i_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(lean_object* v_mod_253_, lean_object* v_as_254_, lean_object* v_i_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_253_, v_as_254_, v_i_255_, v_a_256_);
lean_dec_ref(v_as_254_);
return v_res_257_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
if (lean_obj_tag(v_x_259_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = 1;
return v___x_260_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
}
else
{
if (lean_obj_tag(v_x_259_) == 0)
{
uint8_t v___x_262_; 
v___x_262_ = 0;
return v___x_262_;
}
else
{
lean_object* v_val_263_; lean_object* v_val_264_; uint8_t v___x_265_; 
v_val_263_ = lean_ctor_get(v_x_258_, 0);
v_val_264_ = lean_ctor_get(v_x_259_, 0);
v___x_265_ = lean_string_dec_eq(v_val_263_, v_val_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_266_, v_x_267_);
lean_dec(v_x_267_);
lean_dec(v_x_266_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object* v___x_270_, lean_object* v_f_271_, lean_object* v_x_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = l_Lean_Name_append(v___x_270_, v_x_272_);
v___x_276_ = lean_apply_3(v_f_271_, v___x_275_, v___y_273_, lean_box(0));
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object* v___x_277_, lean_object* v_f_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_277_, v_f_278_, v_x_279_, v___y_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object* v_f_286_, lean_object* v_as_287_, size_t v_sz_288_, size_t v_i_289_, lean_object* v_b_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_a_294_; lean_object* v_snd_295_; uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_lt(v_i_289_, v_sz_288_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref(v_f_286_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_b_290_);
lean_ctor_set(v___x_300_, 1, v___y_291_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v_a_302_; lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; 
v_a_302_ = lean_array_uget_borrowed(v_as_287_, v_i_289_);
lean_inc(v_a_302_);
v___x_303_ = l_IO_FS_DirEntry_path(v_a_302_);
v___x_304_ = l_System_FilePath_isDir(v___x_303_);
v___x_305_ = lean_box(0);
if (v___x_304_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = l_System_FilePath_extension(v___x_303_);
v___x_307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1));
v___x_308_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
if (v___x_308_ == 0)
{
v_a_294_ = v___x_305_;
v_snd_295_ = v___y_291_;
goto v___jp_293_;
}
else
{
lean_object* v_fileName_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_fileName_309_ = lean_ctor_get(v_a_302_, 1);
v___x_310_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc_ref(v_fileName_309_);
v___x_311_ = l_System_FilePath_withExtension(v_fileName_309_, v___x_310_);
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_Name_str___override(v___x_312_, v___x_311_);
lean_inc_ref(v_f_286_);
v___x_314_ = lean_apply_3(v_f_286_, v___x_313_, v___y_291_, lean_box(0));
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_snd_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v_snd_316_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_snd_316_);
lean_dec(v_a_315_);
v_a_294_ = v___x_305_;
v_snd_295_ = v_snd_316_;
goto v___jp_293_;
}
else
{
lean_dec_ref(v_f_286_);
return v___x_314_;
}
}
}
else
{
lean_object* v_fileName_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___x_321_; 
v_fileName_317_ = lean_ctor_get(v_a_302_, 1);
v___x_318_ = lean_box(0);
lean_inc_ref(v_fileName_317_);
v___x_319_ = l_Lean_Name_str___override(v___x_318_, v_fileName_317_);
lean_inc_ref(v_f_286_);
v___f_320_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_320_, 0, v___x_319_);
lean_closure_set(v___f_320_, 1, v_f_286_);
v___x_321_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_303_, v___f_320_, v___y_291_);
lean_dec_ref(v___x_303_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_snd_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v___x_321_);
v_snd_323_ = lean_ctor_get(v_a_322_, 1);
lean_inc(v_snd_323_);
lean_dec(v_a_322_);
v_a_294_ = v___x_305_;
v_snd_295_ = v_snd_323_;
goto v___jp_293_;
}
else
{
lean_dec_ref(v_f_286_);
return v___x_321_;
}
}
}
v___jp_293_:
{
size_t v___x_296_; size_t v___x_297_; 
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_i_289_, v___x_296_);
v_i_289_ = v___x_297_;
v_b_290_ = v_a_294_;
v___y_291_ = v_snd_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object* v_dir_324_, lean_object* v_f_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_io_read_dir(v_dir_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; size_t v_sz_331_; size_t v___x_332_; lean_object* v___x_333_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_box(0);
v_sz_331_ = lean_array_size(v_a_329_);
v___x_332_ = ((size_t)0ULL);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_325_, v_a_329_, v_sz_331_, v___x_332_, v___x_330_, v___y_326_);
lean_dec(v_a_329_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_350_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_snd_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v_snd_338_ = lean_ctor_get(v_a_334_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_a_334_, 0);
lean_dec(v_unused_349_);
v___x_340_ = v_a_334_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snd_338_);
lean_dec(v_a_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_330_);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_snd_338_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_343_);
v___x_345_ = v___x_336_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
return v___x_333_;
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v___y_326_);
lean_dec_ref(v_f_325_);
v_a_351_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_328_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_328_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object* v_dir_359_, lean_object* v_f_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_359_, v_f_360_, v___y_361_);
lean_dec_ref(v_dir_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object* v_f_364_, lean_object* v_as_365_, lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_b_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_372_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_364_, v_as_365_, v_sz_boxed_371_, v_i_boxed_372_, v_b_368_, v___y_369_);
lean_dec_ref(v_as_365_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object* v_self_374_, lean_object* v_mod_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_self_374_);
lean_ctor_set(v___x_379_, 1, v_mod_375_);
v___x_380_ = lean_array_push(v___y_376_, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_378_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object* v_self_383_, lean_object* v_mod_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_383_, v_mod_384_, v___y_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object* v_a_388_, lean_object* v___f_389_, lean_object* v_x_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = l_Lean_Name_append(v_a_388_, v_x_390_);
v___x_394_ = lean_apply_3(v___f_389_, v___x_393_, v___y_391_, lean_box(0));
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object* v_a_395_, lean_object* v___f_396_, lean_object* v_x_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_395_, v___f_396_, v_x_397_, v___y_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object* v_self_401_, lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v_b_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___y_409_; uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_416_ == 0)
{
lean_object* v_pkg_417_; lean_object* v_config_418_; lean_object* v_config_419_; lean_object* v_dir_420_; lean_object* v_srcDir_421_; lean_object* v_srcDir_422_; lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_pkg_417_ = lean_ctor_get(v_self_401_, 0);
v_config_418_ = lean_ctor_get(v_pkg_417_, 6);
v_config_419_ = lean_ctor_get(v_self_401_, 2);
v_dir_420_ = lean_ctor_get(v_pkg_417_, 4);
v_srcDir_421_ = lean_ctor_get(v_config_418_, 5);
v_srcDir_422_ = lean_ctor_get(v_config_419_, 1);
lean_inc_ref(v_self_401_);
v___f_423_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(v___f_423_, 0, v_self_401_);
v___x_424_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
lean_inc_ref(v_srcDir_421_);
v___x_425_ = l_System_FilePath_normalize(v_srcDir_421_);
lean_inc_ref(v_dir_420_);
v___x_426_ = l_Lake_joinRelative(v_dir_420_, v___x_425_);
lean_inc_ref(v_srcDir_422_);
v___x_427_ = l_System_FilePath_normalize(v_srcDir_422_);
v___x_428_ = l_Lake_joinRelative(v___x_426_, v___x_427_);
switch(lean_obj_tag(v___x_424_))
{
case 0:
{
lean_object* v_a_429_; lean_object* v___x_430_; 
lean_dec_ref(v___x_428_);
lean_dec_ref(v___f_423_);
v_a_429_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_429_);
lean_inc_ref(v_self_401_);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_401_, v_a_429_, v___y_406_);
v___y_409_ = v___x_430_;
goto v___jp_408_;
}
case 1:
{
lean_object* v_a_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_a_431_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_431_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_432_, 0, v_a_431_);
lean_closure_set(v___f_432_, 1, v___f_423_);
v___x_433_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc(v_a_431_);
v___x_434_ = l_Lean_modToFilePath(v___x_428_, v_a_431_, v___x_433_);
lean_dec_ref(v___x_428_);
v___x_435_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_434_, v___f_432_, v___y_406_);
lean_dec_ref(v___x_434_);
v___y_409_ = v___x_435_;
goto v___jp_408_;
}
default: 
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_436_);
lean_inc_ref(v_self_401_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_401_, v_a_436_, v___y_406_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_snd_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v___x_437_);
v_snd_439_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_439_);
lean_dec(v_a_438_);
lean_inc(v_a_436_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_440_, 0, v_a_436_);
lean_closure_set(v___f_440_, 1, v___f_423_);
v___x_441_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc(v_a_436_);
v___x_442_ = l_Lean_modToFilePath(v___x_428_, v_a_436_, v___x_441_);
lean_dec_ref(v___x_428_);
v___x_443_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_442_, v___f_440_, v_snd_439_);
lean_dec_ref(v___x_442_);
v___y_409_ = v___x_443_;
goto v___jp_408_;
}
else
{
lean_dec_ref(v___x_428_);
lean_dec_ref(v___f_423_);
lean_dec_ref(v_self_401_);
return v___x_437_;
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v_self_401_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_b_405_);
lean_ctor_set(v___x_444_, 1, v___y_406_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
v___jp_408_:
{
if (lean_obj_tag(v___y_409_) == 0)
{
lean_object* v_a_410_; lean_object* v_fst_411_; lean_object* v_snd_412_; size_t v___x_413_; size_t v___x_414_; 
v_a_410_ = lean_ctor_get(v___y_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v___y_409_);
v_fst_411_ = lean_ctor_get(v_a_410_, 0);
lean_inc(v_fst_411_);
v_snd_412_ = lean_ctor_get(v_a_410_, 1);
lean_inc(v_snd_412_);
lean_dec(v_a_410_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_403_, v___x_413_);
v_i_403_ = v___x_414_;
v_b_405_ = v_fst_411_;
v___y_406_ = v_snd_412_;
goto _start;
}
else
{
lean_dec_ref(v_self_401_);
return v___y_409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object* v_self_446_, lean_object* v_as_447_, lean_object* v_i_448_, lean_object* v_stop_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
size_t v_i_boxed_453_; size_t v_stop_boxed_454_; lean_object* v_res_455_; 
v_i_boxed_453_ = lean_unbox_usize(v_i_448_);
lean_dec(v_i_448_);
v_stop_boxed_454_ = lean_unbox_usize(v_stop_449_);
lean_dec(v_stop_449_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_446_, v_as_447_, v_i_boxed_453_, v_stop_boxed_454_, v_b_450_, v___y_451_);
lean_dec_ref(v_as_447_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object* v_self_458_){
_start:
{
lean_object* v___y_461_; lean_object* v_config_479_; lean_object* v_globs_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_config_479_ = lean_ctor_get(v_self_458_, 2);
v_globs_480_ = lean_ctor_get(v_config_479_, 3);
lean_inc_ref(v_globs_480_);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_array_get_size(v_globs_480_);
v___x_483_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_484_ = lean_nat_dec_lt(v___x_481_, v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec_ref(v_globs_480_);
lean_dec_ref(v_self_458_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_nat_dec_le(v___x_482_, v___x_482_);
if (v___x_487_ == 0)
{
if (v___x_484_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v_globs_480_);
lean_dec_ref(v_self_458_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_483_);
return v___x_488_;
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_482_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_458_, v_globs_480_, v___x_489_, v___x_490_, v___x_486_, v___x_483_);
lean_dec_ref(v_globs_480_);
v___y_461_ = v___x_491_;
goto v___jp_460_;
}
}
else
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((size_t)0ULL);
v___x_493_ = lean_usize_of_nat(v___x_482_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_458_, v_globs_480_, v___x_492_, v___x_493_, v___x_486_, v___x_483_);
lean_dec_ref(v_globs_480_);
v___y_461_ = v___x_494_;
goto v___jp_460_;
}
}
v___jp_460_:
{
if (lean_obj_tag(v___y_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_a_462_ = lean_ctor_get(v___y_461_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___y_461_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v___y_461_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___y_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_snd_466_; lean_object* v___x_468_; 
v_snd_466_ = lean_ctor_get(v_a_462_, 1);
lean_inc(v_snd_466_);
lean_dec(v_a_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v_snd_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_snd_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___y_461_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___y_461_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___y_461_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___y_461_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object* v_self_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lake_LeanLib_getModuleArray(v_self_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object* v_self_498_, lean_object* v_as_499_, size_t v_i_500_, size_t v_stop_501_, lean_object* v_b_502_){
_start:
{
lean_object* v___y_504_; uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_eq(v_i_500_, v_stop_501_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_array_uget_borrowed(v_as_499_, v_i_500_);
lean_inc_ref(v_self_498_);
lean_inc(v___x_509_);
v___x_510_ = l_Lake_LeanLib_findModule_x3f(v___x_509_, v_self_498_);
if (lean_obj_tag(v___x_510_) == 0)
{
v___y_504_ = v_b_502_;
goto v___jp_503_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; 
v_val_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_val_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_array_push(v_b_502_, v_val_511_);
v___y_504_ = v___x_512_;
goto v___jp_503_;
}
}
else
{
lean_dec_ref(v_self_498_);
return v_b_502_;
}
v___jp_503_:
{
size_t v___x_505_; size_t v___x_506_; 
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_500_, v___x_505_);
v_i_500_ = v___x_506_;
v_b_502_ = v___y_504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object* v_self_513_, lean_object* v_as_514_, lean_object* v_i_515_, lean_object* v_stop_516_, lean_object* v_b_517_){
_start:
{
size_t v_i_boxed_518_; size_t v_stop_boxed_519_; lean_object* v_res_520_; 
v_i_boxed_518_ = lean_unbox_usize(v_i_515_);
lean_dec(v_i_515_);
v_stop_boxed_519_ = lean_unbox_usize(v_stop_516_);
lean_dec(v_stop_516_);
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_513_, v_as_514_, v_i_boxed_518_, v_stop_boxed_519_, v_b_517_);
lean_dec_ref(v_as_514_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object* v_self_521_, lean_object* v_as_522_, lean_object* v_start_523_, lean_object* v_stop_524_){
_start:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_526_ = lean_nat_dec_lt(v_start_523_, v_stop_524_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_self_521_);
return v___x_525_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_get_size(v_as_522_);
v___x_528_ = lean_nat_dec_le(v_stop_524_, v___x_527_);
if (v___x_528_ == 0)
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_lt(v_start_523_, v___x_527_);
if (v___x_529_ == 0)
{
lean_dec_ref(v_self_521_);
return v___x_525_;
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_usize_of_nat(v_start_523_);
v___x_531_ = lean_usize_of_nat(v___x_527_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_521_, v_as_522_, v___x_530_, v___x_531_, v___x_525_);
return v___x_532_;
}
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_usize_of_nat(v_start_523_);
v___x_534_ = lean_usize_of_nat(v_stop_524_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_521_, v_as_522_, v___x_533_, v___x_534_, v___x_525_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object* v_self_536_, lean_object* v_as_537_, lean_object* v_start_538_, lean_object* v_stop_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_536_, v_as_537_, v_start_538_, v_stop_539_);
lean_dec(v_stop_539_);
lean_dec(v_start_538_);
lean_dec_ref(v_as_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* v_self_541_){
_start:
{
lean_object* v_config_542_; lean_object* v_roots_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_config_542_ = lean_ctor_get(v_self_541_, 2);
v_roots_543_ = lean_ctor_get(v_config_542_, 2);
lean_inc_ref(v_roots_543_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_array_get_size(v_roots_543_);
v___x_546_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_541_, v_roots_543_, v___x_544_, v___x_545_);
lean_dec_ref(v_roots_543_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* v_self_547_){
_start:
{
lean_object* v_lib_548_; lean_object* v_pkg_549_; 
v_lib_548_ = lean_ctor_get(v_self_547_, 0);
v_pkg_549_ = lean_ctor_get(v_lib_548_, 0);
lean_inc_ref(v_pkg_549_);
return v_pkg_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* v_self_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lake_Module_pkg(v_self_550_);
lean_dec_ref(v_self_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* v_self_552_){
_start:
{
lean_object* v_lib_553_; lean_object* v_pkg_554_; lean_object* v_config_555_; lean_object* v_config_556_; lean_object* v_dir_557_; lean_object* v_srcDir_558_; lean_object* v_srcDir_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_lib_553_ = lean_ctor_get(v_self_552_, 0);
lean_inc_ref(v_lib_553_);
lean_dec_ref(v_self_552_);
v_pkg_554_ = lean_ctor_get(v_lib_553_, 0);
lean_inc_ref(v_pkg_554_);
v_config_555_ = lean_ctor_get(v_pkg_554_, 6);
lean_inc_ref(v_config_555_);
v_config_556_ = lean_ctor_get(v_lib_553_, 2);
lean_inc(v_config_556_);
lean_dec_ref(v_lib_553_);
v_dir_557_ = lean_ctor_get(v_pkg_554_, 4);
lean_inc_ref(v_dir_557_);
lean_dec_ref(v_pkg_554_);
v_srcDir_558_ = lean_ctor_get(v_config_555_, 5);
lean_inc_ref(v_srcDir_558_);
lean_dec_ref(v_config_555_);
v_srcDir_559_ = lean_ctor_get(v_config_556_, 1);
lean_inc_ref(v_srcDir_559_);
lean_dec(v_config_556_);
v___x_560_ = l_System_FilePath_normalize(v_srcDir_558_);
v___x_561_ = l_Lake_joinRelative(v_dir_557_, v___x_560_);
v___x_562_ = l_System_FilePath_normalize(v_srcDir_559_);
v___x_563_ = l_Lake_joinRelative(v___x_561_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_564_, lean_object* v_ext_565_, lean_object* v_self_566_){
_start:
{
lean_object* v_name_567_; lean_object* v___x_568_; 
v_name_567_ = lean_ctor_get(v_self_566_, 1);
lean_inc(v_name_567_);
lean_dec_ref(v_self_566_);
v___x_568_ = l_Lean_modToFilePath(v_dir_564_, v_name_567_, v_ext_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_569_, lean_object* v_ext_570_, lean_object* v_self_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lake_Module_filePath(v_dir_569_, v_ext_570_, v_self_571_);
lean_dec_ref(v_ext_570_);
lean_dec_ref(v_dir_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_573_, lean_object* v_self_574_){
_start:
{
lean_object* v_lib_575_; lean_object* v_pkg_576_; lean_object* v_config_577_; lean_object* v_config_578_; lean_object* v_name_579_; lean_object* v_dir_580_; lean_object* v_srcDir_581_; lean_object* v_srcDir_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_lib_575_ = lean_ctor_get(v_self_574_, 0);
v_pkg_576_ = lean_ctor_get(v_lib_575_, 0);
lean_inc_ref(v_pkg_576_);
v_config_577_ = lean_ctor_get(v_pkg_576_, 6);
lean_inc_ref(v_config_577_);
v_config_578_ = lean_ctor_get(v_lib_575_, 2);
lean_inc(v_config_578_);
v_name_579_ = lean_ctor_get(v_self_574_, 1);
lean_inc(v_name_579_);
lean_dec_ref(v_self_574_);
v_dir_580_ = lean_ctor_get(v_pkg_576_, 4);
lean_inc_ref(v_dir_580_);
lean_dec_ref(v_pkg_576_);
v_srcDir_581_ = lean_ctor_get(v_config_577_, 5);
lean_inc_ref(v_srcDir_581_);
lean_dec_ref(v_config_577_);
v_srcDir_582_ = lean_ctor_get(v_config_578_, 1);
lean_inc_ref(v_srcDir_582_);
lean_dec(v_config_578_);
v___x_583_ = l_System_FilePath_normalize(v_srcDir_581_);
v___x_584_ = l_Lake_joinRelative(v_dir_580_, v___x_583_);
v___x_585_ = l_System_FilePath_normalize(v_srcDir_582_);
v___x_586_ = l_Lake_joinRelative(v___x_584_, v___x_585_);
v___x_587_ = l_Lean_modToFilePath(v___x_586_, v_name_579_, v_ext_573_);
lean_dec_ref(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_588_, lean_object* v_self_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lake_Module_srcPath(v_ext_588_, v_self_589_);
lean_dec_ref(v_ext_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_591_){
_start:
{
lean_object* v_lib_592_; lean_object* v_pkg_593_; lean_object* v_config_594_; lean_object* v_config_595_; lean_object* v_name_596_; lean_object* v_dir_597_; lean_object* v_srcDir_598_; lean_object* v_srcDir_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_lib_592_ = lean_ctor_get(v_self_591_, 0);
v_pkg_593_ = lean_ctor_get(v_lib_592_, 0);
lean_inc_ref(v_pkg_593_);
v_config_594_ = lean_ctor_get(v_pkg_593_, 6);
lean_inc_ref(v_config_594_);
v_config_595_ = lean_ctor_get(v_lib_592_, 2);
lean_inc(v_config_595_);
v_name_596_ = lean_ctor_get(v_self_591_, 1);
lean_inc(v_name_596_);
lean_dec_ref(v_self_591_);
v_dir_597_ = lean_ctor_get(v_pkg_593_, 4);
lean_inc_ref(v_dir_597_);
lean_dec_ref(v_pkg_593_);
v_srcDir_598_ = lean_ctor_get(v_config_594_, 5);
lean_inc_ref(v_srcDir_598_);
lean_dec_ref(v_config_594_);
v_srcDir_599_ = lean_ctor_get(v_config_595_, 1);
lean_inc_ref(v_srcDir_599_);
lean_dec(v_config_595_);
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_601_ = l_System_FilePath_normalize(v_srcDir_598_);
v___x_602_ = l_Lake_joinRelative(v_dir_597_, v___x_601_);
v___x_603_ = l_System_FilePath_normalize(v_srcDir_599_);
v___x_604_ = l_Lake_joinRelative(v___x_602_, v___x_603_);
v___x_605_ = l_Lean_modToFilePath(v___x_604_, v_name_596_, v___x_600_);
lean_dec_ref(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_606_){
_start:
{
lean_object* v_lib_607_; lean_object* v_pkg_608_; lean_object* v_config_609_; lean_object* v_config_610_; lean_object* v_name_611_; lean_object* v_dir_612_; lean_object* v_srcDir_613_; lean_object* v_srcDir_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_lib_607_ = lean_ctor_get(v_self_606_, 0);
v_pkg_608_ = lean_ctor_get(v_lib_607_, 0);
lean_inc_ref(v_pkg_608_);
v_config_609_ = lean_ctor_get(v_pkg_608_, 6);
lean_inc_ref(v_config_609_);
v_config_610_ = lean_ctor_get(v_lib_607_, 2);
lean_inc(v_config_610_);
v_name_611_ = lean_ctor_get(v_self_606_, 1);
lean_inc(v_name_611_);
lean_dec_ref(v_self_606_);
v_dir_612_ = lean_ctor_get(v_pkg_608_, 4);
lean_inc_ref(v_dir_612_);
lean_dec_ref(v_pkg_608_);
v_srcDir_613_ = lean_ctor_get(v_config_609_, 5);
lean_inc_ref(v_srcDir_613_);
lean_dec_ref(v_config_609_);
v_srcDir_614_ = lean_ctor_get(v_config_610_, 1);
lean_inc_ref(v_srcDir_614_);
lean_dec(v_config_610_);
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_616_ = l_System_FilePath_normalize(v_srcDir_613_);
lean_inc_ref(v_dir_612_);
v___x_617_ = l_Lake_joinRelative(v_dir_612_, v___x_616_);
v___x_618_ = l_System_FilePath_normalize(v_srcDir_614_);
v___x_619_ = l_Lake_joinRelative(v___x_617_, v___x_618_);
v___x_620_ = l_Lean_modToFilePath(v___x_619_, v_name_611_, v___x_615_);
lean_dec_ref(v___x_619_);
v___x_621_ = l_Lake_relPathFrom(v_dir_612_, v___x_620_);
lean_dec_ref(v_dir_612_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_622_, lean_object* v_self_623_){
_start:
{
lean_object* v_lib_624_; lean_object* v_pkg_625_; lean_object* v_config_626_; lean_object* v_name_627_; lean_object* v_dir_628_; lean_object* v_buildDir_629_; lean_object* v_leanLibDir_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_lib_624_ = lean_ctor_get(v_self_623_, 0);
v_pkg_625_ = lean_ctor_get(v_lib_624_, 0);
lean_inc_ref(v_pkg_625_);
v_config_626_ = lean_ctor_get(v_pkg_625_, 6);
lean_inc_ref(v_config_626_);
v_name_627_ = lean_ctor_get(v_self_623_, 1);
lean_inc(v_name_627_);
lean_dec_ref(v_self_623_);
v_dir_628_ = lean_ctor_get(v_pkg_625_, 4);
lean_inc_ref(v_dir_628_);
lean_dec_ref(v_pkg_625_);
v_buildDir_629_ = lean_ctor_get(v_config_626_, 6);
lean_inc_ref(v_buildDir_629_);
v_leanLibDir_630_ = lean_ctor_get(v_config_626_, 7);
lean_inc_ref(v_leanLibDir_630_);
lean_dec_ref(v_config_626_);
v___x_631_ = l_System_FilePath_normalize(v_buildDir_629_);
v___x_632_ = l_Lake_joinRelative(v_dir_628_, v___x_631_);
v___x_633_ = l_System_FilePath_normalize(v_leanLibDir_630_);
v___x_634_ = l_Lake_joinRelative(v___x_632_, v___x_633_);
v___x_635_ = l_Lean_modToFilePath(v___x_634_, v_name_627_, v_ext_622_);
lean_dec_ref(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_636_, lean_object* v_self_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lake_Module_leanLibPath(v_ext_636_, v_self_637_);
lean_dec_ref(v_ext_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_640_){
_start:
{
lean_object* v_lib_641_; lean_object* v_pkg_642_; lean_object* v_config_643_; lean_object* v_name_644_; lean_object* v_dir_645_; lean_object* v_buildDir_646_; lean_object* v_leanLibDir_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_lib_641_ = lean_ctor_get(v_self_640_, 0);
v_pkg_642_ = lean_ctor_get(v_lib_641_, 0);
lean_inc_ref(v_pkg_642_);
v_config_643_ = lean_ctor_get(v_pkg_642_, 6);
lean_inc_ref(v_config_643_);
v_name_644_ = lean_ctor_get(v_self_640_, 1);
lean_inc(v_name_644_);
lean_dec_ref(v_self_640_);
v_dir_645_ = lean_ctor_get(v_pkg_642_, 4);
lean_inc_ref(v_dir_645_);
lean_dec_ref(v_pkg_642_);
v_buildDir_646_ = lean_ctor_get(v_config_643_, 6);
lean_inc_ref(v_buildDir_646_);
v_leanLibDir_647_ = lean_ctor_get(v_config_643_, 7);
lean_inc_ref(v_leanLibDir_647_);
lean_dec_ref(v_config_643_);
v___x_648_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_649_ = l_System_FilePath_normalize(v_buildDir_646_);
v___x_650_ = l_Lake_joinRelative(v_dir_645_, v___x_649_);
v___x_651_ = l_System_FilePath_normalize(v_leanLibDir_647_);
v___x_652_ = l_Lake_joinRelative(v___x_650_, v___x_651_);
v___x_653_ = l_Lean_modToFilePath(v___x_652_, v_name_644_, v___x_648_);
lean_dec_ref(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_655_){
_start:
{
lean_object* v_lib_656_; lean_object* v_pkg_657_; lean_object* v_config_658_; lean_object* v_name_659_; lean_object* v_dir_660_; lean_object* v_buildDir_661_; lean_object* v_leanLibDir_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_lib_656_ = lean_ctor_get(v_self_655_, 0);
v_pkg_657_ = lean_ctor_get(v_lib_656_, 0);
lean_inc_ref(v_pkg_657_);
v_config_658_ = lean_ctor_get(v_pkg_657_, 6);
lean_inc_ref(v_config_658_);
v_name_659_ = lean_ctor_get(v_self_655_, 1);
lean_inc(v_name_659_);
lean_dec_ref(v_self_655_);
v_dir_660_ = lean_ctor_get(v_pkg_657_, 4);
lean_inc_ref(v_dir_660_);
lean_dec_ref(v_pkg_657_);
v_buildDir_661_ = lean_ctor_get(v_config_658_, 6);
lean_inc_ref(v_buildDir_661_);
v_leanLibDir_662_ = lean_ctor_get(v_config_658_, 7);
lean_inc_ref(v_leanLibDir_662_);
lean_dec_ref(v_config_658_);
v___x_663_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_664_ = l_System_FilePath_normalize(v_buildDir_661_);
v___x_665_ = l_Lake_joinRelative(v_dir_660_, v___x_664_);
v___x_666_ = l_System_FilePath_normalize(v_leanLibDir_662_);
v___x_667_ = l_Lake_joinRelative(v___x_665_, v___x_666_);
v___x_668_ = l_Lean_modToFilePath(v___x_667_, v_name_659_, v___x_663_);
lean_dec_ref(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_670_){
_start:
{
lean_object* v_lib_671_; lean_object* v_pkg_672_; lean_object* v_config_673_; lean_object* v_name_674_; lean_object* v_dir_675_; lean_object* v_buildDir_676_; lean_object* v_leanLibDir_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_lib_671_ = lean_ctor_get(v_self_670_, 0);
v_pkg_672_ = lean_ctor_get(v_lib_671_, 0);
lean_inc_ref(v_pkg_672_);
v_config_673_ = lean_ctor_get(v_pkg_672_, 6);
lean_inc_ref(v_config_673_);
v_name_674_ = lean_ctor_get(v_self_670_, 1);
lean_inc(v_name_674_);
lean_dec_ref(v_self_670_);
v_dir_675_ = lean_ctor_get(v_pkg_672_, 4);
lean_inc_ref(v_dir_675_);
lean_dec_ref(v_pkg_672_);
v_buildDir_676_ = lean_ctor_get(v_config_673_, 6);
lean_inc_ref(v_buildDir_676_);
v_leanLibDir_677_ = lean_ctor_get(v_config_673_, 7);
lean_inc_ref(v_leanLibDir_677_);
lean_dec_ref(v_config_673_);
v___x_678_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_679_ = l_System_FilePath_normalize(v_buildDir_676_);
v___x_680_ = l_Lake_joinRelative(v_dir_675_, v___x_679_);
v___x_681_ = l_System_FilePath_normalize(v_leanLibDir_677_);
v___x_682_ = l_Lake_joinRelative(v___x_680_, v___x_681_);
v___x_683_ = l_Lean_modToFilePath(v___x_682_, v_name_674_, v___x_678_);
lean_dec_ref(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_685_){
_start:
{
lean_object* v_lib_686_; lean_object* v_pkg_687_; lean_object* v_config_688_; lean_object* v_name_689_; lean_object* v_dir_690_; lean_object* v_buildDir_691_; lean_object* v_leanLibDir_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_lib_686_ = lean_ctor_get(v_self_685_, 0);
v_pkg_687_ = lean_ctor_get(v_lib_686_, 0);
lean_inc_ref(v_pkg_687_);
v_config_688_ = lean_ctor_get(v_pkg_687_, 6);
lean_inc_ref(v_config_688_);
v_name_689_ = lean_ctor_get(v_self_685_, 1);
lean_inc(v_name_689_);
lean_dec_ref(v_self_685_);
v_dir_690_ = lean_ctor_get(v_pkg_687_, 4);
lean_inc_ref(v_dir_690_);
lean_dec_ref(v_pkg_687_);
v_buildDir_691_ = lean_ctor_get(v_config_688_, 6);
lean_inc_ref(v_buildDir_691_);
v_leanLibDir_692_ = lean_ctor_get(v_config_688_, 7);
lean_inc_ref(v_leanLibDir_692_);
lean_dec_ref(v_config_688_);
v___x_693_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_694_ = l_System_FilePath_normalize(v_buildDir_691_);
v___x_695_ = l_Lake_joinRelative(v_dir_690_, v___x_694_);
v___x_696_ = l_System_FilePath_normalize(v_leanLibDir_692_);
v___x_697_ = l_Lake_joinRelative(v___x_695_, v___x_696_);
v___x_698_ = l_Lean_modToFilePath(v___x_697_, v_name_689_, v___x_693_);
lean_dec_ref(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_700_){
_start:
{
lean_object* v_lib_701_; lean_object* v_pkg_702_; lean_object* v_config_703_; lean_object* v_name_704_; lean_object* v_dir_705_; lean_object* v_buildDir_706_; lean_object* v_leanLibDir_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_lib_701_ = lean_ctor_get(v_self_700_, 0);
v_pkg_702_ = lean_ctor_get(v_lib_701_, 0);
lean_inc_ref(v_pkg_702_);
v_config_703_ = lean_ctor_get(v_pkg_702_, 6);
lean_inc_ref(v_config_703_);
v_name_704_ = lean_ctor_get(v_self_700_, 1);
lean_inc(v_name_704_);
lean_dec_ref(v_self_700_);
v_dir_705_ = lean_ctor_get(v_pkg_702_, 4);
lean_inc_ref(v_dir_705_);
lean_dec_ref(v_pkg_702_);
v_buildDir_706_ = lean_ctor_get(v_config_703_, 6);
lean_inc_ref(v_buildDir_706_);
v_leanLibDir_707_ = lean_ctor_get(v_config_703_, 7);
lean_inc_ref(v_leanLibDir_707_);
lean_dec_ref(v_config_703_);
v___x_708_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_709_ = l_System_FilePath_normalize(v_buildDir_706_);
v___x_710_ = l_Lake_joinRelative(v_dir_705_, v___x_709_);
v___x_711_ = l_System_FilePath_normalize(v_leanLibDir_707_);
v___x_712_ = l_Lake_joinRelative(v___x_710_, v___x_711_);
v___x_713_ = l_Lean_modToFilePath(v___x_712_, v_name_704_, v___x_708_);
lean_dec_ref(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_714_, lean_object* v_self_715_){
_start:
{
lean_object* v_lib_716_; lean_object* v_pkg_717_; lean_object* v_config_718_; lean_object* v_name_719_; lean_object* v_dir_720_; lean_object* v_buildDir_721_; lean_object* v_irDir_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_lib_716_ = lean_ctor_get(v_self_715_, 0);
v_pkg_717_ = lean_ctor_get(v_lib_716_, 0);
lean_inc_ref(v_pkg_717_);
v_config_718_ = lean_ctor_get(v_pkg_717_, 6);
lean_inc_ref(v_config_718_);
v_name_719_ = lean_ctor_get(v_self_715_, 1);
lean_inc(v_name_719_);
lean_dec_ref(v_self_715_);
v_dir_720_ = lean_ctor_get(v_pkg_717_, 4);
lean_inc_ref(v_dir_720_);
lean_dec_ref(v_pkg_717_);
v_buildDir_721_ = lean_ctor_get(v_config_718_, 6);
lean_inc_ref(v_buildDir_721_);
v_irDir_722_ = lean_ctor_get(v_config_718_, 10);
lean_inc_ref(v_irDir_722_);
lean_dec_ref(v_config_718_);
v___x_723_ = l_System_FilePath_normalize(v_buildDir_721_);
v___x_724_ = l_Lake_joinRelative(v_dir_720_, v___x_723_);
v___x_725_ = l_System_FilePath_normalize(v_irDir_722_);
v___x_726_ = l_Lake_joinRelative(v___x_724_, v___x_725_);
v___x_727_ = l_Lean_modToFilePath(v___x_726_, v_name_719_, v_ext_714_);
lean_dec_ref(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_728_, lean_object* v_self_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lake_Module_irPath(v_ext_728_, v_self_729_);
lean_dec_ref(v_ext_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_732_){
_start:
{
lean_object* v_lib_733_; lean_object* v_pkg_734_; lean_object* v_config_735_; lean_object* v_name_736_; lean_object* v_dir_737_; lean_object* v_buildDir_738_; lean_object* v_irDir_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_lib_733_ = lean_ctor_get(v_self_732_, 0);
v_pkg_734_ = lean_ctor_get(v_lib_733_, 0);
lean_inc_ref(v_pkg_734_);
v_config_735_ = lean_ctor_get(v_pkg_734_, 6);
lean_inc_ref(v_config_735_);
v_name_736_ = lean_ctor_get(v_self_732_, 1);
lean_inc(v_name_736_);
lean_dec_ref(v_self_732_);
v_dir_737_ = lean_ctor_get(v_pkg_734_, 4);
lean_inc_ref(v_dir_737_);
lean_dec_ref(v_pkg_734_);
v_buildDir_738_ = lean_ctor_get(v_config_735_, 6);
lean_inc_ref(v_buildDir_738_);
v_irDir_739_ = lean_ctor_get(v_config_735_, 10);
lean_inc_ref(v_irDir_739_);
lean_dec_ref(v_config_735_);
v___x_740_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_741_ = l_System_FilePath_normalize(v_buildDir_738_);
v___x_742_ = l_Lake_joinRelative(v_dir_737_, v___x_741_);
v___x_743_ = l_System_FilePath_normalize(v_irDir_739_);
v___x_744_ = l_Lake_joinRelative(v___x_742_, v___x_743_);
v___x_745_ = l_Lean_modToFilePath(v___x_744_, v_name_736_, v___x_740_);
lean_dec_ref(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_747_){
_start:
{
lean_object* v_lib_748_; lean_object* v_pkg_749_; lean_object* v_config_750_; lean_object* v_name_751_; lean_object* v_dir_752_; lean_object* v_buildDir_753_; lean_object* v_leanLibDir_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_lib_748_ = lean_ctor_get(v_self_747_, 0);
v_pkg_749_ = lean_ctor_get(v_lib_748_, 0);
lean_inc_ref(v_pkg_749_);
v_config_750_ = lean_ctor_get(v_pkg_749_, 6);
lean_inc_ref(v_config_750_);
v_name_751_ = lean_ctor_get(v_self_747_, 1);
lean_inc(v_name_751_);
lean_dec_ref(v_self_747_);
v_dir_752_ = lean_ctor_get(v_pkg_749_, 4);
lean_inc_ref(v_dir_752_);
lean_dec_ref(v_pkg_749_);
v_buildDir_753_ = lean_ctor_get(v_config_750_, 6);
lean_inc_ref(v_buildDir_753_);
v_leanLibDir_754_ = lean_ctor_get(v_config_750_, 7);
lean_inc_ref(v_leanLibDir_754_);
lean_dec_ref(v_config_750_);
v___x_755_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_756_ = l_System_FilePath_normalize(v_buildDir_753_);
v___x_757_ = l_Lake_joinRelative(v_dir_752_, v___x_756_);
v___x_758_ = l_System_FilePath_normalize(v_leanLibDir_754_);
v___x_759_ = l_Lake_joinRelative(v___x_757_, v___x_758_);
v___x_760_ = l_Lean_modToFilePath(v___x_759_, v_name_751_, v___x_755_);
lean_dec_ref(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_762_){
_start:
{
lean_object* v_lib_763_; lean_object* v_pkg_764_; lean_object* v_config_765_; lean_object* v_name_766_; lean_object* v_dir_767_; lean_object* v_buildDir_768_; lean_object* v_irDir_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_lib_763_ = lean_ctor_get(v_self_762_, 0);
v_pkg_764_ = lean_ctor_get(v_lib_763_, 0);
lean_inc_ref(v_pkg_764_);
v_config_765_ = lean_ctor_get(v_pkg_764_, 6);
lean_inc_ref(v_config_765_);
v_name_766_ = lean_ctor_get(v_self_762_, 1);
lean_inc(v_name_766_);
lean_dec_ref(v_self_762_);
v_dir_767_ = lean_ctor_get(v_pkg_764_, 4);
lean_inc_ref(v_dir_767_);
lean_dec_ref(v_pkg_764_);
v_buildDir_768_ = lean_ctor_get(v_config_765_, 6);
lean_inc_ref(v_buildDir_768_);
v_irDir_769_ = lean_ctor_get(v_config_765_, 10);
lean_inc_ref(v_irDir_769_);
lean_dec_ref(v_config_765_);
v___x_770_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_771_ = l_System_FilePath_normalize(v_buildDir_768_);
v___x_772_ = l_Lake_joinRelative(v_dir_767_, v___x_771_);
v___x_773_ = l_System_FilePath_normalize(v_irDir_769_);
v___x_774_ = l_Lake_joinRelative(v___x_772_, v___x_773_);
v___x_775_ = l_Lean_modToFilePath(v___x_774_, v_name_766_, v___x_770_);
lean_dec_ref(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_777_){
_start:
{
lean_object* v_lib_778_; lean_object* v_pkg_779_; lean_object* v_config_780_; lean_object* v_name_781_; lean_object* v_dir_782_; lean_object* v_buildDir_783_; lean_object* v_irDir_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_lib_778_ = lean_ctor_get(v_self_777_, 0);
v_pkg_779_ = lean_ctor_get(v_lib_778_, 0);
lean_inc_ref(v_pkg_779_);
v_config_780_ = lean_ctor_get(v_pkg_779_, 6);
lean_inc_ref(v_config_780_);
v_name_781_ = lean_ctor_get(v_self_777_, 1);
lean_inc(v_name_781_);
lean_dec_ref(v_self_777_);
v_dir_782_ = lean_ctor_get(v_pkg_779_, 4);
lean_inc_ref(v_dir_782_);
lean_dec_ref(v_pkg_779_);
v_buildDir_783_ = lean_ctor_get(v_config_780_, 6);
lean_inc_ref(v_buildDir_783_);
v_irDir_784_ = lean_ctor_get(v_config_780_, 10);
lean_inc_ref(v_irDir_784_);
lean_dec_ref(v_config_780_);
v___x_785_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_786_ = l_System_FilePath_normalize(v_buildDir_783_);
v___x_787_ = l_Lake_joinRelative(v_dir_782_, v___x_786_);
v___x_788_ = l_System_FilePath_normalize(v_irDir_784_);
v___x_789_ = l_Lake_joinRelative(v___x_787_, v___x_788_);
v___x_790_ = l_Lean_modToFilePath(v___x_789_, v_name_781_, v___x_785_);
lean_dec_ref(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_792_){
_start:
{
lean_object* v_lib_793_; lean_object* v_pkg_794_; lean_object* v_config_795_; lean_object* v_name_796_; lean_object* v_dir_797_; lean_object* v_buildDir_798_; lean_object* v_irDir_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_lib_793_ = lean_ctor_get(v_self_792_, 0);
v_pkg_794_ = lean_ctor_get(v_lib_793_, 0);
lean_inc_ref(v_pkg_794_);
v_config_795_ = lean_ctor_get(v_pkg_794_, 6);
lean_inc_ref(v_config_795_);
v_name_796_ = lean_ctor_get(v_self_792_, 1);
lean_inc(v_name_796_);
lean_dec_ref(v_self_792_);
v_dir_797_ = lean_ctor_get(v_pkg_794_, 4);
lean_inc_ref(v_dir_797_);
lean_dec_ref(v_pkg_794_);
v_buildDir_798_ = lean_ctor_get(v_config_795_, 6);
lean_inc_ref(v_buildDir_798_);
v_irDir_799_ = lean_ctor_get(v_config_795_, 10);
lean_inc_ref(v_irDir_799_);
lean_dec_ref(v_config_795_);
v___x_800_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_801_ = l_System_FilePath_normalize(v_buildDir_798_);
v___x_802_ = l_Lake_joinRelative(v_dir_797_, v___x_801_);
v___x_803_ = l_System_FilePath_normalize(v_irDir_799_);
v___x_804_ = l_Lake_joinRelative(v___x_802_, v___x_803_);
v___x_805_ = l_Lean_modToFilePath(v___x_804_, v_name_796_, v___x_800_);
lean_dec_ref(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_807_){
_start:
{
lean_object* v_lib_808_; lean_object* v_pkg_809_; lean_object* v_config_810_; lean_object* v_name_811_; lean_object* v_dir_812_; lean_object* v_buildDir_813_; lean_object* v_irDir_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_lib_808_ = lean_ctor_get(v_self_807_, 0);
v_pkg_809_ = lean_ctor_get(v_lib_808_, 0);
lean_inc_ref(v_pkg_809_);
v_config_810_ = lean_ctor_get(v_pkg_809_, 6);
lean_inc_ref(v_config_810_);
v_name_811_ = lean_ctor_get(v_self_807_, 1);
lean_inc(v_name_811_);
lean_dec_ref(v_self_807_);
v_dir_812_ = lean_ctor_get(v_pkg_809_, 4);
lean_inc_ref(v_dir_812_);
lean_dec_ref(v_pkg_809_);
v_buildDir_813_ = lean_ctor_get(v_config_810_, 6);
lean_inc_ref(v_buildDir_813_);
v_irDir_814_ = lean_ctor_get(v_config_810_, 10);
lean_inc_ref(v_irDir_814_);
lean_dec_ref(v_config_810_);
v___x_815_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_816_ = l_System_FilePath_normalize(v_buildDir_813_);
v___x_817_ = l_Lake_joinRelative(v_dir_812_, v___x_816_);
v___x_818_ = l_System_FilePath_normalize(v_irDir_814_);
v___x_819_ = l_Lake_joinRelative(v___x_817_, v___x_818_);
v___x_820_ = l_Lean_modToFilePath(v___x_819_, v_name_811_, v___x_815_);
lean_dec_ref(v___x_819_);
return v___x_820_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_box(0);
v___x_822_ = lean_internal_has_llvm_backend(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_self_823_);
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v_lib_826_; lean_object* v_pkg_827_; lean_object* v_config_828_; lean_object* v_name_829_; lean_object* v_dir_830_; lean_object* v_buildDir_831_; lean_object* v_irDir_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_lib_826_ = lean_ctor_get(v_self_823_, 0);
v_pkg_827_ = lean_ctor_get(v_lib_826_, 0);
lean_inc_ref(v_pkg_827_);
v_config_828_ = lean_ctor_get(v_pkg_827_, 6);
lean_inc_ref(v_config_828_);
v_name_829_ = lean_ctor_get(v_self_823_, 1);
lean_inc(v_name_829_);
lean_dec_ref(v_self_823_);
v_dir_830_ = lean_ctor_get(v_pkg_827_, 4);
lean_inc_ref(v_dir_830_);
lean_dec_ref(v_pkg_827_);
v_buildDir_831_ = lean_ctor_get(v_config_828_, 6);
lean_inc_ref(v_buildDir_831_);
v_irDir_832_ = lean_ctor_get(v_config_828_, 10);
lean_inc_ref(v_irDir_832_);
lean_dec_ref(v_config_828_);
v___x_833_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_834_ = l_System_FilePath_normalize(v_buildDir_831_);
v___x_835_ = l_Lake_joinRelative(v_dir_830_, v___x_834_);
v___x_836_ = l_System_FilePath_normalize(v_irDir_832_);
v___x_837_ = l_Lake_joinRelative(v___x_835_, v___x_836_);
v___x_838_ = l_Lean_modToFilePath(v___x_837_, v_name_829_, v___x_833_);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_841_){
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
v_buildDir_847_ = lean_ctor_get(v_config_844_, 6);
lean_inc_ref(v_buildDir_847_);
v_irDir_848_ = lean_ctor_get(v_config_844_, 10);
lean_inc_ref(v_irDir_848_);
lean_dec_ref(v_config_844_);
v___x_849_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_850_ = l_System_FilePath_normalize(v_buildDir_847_);
v___x_851_ = l_Lake_joinRelative(v_dir_846_, v___x_850_);
v___x_852_ = l_System_FilePath_normalize(v_irDir_848_);
v___x_853_ = l_Lake_joinRelative(v___x_851_, v___x_852_);
v___x_854_ = l_Lean_modToFilePath(v___x_853_, v_name_845_, v___x_849_);
lean_dec_ref(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_857_){
_start:
{
lean_object* v_lib_858_; lean_object* v_name_859_; lean_object* v_pkg_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_lib_858_ = lean_ctor_get(v_self_857_, 0);
lean_inc_ref(v_lib_858_);
v_name_859_ = lean_ctor_get(v_self_857_, 1);
lean_inc(v_name_859_);
lean_dec_ref(v_self_857_);
v_pkg_860_ = lean_ctor_get(v_lib_858_, 0);
lean_inc_ref(v_pkg_860_);
lean_dec_ref(v_lib_858_);
v___x_861_ = l_Lake_Package_id_x3f(v_pkg_860_);
v___x_862_ = l_Lean_mkModuleInitializationStem(v_name_859_, v___x_861_);
lean_dec(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_864_){
_start:
{
lean_object* v_lib_865_; lean_object* v_pkg_866_; lean_object* v_config_867_; lean_object* v_name_868_; lean_object* v_dir_869_; lean_object* v_buildDir_870_; lean_object* v_leanLibDir_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_lib_865_ = lean_ctor_get(v_self_864_, 0);
v_pkg_866_ = lean_ctor_get(v_lib_865_, 0);
lean_inc_ref(v_pkg_866_);
v_config_867_ = lean_ctor_get(v_pkg_866_, 6);
v_name_868_ = lean_ctor_get(v_self_864_, 1);
lean_inc(v_name_868_);
lean_dec_ref(v_self_864_);
v_dir_869_ = lean_ctor_get(v_pkg_866_, 4);
v_buildDir_870_ = lean_ctor_get(v_config_867_, 6);
v_leanLibDir_871_ = lean_ctor_get(v_config_867_, 7);
lean_inc_ref(v_buildDir_870_);
v___x_872_ = l_System_FilePath_normalize(v_buildDir_870_);
lean_inc_ref(v_dir_869_);
v___x_873_ = l_Lake_joinRelative(v_dir_869_, v___x_872_);
lean_inc_ref(v_leanLibDir_871_);
v___x_874_ = l_System_FilePath_normalize(v_leanLibDir_871_);
v___x_875_ = l_Lake_joinRelative(v___x_873_, v___x_874_);
v___x_876_ = l_Lake_Package_id_x3f(v_pkg_866_);
v___x_877_ = l_Lean_mkModuleInitializationStem(v_name_868_, v___x_876_);
lean_dec(v___x_876_);
v___x_878_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_879_ = lean_string_append(v___x_877_, v___x_878_);
v___x_880_ = l_Lake_sharedLibExt;
v___x_881_ = lean_string_append(v___x_879_, v___x_880_);
v___x_882_ = l_Lake_joinRelative(v___x_875_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_883_){
_start:
{
lean_object* v_lib_884_; lean_object* v_pkg_885_; lean_object* v_config_886_; lean_object* v_toLeanConfig_887_; lean_object* v_config_888_; lean_object* v_toLeanConfig_889_; uint8_t v_buildType_890_; lean_object* v_leanOptions_891_; lean_object* v_moreServerOptions_892_; uint8_t v_buildType_893_; lean_object* v_leanOptions_894_; lean_object* v_moreServerOptions_895_; lean_object* v___x_896_; uint8_t v___y_898_; uint8_t v___x_906_; 
v_lib_884_ = lean_ctor_get(v_self_883_, 0);
v_pkg_885_ = lean_ctor_get(v_lib_884_, 0);
v_config_886_ = lean_ctor_get(v_pkg_885_, 6);
v_toLeanConfig_887_ = lean_ctor_get(v_config_886_, 1);
v_config_888_ = lean_ctor_get(v_lib_884_, 2);
v_toLeanConfig_889_ = lean_ctor_get(v_config_888_, 0);
v_buildType_890_ = lean_ctor_get_uint8(v_toLeanConfig_887_, sizeof(void*)*13);
v_leanOptions_891_ = lean_ctor_get(v_toLeanConfig_887_, 0);
v_moreServerOptions_892_ = lean_ctor_get(v_toLeanConfig_887_, 4);
v_buildType_893_ = lean_ctor_get_uint8(v_toLeanConfig_889_, sizeof(void*)*13);
v_leanOptions_894_ = lean_ctor_get(v_toLeanConfig_889_, 0);
v_moreServerOptions_895_ = lean_ctor_get(v_toLeanConfig_889_, 4);
v___x_896_ = lean_box(1);
v___x_906_ = l_Lake_instOrdBuildType_ord(v_buildType_890_, v_buildType_893_);
if (v___x_906_ == 2)
{
v___y_898_ = v_buildType_893_;
goto v___jp_897_;
}
else
{
v___y_898_ = v_buildType_890_;
goto v___jp_897_;
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_899_ = l_Lake_BuildType_leanOptions(v___y_898_);
v___x_900_ = l_Lean_LeanOptions_append(v___x_896_, v___x_899_);
v___x_901_ = l_Lean_LeanOptions_ofArray(v_leanOptions_891_);
v___x_902_ = l_Lean_LeanOptions_appendArray(v___x_901_, v_moreServerOptions_892_);
v___x_903_ = l_Lean_LeanOptions_append(v___x_900_, v___x_902_);
v___x_904_ = l_Lean_LeanOptions_appendArray(v___x_903_, v_leanOptions_894_);
v___x_905_ = l_Lean_LeanOptions_appendArray(v___x_904_, v_moreServerOptions_895_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lake_Module_serverOptions(v_self_907_);
lean_dec_ref(v_self_907_);
return v_res_908_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_909_){
_start:
{
lean_object* v_lib_910_; lean_object* v_pkg_911_; lean_object* v_config_912_; lean_object* v_toLeanConfig_913_; lean_object* v_config_914_; lean_object* v_toLeanConfig_915_; uint8_t v_buildType_916_; uint8_t v_buildType_917_; uint8_t v___x_918_; 
v_lib_910_ = lean_ctor_get(v_self_909_, 0);
v_pkg_911_ = lean_ctor_get(v_lib_910_, 0);
v_config_912_ = lean_ctor_get(v_pkg_911_, 6);
v_toLeanConfig_913_ = lean_ctor_get(v_config_912_, 1);
v_config_914_ = lean_ctor_get(v_lib_910_, 2);
v_toLeanConfig_915_ = lean_ctor_get(v_config_914_, 0);
v_buildType_916_ = lean_ctor_get_uint8(v_toLeanConfig_913_, sizeof(void*)*13);
v_buildType_917_ = lean_ctor_get_uint8(v_toLeanConfig_915_, sizeof(void*)*13);
v___x_918_ = l_Lake_instOrdBuildType_ord(v_buildType_916_, v_buildType_917_);
if (v___x_918_ == 2)
{
return v_buildType_917_;
}
else
{
return v_buildType_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_919_){
_start:
{
uint8_t v_res_920_; lean_object* v_r_921_; 
v_res_920_ = l_Lake_Module_buildType(v_self_919_);
lean_dec_ref(v_self_919_);
v_r_921_ = lean_box(v_res_920_);
return v_r_921_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_922_){
_start:
{
lean_object* v_lib_923_; lean_object* v_config_924_; lean_object* v_toLeanConfig_925_; lean_object* v_pkg_926_; lean_object* v_config_927_; lean_object* v_toLeanConfig_928_; uint8_t v_backend_929_; uint8_t v_backend_930_; uint8_t v___x_931_; 
v_lib_923_ = lean_ctor_get(v_self_922_, 0);
v_config_924_ = lean_ctor_get(v_lib_923_, 2);
v_toLeanConfig_925_ = lean_ctor_get(v_config_924_, 0);
v_pkg_926_ = lean_ctor_get(v_lib_923_, 0);
v_config_927_ = lean_ctor_get(v_pkg_926_, 6);
v_toLeanConfig_928_ = lean_ctor_get(v_config_927_, 1);
v_backend_929_ = lean_ctor_get_uint8(v_toLeanConfig_925_, sizeof(void*)*13 + 1);
v_backend_930_ = lean_ctor_get_uint8(v_toLeanConfig_928_, sizeof(void*)*13 + 1);
v___x_931_ = l_Lake_Backend_orPreferLeft(v_backend_929_, v_backend_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lake_Module_backend(v_self_932_);
lean_dec_ref(v_self_932_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_935_){
_start:
{
lean_object* v_lib_936_; lean_object* v_config_937_; uint8_t v_allowImportAll_938_; 
v_lib_936_ = lean_ctor_get(v_self_935_, 0);
v_config_937_ = lean_ctor_get(v_lib_936_, 2);
v_allowImportAll_938_ = lean_ctor_get_uint8(v_config_937_, sizeof(void*)*9 + 2);
if (v_allowImportAll_938_ == 0)
{
lean_object* v_pkg_939_; lean_object* v_config_940_; uint8_t v_allowImportAll_941_; 
v_pkg_939_ = lean_ctor_get(v_lib_936_, 0);
v_config_940_ = lean_ctor_get(v_pkg_939_, 6);
v_allowImportAll_941_ = lean_ctor_get_uint8(v_config_940_, sizeof(void*)*27 + 5);
return v_allowImportAll_941_;
}
else
{
return v_allowImportAll_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lake_Module_allowImportAll(v_self_942_);
lean_dec_ref(v_self_942_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_945_){
_start:
{
lean_object* v_lib_946_; lean_object* v_pkg_947_; lean_object* v_config_948_; lean_object* v_toLeanConfig_949_; lean_object* v_config_950_; lean_object* v_toLeanConfig_951_; lean_object* v_dynlibs_952_; lean_object* v_dynlibs_953_; lean_object* v___x_954_; 
v_lib_946_ = lean_ctor_get(v_self_945_, 0);
lean_inc_ref(v_lib_946_);
lean_dec_ref(v_self_945_);
v_pkg_947_ = lean_ctor_get(v_lib_946_, 0);
v_config_948_ = lean_ctor_get(v_pkg_947_, 6);
v_toLeanConfig_949_ = lean_ctor_get(v_config_948_, 1);
lean_inc_ref(v_toLeanConfig_949_);
v_config_950_ = lean_ctor_get(v_lib_946_, 2);
lean_inc(v_config_950_);
lean_dec_ref(v_lib_946_);
v_toLeanConfig_951_ = lean_ctor_get(v_config_950_, 0);
lean_inc_ref(v_toLeanConfig_951_);
lean_dec(v_config_950_);
v_dynlibs_952_ = lean_ctor_get(v_toLeanConfig_949_, 11);
lean_inc_ref(v_dynlibs_952_);
lean_dec_ref(v_toLeanConfig_949_);
v_dynlibs_953_ = lean_ctor_get(v_toLeanConfig_951_, 11);
lean_inc_ref(v_dynlibs_953_);
lean_dec_ref(v_toLeanConfig_951_);
v___x_954_ = l_Array_append___redArg(v_dynlibs_952_, v_dynlibs_953_);
lean_dec_ref(v_dynlibs_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_955_){
_start:
{
lean_object* v_lib_956_; lean_object* v_pkg_957_; lean_object* v_config_958_; lean_object* v_toLeanConfig_959_; lean_object* v_config_960_; lean_object* v_toLeanConfig_961_; lean_object* v_plugins_962_; lean_object* v_plugins_963_; lean_object* v___x_964_; 
v_lib_956_ = lean_ctor_get(v_self_955_, 0);
lean_inc_ref(v_lib_956_);
lean_dec_ref(v_self_955_);
v_pkg_957_ = lean_ctor_get(v_lib_956_, 0);
v_config_958_ = lean_ctor_get(v_pkg_957_, 6);
v_toLeanConfig_959_ = lean_ctor_get(v_config_958_, 1);
lean_inc_ref(v_toLeanConfig_959_);
v_config_960_ = lean_ctor_get(v_lib_956_, 2);
lean_inc(v_config_960_);
lean_dec_ref(v_lib_956_);
v_toLeanConfig_961_ = lean_ctor_get(v_config_960_, 0);
lean_inc_ref(v_toLeanConfig_961_);
lean_dec(v_config_960_);
v_plugins_962_ = lean_ctor_get(v_toLeanConfig_959_, 12);
lean_inc_ref(v_plugins_962_);
lean_dec_ref(v_toLeanConfig_959_);
v_plugins_963_ = lean_ctor_get(v_toLeanConfig_961_, 12);
lean_inc_ref(v_plugins_963_);
lean_dec_ref(v_toLeanConfig_961_);
v___x_964_ = l_Array_append___redArg(v_plugins_962_, v_plugins_963_);
lean_dec_ref(v_plugins_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_965_){
_start:
{
lean_object* v_lib_966_; lean_object* v_pkg_967_; lean_object* v_config_968_; lean_object* v_toLeanConfig_969_; lean_object* v_config_970_; lean_object* v_toLeanConfig_971_; uint8_t v_buildType_972_; lean_object* v_leanOptions_973_; uint8_t v_buildType_974_; lean_object* v_leanOptions_975_; uint8_t v___y_977_; uint8_t v___x_982_; 
v_lib_966_ = lean_ctor_get(v_self_965_, 0);
v_pkg_967_ = lean_ctor_get(v_lib_966_, 0);
v_config_968_ = lean_ctor_get(v_pkg_967_, 6);
v_toLeanConfig_969_ = lean_ctor_get(v_config_968_, 1);
v_config_970_ = lean_ctor_get(v_lib_966_, 2);
v_toLeanConfig_971_ = lean_ctor_get(v_config_970_, 0);
v_buildType_972_ = lean_ctor_get_uint8(v_toLeanConfig_969_, sizeof(void*)*13);
v_leanOptions_973_ = lean_ctor_get(v_toLeanConfig_969_, 0);
v_buildType_974_ = lean_ctor_get_uint8(v_toLeanConfig_971_, sizeof(void*)*13);
v_leanOptions_975_ = lean_ctor_get(v_toLeanConfig_971_, 0);
v___x_982_ = l_Lake_instOrdBuildType_ord(v_buildType_972_, v_buildType_974_);
if (v___x_982_ == 2)
{
v___y_977_ = v_buildType_974_;
goto v___jp_976_;
}
else
{
v___y_977_ = v_buildType_972_;
goto v___jp_976_;
}
v___jp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = l_Lake_BuildType_leanOptions(v___y_977_);
v___x_979_ = l_Lean_LeanOptions_ofArray(v_leanOptions_973_);
v___x_980_ = l_Lean_LeanOptions_append(v___x_978_, v___x_979_);
v___x_981_ = l_Lean_LeanOptions_appendArray(v___x_980_, v_leanOptions_975_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lake_Module_leanOptions(v_self_983_);
lean_dec_ref(v_self_983_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_985_){
_start:
{
lean_object* v_lib_986_; lean_object* v_pkg_987_; lean_object* v_config_988_; lean_object* v_toLeanConfig_989_; lean_object* v_config_990_; lean_object* v_toLeanConfig_991_; uint8_t v_buildType_992_; lean_object* v_moreLeanArgs_993_; uint8_t v_buildType_994_; lean_object* v_moreLeanArgs_995_; uint8_t v___y_997_; uint8_t v___x_1001_; 
v_lib_986_ = lean_ctor_get(v_self_985_, 0);
v_pkg_987_ = lean_ctor_get(v_lib_986_, 0);
v_config_988_ = lean_ctor_get(v_pkg_987_, 6);
v_toLeanConfig_989_ = lean_ctor_get(v_config_988_, 1);
v_config_990_ = lean_ctor_get(v_lib_986_, 2);
v_toLeanConfig_991_ = lean_ctor_get(v_config_990_, 0);
v_buildType_992_ = lean_ctor_get_uint8(v_toLeanConfig_989_, sizeof(void*)*13);
v_moreLeanArgs_993_ = lean_ctor_get(v_toLeanConfig_989_, 1);
v_buildType_994_ = lean_ctor_get_uint8(v_toLeanConfig_991_, sizeof(void*)*13);
v_moreLeanArgs_995_ = lean_ctor_get(v_toLeanConfig_991_, 1);
v___x_1001_ = l_Lake_instOrdBuildType_ord(v_buildType_992_, v_buildType_994_);
if (v___x_1001_ == 2)
{
v___y_997_ = v_buildType_994_;
goto v___jp_996_;
}
else
{
v___y_997_ = v_buildType_992_;
goto v___jp_996_;
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = l_Lake_BuildType_leanArgs(v___y_997_);
v___x_999_ = l_Array_append___redArg(v___x_998_, v_moreLeanArgs_993_);
v___x_1000_ = l_Array_append___redArg(v___x_999_, v_moreLeanArgs_995_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lake_Module_leanArgs(v_self_1002_);
lean_dec_ref(v_self_1002_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1004_){
_start:
{
lean_object* v_lib_1005_; lean_object* v_pkg_1006_; lean_object* v_config_1007_; lean_object* v_toLeanConfig_1008_; lean_object* v_config_1009_; lean_object* v_toLeanConfig_1010_; lean_object* v_weakLeanArgs_1011_; lean_object* v_weakLeanArgs_1012_; lean_object* v___x_1013_; 
v_lib_1005_ = lean_ctor_get(v_self_1004_, 0);
lean_inc_ref(v_lib_1005_);
lean_dec_ref(v_self_1004_);
v_pkg_1006_ = lean_ctor_get(v_lib_1005_, 0);
v_config_1007_ = lean_ctor_get(v_pkg_1006_, 6);
v_toLeanConfig_1008_ = lean_ctor_get(v_config_1007_, 1);
lean_inc_ref(v_toLeanConfig_1008_);
v_config_1009_ = lean_ctor_get(v_lib_1005_, 2);
lean_inc(v_config_1009_);
lean_dec_ref(v_lib_1005_);
v_toLeanConfig_1010_ = lean_ctor_get(v_config_1009_, 0);
lean_inc_ref(v_toLeanConfig_1010_);
lean_dec(v_config_1009_);
v_weakLeanArgs_1011_ = lean_ctor_get(v_toLeanConfig_1008_, 2);
lean_inc_ref(v_weakLeanArgs_1011_);
lean_dec_ref(v_toLeanConfig_1008_);
v_weakLeanArgs_1012_ = lean_ctor_get(v_toLeanConfig_1010_, 2);
lean_inc_ref(v_weakLeanArgs_1012_);
lean_dec_ref(v_toLeanConfig_1010_);
v___x_1013_ = l_Array_append___redArg(v_weakLeanArgs_1011_, v_weakLeanArgs_1012_);
lean_dec_ref(v_weakLeanArgs_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1014_){
_start:
{
lean_object* v_lib_1015_; lean_object* v_pkg_1016_; lean_object* v_config_1017_; lean_object* v_toLeanConfig_1018_; lean_object* v_config_1019_; lean_object* v_toLeanConfig_1020_; uint8_t v_buildType_1021_; lean_object* v_moreLeancArgs_1022_; uint8_t v_buildType_1023_; lean_object* v_moreLeancArgs_1024_; uint8_t v___y_1026_; uint8_t v___x_1030_; 
v_lib_1015_ = lean_ctor_get(v_self_1014_, 0);
v_pkg_1016_ = lean_ctor_get(v_lib_1015_, 0);
v_config_1017_ = lean_ctor_get(v_pkg_1016_, 6);
v_toLeanConfig_1018_ = lean_ctor_get(v_config_1017_, 1);
v_config_1019_ = lean_ctor_get(v_lib_1015_, 2);
v_toLeanConfig_1020_ = lean_ctor_get(v_config_1019_, 0);
v_buildType_1021_ = lean_ctor_get_uint8(v_toLeanConfig_1018_, sizeof(void*)*13);
v_moreLeancArgs_1022_ = lean_ctor_get(v_toLeanConfig_1018_, 3);
v_buildType_1023_ = lean_ctor_get_uint8(v_toLeanConfig_1020_, sizeof(void*)*13);
v_moreLeancArgs_1024_ = lean_ctor_get(v_toLeanConfig_1020_, 3);
v___x_1030_ = l_Lake_instOrdBuildType_ord(v_buildType_1021_, v_buildType_1023_);
if (v___x_1030_ == 2)
{
v___y_1026_ = v_buildType_1023_;
goto v___jp_1025_;
}
else
{
v___y_1026_ = v_buildType_1021_;
goto v___jp_1025_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = l_Lake_BuildType_leancArgs(v___y_1026_);
v___x_1028_ = l_Array_append___redArg(v___x_1027_, v_moreLeancArgs_1022_);
v___x_1029_ = l_Array_append___redArg(v___x_1028_, v_moreLeancArgs_1024_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lake_Module_leancArgs(v_self_1031_);
lean_dec_ref(v_self_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1033_){
_start:
{
lean_object* v_lib_1034_; lean_object* v_pkg_1035_; lean_object* v_config_1036_; lean_object* v_toLeanConfig_1037_; lean_object* v_config_1038_; lean_object* v_toLeanConfig_1039_; lean_object* v_weakLeancArgs_1040_; lean_object* v_weakLeancArgs_1041_; lean_object* v___x_1042_; 
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
v_weakLeancArgs_1040_ = lean_ctor_get(v_toLeanConfig_1037_, 5);
lean_inc_ref(v_weakLeancArgs_1040_);
lean_dec_ref(v_toLeanConfig_1037_);
v_weakLeancArgs_1041_ = lean_ctor_get(v_toLeanConfig_1039_, 5);
lean_inc_ref(v_weakLeancArgs_1041_);
lean_dec_ref(v_toLeanConfig_1039_);
v___x_1042_ = l_Array_append___redArg(v_weakLeancArgs_1040_, v_weakLeancArgs_1041_);
lean_dec_ref(v_weakLeancArgs_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1043_){
_start:
{
lean_object* v_lib_1044_; lean_object* v_pkg_1045_; lean_object* v_config_1046_; lean_object* v_toLeanConfig_1047_; lean_object* v_config_1048_; lean_object* v_toLeanConfig_1049_; lean_object* v_moreLinkArgs_1050_; lean_object* v_moreLinkArgs_1051_; lean_object* v___x_1052_; 
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
v_moreLinkArgs_1050_ = lean_ctor_get(v_toLeanConfig_1047_, 8);
lean_inc_ref(v_moreLinkArgs_1050_);
lean_dec_ref(v_toLeanConfig_1047_);
v_moreLinkArgs_1051_ = lean_ctor_get(v_toLeanConfig_1049_, 8);
lean_inc_ref(v_moreLinkArgs_1051_);
lean_dec_ref(v_toLeanConfig_1049_);
v___x_1052_ = l_Array_append___redArg(v_moreLinkArgs_1050_, v_moreLinkArgs_1051_);
lean_dec_ref(v_moreLinkArgs_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1053_){
_start:
{
lean_object* v_lib_1054_; lean_object* v_pkg_1055_; lean_object* v_config_1056_; lean_object* v_toLeanConfig_1057_; lean_object* v_config_1058_; lean_object* v_toLeanConfig_1059_; lean_object* v_weakLinkArgs_1060_; lean_object* v_weakLinkArgs_1061_; lean_object* v___x_1062_; 
v_lib_1054_ = lean_ctor_get(v_self_1053_, 0);
lean_inc_ref(v_lib_1054_);
lean_dec_ref(v_self_1053_);
v_pkg_1055_ = lean_ctor_get(v_lib_1054_, 0);
v_config_1056_ = lean_ctor_get(v_pkg_1055_, 6);
v_toLeanConfig_1057_ = lean_ctor_get(v_config_1056_, 1);
lean_inc_ref(v_toLeanConfig_1057_);
v_config_1058_ = lean_ctor_get(v_lib_1054_, 2);
lean_inc(v_config_1058_);
lean_dec_ref(v_lib_1054_);
v_toLeanConfig_1059_ = lean_ctor_get(v_config_1058_, 0);
lean_inc_ref(v_toLeanConfig_1059_);
lean_dec(v_config_1058_);
v_weakLinkArgs_1060_ = lean_ctor_get(v_toLeanConfig_1057_, 9);
lean_inc_ref(v_weakLinkArgs_1060_);
lean_dec_ref(v_toLeanConfig_1057_);
v_weakLinkArgs_1061_ = lean_ctor_get(v_toLeanConfig_1059_, 9);
lean_inc_ref(v_weakLinkArgs_1061_);
lean_dec_ref(v_toLeanConfig_1059_);
v___x_1062_ = l_Array_append___redArg(v_weakLinkArgs_1060_, v_weakLinkArgs_1061_);
lean_dec_ref(v_weakLinkArgs_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1064_){
_start:
{
lean_object* v_lib_1065_; lean_object* v_pkg_1066_; lean_object* v_config_1067_; uint8_t v_bootstrap_1068_; 
v_lib_1065_ = lean_ctor_get(v_self_1064_, 0);
lean_inc_ref(v_lib_1065_);
lean_dec_ref(v_self_1064_);
v_pkg_1066_ = lean_ctor_get(v_lib_1065_, 0);
lean_inc_ref(v_pkg_1066_);
lean_dec_ref(v_lib_1065_);
v_config_1067_ = lean_ctor_get(v_pkg_1066_, 6);
lean_inc_ref(v_config_1067_);
v_bootstrap_1068_ = lean_ctor_get_uint8(v_config_1067_, sizeof(void*)*27);
if (v_bootstrap_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec_ref(v_config_1067_);
lean_dec_ref(v_pkg_1066_);
v___x_1069_ = lean_box(0);
return v___x_1069_;
}
else
{
lean_object* v_dir_1070_; lean_object* v_buildDir_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_dir_1070_ = lean_ctor_get(v_pkg_1066_, 4);
lean_inc_ref(v_dir_1070_);
lean_dec_ref(v_pkg_1066_);
v_buildDir_1071_ = lean_ctor_get(v_config_1067_, 6);
lean_inc_ref(v_buildDir_1071_);
lean_dec_ref(v_config_1067_);
v___x_1072_ = l_System_FilePath_normalize(v_buildDir_1071_);
v___x_1073_ = l_Lake_joinRelative(v_dir_1070_, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1075_ = l_Lake_joinRelative(v___x_1073_, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1077_){
_start:
{
lean_object* v_lib_1078_; lean_object* v_config_1079_; lean_object* v_toLeanConfig_1080_; lean_object* v_platformIndependent_1081_; 
v_lib_1078_ = lean_ctor_get(v_self_1077_, 0);
v_config_1079_ = lean_ctor_get(v_lib_1078_, 2);
v_toLeanConfig_1080_ = lean_ctor_get(v_config_1079_, 0);
v_platformIndependent_1081_ = lean_ctor_get(v_toLeanConfig_1080_, 10);
if (lean_obj_tag(v_platformIndependent_1081_) == 0)
{
lean_object* v_pkg_1082_; lean_object* v_config_1083_; lean_object* v_toLeanConfig_1084_; lean_object* v_platformIndependent_1085_; 
v_pkg_1082_ = lean_ctor_get(v_lib_1078_, 0);
v_config_1083_ = lean_ctor_get(v_pkg_1082_, 6);
v_toLeanConfig_1084_ = lean_ctor_get(v_config_1083_, 1);
v_platformIndependent_1085_ = lean_ctor_get(v_toLeanConfig_1084_, 10);
lean_inc(v_platformIndependent_1085_);
return v_platformIndependent_1085_;
}
else
{
lean_inc_ref(v_platformIndependent_1081_);
return v_platformIndependent_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lake_Module_platformIndependent(v_self_1086_);
lean_dec_ref(v_self_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1088_){
_start:
{
lean_object* v_lib_1089_; lean_object* v_pkg_1090_; lean_object* v_config_1091_; uint8_t v_precompileModules_1092_; 
v_lib_1089_ = lean_ctor_get(v_self_1088_, 0);
v_pkg_1090_ = lean_ctor_get(v_lib_1089_, 0);
v_config_1091_ = lean_ctor_get(v_pkg_1090_, 6);
v_precompileModules_1092_ = lean_ctor_get_uint8(v_config_1091_, sizeof(void*)*27 + 1);
if (v_precompileModules_1092_ == 0)
{
lean_object* v_config_1093_; uint8_t v_precompileModules_1094_; 
v_config_1093_ = lean_ctor_get(v_lib_1089_, 2);
v_precompileModules_1094_ = lean_ctor_get_uint8(v_config_1093_, sizeof(void*)*9 + 1);
return v_precompileModules_1094_;
}
else
{
return v_precompileModules_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Lake_Module_shouldPrecompile(v_self_1095_);
lean_dec_ref(v_self_1095_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1098_, uint8_t v_shouldExport_1099_){
_start:
{
lean_object* v_lib_1100_; lean_object* v_config_1101_; lean_object* v_nativeFacets_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_lib_1100_ = lean_ctor_get(v_self_1098_, 0);
lean_inc_ref(v_lib_1100_);
lean_dec_ref(v_self_1098_);
v_config_1101_ = lean_ctor_get(v_lib_1100_, 2);
lean_inc(v_config_1101_);
lean_dec_ref(v_lib_1100_);
v_nativeFacets_1102_ = lean_ctor_get(v_config_1101_, 8);
lean_inc_ref(v_nativeFacets_1102_);
lean_dec(v_config_1101_);
v___x_1103_ = lean_box(v_shouldExport_1099_);
v___x_1104_ = lean_apply_1(v_nativeFacets_1102_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1105_, lean_object* v_shouldExport_1106_){
_start:
{
uint8_t v_shouldExport_boxed_1107_; lean_object* v_res_1108_; 
v_shouldExport_boxed_1107_ = lean_unbox(v_shouldExport_1106_);
v_res_1108_ = l_Lake_Module_nativeFacets(v_self_1105_, v_shouldExport_boxed_1107_);
return v_res_1108_;
}
}
lean_object* runtime_initialize_Lake_Config_LeanLib(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Module(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
