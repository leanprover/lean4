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
v_targetDecls_236_ = lean_ctor_get(v_self_231_, 14);
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
v_srcDir_421_ = lean_ctor_get(v_config_418_, 4);
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
lean_inc_n(v_a_431_, 2);
v___f_432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_432_, 0, v_a_431_);
lean_closure_set(v___f_432_, 1, v___f_423_);
v___x_433_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
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
lean_inc_n(v_a_436_, 2);
v___f_440_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_440_, 0, v_a_436_);
lean_closure_set(v___f_440_, 1, v___f_423_);
v___x_441_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
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
v_srcDir_558_ = lean_ctor_get(v_config_555_, 4);
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
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object* v_ext_564_, lean_object* v_self_565_){
_start:
{
lean_object* v_name_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_name_566_ = lean_ctor_get(v_self_565_, 1);
v___x_567_ = l_Lean_Name_getString_x21(v_name_566_);
v___x_568_ = l_System_FilePath_addExtension(v___x_567_, v_ext_564_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object* v_ext_569_, lean_object* v_self_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lake_Module_fileName(v_ext_569_, v_self_570_);
lean_dec_ref(v_self_570_);
lean_dec_ref(v_ext_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_572_, lean_object* v_ext_573_, lean_object* v_self_574_){
_start:
{
lean_object* v_name_575_; lean_object* v___x_576_; 
v_name_575_ = lean_ctor_get(v_self_574_, 1);
lean_inc(v_name_575_);
lean_dec_ref(v_self_574_);
v___x_576_ = l_Lean_modToFilePath(v_dir_572_, v_name_575_, v_ext_573_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_577_, lean_object* v_ext_578_, lean_object* v_self_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lake_Module_filePath(v_dir_577_, v_ext_578_, v_self_579_);
lean_dec_ref(v_ext_578_);
lean_dec_ref(v_dir_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_581_, lean_object* v_self_582_){
_start:
{
lean_object* v_lib_583_; lean_object* v_pkg_584_; lean_object* v_config_585_; lean_object* v_config_586_; lean_object* v_name_587_; lean_object* v_dir_588_; lean_object* v_srcDir_589_; lean_object* v_srcDir_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_lib_583_ = lean_ctor_get(v_self_582_, 0);
v_pkg_584_ = lean_ctor_get(v_lib_583_, 0);
lean_inc_ref(v_pkg_584_);
v_config_585_ = lean_ctor_get(v_pkg_584_, 6);
lean_inc_ref(v_config_585_);
v_config_586_ = lean_ctor_get(v_lib_583_, 2);
lean_inc(v_config_586_);
v_name_587_ = lean_ctor_get(v_self_582_, 1);
lean_inc(v_name_587_);
lean_dec_ref(v_self_582_);
v_dir_588_ = lean_ctor_get(v_pkg_584_, 4);
lean_inc_ref(v_dir_588_);
lean_dec_ref(v_pkg_584_);
v_srcDir_589_ = lean_ctor_get(v_config_585_, 4);
lean_inc_ref(v_srcDir_589_);
lean_dec_ref(v_config_585_);
v_srcDir_590_ = lean_ctor_get(v_config_586_, 1);
lean_inc_ref(v_srcDir_590_);
lean_dec(v_config_586_);
v___x_591_ = l_System_FilePath_normalize(v_srcDir_589_);
v___x_592_ = l_Lake_joinRelative(v_dir_588_, v___x_591_);
v___x_593_ = l_System_FilePath_normalize(v_srcDir_590_);
v___x_594_ = l_Lake_joinRelative(v___x_592_, v___x_593_);
v___x_595_ = l_Lean_modToFilePath(v___x_594_, v_name_587_, v_ext_581_);
lean_dec_ref(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_596_, lean_object* v_self_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lake_Module_srcPath(v_ext_596_, v_self_597_);
lean_dec_ref(v_ext_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_599_){
_start:
{
lean_object* v_lib_600_; lean_object* v_pkg_601_; lean_object* v_config_602_; lean_object* v_config_603_; lean_object* v_name_604_; lean_object* v_dir_605_; lean_object* v_srcDir_606_; lean_object* v_srcDir_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_lib_600_ = lean_ctor_get(v_self_599_, 0);
v_pkg_601_ = lean_ctor_get(v_lib_600_, 0);
lean_inc_ref(v_pkg_601_);
v_config_602_ = lean_ctor_get(v_pkg_601_, 6);
lean_inc_ref(v_config_602_);
v_config_603_ = lean_ctor_get(v_lib_600_, 2);
lean_inc(v_config_603_);
v_name_604_ = lean_ctor_get(v_self_599_, 1);
lean_inc(v_name_604_);
lean_dec_ref(v_self_599_);
v_dir_605_ = lean_ctor_get(v_pkg_601_, 4);
lean_inc_ref(v_dir_605_);
lean_dec_ref(v_pkg_601_);
v_srcDir_606_ = lean_ctor_get(v_config_602_, 4);
lean_inc_ref(v_srcDir_606_);
lean_dec_ref(v_config_602_);
v_srcDir_607_ = lean_ctor_get(v_config_603_, 1);
lean_inc_ref(v_srcDir_607_);
lean_dec(v_config_603_);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_609_ = l_System_FilePath_normalize(v_srcDir_606_);
v___x_610_ = l_Lake_joinRelative(v_dir_605_, v___x_609_);
v___x_611_ = l_System_FilePath_normalize(v_srcDir_607_);
v___x_612_ = l_Lake_joinRelative(v___x_610_, v___x_611_);
v___x_613_ = l_Lean_modToFilePath(v___x_612_, v_name_604_, v___x_608_);
lean_dec_ref(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_614_){
_start:
{
lean_object* v_lib_615_; lean_object* v_pkg_616_; lean_object* v_config_617_; lean_object* v_config_618_; lean_object* v_name_619_; lean_object* v_dir_620_; lean_object* v_srcDir_621_; lean_object* v_srcDir_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_lib_615_ = lean_ctor_get(v_self_614_, 0);
v_pkg_616_ = lean_ctor_get(v_lib_615_, 0);
lean_inc_ref(v_pkg_616_);
v_config_617_ = lean_ctor_get(v_pkg_616_, 6);
lean_inc_ref(v_config_617_);
v_config_618_ = lean_ctor_get(v_lib_615_, 2);
lean_inc(v_config_618_);
v_name_619_ = lean_ctor_get(v_self_614_, 1);
lean_inc(v_name_619_);
lean_dec_ref(v_self_614_);
v_dir_620_ = lean_ctor_get(v_pkg_616_, 4);
lean_inc_ref_n(v_dir_620_, 2);
lean_dec_ref(v_pkg_616_);
v_srcDir_621_ = lean_ctor_get(v_config_617_, 4);
lean_inc_ref(v_srcDir_621_);
lean_dec_ref(v_config_617_);
v_srcDir_622_ = lean_ctor_get(v_config_618_, 1);
lean_inc_ref(v_srcDir_622_);
lean_dec(v_config_618_);
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_624_ = l_System_FilePath_normalize(v_srcDir_621_);
v___x_625_ = l_Lake_joinRelative(v_dir_620_, v___x_624_);
v___x_626_ = l_System_FilePath_normalize(v_srcDir_622_);
v___x_627_ = l_Lake_joinRelative(v___x_625_, v___x_626_);
v___x_628_ = l_Lean_modToFilePath(v___x_627_, v_name_619_, v___x_623_);
lean_dec_ref(v___x_627_);
v___x_629_ = l_Lake_relPathFrom(v_dir_620_, v___x_628_);
lean_dec_ref(v_dir_620_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_630_, lean_object* v_self_631_){
_start:
{
lean_object* v_lib_632_; lean_object* v_pkg_633_; lean_object* v_config_634_; lean_object* v_name_635_; lean_object* v_dir_636_; lean_object* v_buildDir_637_; lean_object* v_leanLibDir_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_lib_632_ = lean_ctor_get(v_self_631_, 0);
v_pkg_633_ = lean_ctor_get(v_lib_632_, 0);
lean_inc_ref(v_pkg_633_);
v_config_634_ = lean_ctor_get(v_pkg_633_, 6);
lean_inc_ref(v_config_634_);
v_name_635_ = lean_ctor_get(v_self_631_, 1);
lean_inc(v_name_635_);
lean_dec_ref(v_self_631_);
v_dir_636_ = lean_ctor_get(v_pkg_633_, 4);
lean_inc_ref(v_dir_636_);
lean_dec_ref(v_pkg_633_);
v_buildDir_637_ = lean_ctor_get(v_config_634_, 5);
lean_inc_ref(v_buildDir_637_);
v_leanLibDir_638_ = lean_ctor_get(v_config_634_, 6);
lean_inc_ref(v_leanLibDir_638_);
lean_dec_ref(v_config_634_);
v___x_639_ = l_System_FilePath_normalize(v_buildDir_637_);
v___x_640_ = l_Lake_joinRelative(v_dir_636_, v___x_639_);
v___x_641_ = l_System_FilePath_normalize(v_leanLibDir_638_);
v___x_642_ = l_Lake_joinRelative(v___x_640_, v___x_641_);
v___x_643_ = l_Lean_modToFilePath(v___x_642_, v_name_635_, v_ext_630_);
lean_dec_ref(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_644_, lean_object* v_self_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lake_Module_leanLibPath(v_ext_644_, v_self_645_);
lean_dec_ref(v_ext_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object* v_self_647_){
_start:
{
lean_object* v_lib_648_; lean_object* v_pkg_649_; lean_object* v_config_650_; lean_object* v_name_651_; lean_object* v_dir_652_; lean_object* v_buildDir_653_; lean_object* v_leanLibDir_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_lib_648_ = lean_ctor_get(v_self_647_, 0);
v_pkg_649_ = lean_ctor_get(v_lib_648_, 0);
lean_inc_ref(v_pkg_649_);
v_config_650_ = lean_ctor_get(v_pkg_649_, 6);
lean_inc_ref(v_config_650_);
v_name_651_ = lean_ctor_get(v_self_647_, 1);
lean_inc(v_name_651_);
lean_dec_ref(v_self_647_);
v_dir_652_ = lean_ctor_get(v_pkg_649_, 4);
lean_inc_ref(v_dir_652_);
lean_dec_ref(v_pkg_649_);
v_buildDir_653_ = lean_ctor_get(v_config_650_, 5);
lean_inc_ref(v_buildDir_653_);
v_leanLibDir_654_ = lean_ctor_get(v_config_650_, 6);
lean_inc_ref(v_leanLibDir_654_);
lean_dec_ref(v_config_650_);
v___x_655_ = l_System_FilePath_normalize(v_buildDir_653_);
v___x_656_ = l_Lake_joinRelative(v_dir_652_, v___x_655_);
v___x_657_ = l_System_FilePath_normalize(v_leanLibDir_654_);
v___x_658_ = l_Lake_joinRelative(v___x_656_, v___x_657_);
v___x_659_ = l_Lean_Name_getPrefix(v_name_651_);
lean_dec(v_name_651_);
v___x_660_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_661_ = l_Lean_modToFilePath(v___x_658_, v___x_659_, v___x_660_);
lean_dec_ref(v___x_658_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_663_){
_start:
{
lean_object* v_lib_664_; lean_object* v_pkg_665_; lean_object* v_config_666_; lean_object* v_name_667_; lean_object* v_dir_668_; lean_object* v_buildDir_669_; lean_object* v_leanLibDir_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_lib_664_ = lean_ctor_get(v_self_663_, 0);
v_pkg_665_ = lean_ctor_get(v_lib_664_, 0);
lean_inc_ref(v_pkg_665_);
v_config_666_ = lean_ctor_get(v_pkg_665_, 6);
lean_inc_ref(v_config_666_);
v_name_667_ = lean_ctor_get(v_self_663_, 1);
lean_inc(v_name_667_);
lean_dec_ref(v_self_663_);
v_dir_668_ = lean_ctor_get(v_pkg_665_, 4);
lean_inc_ref(v_dir_668_);
lean_dec_ref(v_pkg_665_);
v_buildDir_669_ = lean_ctor_get(v_config_666_, 5);
lean_inc_ref(v_buildDir_669_);
v_leanLibDir_670_ = lean_ctor_get(v_config_666_, 6);
lean_inc_ref(v_leanLibDir_670_);
lean_dec_ref(v_config_666_);
v___x_671_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_672_ = l_System_FilePath_normalize(v_buildDir_669_);
v___x_673_ = l_Lake_joinRelative(v_dir_668_, v___x_672_);
v___x_674_ = l_System_FilePath_normalize(v_leanLibDir_670_);
v___x_675_ = l_Lake_joinRelative(v___x_673_, v___x_674_);
v___x_676_ = l_Lean_modToFilePath(v___x_675_, v_name_667_, v___x_671_);
lean_dec_ref(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_678_){
_start:
{
lean_object* v_lib_679_; lean_object* v_pkg_680_; lean_object* v_config_681_; lean_object* v_name_682_; lean_object* v_dir_683_; lean_object* v_buildDir_684_; lean_object* v_leanLibDir_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_lib_679_ = lean_ctor_get(v_self_678_, 0);
v_pkg_680_ = lean_ctor_get(v_lib_679_, 0);
lean_inc_ref(v_pkg_680_);
v_config_681_ = lean_ctor_get(v_pkg_680_, 6);
lean_inc_ref(v_config_681_);
v_name_682_ = lean_ctor_get(v_self_678_, 1);
lean_inc(v_name_682_);
lean_dec_ref(v_self_678_);
v_dir_683_ = lean_ctor_get(v_pkg_680_, 4);
lean_inc_ref(v_dir_683_);
lean_dec_ref(v_pkg_680_);
v_buildDir_684_ = lean_ctor_get(v_config_681_, 5);
lean_inc_ref(v_buildDir_684_);
v_leanLibDir_685_ = lean_ctor_get(v_config_681_, 6);
lean_inc_ref(v_leanLibDir_685_);
lean_dec_ref(v_config_681_);
v___x_686_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_687_ = l_System_FilePath_normalize(v_buildDir_684_);
v___x_688_ = l_Lake_joinRelative(v_dir_683_, v___x_687_);
v___x_689_ = l_System_FilePath_normalize(v_leanLibDir_685_);
v___x_690_ = l_Lake_joinRelative(v___x_688_, v___x_689_);
v___x_691_ = l_Lean_modToFilePath(v___x_690_, v_name_682_, v___x_686_);
lean_dec_ref(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_693_){
_start:
{
lean_object* v_lib_694_; lean_object* v_pkg_695_; lean_object* v_config_696_; lean_object* v_name_697_; lean_object* v_dir_698_; lean_object* v_buildDir_699_; lean_object* v_leanLibDir_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_lib_694_ = lean_ctor_get(v_self_693_, 0);
v_pkg_695_ = lean_ctor_get(v_lib_694_, 0);
lean_inc_ref(v_pkg_695_);
v_config_696_ = lean_ctor_get(v_pkg_695_, 6);
lean_inc_ref(v_config_696_);
v_name_697_ = lean_ctor_get(v_self_693_, 1);
lean_inc(v_name_697_);
lean_dec_ref(v_self_693_);
v_dir_698_ = lean_ctor_get(v_pkg_695_, 4);
lean_inc_ref(v_dir_698_);
lean_dec_ref(v_pkg_695_);
v_buildDir_699_ = lean_ctor_get(v_config_696_, 5);
lean_inc_ref(v_buildDir_699_);
v_leanLibDir_700_ = lean_ctor_get(v_config_696_, 6);
lean_inc_ref(v_leanLibDir_700_);
lean_dec_ref(v_config_696_);
v___x_701_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_702_ = l_System_FilePath_normalize(v_buildDir_699_);
v___x_703_ = l_Lake_joinRelative(v_dir_698_, v___x_702_);
v___x_704_ = l_System_FilePath_normalize(v_leanLibDir_700_);
v___x_705_ = l_Lake_joinRelative(v___x_703_, v___x_704_);
v___x_706_ = l_Lean_modToFilePath(v___x_705_, v_name_697_, v___x_701_);
lean_dec_ref(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_708_){
_start:
{
lean_object* v_lib_709_; lean_object* v_pkg_710_; lean_object* v_config_711_; lean_object* v_name_712_; lean_object* v_dir_713_; lean_object* v_buildDir_714_; lean_object* v_leanLibDir_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_lib_709_ = lean_ctor_get(v_self_708_, 0);
v_pkg_710_ = lean_ctor_get(v_lib_709_, 0);
lean_inc_ref(v_pkg_710_);
v_config_711_ = lean_ctor_get(v_pkg_710_, 6);
lean_inc_ref(v_config_711_);
v_name_712_ = lean_ctor_get(v_self_708_, 1);
lean_inc(v_name_712_);
lean_dec_ref(v_self_708_);
v_dir_713_ = lean_ctor_get(v_pkg_710_, 4);
lean_inc_ref(v_dir_713_);
lean_dec_ref(v_pkg_710_);
v_buildDir_714_ = lean_ctor_get(v_config_711_, 5);
lean_inc_ref(v_buildDir_714_);
v_leanLibDir_715_ = lean_ctor_get(v_config_711_, 6);
lean_inc_ref(v_leanLibDir_715_);
lean_dec_ref(v_config_711_);
v___x_716_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_717_ = l_System_FilePath_normalize(v_buildDir_714_);
v___x_718_ = l_Lake_joinRelative(v_dir_713_, v___x_717_);
v___x_719_ = l_System_FilePath_normalize(v_leanLibDir_715_);
v___x_720_ = l_Lake_joinRelative(v___x_718_, v___x_719_);
v___x_721_ = l_Lean_modToFilePath(v___x_720_, v_name_712_, v___x_716_);
lean_dec_ref(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_723_){
_start:
{
lean_object* v_lib_724_; lean_object* v_pkg_725_; lean_object* v_config_726_; lean_object* v_name_727_; lean_object* v_dir_728_; lean_object* v_buildDir_729_; lean_object* v_leanLibDir_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_lib_724_ = lean_ctor_get(v_self_723_, 0);
v_pkg_725_ = lean_ctor_get(v_lib_724_, 0);
lean_inc_ref(v_pkg_725_);
v_config_726_ = lean_ctor_get(v_pkg_725_, 6);
lean_inc_ref(v_config_726_);
v_name_727_ = lean_ctor_get(v_self_723_, 1);
lean_inc(v_name_727_);
lean_dec_ref(v_self_723_);
v_dir_728_ = lean_ctor_get(v_pkg_725_, 4);
lean_inc_ref(v_dir_728_);
lean_dec_ref(v_pkg_725_);
v_buildDir_729_ = lean_ctor_get(v_config_726_, 5);
lean_inc_ref(v_buildDir_729_);
v_leanLibDir_730_ = lean_ctor_get(v_config_726_, 6);
lean_inc_ref(v_leanLibDir_730_);
lean_dec_ref(v_config_726_);
v___x_731_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_732_ = l_System_FilePath_normalize(v_buildDir_729_);
v___x_733_ = l_Lake_joinRelative(v_dir_728_, v___x_732_);
v___x_734_ = l_System_FilePath_normalize(v_leanLibDir_730_);
v___x_735_ = l_Lake_joinRelative(v___x_733_, v___x_734_);
v___x_736_ = l_Lean_modToFilePath(v___x_735_, v_name_727_, v___x_731_);
lean_dec_ref(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_738_){
_start:
{
lean_object* v_lib_739_; lean_object* v_pkg_740_; lean_object* v_config_741_; lean_object* v_name_742_; lean_object* v_dir_743_; lean_object* v_buildDir_744_; lean_object* v_leanLibDir_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_lib_739_ = lean_ctor_get(v_self_738_, 0);
v_pkg_740_ = lean_ctor_get(v_lib_739_, 0);
lean_inc_ref(v_pkg_740_);
v_config_741_ = lean_ctor_get(v_pkg_740_, 6);
lean_inc_ref(v_config_741_);
v_name_742_ = lean_ctor_get(v_self_738_, 1);
lean_inc(v_name_742_);
lean_dec_ref(v_self_738_);
v_dir_743_ = lean_ctor_get(v_pkg_740_, 4);
lean_inc_ref(v_dir_743_);
lean_dec_ref(v_pkg_740_);
v_buildDir_744_ = lean_ctor_get(v_config_741_, 5);
lean_inc_ref(v_buildDir_744_);
v_leanLibDir_745_ = lean_ctor_get(v_config_741_, 6);
lean_inc_ref(v_leanLibDir_745_);
lean_dec_ref(v_config_741_);
v___x_746_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_747_ = l_System_FilePath_normalize(v_buildDir_744_);
v___x_748_ = l_Lake_joinRelative(v_dir_743_, v___x_747_);
v___x_749_ = l_System_FilePath_normalize(v_leanLibDir_745_);
v___x_750_ = l_Lake_joinRelative(v___x_748_, v___x_749_);
v___x_751_ = l_Lean_modToFilePath(v___x_750_, v_name_742_, v___x_746_);
lean_dec_ref(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_752_, lean_object* v_self_753_){
_start:
{
lean_object* v_lib_754_; lean_object* v_pkg_755_; lean_object* v_config_756_; lean_object* v_name_757_; lean_object* v_dir_758_; lean_object* v_buildDir_759_; lean_object* v_irDir_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_lib_754_ = lean_ctor_get(v_self_753_, 0);
v_pkg_755_ = lean_ctor_get(v_lib_754_, 0);
lean_inc_ref(v_pkg_755_);
v_config_756_ = lean_ctor_get(v_pkg_755_, 6);
lean_inc_ref(v_config_756_);
v_name_757_ = lean_ctor_get(v_self_753_, 1);
lean_inc(v_name_757_);
lean_dec_ref(v_self_753_);
v_dir_758_ = lean_ctor_get(v_pkg_755_, 4);
lean_inc_ref(v_dir_758_);
lean_dec_ref(v_pkg_755_);
v_buildDir_759_ = lean_ctor_get(v_config_756_, 5);
lean_inc_ref(v_buildDir_759_);
v_irDir_760_ = lean_ctor_get(v_config_756_, 9);
lean_inc_ref(v_irDir_760_);
lean_dec_ref(v_config_756_);
v___x_761_ = l_System_FilePath_normalize(v_buildDir_759_);
v___x_762_ = l_Lake_joinRelative(v_dir_758_, v___x_761_);
v___x_763_ = l_System_FilePath_normalize(v_irDir_760_);
v___x_764_ = l_Lake_joinRelative(v___x_762_, v___x_763_);
v___x_765_ = l_Lean_modToFilePath(v___x_764_, v_name_757_, v_ext_752_);
lean_dec_ref(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_766_, lean_object* v_self_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lake_Module_irPath(v_ext_766_, v_self_767_);
lean_dec_ref(v_ext_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_769_){
_start:
{
lean_object* v_lib_770_; lean_object* v_pkg_771_; lean_object* v_config_772_; lean_object* v_name_773_; lean_object* v_dir_774_; lean_object* v_buildDir_775_; lean_object* v_irDir_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_lib_770_ = lean_ctor_get(v_self_769_, 0);
v_pkg_771_ = lean_ctor_get(v_lib_770_, 0);
lean_inc_ref(v_pkg_771_);
v_config_772_ = lean_ctor_get(v_pkg_771_, 6);
lean_inc_ref(v_config_772_);
v_name_773_ = lean_ctor_get(v_self_769_, 1);
lean_inc(v_name_773_);
lean_dec_ref(v_self_769_);
v_dir_774_ = lean_ctor_get(v_pkg_771_, 4);
lean_inc_ref(v_dir_774_);
lean_dec_ref(v_pkg_771_);
v_buildDir_775_ = lean_ctor_get(v_config_772_, 5);
lean_inc_ref(v_buildDir_775_);
v_irDir_776_ = lean_ctor_get(v_config_772_, 9);
lean_inc_ref(v_irDir_776_);
lean_dec_ref(v_config_772_);
v___x_777_ = l_System_FilePath_normalize(v_buildDir_775_);
v___x_778_ = l_Lake_joinRelative(v_dir_774_, v___x_777_);
v___x_779_ = l_System_FilePath_normalize(v_irDir_776_);
v___x_780_ = l_Lake_joinRelative(v___x_778_, v___x_779_);
v___x_781_ = l_Lean_Name_getPrefix(v_name_773_);
lean_dec(v_name_773_);
v___x_782_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_783_ = l_Lean_modToFilePath(v___x_780_, v___x_781_, v___x_782_);
lean_dec_ref(v___x_780_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_785_){
_start:
{
lean_object* v_lib_786_; lean_object* v_pkg_787_; lean_object* v_config_788_; lean_object* v_name_789_; lean_object* v_dir_790_; lean_object* v_buildDir_791_; lean_object* v_irDir_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_lib_786_ = lean_ctor_get(v_self_785_, 0);
v_pkg_787_ = lean_ctor_get(v_lib_786_, 0);
lean_inc_ref(v_pkg_787_);
v_config_788_ = lean_ctor_get(v_pkg_787_, 6);
lean_inc_ref(v_config_788_);
v_name_789_ = lean_ctor_get(v_self_785_, 1);
lean_inc(v_name_789_);
lean_dec_ref(v_self_785_);
v_dir_790_ = lean_ctor_get(v_pkg_787_, 4);
lean_inc_ref(v_dir_790_);
lean_dec_ref(v_pkg_787_);
v_buildDir_791_ = lean_ctor_get(v_config_788_, 5);
lean_inc_ref(v_buildDir_791_);
v_irDir_792_ = lean_ctor_get(v_config_788_, 9);
lean_inc_ref(v_irDir_792_);
lean_dec_ref(v_config_788_);
v___x_793_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_794_ = l_System_FilePath_normalize(v_buildDir_791_);
v___x_795_ = l_Lake_joinRelative(v_dir_790_, v___x_794_);
v___x_796_ = l_System_FilePath_normalize(v_irDir_792_);
v___x_797_ = l_Lake_joinRelative(v___x_795_, v___x_796_);
v___x_798_ = l_Lean_modToFilePath(v___x_797_, v_name_789_, v___x_793_);
lean_dec_ref(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_800_){
_start:
{
lean_object* v_lib_801_; lean_object* v_pkg_802_; lean_object* v_config_803_; lean_object* v_name_804_; lean_object* v_dir_805_; lean_object* v_buildDir_806_; lean_object* v_irDir_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_lib_801_ = lean_ctor_get(v_self_800_, 0);
v_pkg_802_ = lean_ctor_get(v_lib_801_, 0);
lean_inc_ref(v_pkg_802_);
v_config_803_ = lean_ctor_get(v_pkg_802_, 6);
lean_inc_ref(v_config_803_);
v_name_804_ = lean_ctor_get(v_self_800_, 1);
lean_inc(v_name_804_);
lean_dec_ref(v_self_800_);
v_dir_805_ = lean_ctor_get(v_pkg_802_, 4);
lean_inc_ref(v_dir_805_);
lean_dec_ref(v_pkg_802_);
v_buildDir_806_ = lean_ctor_get(v_config_803_, 5);
lean_inc_ref(v_buildDir_806_);
v_irDir_807_ = lean_ctor_get(v_config_803_, 9);
lean_inc_ref(v_irDir_807_);
lean_dec_ref(v_config_803_);
v___x_808_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_809_ = l_System_FilePath_normalize(v_buildDir_806_);
v___x_810_ = l_Lake_joinRelative(v_dir_805_, v___x_809_);
v___x_811_ = l_System_FilePath_normalize(v_irDir_807_);
v___x_812_ = l_Lake_joinRelative(v___x_810_, v___x_811_);
v___x_813_ = l_Lean_modToFilePath(v___x_812_, v_name_804_, v___x_808_);
lean_dec_ref(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_815_){
_start:
{
lean_object* v_lib_816_; lean_object* v_pkg_817_; lean_object* v_config_818_; lean_object* v_name_819_; lean_object* v_dir_820_; lean_object* v_buildDir_821_; lean_object* v_irDir_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_lib_816_ = lean_ctor_get(v_self_815_, 0);
v_pkg_817_ = lean_ctor_get(v_lib_816_, 0);
lean_inc_ref(v_pkg_817_);
v_config_818_ = lean_ctor_get(v_pkg_817_, 6);
lean_inc_ref(v_config_818_);
v_name_819_ = lean_ctor_get(v_self_815_, 1);
lean_inc(v_name_819_);
lean_dec_ref(v_self_815_);
v_dir_820_ = lean_ctor_get(v_pkg_817_, 4);
lean_inc_ref(v_dir_820_);
lean_dec_ref(v_pkg_817_);
v_buildDir_821_ = lean_ctor_get(v_config_818_, 5);
lean_inc_ref(v_buildDir_821_);
v_irDir_822_ = lean_ctor_get(v_config_818_, 9);
lean_inc_ref(v_irDir_822_);
lean_dec_ref(v_config_818_);
v___x_823_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_824_ = l_System_FilePath_normalize(v_buildDir_821_);
v___x_825_ = l_Lake_joinRelative(v_dir_820_, v___x_824_);
v___x_826_ = l_System_FilePath_normalize(v_irDir_822_);
v___x_827_ = l_Lake_joinRelative(v___x_825_, v___x_826_);
v___x_828_ = l_Lean_modToFilePath(v___x_827_, v_name_819_, v___x_823_);
lean_dec_ref(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_830_){
_start:
{
lean_object* v_lib_831_; lean_object* v_pkg_832_; lean_object* v_config_833_; lean_object* v_name_834_; lean_object* v_dir_835_; lean_object* v_buildDir_836_; lean_object* v_irDir_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_lib_831_ = lean_ctor_get(v_self_830_, 0);
v_pkg_832_ = lean_ctor_get(v_lib_831_, 0);
lean_inc_ref(v_pkg_832_);
v_config_833_ = lean_ctor_get(v_pkg_832_, 6);
lean_inc_ref(v_config_833_);
v_name_834_ = lean_ctor_get(v_self_830_, 1);
lean_inc(v_name_834_);
lean_dec_ref(v_self_830_);
v_dir_835_ = lean_ctor_get(v_pkg_832_, 4);
lean_inc_ref(v_dir_835_);
lean_dec_ref(v_pkg_832_);
v_buildDir_836_ = lean_ctor_get(v_config_833_, 5);
lean_inc_ref(v_buildDir_836_);
v_irDir_837_ = lean_ctor_get(v_config_833_, 9);
lean_inc_ref(v_irDir_837_);
lean_dec_ref(v_config_833_);
v___x_838_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_839_ = l_System_FilePath_normalize(v_buildDir_836_);
v___x_840_ = l_Lake_joinRelative(v_dir_835_, v___x_839_);
v___x_841_ = l_System_FilePath_normalize(v_irDir_837_);
v___x_842_ = l_Lake_joinRelative(v___x_840_, v___x_841_);
v___x_843_ = l_Lean_modToFilePath(v___x_842_, v_name_834_, v___x_838_);
lean_dec_ref(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_845_){
_start:
{
lean_object* v_lib_846_; lean_object* v_pkg_847_; lean_object* v_config_848_; lean_object* v_name_849_; lean_object* v_dir_850_; lean_object* v_buildDir_851_; lean_object* v_irDir_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_lib_846_ = lean_ctor_get(v_self_845_, 0);
v_pkg_847_ = lean_ctor_get(v_lib_846_, 0);
lean_inc_ref(v_pkg_847_);
v_config_848_ = lean_ctor_get(v_pkg_847_, 6);
lean_inc_ref(v_config_848_);
v_name_849_ = lean_ctor_get(v_self_845_, 1);
lean_inc(v_name_849_);
lean_dec_ref(v_self_845_);
v_dir_850_ = lean_ctor_get(v_pkg_847_, 4);
lean_inc_ref(v_dir_850_);
lean_dec_ref(v_pkg_847_);
v_buildDir_851_ = lean_ctor_get(v_config_848_, 5);
lean_inc_ref(v_buildDir_851_);
v_irDir_852_ = lean_ctor_get(v_config_848_, 9);
lean_inc_ref(v_irDir_852_);
lean_dec_ref(v_config_848_);
v___x_853_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_854_ = l_System_FilePath_normalize(v_buildDir_851_);
v___x_855_ = l_Lake_joinRelative(v_dir_850_, v___x_854_);
v___x_856_ = l_System_FilePath_normalize(v_irDir_852_);
v___x_857_ = l_Lake_joinRelative(v___x_855_, v___x_856_);
v___x_858_ = l_Lean_modToFilePath(v___x_857_, v_name_849_, v___x_853_);
lean_dec_ref(v___x_857_);
return v___x_858_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_box(0);
v___x_860_ = lean_internal_has_llvm_backend(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_self_861_);
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_lib_864_; lean_object* v_pkg_865_; lean_object* v_config_866_; lean_object* v_name_867_; lean_object* v_dir_868_; lean_object* v_buildDir_869_; lean_object* v_irDir_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_lib_864_ = lean_ctor_get(v_self_861_, 0);
v_pkg_865_ = lean_ctor_get(v_lib_864_, 0);
lean_inc_ref(v_pkg_865_);
v_config_866_ = lean_ctor_get(v_pkg_865_, 6);
lean_inc_ref(v_config_866_);
v_name_867_ = lean_ctor_get(v_self_861_, 1);
lean_inc(v_name_867_);
lean_dec_ref(v_self_861_);
v_dir_868_ = lean_ctor_get(v_pkg_865_, 4);
lean_inc_ref(v_dir_868_);
lean_dec_ref(v_pkg_865_);
v_buildDir_869_ = lean_ctor_get(v_config_866_, 5);
lean_inc_ref(v_buildDir_869_);
v_irDir_870_ = lean_ctor_get(v_config_866_, 9);
lean_inc_ref(v_irDir_870_);
lean_dec_ref(v_config_866_);
v___x_871_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_872_ = l_System_FilePath_normalize(v_buildDir_869_);
v___x_873_ = l_Lake_joinRelative(v_dir_868_, v___x_872_);
v___x_874_ = l_System_FilePath_normalize(v_irDir_870_);
v___x_875_ = l_Lake_joinRelative(v___x_873_, v___x_874_);
v___x_876_ = l_Lean_modToFilePath(v___x_875_, v_name_867_, v___x_871_);
lean_dec_ref(v___x_875_);
v___x_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_879_){
_start:
{
lean_object* v_lib_880_; lean_object* v_pkg_881_; lean_object* v_config_882_; lean_object* v_name_883_; lean_object* v_dir_884_; lean_object* v_buildDir_885_; lean_object* v_irDir_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_lib_880_ = lean_ctor_get(v_self_879_, 0);
v_pkg_881_ = lean_ctor_get(v_lib_880_, 0);
lean_inc_ref(v_pkg_881_);
v_config_882_ = lean_ctor_get(v_pkg_881_, 6);
lean_inc_ref(v_config_882_);
v_name_883_ = lean_ctor_get(v_self_879_, 1);
lean_inc(v_name_883_);
lean_dec_ref(v_self_879_);
v_dir_884_ = lean_ctor_get(v_pkg_881_, 4);
lean_inc_ref(v_dir_884_);
lean_dec_ref(v_pkg_881_);
v_buildDir_885_ = lean_ctor_get(v_config_882_, 5);
lean_inc_ref(v_buildDir_885_);
v_irDir_886_ = lean_ctor_get(v_config_882_, 9);
lean_inc_ref(v_irDir_886_);
lean_dec_ref(v_config_882_);
v___x_887_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_888_ = l_System_FilePath_normalize(v_buildDir_885_);
v___x_889_ = l_Lake_joinRelative(v_dir_884_, v___x_888_);
v___x_890_ = l_System_FilePath_normalize(v_irDir_886_);
v___x_891_ = l_Lake_joinRelative(v___x_889_, v___x_890_);
v___x_892_ = l_Lean_modToFilePath(v___x_891_, v_name_883_, v___x_887_);
lean_dec_ref(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_894_){
_start:
{
lean_object* v_lib_895_; lean_object* v_pkg_896_; lean_object* v_config_897_; lean_object* v_name_898_; lean_object* v_dir_899_; lean_object* v_buildDir_900_; lean_object* v_irDir_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_lib_895_ = lean_ctor_get(v_self_894_, 0);
v_pkg_896_ = lean_ctor_get(v_lib_895_, 0);
lean_inc_ref(v_pkg_896_);
v_config_897_ = lean_ctor_get(v_pkg_896_, 6);
lean_inc_ref(v_config_897_);
v_name_898_ = lean_ctor_get(v_self_894_, 1);
lean_inc(v_name_898_);
lean_dec_ref(v_self_894_);
v_dir_899_ = lean_ctor_get(v_pkg_896_, 4);
lean_inc_ref(v_dir_899_);
lean_dec_ref(v_pkg_896_);
v_buildDir_900_ = lean_ctor_get(v_config_897_, 5);
lean_inc_ref(v_buildDir_900_);
v_irDir_901_ = lean_ctor_get(v_config_897_, 9);
lean_inc_ref(v_irDir_901_);
lean_dec_ref(v_config_897_);
v___x_902_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_903_ = l_System_FilePath_normalize(v_buildDir_900_);
v___x_904_ = l_Lake_joinRelative(v_dir_899_, v___x_903_);
v___x_905_ = l_System_FilePath_normalize(v_irDir_901_);
v___x_906_ = l_Lake_joinRelative(v___x_904_, v___x_905_);
v___x_907_ = l_Lean_modToFilePath(v___x_906_, v_name_898_, v___x_902_);
lean_dec_ref(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_910_){
_start:
{
lean_object* v_lib_911_; lean_object* v_name_912_; lean_object* v_pkg_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_lib_911_ = lean_ctor_get(v_self_910_, 0);
lean_inc_ref(v_lib_911_);
v_name_912_ = lean_ctor_get(v_self_910_, 1);
lean_inc(v_name_912_);
lean_dec_ref(v_self_910_);
v_pkg_913_ = lean_ctor_get(v_lib_911_, 0);
lean_inc_ref(v_pkg_913_);
lean_dec_ref(v_lib_911_);
v___x_914_ = l_Lake_Package_id_x3f(v_pkg_913_);
v___x_915_ = l_Lean_mkModuleInitializationStem(v_name_912_, v___x_914_);
lean_dec(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_917_){
_start:
{
lean_object* v_lib_918_; lean_object* v_pkg_919_; lean_object* v_config_920_; lean_object* v_name_921_; lean_object* v_dir_922_; lean_object* v_buildDir_923_; lean_object* v_leanLibDir_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_lib_918_ = lean_ctor_get(v_self_917_, 0);
v_pkg_919_ = lean_ctor_get(v_lib_918_, 0);
lean_inc_ref(v_pkg_919_);
v_config_920_ = lean_ctor_get(v_pkg_919_, 6);
v_name_921_ = lean_ctor_get(v_self_917_, 1);
lean_inc(v_name_921_);
lean_dec_ref(v_self_917_);
v_dir_922_ = lean_ctor_get(v_pkg_919_, 4);
v_buildDir_923_ = lean_ctor_get(v_config_920_, 5);
v_leanLibDir_924_ = lean_ctor_get(v_config_920_, 6);
lean_inc_ref(v_buildDir_923_);
v___x_925_ = l_System_FilePath_normalize(v_buildDir_923_);
lean_inc_ref(v_dir_922_);
v___x_926_ = l_Lake_joinRelative(v_dir_922_, v___x_925_);
lean_inc_ref(v_leanLibDir_924_);
v___x_927_ = l_System_FilePath_normalize(v_leanLibDir_924_);
v___x_928_ = l_Lake_joinRelative(v___x_926_, v___x_927_);
v___x_929_ = l_Lake_Package_id_x3f(v_pkg_919_);
v___x_930_ = l_Lean_mkModuleInitializationStem(v_name_921_, v___x_929_);
lean_dec(v___x_929_);
v___x_931_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = l_Lake_sharedLibExt;
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
v___x_935_ = l_Lake_joinRelative(v___x_928_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_936_){
_start:
{
lean_object* v_lib_937_; lean_object* v_pkg_938_; lean_object* v_config_939_; lean_object* v_toLeanConfig_940_; lean_object* v_config_941_; lean_object* v_toLeanConfig_942_; uint8_t v_buildType_943_; lean_object* v_leanOptions_944_; lean_object* v_moreServerOptions_945_; uint8_t v_buildType_946_; lean_object* v_leanOptions_947_; lean_object* v_moreServerOptions_948_; lean_object* v___x_949_; uint8_t v___y_951_; uint8_t v___x_959_; 
v_lib_937_ = lean_ctor_get(v_self_936_, 0);
v_pkg_938_ = lean_ctor_get(v_lib_937_, 0);
v_config_939_ = lean_ctor_get(v_pkg_938_, 6);
v_toLeanConfig_940_ = lean_ctor_get(v_config_939_, 1);
v_config_941_ = lean_ctor_get(v_lib_937_, 2);
v_toLeanConfig_942_ = lean_ctor_get(v_config_941_, 0);
v_buildType_943_ = lean_ctor_get_uint8(v_toLeanConfig_940_, sizeof(void*)*13);
v_leanOptions_944_ = lean_ctor_get(v_toLeanConfig_940_, 0);
v_moreServerOptions_945_ = lean_ctor_get(v_toLeanConfig_940_, 4);
v_buildType_946_ = lean_ctor_get_uint8(v_toLeanConfig_942_, sizeof(void*)*13);
v_leanOptions_947_ = lean_ctor_get(v_toLeanConfig_942_, 0);
v_moreServerOptions_948_ = lean_ctor_get(v_toLeanConfig_942_, 4);
v___x_949_ = lean_box(1);
v___x_959_ = l_Lake_instOrdBuildType_ord(v_buildType_943_, v_buildType_946_);
if (v___x_959_ == 2)
{
v___y_951_ = v_buildType_946_;
goto v___jp_950_;
}
else
{
v___y_951_ = v_buildType_943_;
goto v___jp_950_;
}
v___jp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_952_ = l_Lake_BuildType_leanOptions(v___y_951_);
v___x_953_ = l_Lean_LeanOptions_append(v___x_949_, v___x_952_);
v___x_954_ = l_Lean_LeanOptions_ofArray(v_leanOptions_944_);
v___x_955_ = l_Lean_LeanOptions_appendArray(v___x_954_, v_moreServerOptions_945_);
v___x_956_ = l_Lean_LeanOptions_append(v___x_953_, v___x_955_);
v___x_957_ = l_Lean_LeanOptions_appendArray(v___x_956_, v_leanOptions_947_);
v___x_958_ = l_Lean_LeanOptions_appendArray(v___x_957_, v_moreServerOptions_948_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lake_Module_serverOptions(v_self_960_);
lean_dec_ref(v_self_960_);
return v_res_961_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_962_){
_start:
{
lean_object* v_lib_963_; lean_object* v_pkg_964_; lean_object* v_config_965_; lean_object* v_toLeanConfig_966_; lean_object* v_config_967_; lean_object* v_toLeanConfig_968_; uint8_t v_buildType_969_; uint8_t v_buildType_970_; uint8_t v___x_971_; 
v_lib_963_ = lean_ctor_get(v_self_962_, 0);
v_pkg_964_ = lean_ctor_get(v_lib_963_, 0);
v_config_965_ = lean_ctor_get(v_pkg_964_, 6);
v_toLeanConfig_966_ = lean_ctor_get(v_config_965_, 1);
v_config_967_ = lean_ctor_get(v_lib_963_, 2);
v_toLeanConfig_968_ = lean_ctor_get(v_config_967_, 0);
v_buildType_969_ = lean_ctor_get_uint8(v_toLeanConfig_966_, sizeof(void*)*13);
v_buildType_970_ = lean_ctor_get_uint8(v_toLeanConfig_968_, sizeof(void*)*13);
v___x_971_ = l_Lake_instOrdBuildType_ord(v_buildType_969_, v_buildType_970_);
if (v___x_971_ == 2)
{
return v_buildType_970_;
}
else
{
return v_buildType_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_972_){
_start:
{
uint8_t v_res_973_; lean_object* v_r_974_; 
v_res_973_ = l_Lake_Module_buildType(v_self_972_);
lean_dec_ref(v_self_972_);
v_r_974_ = lean_box(v_res_973_);
return v_r_974_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_975_){
_start:
{
lean_object* v_lib_976_; lean_object* v_config_977_; lean_object* v_toLeanConfig_978_; lean_object* v_pkg_979_; lean_object* v_config_980_; lean_object* v_toLeanConfig_981_; uint8_t v_backend_982_; uint8_t v_backend_983_; uint8_t v___x_984_; 
v_lib_976_ = lean_ctor_get(v_self_975_, 0);
v_config_977_ = lean_ctor_get(v_lib_976_, 2);
v_toLeanConfig_978_ = lean_ctor_get(v_config_977_, 0);
v_pkg_979_ = lean_ctor_get(v_lib_976_, 0);
v_config_980_ = lean_ctor_get(v_pkg_979_, 6);
v_toLeanConfig_981_ = lean_ctor_get(v_config_980_, 1);
v_backend_982_ = lean_ctor_get_uint8(v_toLeanConfig_978_, sizeof(void*)*13 + 1);
v_backend_983_ = lean_ctor_get_uint8(v_toLeanConfig_981_, sizeof(void*)*13 + 1);
v___x_984_ = l_Lake_Backend_orPreferLeft(v_backend_982_, v_backend_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_985_){
_start:
{
uint8_t v_res_986_; lean_object* v_r_987_; 
v_res_986_ = l_Lake_Module_backend(v_self_985_);
lean_dec_ref(v_self_985_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_988_){
_start:
{
lean_object* v_lib_989_; lean_object* v_config_990_; uint8_t v_allowImportAll_991_; 
v_lib_989_ = lean_ctor_get(v_self_988_, 0);
v_config_990_ = lean_ctor_get(v_lib_989_, 2);
v_allowImportAll_991_ = lean_ctor_get_uint8(v_config_990_, sizeof(void*)*9 + 2);
if (v_allowImportAll_991_ == 0)
{
lean_object* v_pkg_992_; lean_object* v_config_993_; uint8_t v_allowImportAll_994_; 
v_pkg_992_ = lean_ctor_get(v_lib_989_, 0);
v_config_993_ = lean_ctor_get(v_pkg_992_, 6);
v_allowImportAll_994_ = lean_ctor_get_uint8(v_config_993_, sizeof(void*)*27 + 5);
return v_allowImportAll_994_;
}
else
{
return v_allowImportAll_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Lake_Module_allowImportAll(v_self_995_);
lean_dec_ref(v_self_995_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_998_){
_start:
{
lean_object* v_lib_999_; lean_object* v_pkg_1000_; lean_object* v_config_1001_; lean_object* v_toLeanConfig_1002_; lean_object* v_config_1003_; lean_object* v_toLeanConfig_1004_; lean_object* v_dynlibs_1005_; lean_object* v_dynlibs_1006_; lean_object* v___x_1007_; 
v_lib_999_ = lean_ctor_get(v_self_998_, 0);
lean_inc_ref(v_lib_999_);
lean_dec_ref(v_self_998_);
v_pkg_1000_ = lean_ctor_get(v_lib_999_, 0);
v_config_1001_ = lean_ctor_get(v_pkg_1000_, 6);
v_toLeanConfig_1002_ = lean_ctor_get(v_config_1001_, 1);
lean_inc_ref(v_toLeanConfig_1002_);
v_config_1003_ = lean_ctor_get(v_lib_999_, 2);
lean_inc(v_config_1003_);
lean_dec_ref(v_lib_999_);
v_toLeanConfig_1004_ = lean_ctor_get(v_config_1003_, 0);
lean_inc_ref(v_toLeanConfig_1004_);
lean_dec(v_config_1003_);
v_dynlibs_1005_ = lean_ctor_get(v_toLeanConfig_1002_, 11);
lean_inc_ref(v_dynlibs_1005_);
lean_dec_ref(v_toLeanConfig_1002_);
v_dynlibs_1006_ = lean_ctor_get(v_toLeanConfig_1004_, 11);
lean_inc_ref(v_dynlibs_1006_);
lean_dec_ref(v_toLeanConfig_1004_);
v___x_1007_ = l_Array_append___redArg(v_dynlibs_1005_, v_dynlibs_1006_);
lean_dec_ref(v_dynlibs_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1008_){
_start:
{
lean_object* v_lib_1009_; lean_object* v_pkg_1010_; lean_object* v_config_1011_; lean_object* v_toLeanConfig_1012_; lean_object* v_config_1013_; lean_object* v_toLeanConfig_1014_; lean_object* v_plugins_1015_; lean_object* v_plugins_1016_; lean_object* v___x_1017_; 
v_lib_1009_ = lean_ctor_get(v_self_1008_, 0);
lean_inc_ref(v_lib_1009_);
lean_dec_ref(v_self_1008_);
v_pkg_1010_ = lean_ctor_get(v_lib_1009_, 0);
v_config_1011_ = lean_ctor_get(v_pkg_1010_, 6);
v_toLeanConfig_1012_ = lean_ctor_get(v_config_1011_, 1);
lean_inc_ref(v_toLeanConfig_1012_);
v_config_1013_ = lean_ctor_get(v_lib_1009_, 2);
lean_inc(v_config_1013_);
lean_dec_ref(v_lib_1009_);
v_toLeanConfig_1014_ = lean_ctor_get(v_config_1013_, 0);
lean_inc_ref(v_toLeanConfig_1014_);
lean_dec(v_config_1013_);
v_plugins_1015_ = lean_ctor_get(v_toLeanConfig_1012_, 12);
lean_inc_ref(v_plugins_1015_);
lean_dec_ref(v_toLeanConfig_1012_);
v_plugins_1016_ = lean_ctor_get(v_toLeanConfig_1014_, 12);
lean_inc_ref(v_plugins_1016_);
lean_dec_ref(v_toLeanConfig_1014_);
v___x_1017_ = l_Array_append___redArg(v_plugins_1015_, v_plugins_1016_);
lean_dec_ref(v_plugins_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1018_){
_start:
{
lean_object* v_lib_1019_; lean_object* v_pkg_1020_; lean_object* v_config_1021_; lean_object* v_toLeanConfig_1022_; lean_object* v_config_1023_; lean_object* v_toLeanConfig_1024_; uint8_t v_buildType_1025_; lean_object* v_leanOptions_1026_; uint8_t v_buildType_1027_; lean_object* v_leanOptions_1028_; uint8_t v___y_1030_; uint8_t v___x_1035_; 
v_lib_1019_ = lean_ctor_get(v_self_1018_, 0);
v_pkg_1020_ = lean_ctor_get(v_lib_1019_, 0);
v_config_1021_ = lean_ctor_get(v_pkg_1020_, 6);
v_toLeanConfig_1022_ = lean_ctor_get(v_config_1021_, 1);
v_config_1023_ = lean_ctor_get(v_lib_1019_, 2);
v_toLeanConfig_1024_ = lean_ctor_get(v_config_1023_, 0);
v_buildType_1025_ = lean_ctor_get_uint8(v_toLeanConfig_1022_, sizeof(void*)*13);
v_leanOptions_1026_ = lean_ctor_get(v_toLeanConfig_1022_, 0);
v_buildType_1027_ = lean_ctor_get_uint8(v_toLeanConfig_1024_, sizeof(void*)*13);
v_leanOptions_1028_ = lean_ctor_get(v_toLeanConfig_1024_, 0);
v___x_1035_ = l_Lake_instOrdBuildType_ord(v_buildType_1025_, v_buildType_1027_);
if (v___x_1035_ == 2)
{
v___y_1030_ = v_buildType_1027_;
goto v___jp_1029_;
}
else
{
v___y_1030_ = v_buildType_1025_;
goto v___jp_1029_;
}
v___jp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = l_Lake_BuildType_leanOptions(v___y_1030_);
v___x_1032_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1026_);
v___x_1033_ = l_Lean_LeanOptions_append(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Lean_LeanOptions_appendArray(v___x_1033_, v_leanOptions_1028_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lake_Module_leanOptions(v_self_1036_);
lean_dec_ref(v_self_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1038_){
_start:
{
lean_object* v_lib_1039_; lean_object* v_pkg_1040_; lean_object* v_config_1041_; lean_object* v_toLeanConfig_1042_; lean_object* v_config_1043_; lean_object* v_toLeanConfig_1044_; uint8_t v_buildType_1045_; lean_object* v_moreLeanArgs_1046_; uint8_t v_buildType_1047_; lean_object* v_moreLeanArgs_1048_; uint8_t v___y_1050_; uint8_t v___x_1054_; 
v_lib_1039_ = lean_ctor_get(v_self_1038_, 0);
v_pkg_1040_ = lean_ctor_get(v_lib_1039_, 0);
v_config_1041_ = lean_ctor_get(v_pkg_1040_, 6);
v_toLeanConfig_1042_ = lean_ctor_get(v_config_1041_, 1);
v_config_1043_ = lean_ctor_get(v_lib_1039_, 2);
v_toLeanConfig_1044_ = lean_ctor_get(v_config_1043_, 0);
v_buildType_1045_ = lean_ctor_get_uint8(v_toLeanConfig_1042_, sizeof(void*)*13);
v_moreLeanArgs_1046_ = lean_ctor_get(v_toLeanConfig_1042_, 1);
v_buildType_1047_ = lean_ctor_get_uint8(v_toLeanConfig_1044_, sizeof(void*)*13);
v_moreLeanArgs_1048_ = lean_ctor_get(v_toLeanConfig_1044_, 1);
v___x_1054_ = l_Lake_instOrdBuildType_ord(v_buildType_1045_, v_buildType_1047_);
if (v___x_1054_ == 2)
{
v___y_1050_ = v_buildType_1047_;
goto v___jp_1049_;
}
else
{
v___y_1050_ = v_buildType_1045_;
goto v___jp_1049_;
}
v___jp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = l_Lake_BuildType_leanArgs(v___y_1050_);
v___x_1052_ = l_Array_append___redArg(v___x_1051_, v_moreLeanArgs_1046_);
v___x_1053_ = l_Array_append___redArg(v___x_1052_, v_moreLeanArgs_1048_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lake_Module_leanArgs(v_self_1055_);
lean_dec_ref(v_self_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1057_){
_start:
{
lean_object* v_lib_1058_; lean_object* v_pkg_1059_; lean_object* v_config_1060_; lean_object* v_toLeanConfig_1061_; lean_object* v_config_1062_; lean_object* v_toLeanConfig_1063_; lean_object* v_weakLeanArgs_1064_; lean_object* v_weakLeanArgs_1065_; lean_object* v___x_1066_; 
v_lib_1058_ = lean_ctor_get(v_self_1057_, 0);
lean_inc_ref(v_lib_1058_);
lean_dec_ref(v_self_1057_);
v_pkg_1059_ = lean_ctor_get(v_lib_1058_, 0);
v_config_1060_ = lean_ctor_get(v_pkg_1059_, 6);
v_toLeanConfig_1061_ = lean_ctor_get(v_config_1060_, 1);
lean_inc_ref(v_toLeanConfig_1061_);
v_config_1062_ = lean_ctor_get(v_lib_1058_, 2);
lean_inc(v_config_1062_);
lean_dec_ref(v_lib_1058_);
v_toLeanConfig_1063_ = lean_ctor_get(v_config_1062_, 0);
lean_inc_ref(v_toLeanConfig_1063_);
lean_dec(v_config_1062_);
v_weakLeanArgs_1064_ = lean_ctor_get(v_toLeanConfig_1061_, 2);
lean_inc_ref(v_weakLeanArgs_1064_);
lean_dec_ref(v_toLeanConfig_1061_);
v_weakLeanArgs_1065_ = lean_ctor_get(v_toLeanConfig_1063_, 2);
lean_inc_ref(v_weakLeanArgs_1065_);
lean_dec_ref(v_toLeanConfig_1063_);
v___x_1066_ = l_Array_append___redArg(v_weakLeanArgs_1064_, v_weakLeanArgs_1065_);
lean_dec_ref(v_weakLeanArgs_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1067_){
_start:
{
lean_object* v_lib_1068_; lean_object* v_pkg_1069_; lean_object* v_config_1070_; lean_object* v_toLeanConfig_1071_; lean_object* v_config_1072_; lean_object* v_toLeanConfig_1073_; uint8_t v_buildType_1074_; lean_object* v_moreLeancArgs_1075_; uint8_t v_buildType_1076_; lean_object* v_moreLeancArgs_1077_; uint8_t v___y_1079_; uint8_t v___x_1083_; 
v_lib_1068_ = lean_ctor_get(v_self_1067_, 0);
v_pkg_1069_ = lean_ctor_get(v_lib_1068_, 0);
v_config_1070_ = lean_ctor_get(v_pkg_1069_, 6);
v_toLeanConfig_1071_ = lean_ctor_get(v_config_1070_, 1);
v_config_1072_ = lean_ctor_get(v_lib_1068_, 2);
v_toLeanConfig_1073_ = lean_ctor_get(v_config_1072_, 0);
v_buildType_1074_ = lean_ctor_get_uint8(v_toLeanConfig_1071_, sizeof(void*)*13);
v_moreLeancArgs_1075_ = lean_ctor_get(v_toLeanConfig_1071_, 3);
v_buildType_1076_ = lean_ctor_get_uint8(v_toLeanConfig_1073_, sizeof(void*)*13);
v_moreLeancArgs_1077_ = lean_ctor_get(v_toLeanConfig_1073_, 3);
v___x_1083_ = l_Lake_instOrdBuildType_ord(v_buildType_1074_, v_buildType_1076_);
if (v___x_1083_ == 2)
{
v___y_1079_ = v_buildType_1076_;
goto v___jp_1078_;
}
else
{
v___y_1079_ = v_buildType_1074_;
goto v___jp_1078_;
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = l_Lake_BuildType_leancArgs(v___y_1079_);
v___x_1081_ = l_Array_append___redArg(v___x_1080_, v_moreLeancArgs_1075_);
v___x_1082_ = l_Array_append___redArg(v___x_1081_, v_moreLeancArgs_1077_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lake_Module_leancArgs(v_self_1084_);
lean_dec_ref(v_self_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1086_){
_start:
{
lean_object* v_lib_1087_; lean_object* v_pkg_1088_; lean_object* v_config_1089_; lean_object* v_toLeanConfig_1090_; lean_object* v_config_1091_; lean_object* v_toLeanConfig_1092_; lean_object* v_weakLeancArgs_1093_; lean_object* v_weakLeancArgs_1094_; lean_object* v___x_1095_; 
v_lib_1087_ = lean_ctor_get(v_self_1086_, 0);
lean_inc_ref(v_lib_1087_);
lean_dec_ref(v_self_1086_);
v_pkg_1088_ = lean_ctor_get(v_lib_1087_, 0);
v_config_1089_ = lean_ctor_get(v_pkg_1088_, 6);
v_toLeanConfig_1090_ = lean_ctor_get(v_config_1089_, 1);
lean_inc_ref(v_toLeanConfig_1090_);
v_config_1091_ = lean_ctor_get(v_lib_1087_, 2);
lean_inc(v_config_1091_);
lean_dec_ref(v_lib_1087_);
v_toLeanConfig_1092_ = lean_ctor_get(v_config_1091_, 0);
lean_inc_ref(v_toLeanConfig_1092_);
lean_dec(v_config_1091_);
v_weakLeancArgs_1093_ = lean_ctor_get(v_toLeanConfig_1090_, 5);
lean_inc_ref(v_weakLeancArgs_1093_);
lean_dec_ref(v_toLeanConfig_1090_);
v_weakLeancArgs_1094_ = lean_ctor_get(v_toLeanConfig_1092_, 5);
lean_inc_ref(v_weakLeancArgs_1094_);
lean_dec_ref(v_toLeanConfig_1092_);
v___x_1095_ = l_Array_append___redArg(v_weakLeancArgs_1093_, v_weakLeancArgs_1094_);
lean_dec_ref(v_weakLeancArgs_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1096_){
_start:
{
lean_object* v_lib_1097_; lean_object* v_pkg_1098_; lean_object* v_config_1099_; lean_object* v_toLeanConfig_1100_; lean_object* v_config_1101_; lean_object* v_toLeanConfig_1102_; lean_object* v_moreLinkArgs_1103_; lean_object* v_moreLinkArgs_1104_; lean_object* v___x_1105_; 
v_lib_1097_ = lean_ctor_get(v_self_1096_, 0);
lean_inc_ref(v_lib_1097_);
lean_dec_ref(v_self_1096_);
v_pkg_1098_ = lean_ctor_get(v_lib_1097_, 0);
v_config_1099_ = lean_ctor_get(v_pkg_1098_, 6);
v_toLeanConfig_1100_ = lean_ctor_get(v_config_1099_, 1);
lean_inc_ref(v_toLeanConfig_1100_);
v_config_1101_ = lean_ctor_get(v_lib_1097_, 2);
lean_inc(v_config_1101_);
lean_dec_ref(v_lib_1097_);
v_toLeanConfig_1102_ = lean_ctor_get(v_config_1101_, 0);
lean_inc_ref(v_toLeanConfig_1102_);
lean_dec(v_config_1101_);
v_moreLinkArgs_1103_ = lean_ctor_get(v_toLeanConfig_1100_, 8);
lean_inc_ref(v_moreLinkArgs_1103_);
lean_dec_ref(v_toLeanConfig_1100_);
v_moreLinkArgs_1104_ = lean_ctor_get(v_toLeanConfig_1102_, 8);
lean_inc_ref(v_moreLinkArgs_1104_);
lean_dec_ref(v_toLeanConfig_1102_);
v___x_1105_ = l_Array_append___redArg(v_moreLinkArgs_1103_, v_moreLinkArgs_1104_);
lean_dec_ref(v_moreLinkArgs_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1106_){
_start:
{
lean_object* v_lib_1107_; lean_object* v_pkg_1108_; lean_object* v_config_1109_; lean_object* v_toLeanConfig_1110_; lean_object* v_config_1111_; lean_object* v_toLeanConfig_1112_; lean_object* v_weakLinkArgs_1113_; lean_object* v_weakLinkArgs_1114_; lean_object* v___x_1115_; 
v_lib_1107_ = lean_ctor_get(v_self_1106_, 0);
lean_inc_ref(v_lib_1107_);
lean_dec_ref(v_self_1106_);
v_pkg_1108_ = lean_ctor_get(v_lib_1107_, 0);
v_config_1109_ = lean_ctor_get(v_pkg_1108_, 6);
v_toLeanConfig_1110_ = lean_ctor_get(v_config_1109_, 1);
lean_inc_ref(v_toLeanConfig_1110_);
v_config_1111_ = lean_ctor_get(v_lib_1107_, 2);
lean_inc(v_config_1111_);
lean_dec_ref(v_lib_1107_);
v_toLeanConfig_1112_ = lean_ctor_get(v_config_1111_, 0);
lean_inc_ref(v_toLeanConfig_1112_);
lean_dec(v_config_1111_);
v_weakLinkArgs_1113_ = lean_ctor_get(v_toLeanConfig_1110_, 9);
lean_inc_ref(v_weakLinkArgs_1113_);
lean_dec_ref(v_toLeanConfig_1110_);
v_weakLinkArgs_1114_ = lean_ctor_get(v_toLeanConfig_1112_, 9);
lean_inc_ref(v_weakLinkArgs_1114_);
lean_dec_ref(v_toLeanConfig_1112_);
v___x_1115_ = l_Array_append___redArg(v_weakLinkArgs_1113_, v_weakLinkArgs_1114_);
lean_dec_ref(v_weakLinkArgs_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1117_){
_start:
{
lean_object* v_lib_1118_; lean_object* v_pkg_1119_; lean_object* v_config_1120_; uint8_t v_bootstrap_1121_; 
v_lib_1118_ = lean_ctor_get(v_self_1117_, 0);
lean_inc_ref(v_lib_1118_);
lean_dec_ref(v_self_1117_);
v_pkg_1119_ = lean_ctor_get(v_lib_1118_, 0);
lean_inc_ref(v_pkg_1119_);
lean_dec_ref(v_lib_1118_);
v_config_1120_ = lean_ctor_get(v_pkg_1119_, 6);
lean_inc_ref(v_config_1120_);
v_bootstrap_1121_ = lean_ctor_get_uint8(v_config_1120_, sizeof(void*)*27);
if (v_bootstrap_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_config_1120_);
lean_dec_ref(v_pkg_1119_);
v___x_1122_ = lean_box(0);
return v___x_1122_;
}
else
{
lean_object* v_dir_1123_; lean_object* v_buildDir_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_dir_1123_ = lean_ctor_get(v_pkg_1119_, 4);
lean_inc_ref(v_dir_1123_);
lean_dec_ref(v_pkg_1119_);
v_buildDir_1124_ = lean_ctor_get(v_config_1120_, 5);
lean_inc_ref(v_buildDir_1124_);
lean_dec_ref(v_config_1120_);
v___x_1125_ = l_System_FilePath_normalize(v_buildDir_1124_);
v___x_1126_ = l_Lake_joinRelative(v_dir_1123_, v___x_1125_);
v___x_1127_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1128_ = l_Lake_joinRelative(v___x_1126_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1130_){
_start:
{
lean_object* v_lib_1131_; lean_object* v_config_1132_; lean_object* v_toLeanConfig_1133_; lean_object* v_platformIndependent_1134_; 
v_lib_1131_ = lean_ctor_get(v_self_1130_, 0);
v_config_1132_ = lean_ctor_get(v_lib_1131_, 2);
v_toLeanConfig_1133_ = lean_ctor_get(v_config_1132_, 0);
v_platformIndependent_1134_ = lean_ctor_get(v_toLeanConfig_1133_, 10);
if (lean_obj_tag(v_platformIndependent_1134_) == 0)
{
lean_object* v_pkg_1135_; lean_object* v_config_1136_; lean_object* v_toLeanConfig_1137_; lean_object* v_platformIndependent_1138_; 
v_pkg_1135_ = lean_ctor_get(v_lib_1131_, 0);
v_config_1136_ = lean_ctor_get(v_pkg_1135_, 6);
v_toLeanConfig_1137_ = lean_ctor_get(v_config_1136_, 1);
v_platformIndependent_1138_ = lean_ctor_get(v_toLeanConfig_1137_, 10);
lean_inc(v_platformIndependent_1138_);
return v_platformIndependent_1138_;
}
else
{
lean_inc_ref(v_platformIndependent_1134_);
return v_platformIndependent_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lake_Module_platformIndependent(v_self_1139_);
lean_dec_ref(v_self_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1141_){
_start:
{
lean_object* v_lib_1142_; lean_object* v_pkg_1143_; lean_object* v_config_1144_; uint8_t v_precompileModules_1145_; 
v_lib_1142_ = lean_ctor_get(v_self_1141_, 0);
v_pkg_1143_ = lean_ctor_get(v_lib_1142_, 0);
v_config_1144_ = lean_ctor_get(v_pkg_1143_, 6);
v_precompileModules_1145_ = lean_ctor_get_uint8(v_config_1144_, sizeof(void*)*27 + 1);
if (v_precompileModules_1145_ == 0)
{
lean_object* v_config_1146_; uint8_t v_precompileModules_1147_; 
v_config_1146_ = lean_ctor_get(v_lib_1142_, 2);
v_precompileModules_1147_ = lean_ctor_get_uint8(v_config_1146_, sizeof(void*)*9 + 1);
return v_precompileModules_1147_;
}
else
{
return v_precompileModules_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1148_){
_start:
{
uint8_t v_res_1149_; lean_object* v_r_1150_; 
v_res_1149_ = l_Lake_Module_shouldPrecompile(v_self_1148_);
lean_dec_ref(v_self_1148_);
v_r_1150_ = lean_box(v_res_1149_);
return v_r_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1151_, uint8_t v_shouldExport_1152_){
_start:
{
lean_object* v_lib_1153_; lean_object* v_config_1154_; lean_object* v_nativeFacets_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_lib_1153_ = lean_ctor_get(v_self_1151_, 0);
lean_inc_ref(v_lib_1153_);
lean_dec_ref(v_self_1151_);
v_config_1154_ = lean_ctor_get(v_lib_1153_, 2);
lean_inc(v_config_1154_);
lean_dec_ref(v_lib_1153_);
v_nativeFacets_1155_ = lean_ctor_get(v_config_1154_, 8);
lean_inc_ref(v_nativeFacets_1155_);
lean_dec(v_config_1154_);
v___x_1156_ = lean_box(v_shouldExport_1152_);
v___x_1157_ = lean_apply_1(v_nativeFacets_1155_, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1158_, lean_object* v_shouldExport_1159_){
_start:
{
uint8_t v_shouldExport_boxed_1160_; lean_object* v_res_1161_; 
v_shouldExport_boxed_1160_ = lean_unbox(v_shouldExport_1159_);
v_res_1161_ = l_Lake_Module_nativeFacets(v_self_1158_, v_shouldExport_boxed_1160_);
return v_res_1161_;
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
