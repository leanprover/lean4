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
lean_dec_ref_known(v___x_314_, 1);
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
lean_dec_ref_known(v___x_321_, 1);
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
lean_dec_ref_known(v___x_328_, 1);
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
lean_dec_ref_known(v___x_437_, 1);
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
lean_dec_ref_known(v___y_409_, 1);
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
lean_dec_ref_known(v___x_510_, 1);
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
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object* v_self_723_){
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
v___x_731_ = ((lean_object*)(l_Lake_Module_irSigFile___closed__0));
v___x_732_ = l_System_FilePath_normalize(v_buildDir_729_);
v___x_733_ = l_Lake_joinRelative(v_dir_728_, v___x_732_);
v___x_734_ = l_System_FilePath_normalize(v_leanLibDir_730_);
v___x_735_ = l_Lake_joinRelative(v___x_733_, v___x_734_);
v___x_736_ = l_Lean_modToFilePath(v___x_735_, v_name_727_, v___x_731_);
lean_dec_ref(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_738_){
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
v___x_746_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_747_ = l_System_FilePath_normalize(v_buildDir_744_);
v___x_748_ = l_Lake_joinRelative(v_dir_743_, v___x_747_);
v___x_749_ = l_System_FilePath_normalize(v_leanLibDir_745_);
v___x_750_ = l_Lake_joinRelative(v___x_748_, v___x_749_);
v___x_751_ = l_Lean_modToFilePath(v___x_750_, v_name_742_, v___x_746_);
lean_dec_ref(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_753_){
_start:
{
lean_object* v_lib_754_; lean_object* v_pkg_755_; lean_object* v_config_756_; lean_object* v_name_757_; lean_object* v_dir_758_; lean_object* v_buildDir_759_; lean_object* v_leanLibDir_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
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
v_leanLibDir_760_ = lean_ctor_get(v_config_756_, 6);
lean_inc_ref(v_leanLibDir_760_);
lean_dec_ref(v_config_756_);
v___x_761_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_762_ = l_System_FilePath_normalize(v_buildDir_759_);
v___x_763_ = l_Lake_joinRelative(v_dir_758_, v___x_762_);
v___x_764_ = l_System_FilePath_normalize(v_leanLibDir_760_);
v___x_765_ = l_Lake_joinRelative(v___x_763_, v___x_764_);
v___x_766_ = l_Lean_modToFilePath(v___x_765_, v_name_757_, v___x_761_);
lean_dec_ref(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_767_, lean_object* v_self_768_){
_start:
{
lean_object* v_lib_769_; lean_object* v_pkg_770_; lean_object* v_config_771_; lean_object* v_name_772_; lean_object* v_dir_773_; lean_object* v_buildDir_774_; lean_object* v_irDir_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_lib_769_ = lean_ctor_get(v_self_768_, 0);
v_pkg_770_ = lean_ctor_get(v_lib_769_, 0);
lean_inc_ref(v_pkg_770_);
v_config_771_ = lean_ctor_get(v_pkg_770_, 6);
lean_inc_ref(v_config_771_);
v_name_772_ = lean_ctor_get(v_self_768_, 1);
lean_inc(v_name_772_);
lean_dec_ref(v_self_768_);
v_dir_773_ = lean_ctor_get(v_pkg_770_, 4);
lean_inc_ref(v_dir_773_);
lean_dec_ref(v_pkg_770_);
v_buildDir_774_ = lean_ctor_get(v_config_771_, 5);
lean_inc_ref(v_buildDir_774_);
v_irDir_775_ = lean_ctor_get(v_config_771_, 9);
lean_inc_ref(v_irDir_775_);
lean_dec_ref(v_config_771_);
v___x_776_ = l_System_FilePath_normalize(v_buildDir_774_);
v___x_777_ = l_Lake_joinRelative(v_dir_773_, v___x_776_);
v___x_778_ = l_System_FilePath_normalize(v_irDir_775_);
v___x_779_ = l_Lake_joinRelative(v___x_777_, v___x_778_);
v___x_780_ = l_Lean_modToFilePath(v___x_779_, v_name_772_, v_ext_767_);
lean_dec_ref(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_781_, lean_object* v_self_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lake_Module_irPath(v_ext_781_, v_self_782_);
lean_dec_ref(v_ext_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_784_){
_start:
{
lean_object* v_lib_785_; lean_object* v_pkg_786_; lean_object* v_config_787_; lean_object* v_name_788_; lean_object* v_dir_789_; lean_object* v_buildDir_790_; lean_object* v_irDir_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_lib_785_ = lean_ctor_get(v_self_784_, 0);
v_pkg_786_ = lean_ctor_get(v_lib_785_, 0);
lean_inc_ref(v_pkg_786_);
v_config_787_ = lean_ctor_get(v_pkg_786_, 6);
lean_inc_ref(v_config_787_);
v_name_788_ = lean_ctor_get(v_self_784_, 1);
lean_inc(v_name_788_);
lean_dec_ref(v_self_784_);
v_dir_789_ = lean_ctor_get(v_pkg_786_, 4);
lean_inc_ref(v_dir_789_);
lean_dec_ref(v_pkg_786_);
v_buildDir_790_ = lean_ctor_get(v_config_787_, 5);
lean_inc_ref(v_buildDir_790_);
v_irDir_791_ = lean_ctor_get(v_config_787_, 9);
lean_inc_ref(v_irDir_791_);
lean_dec_ref(v_config_787_);
v___x_792_ = l_System_FilePath_normalize(v_buildDir_790_);
v___x_793_ = l_Lake_joinRelative(v_dir_789_, v___x_792_);
v___x_794_ = l_System_FilePath_normalize(v_irDir_791_);
v___x_795_ = l_Lake_joinRelative(v___x_793_, v___x_794_);
v___x_796_ = l_Lean_Name_getPrefix(v_name_788_);
lean_dec(v_name_788_);
v___x_797_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_798_ = l_Lean_modToFilePath(v___x_795_, v___x_796_, v___x_797_);
lean_dec_ref(v___x_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_800_){
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
v___x_808_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_809_ = l_System_FilePath_normalize(v_buildDir_806_);
v___x_810_ = l_Lake_joinRelative(v_dir_805_, v___x_809_);
v___x_811_ = l_System_FilePath_normalize(v_irDir_807_);
v___x_812_ = l_Lake_joinRelative(v___x_810_, v___x_811_);
v___x_813_ = l_Lean_modToFilePath(v___x_812_, v_name_804_, v___x_808_);
lean_dec_ref(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_815_){
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
v___x_823_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_824_ = l_System_FilePath_normalize(v_buildDir_821_);
v___x_825_ = l_Lake_joinRelative(v_dir_820_, v___x_824_);
v___x_826_ = l_System_FilePath_normalize(v_irDir_822_);
v___x_827_ = l_Lake_joinRelative(v___x_825_, v___x_826_);
v___x_828_ = l_Lean_modToFilePath(v___x_827_, v_name_819_, v___x_823_);
lean_dec_ref(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_830_){
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
v___x_838_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_839_ = l_System_FilePath_normalize(v_buildDir_836_);
v___x_840_ = l_Lake_joinRelative(v_dir_835_, v___x_839_);
v___x_841_ = l_System_FilePath_normalize(v_irDir_837_);
v___x_842_ = l_Lake_joinRelative(v___x_840_, v___x_841_);
v___x_843_ = l_Lean_modToFilePath(v___x_842_, v_name_834_, v___x_838_);
lean_dec_ref(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_845_){
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
v___x_853_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_854_ = l_System_FilePath_normalize(v_buildDir_851_);
v___x_855_ = l_Lake_joinRelative(v_dir_850_, v___x_854_);
v___x_856_ = l_System_FilePath_normalize(v_irDir_852_);
v___x_857_ = l_Lake_joinRelative(v___x_855_, v___x_856_);
v___x_858_ = l_Lean_modToFilePath(v___x_857_, v_name_849_, v___x_853_);
lean_dec_ref(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_860_){
_start:
{
lean_object* v_lib_861_; lean_object* v_pkg_862_; lean_object* v_config_863_; lean_object* v_name_864_; lean_object* v_dir_865_; lean_object* v_buildDir_866_; lean_object* v_irDir_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_lib_861_ = lean_ctor_get(v_self_860_, 0);
v_pkg_862_ = lean_ctor_get(v_lib_861_, 0);
lean_inc_ref(v_pkg_862_);
v_config_863_ = lean_ctor_get(v_pkg_862_, 6);
lean_inc_ref(v_config_863_);
v_name_864_ = lean_ctor_get(v_self_860_, 1);
lean_inc(v_name_864_);
lean_dec_ref(v_self_860_);
v_dir_865_ = lean_ctor_get(v_pkg_862_, 4);
lean_inc_ref(v_dir_865_);
lean_dec_ref(v_pkg_862_);
v_buildDir_866_ = lean_ctor_get(v_config_863_, 5);
lean_inc_ref(v_buildDir_866_);
v_irDir_867_ = lean_ctor_get(v_config_863_, 9);
lean_inc_ref(v_irDir_867_);
lean_dec_ref(v_config_863_);
v___x_868_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_869_ = l_System_FilePath_normalize(v_buildDir_866_);
v___x_870_ = l_Lake_joinRelative(v_dir_865_, v___x_869_);
v___x_871_ = l_System_FilePath_normalize(v_irDir_867_);
v___x_872_ = l_Lake_joinRelative(v___x_870_, v___x_871_);
v___x_873_ = l_Lean_modToFilePath(v___x_872_, v_name_864_, v___x_868_);
lean_dec_ref(v___x_872_);
return v___x_873_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_box(0);
v___x_875_ = lean_internal_has_llvm_backend(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec_ref(v_self_876_);
v___x_878_ = lean_box(0);
return v___x_878_;
}
else
{
lean_object* v_lib_879_; lean_object* v_pkg_880_; lean_object* v_config_881_; lean_object* v_name_882_; lean_object* v_dir_883_; lean_object* v_buildDir_884_; lean_object* v_irDir_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_lib_879_ = lean_ctor_get(v_self_876_, 0);
v_pkg_880_ = lean_ctor_get(v_lib_879_, 0);
lean_inc_ref(v_pkg_880_);
v_config_881_ = lean_ctor_get(v_pkg_880_, 6);
lean_inc_ref(v_config_881_);
v_name_882_ = lean_ctor_get(v_self_876_, 1);
lean_inc(v_name_882_);
lean_dec_ref(v_self_876_);
v_dir_883_ = lean_ctor_get(v_pkg_880_, 4);
lean_inc_ref(v_dir_883_);
lean_dec_ref(v_pkg_880_);
v_buildDir_884_ = lean_ctor_get(v_config_881_, 5);
lean_inc_ref(v_buildDir_884_);
v_irDir_885_ = lean_ctor_get(v_config_881_, 9);
lean_inc_ref(v_irDir_885_);
lean_dec_ref(v_config_881_);
v___x_886_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_887_ = l_System_FilePath_normalize(v_buildDir_884_);
v___x_888_ = l_Lake_joinRelative(v_dir_883_, v___x_887_);
v___x_889_ = l_System_FilePath_normalize(v_irDir_885_);
v___x_890_ = l_Lake_joinRelative(v___x_888_, v___x_889_);
v___x_891_ = l_Lean_modToFilePath(v___x_890_, v_name_882_, v___x_886_);
lean_dec_ref(v___x_890_);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_894_){
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
v___x_902_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_903_ = l_System_FilePath_normalize(v_buildDir_900_);
v___x_904_ = l_Lake_joinRelative(v_dir_899_, v___x_903_);
v___x_905_ = l_System_FilePath_normalize(v_irDir_901_);
v___x_906_ = l_Lake_joinRelative(v___x_904_, v___x_905_);
v___x_907_ = l_Lean_modToFilePath(v___x_906_, v_name_898_, v___x_902_);
lean_dec_ref(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_909_){
_start:
{
lean_object* v_lib_910_; lean_object* v_pkg_911_; lean_object* v_config_912_; lean_object* v_name_913_; lean_object* v_dir_914_; lean_object* v_buildDir_915_; lean_object* v_irDir_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_lib_910_ = lean_ctor_get(v_self_909_, 0);
v_pkg_911_ = lean_ctor_get(v_lib_910_, 0);
lean_inc_ref(v_pkg_911_);
v_config_912_ = lean_ctor_get(v_pkg_911_, 6);
lean_inc_ref(v_config_912_);
v_name_913_ = lean_ctor_get(v_self_909_, 1);
lean_inc(v_name_913_);
lean_dec_ref(v_self_909_);
v_dir_914_ = lean_ctor_get(v_pkg_911_, 4);
lean_inc_ref(v_dir_914_);
lean_dec_ref(v_pkg_911_);
v_buildDir_915_ = lean_ctor_get(v_config_912_, 5);
lean_inc_ref(v_buildDir_915_);
v_irDir_916_ = lean_ctor_get(v_config_912_, 9);
lean_inc_ref(v_irDir_916_);
lean_dec_ref(v_config_912_);
v___x_917_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_918_ = l_System_FilePath_normalize(v_buildDir_915_);
v___x_919_ = l_Lake_joinRelative(v_dir_914_, v___x_918_);
v___x_920_ = l_System_FilePath_normalize(v_irDir_916_);
v___x_921_ = l_Lake_joinRelative(v___x_919_, v___x_920_);
v___x_922_ = l_Lean_modToFilePath(v___x_921_, v_name_913_, v___x_917_);
lean_dec_ref(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_925_){
_start:
{
lean_object* v_lib_926_; lean_object* v_name_927_; lean_object* v_pkg_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_lib_926_ = lean_ctor_get(v_self_925_, 0);
lean_inc_ref(v_lib_926_);
v_name_927_ = lean_ctor_get(v_self_925_, 1);
lean_inc(v_name_927_);
lean_dec_ref(v_self_925_);
v_pkg_928_ = lean_ctor_get(v_lib_926_, 0);
lean_inc_ref(v_pkg_928_);
lean_dec_ref(v_lib_926_);
v___x_929_ = l_Lake_Package_id_x3f(v_pkg_928_);
v___x_930_ = l_Lean_mkModuleInitializationStem(v_name_927_, v___x_929_);
lean_dec(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_932_){
_start:
{
lean_object* v_lib_933_; lean_object* v_pkg_934_; lean_object* v_config_935_; lean_object* v_name_936_; lean_object* v_dir_937_; lean_object* v_buildDir_938_; lean_object* v_leanLibDir_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_lib_933_ = lean_ctor_get(v_self_932_, 0);
v_pkg_934_ = lean_ctor_get(v_lib_933_, 0);
lean_inc_ref(v_pkg_934_);
v_config_935_ = lean_ctor_get(v_pkg_934_, 6);
v_name_936_ = lean_ctor_get(v_self_932_, 1);
lean_inc(v_name_936_);
lean_dec_ref(v_self_932_);
v_dir_937_ = lean_ctor_get(v_pkg_934_, 4);
v_buildDir_938_ = lean_ctor_get(v_config_935_, 5);
v_leanLibDir_939_ = lean_ctor_get(v_config_935_, 6);
lean_inc_ref(v_buildDir_938_);
v___x_940_ = l_System_FilePath_normalize(v_buildDir_938_);
lean_inc_ref(v_dir_937_);
v___x_941_ = l_Lake_joinRelative(v_dir_937_, v___x_940_);
lean_inc_ref(v_leanLibDir_939_);
v___x_942_ = l_System_FilePath_normalize(v_leanLibDir_939_);
v___x_943_ = l_Lake_joinRelative(v___x_941_, v___x_942_);
v___x_944_ = l_Lake_Package_id_x3f(v_pkg_934_);
v___x_945_ = l_Lean_mkModuleInitializationStem(v_name_936_, v___x_944_);
lean_dec(v___x_944_);
v___x_946_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___x_948_ = l_Lake_sharedLibExt;
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___x_950_ = l_Lake_joinRelative(v___x_943_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_951_){
_start:
{
lean_object* v_lib_952_; lean_object* v_pkg_953_; lean_object* v_config_954_; lean_object* v_toLeanConfig_955_; lean_object* v_config_956_; lean_object* v_toLeanConfig_957_; uint8_t v_buildType_958_; lean_object* v_leanOptions_959_; lean_object* v_moreServerOptions_960_; uint8_t v_buildType_961_; lean_object* v_leanOptions_962_; lean_object* v_moreServerOptions_963_; lean_object* v___x_964_; uint8_t v___y_966_; uint8_t v___x_974_; 
v_lib_952_ = lean_ctor_get(v_self_951_, 0);
v_pkg_953_ = lean_ctor_get(v_lib_952_, 0);
v_config_954_ = lean_ctor_get(v_pkg_953_, 6);
v_toLeanConfig_955_ = lean_ctor_get(v_config_954_, 1);
v_config_956_ = lean_ctor_get(v_lib_952_, 2);
v_toLeanConfig_957_ = lean_ctor_get(v_config_956_, 0);
v_buildType_958_ = lean_ctor_get_uint8(v_toLeanConfig_955_, sizeof(void*)*13);
v_leanOptions_959_ = lean_ctor_get(v_toLeanConfig_955_, 0);
v_moreServerOptions_960_ = lean_ctor_get(v_toLeanConfig_955_, 4);
v_buildType_961_ = lean_ctor_get_uint8(v_toLeanConfig_957_, sizeof(void*)*13);
v_leanOptions_962_ = lean_ctor_get(v_toLeanConfig_957_, 0);
v_moreServerOptions_963_ = lean_ctor_get(v_toLeanConfig_957_, 4);
v___x_964_ = lean_box(1);
v___x_974_ = l_Lake_instOrdBuildType_ord(v_buildType_958_, v_buildType_961_);
if (v___x_974_ == 2)
{
v___y_966_ = v_buildType_961_;
goto v___jp_965_;
}
else
{
v___y_966_ = v_buildType_958_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_967_ = l_Lake_BuildType_leanOptions(v___y_966_);
v___x_968_ = l_Lean_LeanOptions_append(v___x_964_, v___x_967_);
v___x_969_ = l_Lean_LeanOptions_ofArray(v_leanOptions_959_);
v___x_970_ = l_Lean_LeanOptions_appendArray(v___x_969_, v_moreServerOptions_960_);
v___x_971_ = l_Lean_LeanOptions_append(v___x_968_, v___x_970_);
v___x_972_ = l_Lean_LeanOptions_appendArray(v___x_971_, v_leanOptions_962_);
v___x_973_ = l_Lean_LeanOptions_appendArray(v___x_972_, v_moreServerOptions_963_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lake_Module_serverOptions(v_self_975_);
lean_dec_ref(v_self_975_);
return v_res_976_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_977_){
_start:
{
lean_object* v_lib_978_; lean_object* v_pkg_979_; lean_object* v_config_980_; lean_object* v_toLeanConfig_981_; lean_object* v_config_982_; lean_object* v_toLeanConfig_983_; uint8_t v_buildType_984_; uint8_t v_buildType_985_; uint8_t v___x_986_; 
v_lib_978_ = lean_ctor_get(v_self_977_, 0);
v_pkg_979_ = lean_ctor_get(v_lib_978_, 0);
v_config_980_ = lean_ctor_get(v_pkg_979_, 6);
v_toLeanConfig_981_ = lean_ctor_get(v_config_980_, 1);
v_config_982_ = lean_ctor_get(v_lib_978_, 2);
v_toLeanConfig_983_ = lean_ctor_get(v_config_982_, 0);
v_buildType_984_ = lean_ctor_get_uint8(v_toLeanConfig_981_, sizeof(void*)*13);
v_buildType_985_ = lean_ctor_get_uint8(v_toLeanConfig_983_, sizeof(void*)*13);
v___x_986_ = l_Lake_instOrdBuildType_ord(v_buildType_984_, v_buildType_985_);
if (v___x_986_ == 2)
{
return v_buildType_985_;
}
else
{
return v_buildType_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_Lake_Module_buildType(v_self_987_);
lean_dec_ref(v_self_987_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_990_){
_start:
{
lean_object* v_lib_991_; lean_object* v_config_992_; lean_object* v_toLeanConfig_993_; lean_object* v_pkg_994_; lean_object* v_config_995_; lean_object* v_toLeanConfig_996_; uint8_t v_backend_997_; uint8_t v_backend_998_; uint8_t v___x_999_; 
v_lib_991_ = lean_ctor_get(v_self_990_, 0);
v_config_992_ = lean_ctor_get(v_lib_991_, 2);
v_toLeanConfig_993_ = lean_ctor_get(v_config_992_, 0);
v_pkg_994_ = lean_ctor_get(v_lib_991_, 0);
v_config_995_ = lean_ctor_get(v_pkg_994_, 6);
v_toLeanConfig_996_ = lean_ctor_get(v_config_995_, 1);
v_backend_997_ = lean_ctor_get_uint8(v_toLeanConfig_993_, sizeof(void*)*13 + 1);
v_backend_998_ = lean_ctor_get_uint8(v_toLeanConfig_996_, sizeof(void*)*13 + 1);
v___x_999_ = l_Lake_Backend_orPreferLeft(v_backend_997_, v_backend_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Lake_Module_backend(v_self_1000_);
lean_dec_ref(v_self_1000_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_1003_){
_start:
{
lean_object* v_lib_1004_; lean_object* v_config_1005_; uint8_t v_allowImportAll_1006_; 
v_lib_1004_ = lean_ctor_get(v_self_1003_, 0);
v_config_1005_ = lean_ctor_get(v_lib_1004_, 2);
v_allowImportAll_1006_ = lean_ctor_get_uint8(v_config_1005_, sizeof(void*)*9 + 2);
if (v_allowImportAll_1006_ == 0)
{
lean_object* v_pkg_1007_; lean_object* v_config_1008_; uint8_t v_allowImportAll_1009_; 
v_pkg_1007_ = lean_ctor_get(v_lib_1004_, 0);
v_config_1008_ = lean_ctor_get(v_pkg_1007_, 6);
v_allowImportAll_1009_ = lean_ctor_get_uint8(v_config_1008_, sizeof(void*)*27 + 5);
return v_allowImportAll_1009_;
}
else
{
return v_allowImportAll_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l_Lake_Module_allowImportAll(v_self_1010_);
lean_dec_ref(v_self_1010_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_requiresModuleSystem(lean_object* v_self_1013_){
_start:
{
lean_object* v_lib_1014_; lean_object* v_config_1015_; lean_object* v_toLeanConfig_1016_; uint8_t v_requiresModuleSystem_1017_; 
v_lib_1014_ = lean_ctor_get(v_self_1013_, 0);
v_config_1015_ = lean_ctor_get(v_lib_1014_, 2);
v_toLeanConfig_1016_ = lean_ctor_get(v_config_1015_, 0);
v_requiresModuleSystem_1017_ = lean_ctor_get_uint8(v_toLeanConfig_1016_, sizeof(void*)*13 + 2);
if (v_requiresModuleSystem_1017_ == 0)
{
lean_object* v_pkg_1018_; lean_object* v_config_1019_; lean_object* v_toLeanConfig_1020_; uint8_t v_requiresModuleSystem_1021_; 
v_pkg_1018_ = lean_ctor_get(v_lib_1014_, 0);
v_config_1019_ = lean_ctor_get(v_pkg_1018_, 6);
v_toLeanConfig_1020_ = lean_ctor_get(v_config_1019_, 1);
v_requiresModuleSystem_1021_ = lean_ctor_get_uint8(v_toLeanConfig_1020_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_1021_;
}
else
{
return v_requiresModuleSystem_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object* v_self_1022_){
_start:
{
uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_res_1023_ = l_Lake_Module_requiresModuleSystem(v_self_1022_);
lean_dec_ref(v_self_1022_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowNonModules(lean_object* v_self_1025_){
_start:
{
lean_object* v_lib_1026_; lean_object* v_config_1027_; lean_object* v_toLeanConfig_1028_; uint8_t v_allowNonModules_1029_; 
v_lib_1026_ = lean_ctor_get(v_self_1025_, 0);
v_config_1027_ = lean_ctor_get(v_lib_1026_, 2);
v_toLeanConfig_1028_ = lean_ctor_get(v_config_1027_, 0);
v_allowNonModules_1029_ = lean_ctor_get_uint8(v_toLeanConfig_1028_, sizeof(void*)*13 + 3);
if (v_allowNonModules_1029_ == 0)
{
lean_object* v_pkg_1030_; lean_object* v_config_1031_; lean_object* v_toLeanConfig_1032_; uint8_t v_allowNonModules_1033_; 
v_pkg_1030_ = lean_ctor_get(v_lib_1026_, 0);
v_config_1031_ = lean_ctor_get(v_pkg_1030_, 6);
v_toLeanConfig_1032_ = lean_ctor_get(v_config_1031_, 1);
v_allowNonModules_1033_ = lean_ctor_get_uint8(v_toLeanConfig_1032_, sizeof(void*)*13 + 3);
return v_allowNonModules_1033_;
}
else
{
return v_allowNonModules_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object* v_self_1034_){
_start:
{
uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_res_1035_ = l_Lake_Module_allowNonModules(v_self_1034_);
lean_dec_ref(v_self_1034_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_1037_){
_start:
{
lean_object* v_lib_1038_; lean_object* v_pkg_1039_; lean_object* v_config_1040_; lean_object* v_toLeanConfig_1041_; lean_object* v_config_1042_; lean_object* v_toLeanConfig_1043_; lean_object* v_dynlibs_1044_; lean_object* v_dynlibs_1045_; lean_object* v___x_1046_; 
v_lib_1038_ = lean_ctor_get(v_self_1037_, 0);
lean_inc_ref(v_lib_1038_);
lean_dec_ref(v_self_1037_);
v_pkg_1039_ = lean_ctor_get(v_lib_1038_, 0);
v_config_1040_ = lean_ctor_get(v_pkg_1039_, 6);
v_toLeanConfig_1041_ = lean_ctor_get(v_config_1040_, 1);
lean_inc_ref(v_toLeanConfig_1041_);
v_config_1042_ = lean_ctor_get(v_lib_1038_, 2);
lean_inc(v_config_1042_);
lean_dec_ref(v_lib_1038_);
v_toLeanConfig_1043_ = lean_ctor_get(v_config_1042_, 0);
lean_inc_ref(v_toLeanConfig_1043_);
lean_dec(v_config_1042_);
v_dynlibs_1044_ = lean_ctor_get(v_toLeanConfig_1041_, 11);
lean_inc_ref(v_dynlibs_1044_);
lean_dec_ref(v_toLeanConfig_1041_);
v_dynlibs_1045_ = lean_ctor_get(v_toLeanConfig_1043_, 11);
lean_inc_ref(v_dynlibs_1045_);
lean_dec_ref(v_toLeanConfig_1043_);
v___x_1046_ = l_Array_append___redArg(v_dynlibs_1044_, v_dynlibs_1045_);
lean_dec_ref(v_dynlibs_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1047_){
_start:
{
lean_object* v_lib_1048_; lean_object* v_pkg_1049_; lean_object* v_config_1050_; lean_object* v_toLeanConfig_1051_; lean_object* v_config_1052_; lean_object* v_toLeanConfig_1053_; lean_object* v_plugins_1054_; lean_object* v_plugins_1055_; lean_object* v___x_1056_; 
v_lib_1048_ = lean_ctor_get(v_self_1047_, 0);
lean_inc_ref(v_lib_1048_);
lean_dec_ref(v_self_1047_);
v_pkg_1049_ = lean_ctor_get(v_lib_1048_, 0);
v_config_1050_ = lean_ctor_get(v_pkg_1049_, 6);
v_toLeanConfig_1051_ = lean_ctor_get(v_config_1050_, 1);
lean_inc_ref(v_toLeanConfig_1051_);
v_config_1052_ = lean_ctor_get(v_lib_1048_, 2);
lean_inc(v_config_1052_);
lean_dec_ref(v_lib_1048_);
v_toLeanConfig_1053_ = lean_ctor_get(v_config_1052_, 0);
lean_inc_ref(v_toLeanConfig_1053_);
lean_dec(v_config_1052_);
v_plugins_1054_ = lean_ctor_get(v_toLeanConfig_1051_, 12);
lean_inc_ref(v_plugins_1054_);
lean_dec_ref(v_toLeanConfig_1051_);
v_plugins_1055_ = lean_ctor_get(v_toLeanConfig_1053_, 12);
lean_inc_ref(v_plugins_1055_);
lean_dec_ref(v_toLeanConfig_1053_);
v___x_1056_ = l_Array_append___redArg(v_plugins_1054_, v_plugins_1055_);
lean_dec_ref(v_plugins_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1057_){
_start:
{
lean_object* v_lib_1058_; lean_object* v_pkg_1059_; lean_object* v_config_1060_; lean_object* v_toLeanConfig_1061_; lean_object* v_config_1062_; lean_object* v_toLeanConfig_1063_; uint8_t v_buildType_1064_; lean_object* v_leanOptions_1065_; uint8_t v_buildType_1066_; lean_object* v_leanOptions_1067_; uint8_t v___y_1069_; uint8_t v___x_1074_; 
v_lib_1058_ = lean_ctor_get(v_self_1057_, 0);
v_pkg_1059_ = lean_ctor_get(v_lib_1058_, 0);
v_config_1060_ = lean_ctor_get(v_pkg_1059_, 6);
v_toLeanConfig_1061_ = lean_ctor_get(v_config_1060_, 1);
v_config_1062_ = lean_ctor_get(v_lib_1058_, 2);
v_toLeanConfig_1063_ = lean_ctor_get(v_config_1062_, 0);
v_buildType_1064_ = lean_ctor_get_uint8(v_toLeanConfig_1061_, sizeof(void*)*13);
v_leanOptions_1065_ = lean_ctor_get(v_toLeanConfig_1061_, 0);
v_buildType_1066_ = lean_ctor_get_uint8(v_toLeanConfig_1063_, sizeof(void*)*13);
v_leanOptions_1067_ = lean_ctor_get(v_toLeanConfig_1063_, 0);
v___x_1074_ = l_Lake_instOrdBuildType_ord(v_buildType_1064_, v_buildType_1066_);
if (v___x_1074_ == 2)
{
v___y_1069_ = v_buildType_1066_;
goto v___jp_1068_;
}
else
{
v___y_1069_ = v_buildType_1064_;
goto v___jp_1068_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = l_Lake_BuildType_leanOptions(v___y_1069_);
v___x_1071_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1065_);
v___x_1072_ = l_Lean_LeanOptions_append(v___x_1070_, v___x_1071_);
v___x_1073_ = l_Lean_LeanOptions_appendArray(v___x_1072_, v_leanOptions_1067_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lake_Module_leanOptions(v_self_1075_);
lean_dec_ref(v_self_1075_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1077_){
_start:
{
lean_object* v_lib_1078_; lean_object* v_pkg_1079_; lean_object* v_config_1080_; lean_object* v_toLeanConfig_1081_; lean_object* v_config_1082_; lean_object* v_toLeanConfig_1083_; uint8_t v_buildType_1084_; lean_object* v_moreLeanArgs_1085_; uint8_t v_buildType_1086_; lean_object* v_moreLeanArgs_1087_; uint8_t v___y_1089_; uint8_t v___x_1093_; 
v_lib_1078_ = lean_ctor_get(v_self_1077_, 0);
v_pkg_1079_ = lean_ctor_get(v_lib_1078_, 0);
v_config_1080_ = lean_ctor_get(v_pkg_1079_, 6);
v_toLeanConfig_1081_ = lean_ctor_get(v_config_1080_, 1);
v_config_1082_ = lean_ctor_get(v_lib_1078_, 2);
v_toLeanConfig_1083_ = lean_ctor_get(v_config_1082_, 0);
v_buildType_1084_ = lean_ctor_get_uint8(v_toLeanConfig_1081_, sizeof(void*)*13);
v_moreLeanArgs_1085_ = lean_ctor_get(v_toLeanConfig_1081_, 1);
v_buildType_1086_ = lean_ctor_get_uint8(v_toLeanConfig_1083_, sizeof(void*)*13);
v_moreLeanArgs_1087_ = lean_ctor_get(v_toLeanConfig_1083_, 1);
v___x_1093_ = l_Lake_instOrdBuildType_ord(v_buildType_1084_, v_buildType_1086_);
if (v___x_1093_ == 2)
{
v___y_1089_ = v_buildType_1086_;
goto v___jp_1088_;
}
else
{
v___y_1089_ = v_buildType_1084_;
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = l_Lake_BuildType_leanArgs(v___y_1089_);
v___x_1091_ = l_Array_append___redArg(v___x_1090_, v_moreLeanArgs_1085_);
v___x_1092_ = l_Array_append___redArg(v___x_1091_, v_moreLeanArgs_1087_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_Module_leanArgs(v_self_1094_);
lean_dec_ref(v_self_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1096_){
_start:
{
lean_object* v_lib_1097_; lean_object* v_pkg_1098_; lean_object* v_config_1099_; lean_object* v_toLeanConfig_1100_; lean_object* v_config_1101_; lean_object* v_toLeanConfig_1102_; lean_object* v_weakLeanArgs_1103_; lean_object* v_weakLeanArgs_1104_; lean_object* v___x_1105_; 
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
v_weakLeanArgs_1103_ = lean_ctor_get(v_toLeanConfig_1100_, 2);
lean_inc_ref(v_weakLeanArgs_1103_);
lean_dec_ref(v_toLeanConfig_1100_);
v_weakLeanArgs_1104_ = lean_ctor_get(v_toLeanConfig_1102_, 2);
lean_inc_ref(v_weakLeanArgs_1104_);
lean_dec_ref(v_toLeanConfig_1102_);
v___x_1105_ = l_Array_append___redArg(v_weakLeanArgs_1103_, v_weakLeanArgs_1104_);
lean_dec_ref(v_weakLeanArgs_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1106_){
_start:
{
lean_object* v_lib_1107_; lean_object* v_pkg_1108_; lean_object* v_config_1109_; lean_object* v_toLeanConfig_1110_; lean_object* v_config_1111_; lean_object* v_toLeanConfig_1112_; uint8_t v_buildType_1113_; lean_object* v_moreLeancArgs_1114_; uint8_t v_buildType_1115_; lean_object* v_moreLeancArgs_1116_; uint8_t v___y_1118_; uint8_t v___x_1122_; 
v_lib_1107_ = lean_ctor_get(v_self_1106_, 0);
v_pkg_1108_ = lean_ctor_get(v_lib_1107_, 0);
v_config_1109_ = lean_ctor_get(v_pkg_1108_, 6);
v_toLeanConfig_1110_ = lean_ctor_get(v_config_1109_, 1);
v_config_1111_ = lean_ctor_get(v_lib_1107_, 2);
v_toLeanConfig_1112_ = lean_ctor_get(v_config_1111_, 0);
v_buildType_1113_ = lean_ctor_get_uint8(v_toLeanConfig_1110_, sizeof(void*)*13);
v_moreLeancArgs_1114_ = lean_ctor_get(v_toLeanConfig_1110_, 3);
v_buildType_1115_ = lean_ctor_get_uint8(v_toLeanConfig_1112_, sizeof(void*)*13);
v_moreLeancArgs_1116_ = lean_ctor_get(v_toLeanConfig_1112_, 3);
v___x_1122_ = l_Lake_instOrdBuildType_ord(v_buildType_1113_, v_buildType_1115_);
if (v___x_1122_ == 2)
{
v___y_1118_ = v_buildType_1115_;
goto v___jp_1117_;
}
else
{
v___y_1118_ = v_buildType_1113_;
goto v___jp_1117_;
}
v___jp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lake_BuildType_leancArgs(v___y_1118_);
v___x_1120_ = l_Array_append___redArg(v___x_1119_, v_moreLeancArgs_1114_);
v___x_1121_ = l_Array_append___redArg(v___x_1120_, v_moreLeancArgs_1116_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lake_Module_leancArgs(v_self_1123_);
lean_dec_ref(v_self_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1125_){
_start:
{
lean_object* v_lib_1126_; lean_object* v_pkg_1127_; lean_object* v_config_1128_; lean_object* v_toLeanConfig_1129_; lean_object* v_config_1130_; lean_object* v_toLeanConfig_1131_; lean_object* v_weakLeancArgs_1132_; lean_object* v_weakLeancArgs_1133_; lean_object* v___x_1134_; 
v_lib_1126_ = lean_ctor_get(v_self_1125_, 0);
lean_inc_ref(v_lib_1126_);
lean_dec_ref(v_self_1125_);
v_pkg_1127_ = lean_ctor_get(v_lib_1126_, 0);
v_config_1128_ = lean_ctor_get(v_pkg_1127_, 6);
v_toLeanConfig_1129_ = lean_ctor_get(v_config_1128_, 1);
lean_inc_ref(v_toLeanConfig_1129_);
v_config_1130_ = lean_ctor_get(v_lib_1126_, 2);
lean_inc(v_config_1130_);
lean_dec_ref(v_lib_1126_);
v_toLeanConfig_1131_ = lean_ctor_get(v_config_1130_, 0);
lean_inc_ref(v_toLeanConfig_1131_);
lean_dec(v_config_1130_);
v_weakLeancArgs_1132_ = lean_ctor_get(v_toLeanConfig_1129_, 5);
lean_inc_ref(v_weakLeancArgs_1132_);
lean_dec_ref(v_toLeanConfig_1129_);
v_weakLeancArgs_1133_ = lean_ctor_get(v_toLeanConfig_1131_, 5);
lean_inc_ref(v_weakLeancArgs_1133_);
lean_dec_ref(v_toLeanConfig_1131_);
v___x_1134_ = l_Array_append___redArg(v_weakLeancArgs_1132_, v_weakLeancArgs_1133_);
lean_dec_ref(v_weakLeancArgs_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1135_){
_start:
{
lean_object* v_lib_1136_; lean_object* v_pkg_1137_; lean_object* v_config_1138_; lean_object* v_toLeanConfig_1139_; lean_object* v_config_1140_; lean_object* v_toLeanConfig_1141_; lean_object* v_moreLinkArgs_1142_; lean_object* v_moreLinkArgs_1143_; lean_object* v___x_1144_; 
v_lib_1136_ = lean_ctor_get(v_self_1135_, 0);
lean_inc_ref(v_lib_1136_);
lean_dec_ref(v_self_1135_);
v_pkg_1137_ = lean_ctor_get(v_lib_1136_, 0);
v_config_1138_ = lean_ctor_get(v_pkg_1137_, 6);
v_toLeanConfig_1139_ = lean_ctor_get(v_config_1138_, 1);
lean_inc_ref(v_toLeanConfig_1139_);
v_config_1140_ = lean_ctor_get(v_lib_1136_, 2);
lean_inc(v_config_1140_);
lean_dec_ref(v_lib_1136_);
v_toLeanConfig_1141_ = lean_ctor_get(v_config_1140_, 0);
lean_inc_ref(v_toLeanConfig_1141_);
lean_dec(v_config_1140_);
v_moreLinkArgs_1142_ = lean_ctor_get(v_toLeanConfig_1139_, 8);
lean_inc_ref(v_moreLinkArgs_1142_);
lean_dec_ref(v_toLeanConfig_1139_);
v_moreLinkArgs_1143_ = lean_ctor_get(v_toLeanConfig_1141_, 8);
lean_inc_ref(v_moreLinkArgs_1143_);
lean_dec_ref(v_toLeanConfig_1141_);
v___x_1144_ = l_Array_append___redArg(v_moreLinkArgs_1142_, v_moreLinkArgs_1143_);
lean_dec_ref(v_moreLinkArgs_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1145_){
_start:
{
lean_object* v_lib_1146_; lean_object* v_pkg_1147_; lean_object* v_config_1148_; lean_object* v_toLeanConfig_1149_; lean_object* v_config_1150_; lean_object* v_toLeanConfig_1151_; lean_object* v_weakLinkArgs_1152_; lean_object* v_weakLinkArgs_1153_; lean_object* v___x_1154_; 
v_lib_1146_ = lean_ctor_get(v_self_1145_, 0);
lean_inc_ref(v_lib_1146_);
lean_dec_ref(v_self_1145_);
v_pkg_1147_ = lean_ctor_get(v_lib_1146_, 0);
v_config_1148_ = lean_ctor_get(v_pkg_1147_, 6);
v_toLeanConfig_1149_ = lean_ctor_get(v_config_1148_, 1);
lean_inc_ref(v_toLeanConfig_1149_);
v_config_1150_ = lean_ctor_get(v_lib_1146_, 2);
lean_inc(v_config_1150_);
lean_dec_ref(v_lib_1146_);
v_toLeanConfig_1151_ = lean_ctor_get(v_config_1150_, 0);
lean_inc_ref(v_toLeanConfig_1151_);
lean_dec(v_config_1150_);
v_weakLinkArgs_1152_ = lean_ctor_get(v_toLeanConfig_1149_, 9);
lean_inc_ref(v_weakLinkArgs_1152_);
lean_dec_ref(v_toLeanConfig_1149_);
v_weakLinkArgs_1153_ = lean_ctor_get(v_toLeanConfig_1151_, 9);
lean_inc_ref(v_weakLinkArgs_1153_);
lean_dec_ref(v_toLeanConfig_1151_);
v___x_1154_ = l_Array_append___redArg(v_weakLinkArgs_1152_, v_weakLinkArgs_1153_);
lean_dec_ref(v_weakLinkArgs_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1156_){
_start:
{
lean_object* v_lib_1157_; lean_object* v_pkg_1158_; lean_object* v_config_1159_; uint8_t v_bootstrap_1160_; 
v_lib_1157_ = lean_ctor_get(v_self_1156_, 0);
lean_inc_ref(v_lib_1157_);
lean_dec_ref(v_self_1156_);
v_pkg_1158_ = lean_ctor_get(v_lib_1157_, 0);
lean_inc_ref(v_pkg_1158_);
lean_dec_ref(v_lib_1157_);
v_config_1159_ = lean_ctor_get(v_pkg_1158_, 6);
lean_inc_ref(v_config_1159_);
v_bootstrap_1160_ = lean_ctor_get_uint8(v_config_1159_, sizeof(void*)*27);
if (v_bootstrap_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_config_1159_);
lean_dec_ref(v_pkg_1158_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
else
{
lean_object* v_dir_1162_; lean_object* v_buildDir_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_dir_1162_ = lean_ctor_get(v_pkg_1158_, 4);
lean_inc_ref(v_dir_1162_);
lean_dec_ref(v_pkg_1158_);
v_buildDir_1163_ = lean_ctor_get(v_config_1159_, 5);
lean_inc_ref(v_buildDir_1163_);
lean_dec_ref(v_config_1159_);
v___x_1164_ = l_System_FilePath_normalize(v_buildDir_1163_);
v___x_1165_ = l_Lake_joinRelative(v_dir_1162_, v___x_1164_);
v___x_1166_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1167_ = l_Lake_joinRelative(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1169_){
_start:
{
lean_object* v_lib_1170_; lean_object* v_config_1171_; lean_object* v_toLeanConfig_1172_; lean_object* v_platformIndependent_1173_; 
v_lib_1170_ = lean_ctor_get(v_self_1169_, 0);
v_config_1171_ = lean_ctor_get(v_lib_1170_, 2);
v_toLeanConfig_1172_ = lean_ctor_get(v_config_1171_, 0);
v_platformIndependent_1173_ = lean_ctor_get(v_toLeanConfig_1172_, 10);
if (lean_obj_tag(v_platformIndependent_1173_) == 0)
{
lean_object* v_pkg_1174_; lean_object* v_config_1175_; lean_object* v_toLeanConfig_1176_; lean_object* v_platformIndependent_1177_; 
v_pkg_1174_ = lean_ctor_get(v_lib_1170_, 0);
v_config_1175_ = lean_ctor_get(v_pkg_1174_, 6);
v_toLeanConfig_1176_ = lean_ctor_get(v_config_1175_, 1);
v_platformIndependent_1177_ = lean_ctor_get(v_toLeanConfig_1176_, 10);
lean_inc(v_platformIndependent_1177_);
return v_platformIndependent_1177_;
}
else
{
lean_inc_ref(v_platformIndependent_1173_);
return v_platformIndependent_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lake_Module_platformIndependent(v_self_1178_);
lean_dec_ref(v_self_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1180_){
_start:
{
lean_object* v_lib_1181_; lean_object* v_pkg_1182_; lean_object* v_config_1183_; uint8_t v_precompileModules_1184_; 
v_lib_1181_ = lean_ctor_get(v_self_1180_, 0);
v_pkg_1182_ = lean_ctor_get(v_lib_1181_, 0);
v_config_1183_ = lean_ctor_get(v_pkg_1182_, 6);
v_precompileModules_1184_ = lean_ctor_get_uint8(v_config_1183_, sizeof(void*)*27 + 1);
if (v_precompileModules_1184_ == 0)
{
lean_object* v_config_1185_; uint8_t v_precompileModules_1186_; 
v_config_1185_ = lean_ctor_get(v_lib_1181_, 2);
v_precompileModules_1186_ = lean_ctor_get_uint8(v_config_1185_, sizeof(void*)*9 + 1);
return v_precompileModules_1186_;
}
else
{
return v_precompileModules_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Lake_Module_shouldPrecompile(v_self_1187_);
lean_dec_ref(v_self_1187_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1190_, uint8_t v_shouldExport_1191_){
_start:
{
lean_object* v_lib_1192_; lean_object* v_config_1193_; lean_object* v_nativeFacets_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_lib_1192_ = lean_ctor_get(v_self_1190_, 0);
lean_inc_ref(v_lib_1192_);
lean_dec_ref(v_self_1190_);
v_config_1193_ = lean_ctor_get(v_lib_1192_, 2);
lean_inc(v_config_1193_);
lean_dec_ref(v_lib_1192_);
v_nativeFacets_1194_ = lean_ctor_get(v_config_1193_, 8);
lean_inc_ref(v_nativeFacets_1194_);
lean_dec(v_config_1193_);
v___x_1195_ = lean_box(v_shouldExport_1191_);
v___x_1196_ = lean_apply_1(v_nativeFacets_1194_, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1197_, lean_object* v_shouldExport_1198_){
_start:
{
uint8_t v_shouldExport_boxed_1199_; lean_object* v_res_1200_; 
v_shouldExport_boxed_1199_ = lean_unbox(v_shouldExport_1198_);
v_res_1200_ = l_Lake_Module_nativeFacets(v_self_1197_, v_shouldExport_boxed_1199_);
return v_res_1200_;
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
