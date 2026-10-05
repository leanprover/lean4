// Lean compiler output
// Module: Lake.Config.Module
// Imports: public import Lake.Config.LeanLib public import Lean.Compiler.Options
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
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_LeanOptions_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instOrdBuildType_ord(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_Package_id_x3f(lean_object*);
lean_object* l_Lean_mkModuleInitializationStem(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Module_irTraceFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ir.trace"};
static const lean_object* l_Lake_Module_irTraceFile___closed__0 = (const lean_object*)&l_Lake_Module_irTraceFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_irTraceFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object*);
static const lean_string_object l_Lake_Module_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setup.json"};
static const lean_object* l_Lake_Module_setupFile___closed__0 = (const lean_object*)&l_Lake_Module_setupFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object*);
static const lean_string_object l_Lake_Module_irSetupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "irsetup.json"};
static const lean_object* l_Lake_Module_irSetupFile___closed__0 = (const lean_object*)&l_Lake_Module_irSetupFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Module_irSetupFile(lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_Module_postponeCompile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_postponeCompile___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(lean_object* v_s_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_string_utf8_byte_size(v_s_85_);
v___x_87_ = lean_unsigned_to_nat(5u);
v___x_88_ = lean_nat_dec_le(v___x_87_, v___x_86_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec_ref(v_s_85_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_90_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0));
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_nat_sub(v___x_86_, v___x_87_);
v___x_93_ = lean_string_memcmp(v_s_85_, v___x_90_, v___x_92_, v___x_91_, v___x_87_);
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
lean_ctor_set(v___x_95_, 2, v___x_86_);
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
size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((size_t)0ULL);
v___x_240_ = lean_usize_of_nat(v___x_237_);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_229_, v_targetDecls_234_, v___x_239_, v___x_240_, v___x_236_);
lean_dec_ref(v_targetDecls_234_);
v___y_231_ = v___x_241_;
goto v___jp_230_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(lean_object* v_mod_242_, lean_object* v_as_243_, lean_object* v_i_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_242_, v_as_243_, v_i_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(lean_object* v_mod_247_, lean_object* v_as_248_, lean_object* v_i_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_247_, v_as_248_, v_i_249_, v_a_250_);
lean_dec_ref(v_as_248_);
return v_res_251_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object* v_x_252_, lean_object* v_x_253_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_x_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object* v___x_264_, lean_object* v_f_265_, lean_object* v_x_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l_Lean_Name_append(v___x_264_, v_x_266_);
v___x_270_ = lean_apply_3(v_f_265_, v___x_269_, v___y_267_, lean_box(0));
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object* v___x_271_, lean_object* v_f_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_271_, v_f_272_, v_x_273_, v___y_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object* v_f_280_, lean_object* v_as_281_, size_t v_sz_282_, size_t v_i_283_, lean_object* v_b_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_a_288_; lean_object* v_snd_289_; uint8_t v___x_293_; 
v___x_293_ = lean_usize_dec_lt(v_i_283_, v_sz_282_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v_f_280_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_b_284_);
lean_ctor_set(v___x_294_, 1, v___y_285_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v_a_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_296_ = lean_box(0);
v_a_297_ = lean_array_uget_borrowed(v_as_281_, v_i_283_);
lean_inc(v_a_297_);
v___x_298_ = l_IO_FS_DirEntry_path(v_a_297_);
v___x_299_ = l_System_FilePath_isDir(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = l_System_FilePath_extension(v___x_298_);
v___x_301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1));
v___x_302_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
if (v___x_302_ == 0)
{
v_a_288_ = v___x_296_;
v_snd_289_ = v___y_285_;
goto v___jp_287_;
}
else
{
lean_object* v_fileName_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_fileName_303_ = lean_ctor_get(v_a_297_, 1);
v___x_304_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc_ref(v_fileName_303_);
v___x_305_ = l_System_FilePath_withExtension(v_fileName_303_, v___x_304_);
v___x_306_ = lean_box(0);
v___x_307_ = l_Lean_Name_str___override(v___x_306_, v___x_305_);
lean_inc_ref(v_f_280_);
v___x_308_ = lean_apply_3(v_f_280_, v___x_307_, v___y_285_, lean_box(0));
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v_snd_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
v_snd_310_ = lean_ctor_get(v_a_309_, 1);
lean_inc(v_snd_310_);
lean_dec(v_a_309_);
v_a_288_ = v___x_296_;
v_snd_289_ = v_snd_310_;
goto v___jp_287_;
}
else
{
lean_dec_ref(v_f_280_);
return v___x_308_;
}
}
}
else
{
lean_object* v_fileName_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v_fileName_311_ = lean_ctor_get(v_a_297_, 1);
v___x_312_ = lean_box(0);
lean_inc_ref(v_fileName_311_);
v___x_313_ = l_Lean_Name_str___override(v___x_312_, v_fileName_311_);
lean_inc_ref(v_f_280_);
v___f_314_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_314_, 0, v___x_313_);
lean_closure_set(v___f_314_, 1, v_f_280_);
v___x_315_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_298_, v___f_314_, v___y_285_);
lean_dec_ref(v___x_298_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v_snd_317_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v_snd_317_ = lean_ctor_get(v_a_316_, 1);
lean_inc(v_snd_317_);
lean_dec(v_a_316_);
v_a_288_ = v___x_296_;
v_snd_289_ = v_snd_317_;
goto v___jp_287_;
}
else
{
lean_dec_ref(v_f_280_);
return v___x_315_;
}
}
}
v___jp_287_:
{
size_t v___x_290_; size_t v___x_291_; 
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_add(v_i_283_, v___x_290_);
v_i_283_ = v___x_291_;
v_b_284_ = v_a_288_;
v___y_285_ = v_snd_289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object* v_dir_318_, lean_object* v_f_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_io_read_dir(v_dir_318_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; size_t v_sz_325_; size_t v___x_326_; lean_object* v___x_327_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = lean_box(0);
v_sz_325_ = lean_array_size(v_a_323_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_319_, v_a_323_, v_sz_325_, v___x_326_, v___x_324_, v___y_320_);
lean_dec(v_a_323_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_344_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_344_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_344_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_344_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_342_; 
v_snd_332_ = lean_ctor_get(v_a_328_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_328_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v_a_328_, 0);
lean_dec(v_unused_343_);
v___x_334_ = v_a_328_;
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_dec(v_a_328_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_324_);
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_snd_332_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_337_);
v___x_339_ = v___x_330_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
else
{
return v___x_327_;
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v___y_320_);
lean_dec_ref(v_f_319_);
v_a_345_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_322_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_322_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object* v_dir_353_, lean_object* v_f_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_353_, v_f_354_, v___y_355_);
lean_dec_ref(v_dir_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object* v_f_358_, lean_object* v_as_359_, lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
size_t v_sz_boxed_365_; size_t v_i_boxed_366_; lean_object* v_res_367_; 
v_sz_boxed_365_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_366_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_358_, v_as_359_, v_sz_boxed_365_, v_i_boxed_366_, v_b_362_, v___y_363_);
lean_dec_ref(v_as_359_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object* v_self_368_, lean_object* v_mod_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_self_368_);
lean_ctor_set(v___x_373_, 1, v_mod_369_);
v___x_374_ = lean_array_push(v___y_370_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_372_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object* v_self_377_, lean_object* v_mod_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_377_, v_mod_378_, v___y_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object* v_a_382_, lean_object* v___f_383_, lean_object* v_x_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = l_Lean_Name_append(v_a_382_, v_x_384_);
v___x_388_ = lean_apply_3(v___f_383_, v___x_387_, v___y_385_, lean_box(0));
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object* v_a_389_, lean_object* v___f_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_389_, v___f_390_, v_x_391_, v___y_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object* v_self_395_, lean_object* v_as_396_, size_t v_i_397_, size_t v_stop_398_, lean_object* v_b_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___y_403_; uint8_t v___x_410_; 
v___x_410_ = lean_usize_dec_eq(v_i_397_, v_stop_398_);
if (v___x_410_ == 0)
{
lean_object* v_pkg_411_; lean_object* v_config_412_; lean_object* v_config_413_; lean_object* v_dir_414_; lean_object* v_srcDir_415_; lean_object* v_srcDir_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_pkg_411_ = lean_ctor_get(v_self_395_, 0);
v_config_412_ = lean_ctor_get(v_pkg_411_, 6);
v_config_413_ = lean_ctor_get(v_self_395_, 2);
v_dir_414_ = lean_ctor_get(v_pkg_411_, 4);
v_srcDir_415_ = lean_ctor_get(v_config_412_, 4);
v_srcDir_416_ = lean_ctor_get(v_config_413_, 1);
lean_inc_ref(v_self_395_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(v___f_417_, 0, v_self_395_);
v___x_418_ = lean_array_uget_borrowed(v_as_396_, v_i_397_);
lean_inc_ref(v_srcDir_415_);
v___x_419_ = l_System_FilePath_normalize(v_srcDir_415_);
lean_inc_ref(v_dir_414_);
v___x_420_ = l_Lake_joinRelative(v_dir_414_, v___x_419_);
lean_inc_ref(v_srcDir_416_);
v___x_421_ = l_System_FilePath_normalize(v_srcDir_416_);
v___x_422_ = l_Lake_joinRelative(v___x_420_, v___x_421_);
switch(lean_obj_tag(v___x_418_))
{
case 0:
{
lean_object* v_a_423_; lean_object* v___x_424_; 
lean_dec_ref(v___x_422_);
lean_dec_ref(v___f_417_);
v_a_423_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_423_);
lean_inc_ref(v_self_395_);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_395_, v_a_423_, v___y_400_);
v___y_403_ = v___x_424_;
goto v___jp_402_;
}
case 1:
{
lean_object* v_a_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_a_425_ = lean_ctor_get(v___x_418_, 0);
lean_inc_n(v_a_425_, 2);
v___f_426_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_426_, 0, v_a_425_);
lean_closure_set(v___f_426_, 1, v___f_417_);
v___x_427_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_428_ = l_Lean_modToFilePath(v___x_422_, v_a_425_, v___x_427_);
lean_dec_ref(v___x_422_);
v___x_429_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_428_, v___f_426_, v___y_400_);
lean_dec_ref(v___x_428_);
v___y_403_ = v___x_429_;
goto v___jp_402_;
}
default: 
{
lean_object* v_a_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_418_, 0);
lean_inc_n(v_a_430_, 2);
v___f_431_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_431_, 0, v_a_430_);
lean_closure_set(v___f_431_, 1, v___f_417_);
lean_inc_ref(v_self_395_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_395_, v_a_430_, v___y_400_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v_snd_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v_snd_434_ = lean_ctor_get(v_a_433_, 1);
lean_inc(v_snd_434_);
lean_dec(v_a_433_);
v___x_435_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc(v_a_430_);
v___x_436_ = l_Lean_modToFilePath(v___x_422_, v_a_430_, v___x_435_);
lean_dec_ref(v___x_422_);
v___x_437_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_436_, v___f_431_, v_snd_434_);
lean_dec_ref(v___x_436_);
v___y_403_ = v___x_437_;
goto v___jp_402_;
}
else
{
lean_dec_ref(v___f_431_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v_self_395_);
return v___x_432_;
}
}
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref(v_self_395_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_b_399_);
lean_ctor_set(v___x_438_, 1, v___y_400_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
v___jp_402_:
{
if (lean_obj_tag(v___y_403_) == 0)
{
lean_object* v_a_404_; lean_object* v_fst_405_; lean_object* v_snd_406_; size_t v___x_407_; size_t v___x_408_; 
v_a_404_ = lean_ctor_get(v___y_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___y_403_, 1);
v_fst_405_ = lean_ctor_get(v_a_404_, 0);
lean_inc(v_fst_405_);
v_snd_406_ = lean_ctor_get(v_a_404_, 1);
lean_inc(v_snd_406_);
lean_dec(v_a_404_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_397_, v___x_407_);
v_i_397_ = v___x_408_;
v_b_399_ = v_fst_405_;
v___y_400_ = v_snd_406_;
goto _start;
}
else
{
lean_dec_ref(v_self_395_);
return v___y_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object* v_self_440_, lean_object* v_as_441_, lean_object* v_i_442_, lean_object* v_stop_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
size_t v_i_boxed_447_; size_t v_stop_boxed_448_; lean_object* v_res_449_; 
v_i_boxed_447_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_stop_boxed_448_ = lean_unbox_usize(v_stop_443_);
lean_dec(v_stop_443_);
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_440_, v_as_441_, v_i_boxed_447_, v_stop_boxed_448_, v_b_444_, v___y_445_);
lean_dec_ref(v_as_441_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object* v_self_452_){
_start:
{
lean_object* v___y_455_; lean_object* v_config_473_; lean_object* v_globs_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_config_473_ = lean_ctor_get(v_self_452_, 2);
v_globs_474_ = lean_ctor_get(v_config_473_, 3);
lean_inc_ref(v_globs_474_);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_array_get_size(v_globs_474_);
v___x_477_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_478_ = lean_nat_dec_lt(v___x_475_, v___x_476_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_globs_474_);
lean_dec_ref(v_self_452_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_nat_dec_le(v___x_476_, v___x_476_);
if (v___x_481_ == 0)
{
if (v___x_478_ == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v_globs_474_);
lean_dec_ref(v_self_452_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_477_);
return v___x_482_;
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_476_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_452_, v_globs_474_, v___x_483_, v___x_484_, v___x_480_, v___x_477_);
lean_dec_ref(v_globs_474_);
v___y_455_ = v___x_485_;
goto v___jp_454_;
}
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_476_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_452_, v_globs_474_, v___x_486_, v___x_487_, v___x_480_, v___x_477_);
lean_dec_ref(v_globs_474_);
v___y_455_ = v___x_488_;
goto v___jp_454_;
}
}
v___jp_454_:
{
if (lean_obj_tag(v___y_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_a_456_ = lean_ctor_get(v___y_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___y_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v___y_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___y_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_snd_460_; lean_object* v___x_462_; 
v_snd_460_ = lean_ctor_get(v_a_456_, 1);
lean_inc(v_snd_460_);
lean_dec(v_a_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_snd_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_snd_460_);
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
v_a_465_ = lean_ctor_get(v___y_455_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___y_455_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___y_455_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___y_455_);
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
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object* v_self_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lake_LeanLib_getModuleArray(v_self_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object* v_self_492_, lean_object* v_as_493_, size_t v_i_494_, size_t v_stop_495_, lean_object* v_b_496_){
_start:
{
lean_object* v___y_498_; uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_eq(v_i_494_, v_stop_495_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_array_uget_borrowed(v_as_493_, v_i_494_);
lean_inc_ref(v_self_492_);
lean_inc(v___x_503_);
v___x_504_ = l_Lake_LeanLib_findModule_x3f(v___x_503_, v_self_492_);
if (lean_obj_tag(v___x_504_) == 0)
{
v___y_498_ = v_b_496_;
goto v___jp_497_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; 
v_val_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_val_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_array_push(v_b_496_, v_val_505_);
v___y_498_ = v___x_506_;
goto v___jp_497_;
}
}
else
{
lean_dec_ref(v_self_492_);
return v_b_496_;
}
v___jp_497_:
{
size_t v___x_499_; size_t v___x_500_; 
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_494_, v___x_499_);
v_i_494_ = v___x_500_;
v_b_496_ = v___y_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object* v_self_507_, lean_object* v_as_508_, lean_object* v_i_509_, lean_object* v_stop_510_, lean_object* v_b_511_){
_start:
{
size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_510_);
lean_dec(v_stop_510_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_507_, v_as_508_, v_i_boxed_512_, v_stop_boxed_513_, v_b_511_);
lean_dec_ref(v_as_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object* v_self_515_, lean_object* v_as_516_, lean_object* v_start_517_, lean_object* v_stop_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_520_ = lean_nat_dec_lt(v_start_517_, v_stop_518_);
if (v___x_520_ == 0)
{
lean_dec_ref(v_self_515_);
return v___x_519_;
}
else
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_as_516_);
v___x_522_ = lean_nat_dec_le(v_stop_518_, v___x_521_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; 
v___x_523_ = lean_nat_dec_lt(v_start_517_, v___x_521_);
if (v___x_523_ == 0)
{
lean_dec_ref(v_self_515_);
return v___x_519_;
}
else
{
size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_usize_of_nat(v_start_517_);
v___x_525_ = lean_usize_of_nat(v___x_521_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_515_, v_as_516_, v___x_524_, v___x_525_, v___x_519_);
return v___x_526_;
}
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_usize_of_nat(v_start_517_);
v___x_528_ = lean_usize_of_nat(v_stop_518_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_515_, v_as_516_, v___x_527_, v___x_528_, v___x_519_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object* v_self_530_, lean_object* v_as_531_, lean_object* v_start_532_, lean_object* v_stop_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_530_, v_as_531_, v_start_532_, v_stop_533_);
lean_dec(v_stop_533_);
lean_dec(v_start_532_);
lean_dec_ref(v_as_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* v_self_535_){
_start:
{
lean_object* v_config_536_; lean_object* v_roots_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_config_536_ = lean_ctor_get(v_self_535_, 2);
v_roots_537_ = lean_ctor_get(v_config_536_, 2);
lean_inc_ref(v_roots_537_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_roots_537_);
v___x_540_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_535_, v_roots_537_, v___x_538_, v___x_539_);
lean_dec_ref(v_roots_537_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* v_self_541_){
_start:
{
lean_object* v_lib_542_; lean_object* v_pkg_543_; 
v_lib_542_ = lean_ctor_get(v_self_541_, 0);
v_pkg_543_ = lean_ctor_get(v_lib_542_, 0);
lean_inc_ref(v_pkg_543_);
return v_pkg_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* v_self_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lake_Module_pkg(v_self_544_);
lean_dec_ref(v_self_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* v_self_546_){
_start:
{
lean_object* v_lib_547_; lean_object* v_pkg_548_; lean_object* v_config_549_; lean_object* v_config_550_; lean_object* v_dir_551_; lean_object* v_srcDir_552_; lean_object* v_srcDir_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_lib_547_ = lean_ctor_get(v_self_546_, 0);
lean_inc_ref(v_lib_547_);
lean_dec_ref(v_self_546_);
v_pkg_548_ = lean_ctor_get(v_lib_547_, 0);
lean_inc_ref(v_pkg_548_);
v_config_549_ = lean_ctor_get(v_pkg_548_, 6);
lean_inc_ref(v_config_549_);
v_config_550_ = lean_ctor_get(v_lib_547_, 2);
lean_inc(v_config_550_);
lean_dec_ref(v_lib_547_);
v_dir_551_ = lean_ctor_get(v_pkg_548_, 4);
lean_inc_ref(v_dir_551_);
lean_dec_ref(v_pkg_548_);
v_srcDir_552_ = lean_ctor_get(v_config_549_, 4);
lean_inc_ref(v_srcDir_552_);
lean_dec_ref(v_config_549_);
v_srcDir_553_ = lean_ctor_get(v_config_550_, 1);
lean_inc_ref(v_srcDir_553_);
lean_dec(v_config_550_);
v___x_554_ = l_System_FilePath_normalize(v_srcDir_552_);
v___x_555_ = l_Lake_joinRelative(v_dir_551_, v___x_554_);
v___x_556_ = l_System_FilePath_normalize(v_srcDir_553_);
v___x_557_ = l_Lake_joinRelative(v___x_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object* v_ext_558_, lean_object* v_self_559_){
_start:
{
lean_object* v_name_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_name_560_ = lean_ctor_get(v_self_559_, 1);
v___x_561_ = l_Lean_Name_getString_x21(v_name_560_);
v___x_562_ = l_System_FilePath_addExtension(v___x_561_, v_ext_558_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object* v_ext_563_, lean_object* v_self_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lake_Module_fileName(v_ext_563_, v_self_564_);
lean_dec_ref(v_self_564_);
lean_dec_ref(v_ext_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_566_, lean_object* v_ext_567_, lean_object* v_self_568_){
_start:
{
lean_object* v_name_569_; lean_object* v___x_570_; 
v_name_569_ = lean_ctor_get(v_self_568_, 1);
lean_inc(v_name_569_);
lean_dec_ref(v_self_568_);
v___x_570_ = l_Lean_modToFilePath(v_dir_566_, v_name_569_, v_ext_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_571_, lean_object* v_ext_572_, lean_object* v_self_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lake_Module_filePath(v_dir_571_, v_ext_572_, v_self_573_);
lean_dec_ref(v_ext_572_);
lean_dec_ref(v_dir_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_575_, lean_object* v_self_576_){
_start:
{
lean_object* v_lib_577_; lean_object* v_pkg_578_; lean_object* v_config_579_; lean_object* v_config_580_; lean_object* v_name_581_; lean_object* v_dir_582_; lean_object* v_srcDir_583_; lean_object* v_srcDir_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_lib_577_ = lean_ctor_get(v_self_576_, 0);
v_pkg_578_ = lean_ctor_get(v_lib_577_, 0);
lean_inc_ref(v_pkg_578_);
v_config_579_ = lean_ctor_get(v_pkg_578_, 6);
lean_inc_ref(v_config_579_);
v_config_580_ = lean_ctor_get(v_lib_577_, 2);
lean_inc(v_config_580_);
v_name_581_ = lean_ctor_get(v_self_576_, 1);
lean_inc(v_name_581_);
lean_dec_ref(v_self_576_);
v_dir_582_ = lean_ctor_get(v_pkg_578_, 4);
lean_inc_ref(v_dir_582_);
lean_dec_ref(v_pkg_578_);
v_srcDir_583_ = lean_ctor_get(v_config_579_, 4);
lean_inc_ref(v_srcDir_583_);
lean_dec_ref(v_config_579_);
v_srcDir_584_ = lean_ctor_get(v_config_580_, 1);
lean_inc_ref(v_srcDir_584_);
lean_dec(v_config_580_);
v___x_585_ = l_System_FilePath_normalize(v_srcDir_583_);
v___x_586_ = l_Lake_joinRelative(v_dir_582_, v___x_585_);
v___x_587_ = l_System_FilePath_normalize(v_srcDir_584_);
v___x_588_ = l_Lake_joinRelative(v___x_586_, v___x_587_);
v___x_589_ = l_Lean_modToFilePath(v___x_588_, v_name_581_, v_ext_575_);
lean_dec_ref(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_590_, lean_object* v_self_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lake_Module_srcPath(v_ext_590_, v_self_591_);
lean_dec_ref(v_ext_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_593_){
_start:
{
lean_object* v_lib_594_; lean_object* v_pkg_595_; lean_object* v_config_596_; lean_object* v_config_597_; lean_object* v_name_598_; lean_object* v_dir_599_; lean_object* v_srcDir_600_; lean_object* v_srcDir_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_lib_594_ = lean_ctor_get(v_self_593_, 0);
v_pkg_595_ = lean_ctor_get(v_lib_594_, 0);
lean_inc_ref(v_pkg_595_);
v_config_596_ = lean_ctor_get(v_pkg_595_, 6);
lean_inc_ref(v_config_596_);
v_config_597_ = lean_ctor_get(v_lib_594_, 2);
lean_inc(v_config_597_);
v_name_598_ = lean_ctor_get(v_self_593_, 1);
lean_inc(v_name_598_);
lean_dec_ref(v_self_593_);
v_dir_599_ = lean_ctor_get(v_pkg_595_, 4);
lean_inc_ref(v_dir_599_);
lean_dec_ref(v_pkg_595_);
v_srcDir_600_ = lean_ctor_get(v_config_596_, 4);
lean_inc_ref(v_srcDir_600_);
lean_dec_ref(v_config_596_);
v_srcDir_601_ = lean_ctor_get(v_config_597_, 1);
lean_inc_ref(v_srcDir_601_);
lean_dec(v_config_597_);
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_603_ = l_System_FilePath_normalize(v_srcDir_600_);
v___x_604_ = l_Lake_joinRelative(v_dir_599_, v___x_603_);
v___x_605_ = l_System_FilePath_normalize(v_srcDir_601_);
v___x_606_ = l_Lake_joinRelative(v___x_604_, v___x_605_);
v___x_607_ = l_Lean_modToFilePath(v___x_606_, v_name_598_, v___x_602_);
lean_dec_ref(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_608_){
_start:
{
lean_object* v_lib_609_; lean_object* v_pkg_610_; lean_object* v_config_611_; lean_object* v_config_612_; lean_object* v_name_613_; lean_object* v_dir_614_; lean_object* v_srcDir_615_; lean_object* v_srcDir_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_lib_609_ = lean_ctor_get(v_self_608_, 0);
v_pkg_610_ = lean_ctor_get(v_lib_609_, 0);
lean_inc_ref(v_pkg_610_);
v_config_611_ = lean_ctor_get(v_pkg_610_, 6);
lean_inc_ref(v_config_611_);
v_config_612_ = lean_ctor_get(v_lib_609_, 2);
lean_inc(v_config_612_);
v_name_613_ = lean_ctor_get(v_self_608_, 1);
lean_inc(v_name_613_);
lean_dec_ref(v_self_608_);
v_dir_614_ = lean_ctor_get(v_pkg_610_, 4);
lean_inc_ref_n(v_dir_614_, 2);
lean_dec_ref(v_pkg_610_);
v_srcDir_615_ = lean_ctor_get(v_config_611_, 4);
lean_inc_ref(v_srcDir_615_);
lean_dec_ref(v_config_611_);
v_srcDir_616_ = lean_ctor_get(v_config_612_, 1);
lean_inc_ref(v_srcDir_616_);
lean_dec(v_config_612_);
v___x_617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_618_ = l_System_FilePath_normalize(v_srcDir_615_);
v___x_619_ = l_Lake_joinRelative(v_dir_614_, v___x_618_);
v___x_620_ = l_System_FilePath_normalize(v_srcDir_616_);
v___x_621_ = l_Lake_joinRelative(v___x_619_, v___x_620_);
v___x_622_ = l_Lean_modToFilePath(v___x_621_, v_name_613_, v___x_617_);
lean_dec_ref(v___x_621_);
v___x_623_ = l_Lake_relPathFrom(v_dir_614_, v___x_622_);
lean_dec_ref(v_dir_614_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_624_, lean_object* v_self_625_){
_start:
{
lean_object* v_lib_626_; lean_object* v_pkg_627_; lean_object* v_config_628_; lean_object* v_name_629_; lean_object* v_dir_630_; lean_object* v_buildDir_631_; lean_object* v_leanLibDir_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_lib_626_ = lean_ctor_get(v_self_625_, 0);
v_pkg_627_ = lean_ctor_get(v_lib_626_, 0);
lean_inc_ref(v_pkg_627_);
v_config_628_ = lean_ctor_get(v_pkg_627_, 6);
lean_inc_ref(v_config_628_);
v_name_629_ = lean_ctor_get(v_self_625_, 1);
lean_inc(v_name_629_);
lean_dec_ref(v_self_625_);
v_dir_630_ = lean_ctor_get(v_pkg_627_, 4);
lean_inc_ref(v_dir_630_);
lean_dec_ref(v_pkg_627_);
v_buildDir_631_ = lean_ctor_get(v_config_628_, 5);
lean_inc_ref(v_buildDir_631_);
v_leanLibDir_632_ = lean_ctor_get(v_config_628_, 6);
lean_inc_ref(v_leanLibDir_632_);
lean_dec_ref(v_config_628_);
v___x_633_ = l_System_FilePath_normalize(v_buildDir_631_);
v___x_634_ = l_Lake_joinRelative(v_dir_630_, v___x_633_);
v___x_635_ = l_System_FilePath_normalize(v_leanLibDir_632_);
v___x_636_ = l_Lake_joinRelative(v___x_634_, v___x_635_);
v___x_637_ = l_Lean_modToFilePath(v___x_636_, v_name_629_, v_ext_624_);
lean_dec_ref(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_638_, lean_object* v_self_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lake_Module_leanLibPath(v_ext_638_, v_self_639_);
lean_dec_ref(v_ext_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object* v_self_641_){
_start:
{
lean_object* v_lib_642_; lean_object* v_pkg_643_; lean_object* v_config_644_; lean_object* v_name_645_; lean_object* v_dir_646_; lean_object* v_buildDir_647_; lean_object* v_leanLibDir_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_lib_642_ = lean_ctor_get(v_self_641_, 0);
v_pkg_643_ = lean_ctor_get(v_lib_642_, 0);
lean_inc_ref(v_pkg_643_);
v_config_644_ = lean_ctor_get(v_pkg_643_, 6);
lean_inc_ref(v_config_644_);
v_name_645_ = lean_ctor_get(v_self_641_, 1);
lean_inc(v_name_645_);
lean_dec_ref(v_self_641_);
v_dir_646_ = lean_ctor_get(v_pkg_643_, 4);
lean_inc_ref(v_dir_646_);
lean_dec_ref(v_pkg_643_);
v_buildDir_647_ = lean_ctor_get(v_config_644_, 5);
lean_inc_ref(v_buildDir_647_);
v_leanLibDir_648_ = lean_ctor_get(v_config_644_, 6);
lean_inc_ref(v_leanLibDir_648_);
lean_dec_ref(v_config_644_);
v___x_649_ = l_System_FilePath_normalize(v_buildDir_647_);
v___x_650_ = l_Lake_joinRelative(v_dir_646_, v___x_649_);
v___x_651_ = l_System_FilePath_normalize(v_leanLibDir_648_);
v___x_652_ = l_Lake_joinRelative(v___x_650_, v___x_651_);
v___x_653_ = l_Lean_Name_getPrefix(v_name_645_);
lean_dec(v_name_645_);
v___x_654_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_655_ = l_Lean_modToFilePath(v___x_652_, v___x_653_, v___x_654_);
lean_dec_ref(v___x_652_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_657_){
_start:
{
lean_object* v_lib_658_; lean_object* v_pkg_659_; lean_object* v_config_660_; lean_object* v_name_661_; lean_object* v_dir_662_; lean_object* v_buildDir_663_; lean_object* v_leanLibDir_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_lib_658_ = lean_ctor_get(v_self_657_, 0);
v_pkg_659_ = lean_ctor_get(v_lib_658_, 0);
lean_inc_ref(v_pkg_659_);
v_config_660_ = lean_ctor_get(v_pkg_659_, 6);
lean_inc_ref(v_config_660_);
v_name_661_ = lean_ctor_get(v_self_657_, 1);
lean_inc(v_name_661_);
lean_dec_ref(v_self_657_);
v_dir_662_ = lean_ctor_get(v_pkg_659_, 4);
lean_inc_ref(v_dir_662_);
lean_dec_ref(v_pkg_659_);
v_buildDir_663_ = lean_ctor_get(v_config_660_, 5);
lean_inc_ref(v_buildDir_663_);
v_leanLibDir_664_ = lean_ctor_get(v_config_660_, 6);
lean_inc_ref(v_leanLibDir_664_);
lean_dec_ref(v_config_660_);
v___x_665_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_666_ = l_System_FilePath_normalize(v_buildDir_663_);
v___x_667_ = l_Lake_joinRelative(v_dir_662_, v___x_666_);
v___x_668_ = l_System_FilePath_normalize(v_leanLibDir_664_);
v___x_669_ = l_Lake_joinRelative(v___x_667_, v___x_668_);
v___x_670_ = l_Lean_modToFilePath(v___x_669_, v_name_661_, v___x_665_);
lean_dec_ref(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_672_){
_start:
{
lean_object* v_lib_673_; lean_object* v_pkg_674_; lean_object* v_config_675_; lean_object* v_name_676_; lean_object* v_dir_677_; lean_object* v_buildDir_678_; lean_object* v_leanLibDir_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_lib_673_ = lean_ctor_get(v_self_672_, 0);
v_pkg_674_ = lean_ctor_get(v_lib_673_, 0);
lean_inc_ref(v_pkg_674_);
v_config_675_ = lean_ctor_get(v_pkg_674_, 6);
lean_inc_ref(v_config_675_);
v_name_676_ = lean_ctor_get(v_self_672_, 1);
lean_inc(v_name_676_);
lean_dec_ref(v_self_672_);
v_dir_677_ = lean_ctor_get(v_pkg_674_, 4);
lean_inc_ref(v_dir_677_);
lean_dec_ref(v_pkg_674_);
v_buildDir_678_ = lean_ctor_get(v_config_675_, 5);
lean_inc_ref(v_buildDir_678_);
v_leanLibDir_679_ = lean_ctor_get(v_config_675_, 6);
lean_inc_ref(v_leanLibDir_679_);
lean_dec_ref(v_config_675_);
v___x_680_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_681_ = l_System_FilePath_normalize(v_buildDir_678_);
v___x_682_ = l_Lake_joinRelative(v_dir_677_, v___x_681_);
v___x_683_ = l_System_FilePath_normalize(v_leanLibDir_679_);
v___x_684_ = l_Lake_joinRelative(v___x_682_, v___x_683_);
v___x_685_ = l_Lean_modToFilePath(v___x_684_, v_name_676_, v___x_680_);
lean_dec_ref(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_687_){
_start:
{
lean_object* v_lib_688_; lean_object* v_pkg_689_; lean_object* v_config_690_; lean_object* v_name_691_; lean_object* v_dir_692_; lean_object* v_buildDir_693_; lean_object* v_leanLibDir_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_lib_688_ = lean_ctor_get(v_self_687_, 0);
v_pkg_689_ = lean_ctor_get(v_lib_688_, 0);
lean_inc_ref(v_pkg_689_);
v_config_690_ = lean_ctor_get(v_pkg_689_, 6);
lean_inc_ref(v_config_690_);
v_name_691_ = lean_ctor_get(v_self_687_, 1);
lean_inc(v_name_691_);
lean_dec_ref(v_self_687_);
v_dir_692_ = lean_ctor_get(v_pkg_689_, 4);
lean_inc_ref(v_dir_692_);
lean_dec_ref(v_pkg_689_);
v_buildDir_693_ = lean_ctor_get(v_config_690_, 5);
lean_inc_ref(v_buildDir_693_);
v_leanLibDir_694_ = lean_ctor_get(v_config_690_, 6);
lean_inc_ref(v_leanLibDir_694_);
lean_dec_ref(v_config_690_);
v___x_695_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_696_ = l_System_FilePath_normalize(v_buildDir_693_);
v___x_697_ = l_Lake_joinRelative(v_dir_692_, v___x_696_);
v___x_698_ = l_System_FilePath_normalize(v_leanLibDir_694_);
v___x_699_ = l_Lake_joinRelative(v___x_697_, v___x_698_);
v___x_700_ = l_Lean_modToFilePath(v___x_699_, v_name_691_, v___x_695_);
lean_dec_ref(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_702_){
_start:
{
lean_object* v_lib_703_; lean_object* v_pkg_704_; lean_object* v_config_705_; lean_object* v_name_706_; lean_object* v_dir_707_; lean_object* v_buildDir_708_; lean_object* v_leanLibDir_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_lib_703_ = lean_ctor_get(v_self_702_, 0);
v_pkg_704_ = lean_ctor_get(v_lib_703_, 0);
lean_inc_ref(v_pkg_704_);
v_config_705_ = lean_ctor_get(v_pkg_704_, 6);
lean_inc_ref(v_config_705_);
v_name_706_ = lean_ctor_get(v_self_702_, 1);
lean_inc(v_name_706_);
lean_dec_ref(v_self_702_);
v_dir_707_ = lean_ctor_get(v_pkg_704_, 4);
lean_inc_ref(v_dir_707_);
lean_dec_ref(v_pkg_704_);
v_buildDir_708_ = lean_ctor_get(v_config_705_, 5);
lean_inc_ref(v_buildDir_708_);
v_leanLibDir_709_ = lean_ctor_get(v_config_705_, 6);
lean_inc_ref(v_leanLibDir_709_);
lean_dec_ref(v_config_705_);
v___x_710_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_711_ = l_System_FilePath_normalize(v_buildDir_708_);
v___x_712_ = l_Lake_joinRelative(v_dir_707_, v___x_711_);
v___x_713_ = l_System_FilePath_normalize(v_leanLibDir_709_);
v___x_714_ = l_Lake_joinRelative(v___x_712_, v___x_713_);
v___x_715_ = l_Lean_modToFilePath(v___x_714_, v_name_706_, v___x_710_);
lean_dec_ref(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object* v_self_717_){
_start:
{
lean_object* v_lib_718_; lean_object* v_pkg_719_; lean_object* v_config_720_; lean_object* v_name_721_; lean_object* v_dir_722_; lean_object* v_buildDir_723_; lean_object* v_leanLibDir_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_lib_718_ = lean_ctor_get(v_self_717_, 0);
v_pkg_719_ = lean_ctor_get(v_lib_718_, 0);
lean_inc_ref(v_pkg_719_);
v_config_720_ = lean_ctor_get(v_pkg_719_, 6);
lean_inc_ref(v_config_720_);
v_name_721_ = lean_ctor_get(v_self_717_, 1);
lean_inc(v_name_721_);
lean_dec_ref(v_self_717_);
v_dir_722_ = lean_ctor_get(v_pkg_719_, 4);
lean_inc_ref(v_dir_722_);
lean_dec_ref(v_pkg_719_);
v_buildDir_723_ = lean_ctor_get(v_config_720_, 5);
lean_inc_ref(v_buildDir_723_);
v_leanLibDir_724_ = lean_ctor_get(v_config_720_, 6);
lean_inc_ref(v_leanLibDir_724_);
lean_dec_ref(v_config_720_);
v___x_725_ = ((lean_object*)(l_Lake_Module_irSigFile___closed__0));
v___x_726_ = l_System_FilePath_normalize(v_buildDir_723_);
v___x_727_ = l_Lake_joinRelative(v_dir_722_, v___x_726_);
v___x_728_ = l_System_FilePath_normalize(v_leanLibDir_724_);
v___x_729_ = l_Lake_joinRelative(v___x_727_, v___x_728_);
v___x_730_ = l_Lean_modToFilePath(v___x_729_, v_name_721_, v___x_725_);
lean_dec_ref(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_732_){
_start:
{
lean_object* v_lib_733_; lean_object* v_pkg_734_; lean_object* v_config_735_; lean_object* v_name_736_; lean_object* v_dir_737_; lean_object* v_buildDir_738_; lean_object* v_leanLibDir_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
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
v_buildDir_738_ = lean_ctor_get(v_config_735_, 5);
lean_inc_ref(v_buildDir_738_);
v_leanLibDir_739_ = lean_ctor_get(v_config_735_, 6);
lean_inc_ref(v_leanLibDir_739_);
lean_dec_ref(v_config_735_);
v___x_740_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_741_ = l_System_FilePath_normalize(v_buildDir_738_);
v___x_742_ = l_Lake_joinRelative(v_dir_737_, v___x_741_);
v___x_743_ = l_System_FilePath_normalize(v_leanLibDir_739_);
v___x_744_ = l_Lake_joinRelative(v___x_742_, v___x_743_);
v___x_745_ = l_Lean_modToFilePath(v___x_744_, v_name_736_, v___x_740_);
lean_dec_ref(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_747_){
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
v_buildDir_753_ = lean_ctor_get(v_config_750_, 5);
lean_inc_ref(v_buildDir_753_);
v_leanLibDir_754_ = lean_ctor_get(v_config_750_, 6);
lean_inc_ref(v_leanLibDir_754_);
lean_dec_ref(v_config_750_);
v___x_755_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_756_ = l_System_FilePath_normalize(v_buildDir_753_);
v___x_757_ = l_Lake_joinRelative(v_dir_752_, v___x_756_);
v___x_758_ = l_System_FilePath_normalize(v_leanLibDir_754_);
v___x_759_ = l_Lake_joinRelative(v___x_757_, v___x_758_);
v___x_760_ = l_Lean_modToFilePath(v___x_759_, v_name_751_, v___x_755_);
lean_dec_ref(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irTraceFile(lean_object* v_self_762_){
_start:
{
lean_object* v_lib_763_; lean_object* v_pkg_764_; lean_object* v_config_765_; lean_object* v_name_766_; lean_object* v_dir_767_; lean_object* v_buildDir_768_; lean_object* v_leanLibDir_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
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
v_buildDir_768_ = lean_ctor_get(v_config_765_, 5);
lean_inc_ref(v_buildDir_768_);
v_leanLibDir_769_ = lean_ctor_get(v_config_765_, 6);
lean_inc_ref(v_leanLibDir_769_);
lean_dec_ref(v_config_765_);
v___x_770_ = ((lean_object*)(l_Lake_Module_irTraceFile___closed__0));
v___x_771_ = l_System_FilePath_normalize(v_buildDir_768_);
v___x_772_ = l_Lake_joinRelative(v_dir_767_, v___x_771_);
v___x_773_ = l_System_FilePath_normalize(v_leanLibDir_769_);
v___x_774_ = l_Lake_joinRelative(v___x_772_, v___x_773_);
v___x_775_ = l_Lean_modToFilePath(v___x_774_, v_name_766_, v___x_770_);
lean_dec_ref(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_776_, lean_object* v_self_777_){
_start:
{
lean_object* v_lib_778_; lean_object* v_pkg_779_; lean_object* v_config_780_; lean_object* v_name_781_; lean_object* v_dir_782_; lean_object* v_buildDir_783_; lean_object* v_irDir_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
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
v_buildDir_783_ = lean_ctor_get(v_config_780_, 5);
lean_inc_ref(v_buildDir_783_);
v_irDir_784_ = lean_ctor_get(v_config_780_, 9);
lean_inc_ref(v_irDir_784_);
lean_dec_ref(v_config_780_);
v___x_785_ = l_System_FilePath_normalize(v_buildDir_783_);
v___x_786_ = l_Lake_joinRelative(v_dir_782_, v___x_785_);
v___x_787_ = l_System_FilePath_normalize(v_irDir_784_);
v___x_788_ = l_Lake_joinRelative(v___x_786_, v___x_787_);
v___x_789_ = l_Lean_modToFilePath(v___x_788_, v_name_781_, v_ext_776_);
lean_dec_ref(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_790_, lean_object* v_self_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lake_Module_irPath(v_ext_790_, v_self_791_);
lean_dec_ref(v_ext_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_793_){
_start:
{
lean_object* v_lib_794_; lean_object* v_pkg_795_; lean_object* v_config_796_; lean_object* v_name_797_; lean_object* v_dir_798_; lean_object* v_buildDir_799_; lean_object* v_irDir_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_lib_794_ = lean_ctor_get(v_self_793_, 0);
v_pkg_795_ = lean_ctor_get(v_lib_794_, 0);
lean_inc_ref(v_pkg_795_);
v_config_796_ = lean_ctor_get(v_pkg_795_, 6);
lean_inc_ref(v_config_796_);
v_name_797_ = lean_ctor_get(v_self_793_, 1);
lean_inc(v_name_797_);
lean_dec_ref(v_self_793_);
v_dir_798_ = lean_ctor_get(v_pkg_795_, 4);
lean_inc_ref(v_dir_798_);
lean_dec_ref(v_pkg_795_);
v_buildDir_799_ = lean_ctor_get(v_config_796_, 5);
lean_inc_ref(v_buildDir_799_);
v_irDir_800_ = lean_ctor_get(v_config_796_, 9);
lean_inc_ref(v_irDir_800_);
lean_dec_ref(v_config_796_);
v___x_801_ = l_System_FilePath_normalize(v_buildDir_799_);
v___x_802_ = l_Lake_joinRelative(v_dir_798_, v___x_801_);
v___x_803_ = l_System_FilePath_normalize(v_irDir_800_);
v___x_804_ = l_Lake_joinRelative(v___x_802_, v___x_803_);
v___x_805_ = l_Lean_Name_getPrefix(v_name_797_);
lean_dec(v_name_797_);
v___x_806_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_807_ = l_Lean_modToFilePath(v___x_804_, v___x_805_, v___x_806_);
lean_dec_ref(v___x_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_809_){
_start:
{
lean_object* v_lib_810_; lean_object* v_pkg_811_; lean_object* v_config_812_; lean_object* v_name_813_; lean_object* v_dir_814_; lean_object* v_buildDir_815_; lean_object* v_irDir_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_lib_810_ = lean_ctor_get(v_self_809_, 0);
v_pkg_811_ = lean_ctor_get(v_lib_810_, 0);
lean_inc_ref(v_pkg_811_);
v_config_812_ = lean_ctor_get(v_pkg_811_, 6);
lean_inc_ref(v_config_812_);
v_name_813_ = lean_ctor_get(v_self_809_, 1);
lean_inc(v_name_813_);
lean_dec_ref(v_self_809_);
v_dir_814_ = lean_ctor_get(v_pkg_811_, 4);
lean_inc_ref(v_dir_814_);
lean_dec_ref(v_pkg_811_);
v_buildDir_815_ = lean_ctor_get(v_config_812_, 5);
lean_inc_ref(v_buildDir_815_);
v_irDir_816_ = lean_ctor_get(v_config_812_, 9);
lean_inc_ref(v_irDir_816_);
lean_dec_ref(v_config_812_);
v___x_817_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_818_ = l_System_FilePath_normalize(v_buildDir_815_);
v___x_819_ = l_Lake_joinRelative(v_dir_814_, v___x_818_);
v___x_820_ = l_System_FilePath_normalize(v_irDir_816_);
v___x_821_ = l_Lake_joinRelative(v___x_819_, v___x_820_);
v___x_822_ = l_Lean_modToFilePath(v___x_821_, v_name_813_, v___x_817_);
lean_dec_ref(v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSetupFile(lean_object* v_self_824_){
_start:
{
lean_object* v_lib_825_; lean_object* v_pkg_826_; lean_object* v_config_827_; lean_object* v_name_828_; lean_object* v_dir_829_; lean_object* v_buildDir_830_; lean_object* v_irDir_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_lib_825_ = lean_ctor_get(v_self_824_, 0);
v_pkg_826_ = lean_ctor_get(v_lib_825_, 0);
lean_inc_ref(v_pkg_826_);
v_config_827_ = lean_ctor_get(v_pkg_826_, 6);
lean_inc_ref(v_config_827_);
v_name_828_ = lean_ctor_get(v_self_824_, 1);
lean_inc(v_name_828_);
lean_dec_ref(v_self_824_);
v_dir_829_ = lean_ctor_get(v_pkg_826_, 4);
lean_inc_ref(v_dir_829_);
lean_dec_ref(v_pkg_826_);
v_buildDir_830_ = lean_ctor_get(v_config_827_, 5);
lean_inc_ref(v_buildDir_830_);
v_irDir_831_ = lean_ctor_get(v_config_827_, 9);
lean_inc_ref(v_irDir_831_);
lean_dec_ref(v_config_827_);
v___x_832_ = ((lean_object*)(l_Lake_Module_irSetupFile___closed__0));
v___x_833_ = l_System_FilePath_normalize(v_buildDir_830_);
v___x_834_ = l_Lake_joinRelative(v_dir_829_, v___x_833_);
v___x_835_ = l_System_FilePath_normalize(v_irDir_831_);
v___x_836_ = l_Lake_joinRelative(v___x_834_, v___x_835_);
v___x_837_ = l_Lean_modToFilePath(v___x_836_, v_name_828_, v___x_832_);
lean_dec_ref(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_839_){
_start:
{
lean_object* v_lib_840_; lean_object* v_pkg_841_; lean_object* v_config_842_; lean_object* v_name_843_; lean_object* v_dir_844_; lean_object* v_buildDir_845_; lean_object* v_irDir_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_lib_840_ = lean_ctor_get(v_self_839_, 0);
v_pkg_841_ = lean_ctor_get(v_lib_840_, 0);
lean_inc_ref(v_pkg_841_);
v_config_842_ = lean_ctor_get(v_pkg_841_, 6);
lean_inc_ref(v_config_842_);
v_name_843_ = lean_ctor_get(v_self_839_, 1);
lean_inc(v_name_843_);
lean_dec_ref(v_self_839_);
v_dir_844_ = lean_ctor_get(v_pkg_841_, 4);
lean_inc_ref(v_dir_844_);
lean_dec_ref(v_pkg_841_);
v_buildDir_845_ = lean_ctor_get(v_config_842_, 5);
lean_inc_ref(v_buildDir_845_);
v_irDir_846_ = lean_ctor_get(v_config_842_, 9);
lean_inc_ref(v_irDir_846_);
lean_dec_ref(v_config_842_);
v___x_847_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_848_ = l_System_FilePath_normalize(v_buildDir_845_);
v___x_849_ = l_Lake_joinRelative(v_dir_844_, v___x_848_);
v___x_850_ = l_System_FilePath_normalize(v_irDir_846_);
v___x_851_ = l_Lake_joinRelative(v___x_849_, v___x_850_);
v___x_852_ = l_Lean_modToFilePath(v___x_851_, v_name_843_, v___x_847_);
lean_dec_ref(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_854_){
_start:
{
lean_object* v_lib_855_; lean_object* v_pkg_856_; lean_object* v_config_857_; lean_object* v_name_858_; lean_object* v_dir_859_; lean_object* v_buildDir_860_; lean_object* v_irDir_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_lib_855_ = lean_ctor_get(v_self_854_, 0);
v_pkg_856_ = lean_ctor_get(v_lib_855_, 0);
lean_inc_ref(v_pkg_856_);
v_config_857_ = lean_ctor_get(v_pkg_856_, 6);
lean_inc_ref(v_config_857_);
v_name_858_ = lean_ctor_get(v_self_854_, 1);
lean_inc(v_name_858_);
lean_dec_ref(v_self_854_);
v_dir_859_ = lean_ctor_get(v_pkg_856_, 4);
lean_inc_ref(v_dir_859_);
lean_dec_ref(v_pkg_856_);
v_buildDir_860_ = lean_ctor_get(v_config_857_, 5);
lean_inc_ref(v_buildDir_860_);
v_irDir_861_ = lean_ctor_get(v_config_857_, 9);
lean_inc_ref(v_irDir_861_);
lean_dec_ref(v_config_857_);
v___x_862_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_863_ = l_System_FilePath_normalize(v_buildDir_860_);
v___x_864_ = l_Lake_joinRelative(v_dir_859_, v___x_863_);
v___x_865_ = l_System_FilePath_normalize(v_irDir_861_);
v___x_866_ = l_Lake_joinRelative(v___x_864_, v___x_865_);
v___x_867_ = l_Lean_modToFilePath(v___x_866_, v_name_858_, v___x_862_);
lean_dec_ref(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_869_){
_start:
{
lean_object* v_lib_870_; lean_object* v_pkg_871_; lean_object* v_config_872_; lean_object* v_name_873_; lean_object* v_dir_874_; lean_object* v_buildDir_875_; lean_object* v_irDir_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_lib_870_ = lean_ctor_get(v_self_869_, 0);
v_pkg_871_ = lean_ctor_get(v_lib_870_, 0);
lean_inc_ref(v_pkg_871_);
v_config_872_ = lean_ctor_get(v_pkg_871_, 6);
lean_inc_ref(v_config_872_);
v_name_873_ = lean_ctor_get(v_self_869_, 1);
lean_inc(v_name_873_);
lean_dec_ref(v_self_869_);
v_dir_874_ = lean_ctor_get(v_pkg_871_, 4);
lean_inc_ref(v_dir_874_);
lean_dec_ref(v_pkg_871_);
v_buildDir_875_ = lean_ctor_get(v_config_872_, 5);
lean_inc_ref(v_buildDir_875_);
v_irDir_876_ = lean_ctor_get(v_config_872_, 9);
lean_inc_ref(v_irDir_876_);
lean_dec_ref(v_config_872_);
v___x_877_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_878_ = l_System_FilePath_normalize(v_buildDir_875_);
v___x_879_ = l_Lake_joinRelative(v_dir_874_, v___x_878_);
v___x_880_ = l_System_FilePath_normalize(v_irDir_876_);
v___x_881_ = l_Lake_joinRelative(v___x_879_, v___x_880_);
v___x_882_ = l_Lean_modToFilePath(v___x_881_, v_name_873_, v___x_877_);
lean_dec_ref(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_884_){
_start:
{
lean_object* v_lib_885_; lean_object* v_pkg_886_; lean_object* v_config_887_; lean_object* v_name_888_; lean_object* v_dir_889_; lean_object* v_buildDir_890_; lean_object* v_irDir_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_lib_885_ = lean_ctor_get(v_self_884_, 0);
v_pkg_886_ = lean_ctor_get(v_lib_885_, 0);
lean_inc_ref(v_pkg_886_);
v_config_887_ = lean_ctor_get(v_pkg_886_, 6);
lean_inc_ref(v_config_887_);
v_name_888_ = lean_ctor_get(v_self_884_, 1);
lean_inc(v_name_888_);
lean_dec_ref(v_self_884_);
v_dir_889_ = lean_ctor_get(v_pkg_886_, 4);
lean_inc_ref(v_dir_889_);
lean_dec_ref(v_pkg_886_);
v_buildDir_890_ = lean_ctor_get(v_config_887_, 5);
lean_inc_ref(v_buildDir_890_);
v_irDir_891_ = lean_ctor_get(v_config_887_, 9);
lean_inc_ref(v_irDir_891_);
lean_dec_ref(v_config_887_);
v___x_892_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_893_ = l_System_FilePath_normalize(v_buildDir_890_);
v___x_894_ = l_Lake_joinRelative(v_dir_889_, v___x_893_);
v___x_895_ = l_System_FilePath_normalize(v_irDir_891_);
v___x_896_ = l_Lake_joinRelative(v___x_894_, v___x_895_);
v___x_897_ = l_Lean_modToFilePath(v___x_896_, v_name_888_, v___x_892_);
lean_dec_ref(v___x_896_);
return v___x_897_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_internal_has_llvm_backend(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v_self_900_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
else
{
lean_object* v_lib_903_; lean_object* v_pkg_904_; lean_object* v_config_905_; lean_object* v_name_906_; lean_object* v_dir_907_; lean_object* v_buildDir_908_; lean_object* v_irDir_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_lib_903_ = lean_ctor_get(v_self_900_, 0);
v_pkg_904_ = lean_ctor_get(v_lib_903_, 0);
lean_inc_ref(v_pkg_904_);
v_config_905_ = lean_ctor_get(v_pkg_904_, 6);
lean_inc_ref(v_config_905_);
v_name_906_ = lean_ctor_get(v_self_900_, 1);
lean_inc(v_name_906_);
lean_dec_ref(v_self_900_);
v_dir_907_ = lean_ctor_get(v_pkg_904_, 4);
lean_inc_ref(v_dir_907_);
lean_dec_ref(v_pkg_904_);
v_buildDir_908_ = lean_ctor_get(v_config_905_, 5);
lean_inc_ref(v_buildDir_908_);
v_irDir_909_ = lean_ctor_get(v_config_905_, 9);
lean_inc_ref(v_irDir_909_);
lean_dec_ref(v_config_905_);
v___x_910_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_911_ = l_System_FilePath_normalize(v_buildDir_908_);
v___x_912_ = l_Lake_joinRelative(v_dir_907_, v___x_911_);
v___x_913_ = l_System_FilePath_normalize(v_irDir_909_);
v___x_914_ = l_Lake_joinRelative(v___x_912_, v___x_913_);
v___x_915_ = l_Lean_modToFilePath(v___x_914_, v_name_906_, v___x_910_);
lean_dec_ref(v___x_914_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_918_){
_start:
{
lean_object* v_lib_919_; lean_object* v_pkg_920_; lean_object* v_config_921_; lean_object* v_name_922_; lean_object* v_dir_923_; lean_object* v_buildDir_924_; lean_object* v_irDir_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_lib_919_ = lean_ctor_get(v_self_918_, 0);
v_pkg_920_ = lean_ctor_get(v_lib_919_, 0);
lean_inc_ref(v_pkg_920_);
v_config_921_ = lean_ctor_get(v_pkg_920_, 6);
lean_inc_ref(v_config_921_);
v_name_922_ = lean_ctor_get(v_self_918_, 1);
lean_inc(v_name_922_);
lean_dec_ref(v_self_918_);
v_dir_923_ = lean_ctor_get(v_pkg_920_, 4);
lean_inc_ref(v_dir_923_);
lean_dec_ref(v_pkg_920_);
v_buildDir_924_ = lean_ctor_get(v_config_921_, 5);
lean_inc_ref(v_buildDir_924_);
v_irDir_925_ = lean_ctor_get(v_config_921_, 9);
lean_inc_ref(v_irDir_925_);
lean_dec_ref(v_config_921_);
v___x_926_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_927_ = l_System_FilePath_normalize(v_buildDir_924_);
v___x_928_ = l_Lake_joinRelative(v_dir_923_, v___x_927_);
v___x_929_ = l_System_FilePath_normalize(v_irDir_925_);
v___x_930_ = l_Lake_joinRelative(v___x_928_, v___x_929_);
v___x_931_ = l_Lean_modToFilePath(v___x_930_, v_name_922_, v___x_926_);
lean_dec_ref(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_933_){
_start:
{
lean_object* v_lib_934_; lean_object* v_pkg_935_; lean_object* v_config_936_; lean_object* v_name_937_; lean_object* v_dir_938_; lean_object* v_buildDir_939_; lean_object* v_irDir_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_lib_934_ = lean_ctor_get(v_self_933_, 0);
v_pkg_935_ = lean_ctor_get(v_lib_934_, 0);
lean_inc_ref(v_pkg_935_);
v_config_936_ = lean_ctor_get(v_pkg_935_, 6);
lean_inc_ref(v_config_936_);
v_name_937_ = lean_ctor_get(v_self_933_, 1);
lean_inc(v_name_937_);
lean_dec_ref(v_self_933_);
v_dir_938_ = lean_ctor_get(v_pkg_935_, 4);
lean_inc_ref(v_dir_938_);
lean_dec_ref(v_pkg_935_);
v_buildDir_939_ = lean_ctor_get(v_config_936_, 5);
lean_inc_ref(v_buildDir_939_);
v_irDir_940_ = lean_ctor_get(v_config_936_, 9);
lean_inc_ref(v_irDir_940_);
lean_dec_ref(v_config_936_);
v___x_941_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_942_ = l_System_FilePath_normalize(v_buildDir_939_);
v___x_943_ = l_Lake_joinRelative(v_dir_938_, v___x_942_);
v___x_944_ = l_System_FilePath_normalize(v_irDir_940_);
v___x_945_ = l_Lake_joinRelative(v___x_943_, v___x_944_);
v___x_946_ = l_Lean_modToFilePath(v___x_945_, v_name_937_, v___x_941_);
lean_dec_ref(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_949_){
_start:
{
lean_object* v_lib_950_; lean_object* v_name_951_; lean_object* v_pkg_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_lib_950_ = lean_ctor_get(v_self_949_, 0);
lean_inc_ref(v_lib_950_);
v_name_951_ = lean_ctor_get(v_self_949_, 1);
lean_inc(v_name_951_);
lean_dec_ref(v_self_949_);
v_pkg_952_ = lean_ctor_get(v_lib_950_, 0);
lean_inc_ref(v_pkg_952_);
lean_dec_ref(v_lib_950_);
v___x_953_ = l_Lake_Package_id_x3f(v_pkg_952_);
v___x_954_ = l_Lean_mkModuleInitializationStem(v_name_951_, v___x_953_);
lean_dec(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_956_){
_start:
{
lean_object* v_lib_957_; lean_object* v_pkg_958_; lean_object* v_config_959_; lean_object* v_name_960_; lean_object* v_dir_961_; lean_object* v_buildDir_962_; lean_object* v_leanLibDir_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_lib_957_ = lean_ctor_get(v_self_956_, 0);
v_pkg_958_ = lean_ctor_get(v_lib_957_, 0);
lean_inc_ref(v_pkg_958_);
v_config_959_ = lean_ctor_get(v_pkg_958_, 6);
v_name_960_ = lean_ctor_get(v_self_956_, 1);
lean_inc(v_name_960_);
lean_dec_ref(v_self_956_);
v_dir_961_ = lean_ctor_get(v_pkg_958_, 4);
v_buildDir_962_ = lean_ctor_get(v_config_959_, 5);
v_leanLibDir_963_ = lean_ctor_get(v_config_959_, 6);
lean_inc_ref(v_buildDir_962_);
v___x_964_ = l_System_FilePath_normalize(v_buildDir_962_);
lean_inc_ref(v_dir_961_);
v___x_965_ = l_Lake_joinRelative(v_dir_961_, v___x_964_);
lean_inc_ref(v_leanLibDir_963_);
v___x_966_ = l_System_FilePath_normalize(v_leanLibDir_963_);
v___x_967_ = l_Lake_joinRelative(v___x_965_, v___x_966_);
v___x_968_ = l_Lake_Package_id_x3f(v_pkg_958_);
v___x_969_ = l_Lean_mkModuleInitializationStem(v_name_960_, v___x_968_);
lean_dec(v___x_968_);
v___x_970_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_971_ = lean_string_append(v___x_969_, v___x_970_);
v___x_972_ = l_Lake_sharedLibExt;
v___x_973_ = lean_string_append(v___x_971_, v___x_972_);
v___x_974_ = l_Lake_joinRelative(v___x_967_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_975_){
_start:
{
lean_object* v_lib_976_; lean_object* v_pkg_977_; lean_object* v_config_978_; lean_object* v_toLeanConfig_979_; lean_object* v_config_980_; lean_object* v_toLeanConfig_981_; uint8_t v_buildType_982_; lean_object* v_leanOptions_983_; lean_object* v_moreServerOptions_984_; uint8_t v_buildType_985_; lean_object* v_leanOptions_986_; lean_object* v_moreServerOptions_987_; lean_object* v___x_988_; uint8_t v___y_990_; uint8_t v___x_998_; 
v_lib_976_ = lean_ctor_get(v_self_975_, 0);
v_pkg_977_ = lean_ctor_get(v_lib_976_, 0);
v_config_978_ = lean_ctor_get(v_pkg_977_, 6);
v_toLeanConfig_979_ = lean_ctor_get(v_config_978_, 1);
v_config_980_ = lean_ctor_get(v_lib_976_, 2);
v_toLeanConfig_981_ = lean_ctor_get(v_config_980_, 0);
v_buildType_982_ = lean_ctor_get_uint8(v_toLeanConfig_979_, sizeof(void*)*13);
v_leanOptions_983_ = lean_ctor_get(v_toLeanConfig_979_, 0);
v_moreServerOptions_984_ = lean_ctor_get(v_toLeanConfig_979_, 4);
v_buildType_985_ = lean_ctor_get_uint8(v_toLeanConfig_981_, sizeof(void*)*13);
v_leanOptions_986_ = lean_ctor_get(v_toLeanConfig_981_, 0);
v_moreServerOptions_987_ = lean_ctor_get(v_toLeanConfig_981_, 4);
v___x_988_ = lean_box(1);
v___x_998_ = l_Lake_instOrdBuildType_ord(v_buildType_982_, v_buildType_985_);
if (v___x_998_ == 2)
{
v___y_990_ = v_buildType_985_;
goto v___jp_989_;
}
else
{
v___y_990_ = v_buildType_982_;
goto v___jp_989_;
}
v___jp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_991_ = l_Lake_BuildType_leanOptions(v___y_990_);
v___x_992_ = l_Lean_LeanOptions_append(v___x_988_, v___x_991_);
v___x_993_ = l_Lean_LeanOptions_ofArray(v_leanOptions_983_);
v___x_994_ = l_Lean_LeanOptions_appendArray(v___x_993_, v_moreServerOptions_984_);
v___x_995_ = l_Lean_LeanOptions_append(v___x_992_, v___x_994_);
v___x_996_ = l_Lean_LeanOptions_appendArray(v___x_995_, v_leanOptions_986_);
v___x_997_ = l_Lean_LeanOptions_appendArray(v___x_996_, v_moreServerOptions_987_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lake_Module_serverOptions(v_self_999_);
lean_dec_ref(v_self_999_);
return v_res_1000_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_1001_){
_start:
{
lean_object* v_lib_1002_; lean_object* v_pkg_1003_; lean_object* v_config_1004_; lean_object* v_toLeanConfig_1005_; lean_object* v_config_1006_; lean_object* v_toLeanConfig_1007_; uint8_t v_buildType_1008_; uint8_t v_buildType_1009_; uint8_t v___x_1010_; 
v_lib_1002_ = lean_ctor_get(v_self_1001_, 0);
v_pkg_1003_ = lean_ctor_get(v_lib_1002_, 0);
v_config_1004_ = lean_ctor_get(v_pkg_1003_, 6);
v_toLeanConfig_1005_ = lean_ctor_get(v_config_1004_, 1);
v_config_1006_ = lean_ctor_get(v_lib_1002_, 2);
v_toLeanConfig_1007_ = lean_ctor_get(v_config_1006_, 0);
v_buildType_1008_ = lean_ctor_get_uint8(v_toLeanConfig_1005_, sizeof(void*)*13);
v_buildType_1009_ = lean_ctor_get_uint8(v_toLeanConfig_1007_, sizeof(void*)*13);
v___x_1010_ = l_Lake_instOrdBuildType_ord(v_buildType_1008_, v_buildType_1009_);
if (v___x_1010_ == 2)
{
return v_buildType_1009_;
}
else
{
return v_buildType_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Lake_Module_buildType(v_self_1011_);
lean_dec_ref(v_self_1011_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_1014_){
_start:
{
lean_object* v_lib_1015_; lean_object* v_config_1016_; lean_object* v_toLeanConfig_1017_; lean_object* v_pkg_1018_; lean_object* v_config_1019_; lean_object* v_toLeanConfig_1020_; uint8_t v_backend_1021_; uint8_t v_backend_1022_; uint8_t v___x_1023_; 
v_lib_1015_ = lean_ctor_get(v_self_1014_, 0);
v_config_1016_ = lean_ctor_get(v_lib_1015_, 2);
v_toLeanConfig_1017_ = lean_ctor_get(v_config_1016_, 0);
v_pkg_1018_ = lean_ctor_get(v_lib_1015_, 0);
v_config_1019_ = lean_ctor_get(v_pkg_1018_, 6);
v_toLeanConfig_1020_ = lean_ctor_get(v_config_1019_, 1);
v_backend_1021_ = lean_ctor_get_uint8(v_toLeanConfig_1017_, sizeof(void*)*13 + 1);
v_backend_1022_ = lean_ctor_get_uint8(v_toLeanConfig_1020_, sizeof(void*)*13 + 1);
v___x_1023_ = l_Lake_Backend_orPreferLeft(v_backend_1021_, v_backend_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = l_Lake_Module_backend(v_self_1024_);
lean_dec_ref(v_self_1024_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_1027_){
_start:
{
lean_object* v_lib_1028_; lean_object* v_config_1029_; uint8_t v_allowImportAll_1030_; 
v_lib_1028_ = lean_ctor_get(v_self_1027_, 0);
v_config_1029_ = lean_ctor_get(v_lib_1028_, 2);
v_allowImportAll_1030_ = lean_ctor_get_uint8(v_config_1029_, sizeof(void*)*9 + 3);
if (v_allowImportAll_1030_ == 0)
{
lean_object* v_pkg_1031_; lean_object* v_config_1032_; uint8_t v_allowImportAll_1033_; 
v_pkg_1031_ = lean_ctor_get(v_lib_1028_, 0);
v_config_1032_ = lean_ctor_get(v_pkg_1031_, 6);
v_allowImportAll_1033_ = lean_ctor_get_uint8(v_config_1032_, sizeof(void*)*28 + 5);
return v_allowImportAll_1033_;
}
else
{
return v_allowImportAll_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_1034_){
_start:
{
uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_res_1035_ = l_Lake_Module_allowImportAll(v_self_1034_);
lean_dec_ref(v_self_1034_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_requiresModuleSystem(lean_object* v_self_1037_){
_start:
{
lean_object* v_lib_1038_; lean_object* v_config_1039_; lean_object* v_toLeanConfig_1040_; uint8_t v_requiresModuleSystem_1041_; 
v_lib_1038_ = lean_ctor_get(v_self_1037_, 0);
v_config_1039_ = lean_ctor_get(v_lib_1038_, 2);
v_toLeanConfig_1040_ = lean_ctor_get(v_config_1039_, 0);
v_requiresModuleSystem_1041_ = lean_ctor_get_uint8(v_toLeanConfig_1040_, sizeof(void*)*13 + 3);
if (v_requiresModuleSystem_1041_ == 0)
{
lean_object* v_pkg_1042_; lean_object* v_config_1043_; lean_object* v_toLeanConfig_1044_; uint8_t v_requiresModuleSystem_1045_; 
v_pkg_1042_ = lean_ctor_get(v_lib_1038_, 0);
v_config_1043_ = lean_ctor_get(v_pkg_1042_, 6);
v_toLeanConfig_1044_ = lean_ctor_get(v_config_1043_, 1);
v_requiresModuleSystem_1045_ = lean_ctor_get_uint8(v_toLeanConfig_1044_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_1045_;
}
else
{
return v_requiresModuleSystem_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object* v_self_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Lake_Module_requiresModuleSystem(v_self_1046_);
lean_dec_ref(v_self_1046_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowNonModules(lean_object* v_self_1049_){
_start:
{
lean_object* v_lib_1050_; lean_object* v_config_1051_; lean_object* v_toLeanConfig_1052_; uint8_t v_allowNonModules_1053_; 
v_lib_1050_ = lean_ctor_get(v_self_1049_, 0);
v_config_1051_ = lean_ctor_get(v_lib_1050_, 2);
v_toLeanConfig_1052_ = lean_ctor_get(v_config_1051_, 0);
v_allowNonModules_1053_ = lean_ctor_get_uint8(v_toLeanConfig_1052_, sizeof(void*)*13 + 4);
if (v_allowNonModules_1053_ == 0)
{
lean_object* v_pkg_1054_; lean_object* v_config_1055_; lean_object* v_toLeanConfig_1056_; uint8_t v_allowNonModules_1057_; 
v_pkg_1054_ = lean_ctor_get(v_lib_1050_, 0);
v_config_1055_ = lean_ctor_get(v_pkg_1054_, 6);
v_toLeanConfig_1056_ = lean_ctor_get(v_config_1055_, 1);
v_allowNonModules_1057_ = lean_ctor_get_uint8(v_toLeanConfig_1056_, sizeof(void*)*13 + 4);
return v_allowNonModules_1057_;
}
else
{
return v_allowNonModules_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object* v_self_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Lake_Module_allowNonModules(v_self_1058_);
lean_dec_ref(v_self_1058_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_1061_){
_start:
{
lean_object* v_lib_1062_; lean_object* v_pkg_1063_; lean_object* v_config_1064_; lean_object* v_toLeanConfig_1065_; lean_object* v_config_1066_; lean_object* v_toLeanConfig_1067_; lean_object* v_dynlibs_1068_; lean_object* v_dynlibs_1069_; lean_object* v___x_1070_; 
v_lib_1062_ = lean_ctor_get(v_self_1061_, 0);
lean_inc_ref(v_lib_1062_);
lean_dec_ref(v_self_1061_);
v_pkg_1063_ = lean_ctor_get(v_lib_1062_, 0);
v_config_1064_ = lean_ctor_get(v_pkg_1063_, 6);
v_toLeanConfig_1065_ = lean_ctor_get(v_config_1064_, 1);
lean_inc_ref(v_toLeanConfig_1065_);
v_config_1066_ = lean_ctor_get(v_lib_1062_, 2);
lean_inc(v_config_1066_);
lean_dec_ref(v_lib_1062_);
v_toLeanConfig_1067_ = lean_ctor_get(v_config_1066_, 0);
lean_inc_ref(v_toLeanConfig_1067_);
lean_dec(v_config_1066_);
v_dynlibs_1068_ = lean_ctor_get(v_toLeanConfig_1065_, 11);
lean_inc_ref(v_dynlibs_1068_);
lean_dec_ref(v_toLeanConfig_1065_);
v_dynlibs_1069_ = lean_ctor_get(v_toLeanConfig_1067_, 11);
lean_inc_ref(v_dynlibs_1069_);
lean_dec_ref(v_toLeanConfig_1067_);
v___x_1070_ = l_Array_append___redArg(v_dynlibs_1068_, v_dynlibs_1069_);
lean_dec_ref(v_dynlibs_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1071_){
_start:
{
lean_object* v_lib_1072_; lean_object* v_pkg_1073_; lean_object* v_config_1074_; lean_object* v_toLeanConfig_1075_; lean_object* v_config_1076_; lean_object* v_toLeanConfig_1077_; lean_object* v_plugins_1078_; lean_object* v_plugins_1079_; lean_object* v___x_1080_; 
v_lib_1072_ = lean_ctor_get(v_self_1071_, 0);
lean_inc_ref(v_lib_1072_);
lean_dec_ref(v_self_1071_);
v_pkg_1073_ = lean_ctor_get(v_lib_1072_, 0);
v_config_1074_ = lean_ctor_get(v_pkg_1073_, 6);
v_toLeanConfig_1075_ = lean_ctor_get(v_config_1074_, 1);
lean_inc_ref(v_toLeanConfig_1075_);
v_config_1076_ = lean_ctor_get(v_lib_1072_, 2);
lean_inc(v_config_1076_);
lean_dec_ref(v_lib_1072_);
v_toLeanConfig_1077_ = lean_ctor_get(v_config_1076_, 0);
lean_inc_ref(v_toLeanConfig_1077_);
lean_dec(v_config_1076_);
v_plugins_1078_ = lean_ctor_get(v_toLeanConfig_1075_, 12);
lean_inc_ref(v_plugins_1078_);
lean_dec_ref(v_toLeanConfig_1075_);
v_plugins_1079_ = lean_ctor_get(v_toLeanConfig_1077_, 12);
lean_inc_ref(v_plugins_1079_);
lean_dec_ref(v_toLeanConfig_1077_);
v___x_1080_ = l_Array_append___redArg(v_plugins_1078_, v_plugins_1079_);
lean_dec_ref(v_plugins_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1081_){
_start:
{
lean_object* v_lib_1082_; lean_object* v_pkg_1083_; lean_object* v_config_1084_; lean_object* v_toLeanConfig_1085_; lean_object* v_config_1086_; lean_object* v_toLeanConfig_1087_; uint8_t v_buildType_1088_; lean_object* v_leanOptions_1089_; uint8_t v_buildType_1090_; lean_object* v_leanOptions_1091_; uint8_t v___y_1093_; uint8_t v___x_1098_; 
v_lib_1082_ = lean_ctor_get(v_self_1081_, 0);
v_pkg_1083_ = lean_ctor_get(v_lib_1082_, 0);
v_config_1084_ = lean_ctor_get(v_pkg_1083_, 6);
v_toLeanConfig_1085_ = lean_ctor_get(v_config_1084_, 1);
v_config_1086_ = lean_ctor_get(v_lib_1082_, 2);
v_toLeanConfig_1087_ = lean_ctor_get(v_config_1086_, 0);
v_buildType_1088_ = lean_ctor_get_uint8(v_toLeanConfig_1085_, sizeof(void*)*13);
v_leanOptions_1089_ = lean_ctor_get(v_toLeanConfig_1085_, 0);
v_buildType_1090_ = lean_ctor_get_uint8(v_toLeanConfig_1087_, sizeof(void*)*13);
v_leanOptions_1091_ = lean_ctor_get(v_toLeanConfig_1087_, 0);
v___x_1098_ = l_Lake_instOrdBuildType_ord(v_buildType_1088_, v_buildType_1090_);
if (v___x_1098_ == 2)
{
v___y_1093_ = v_buildType_1090_;
goto v___jp_1092_;
}
else
{
v___y_1093_ = v_buildType_1088_;
goto v___jp_1092_;
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = l_Lake_BuildType_leanOptions(v___y_1093_);
v___x_1095_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1089_);
v___x_1096_ = l_Lean_LeanOptions_append(v___x_1094_, v___x_1095_);
v___x_1097_ = l_Lean_LeanOptions_appendArray(v___x_1096_, v_leanOptions_1091_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lake_Module_leanOptions(v_self_1099_);
lean_dec_ref(v_self_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_postponeCompile(lean_object* v_self_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v_lib_1103_; lean_object* v_pkg_1104_; lean_object* v_config_1105_; lean_object* v_toLeanConfig_1106_; lean_object* v_config_1107_; lean_object* v_toLeanConfig_1108_; uint8_t v_buildType_1109_; lean_object* v_leanOptions_1110_; uint8_t v_buildType_1111_; lean_object* v_leanOptions_1112_; uint8_t v___y_1114_; uint8_t v___x_1123_; 
v___x_1102_ = l_Lean_KVMap_instValueBool;
v_lib_1103_ = lean_ctor_get(v_self_1101_, 0);
v_pkg_1104_ = lean_ctor_get(v_lib_1103_, 0);
v_config_1105_ = lean_ctor_get(v_pkg_1104_, 6);
v_toLeanConfig_1106_ = lean_ctor_get(v_config_1105_, 1);
v_config_1107_ = lean_ctor_get(v_lib_1103_, 2);
v_toLeanConfig_1108_ = lean_ctor_get(v_config_1107_, 0);
v_buildType_1109_ = lean_ctor_get_uint8(v_toLeanConfig_1106_, sizeof(void*)*13);
v_leanOptions_1110_ = lean_ctor_get(v_toLeanConfig_1106_, 0);
v_buildType_1111_ = lean_ctor_get_uint8(v_toLeanConfig_1108_, sizeof(void*)*13);
v_leanOptions_1112_ = lean_ctor_get(v_toLeanConfig_1108_, 0);
v___x_1123_ = l_Lake_instOrdBuildType_ord(v_buildType_1109_, v_buildType_1111_);
if (v___x_1123_ == 2)
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
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1115_ = l_Lake_BuildType_leanOptions(v___y_1114_);
v___x_1116_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1110_);
v___x_1117_ = l_Lean_LeanOptions_append(v___x_1115_, v___x_1116_);
v___x_1118_ = l_Lean_LeanOptions_appendArray(v___x_1117_, v_leanOptions_1112_);
v___x_1119_ = l_Lean_LeanOptions_toOptions(v___x_1118_);
v___x_1120_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1121_ = l_Lean_Option_get___redArg(v___x_1102_, v___x_1119_, v___x_1120_);
lean_dec_ref(v___x_1119_);
v___x_1122_ = lean_unbox(v___x_1121_);
lean_dec(v___x_1121_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_postponeCompile___boxed(lean_object* v_self_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_Lake_Module_postponeCompile(v_self_1124_);
lean_dec_ref(v_self_1124_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
static lean_object* _init_l_Lake_Module_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1128_){
_start:
{
lean_object* v_lib_1129_; lean_object* v_pkg_1130_; lean_object* v_config_1131_; lean_object* v_toLeanConfig_1132_; lean_object* v_config_1133_; lean_object* v_toLeanConfig_1134_; lean_object* v_moreLeanArgs_1135_; lean_object* v_moreLeanArgs_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_lib_1129_ = lean_ctor_get(v_self_1128_, 0);
v_pkg_1130_ = lean_ctor_get(v_lib_1129_, 0);
v_config_1131_ = lean_ctor_get(v_pkg_1130_, 6);
v_toLeanConfig_1132_ = lean_ctor_get(v_config_1131_, 1);
v_config_1133_ = lean_ctor_get(v_lib_1129_, 2);
v_toLeanConfig_1134_ = lean_ctor_get(v_config_1133_, 0);
v_moreLeanArgs_1135_ = lean_ctor_get(v_toLeanConfig_1132_, 1);
v_moreLeanArgs_1136_ = lean_ctor_get(v_toLeanConfig_1134_, 1);
v___x_1137_ = lean_obj_once(&l_Lake_Module_leanArgs___closed__0, &l_Lake_Module_leanArgs___closed__0_once, _init_l_Lake_Module_leanArgs___closed__0);
v___x_1138_ = l_Array_append___redArg(v___x_1137_, v_moreLeanArgs_1135_);
v___x_1139_ = l_Array_append___redArg(v___x_1138_, v_moreLeanArgs_1136_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lake_Module_leanArgs(v_self_1140_);
lean_dec_ref(v_self_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1142_){
_start:
{
lean_object* v_lib_1143_; lean_object* v_pkg_1144_; lean_object* v_config_1145_; lean_object* v_toLeanConfig_1146_; lean_object* v_config_1147_; lean_object* v_toLeanConfig_1148_; lean_object* v_weakLeanArgs_1149_; lean_object* v_weakLeanArgs_1150_; lean_object* v___x_1151_; 
v_lib_1143_ = lean_ctor_get(v_self_1142_, 0);
lean_inc_ref(v_lib_1143_);
lean_dec_ref(v_self_1142_);
v_pkg_1144_ = lean_ctor_get(v_lib_1143_, 0);
v_config_1145_ = lean_ctor_get(v_pkg_1144_, 6);
v_toLeanConfig_1146_ = lean_ctor_get(v_config_1145_, 1);
lean_inc_ref(v_toLeanConfig_1146_);
v_config_1147_ = lean_ctor_get(v_lib_1143_, 2);
lean_inc(v_config_1147_);
lean_dec_ref(v_lib_1143_);
v_toLeanConfig_1148_ = lean_ctor_get(v_config_1147_, 0);
lean_inc_ref(v_toLeanConfig_1148_);
lean_dec(v_config_1147_);
v_weakLeanArgs_1149_ = lean_ctor_get(v_toLeanConfig_1146_, 2);
lean_inc_ref(v_weakLeanArgs_1149_);
lean_dec_ref(v_toLeanConfig_1146_);
v_weakLeanArgs_1150_ = lean_ctor_get(v_toLeanConfig_1148_, 2);
lean_inc_ref(v_weakLeanArgs_1150_);
lean_dec_ref(v_toLeanConfig_1148_);
v___x_1151_ = l_Array_append___redArg(v_weakLeanArgs_1149_, v_weakLeanArgs_1150_);
lean_dec_ref(v_weakLeanArgs_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1152_){
_start:
{
lean_object* v_lib_1153_; lean_object* v_pkg_1154_; lean_object* v_config_1155_; lean_object* v_toLeanConfig_1156_; lean_object* v_config_1157_; lean_object* v_toLeanConfig_1158_; uint8_t v_buildType_1159_; lean_object* v_moreLeancArgs_1160_; uint8_t v_buildType_1161_; lean_object* v_moreLeancArgs_1162_; uint8_t v___y_1164_; uint8_t v___x_1168_; 
v_lib_1153_ = lean_ctor_get(v_self_1152_, 0);
v_pkg_1154_ = lean_ctor_get(v_lib_1153_, 0);
v_config_1155_ = lean_ctor_get(v_pkg_1154_, 6);
v_toLeanConfig_1156_ = lean_ctor_get(v_config_1155_, 1);
v_config_1157_ = lean_ctor_get(v_lib_1153_, 2);
v_toLeanConfig_1158_ = lean_ctor_get(v_config_1157_, 0);
v_buildType_1159_ = lean_ctor_get_uint8(v_toLeanConfig_1156_, sizeof(void*)*13);
v_moreLeancArgs_1160_ = lean_ctor_get(v_toLeanConfig_1156_, 3);
v_buildType_1161_ = lean_ctor_get_uint8(v_toLeanConfig_1158_, sizeof(void*)*13);
v_moreLeancArgs_1162_ = lean_ctor_get(v_toLeanConfig_1158_, 3);
v___x_1168_ = l_Lake_instOrdBuildType_ord(v_buildType_1159_, v_buildType_1161_);
if (v___x_1168_ == 2)
{
v___y_1164_ = v_buildType_1161_;
goto v___jp_1163_;
}
else
{
v___y_1164_ = v_buildType_1159_;
goto v___jp_1163_;
}
v___jp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = l_Lake_BuildType_leancArgs(v___y_1164_);
v___x_1166_ = l_Array_append___redArg(v___x_1165_, v_moreLeancArgs_1160_);
v___x_1167_ = l_Array_append___redArg(v___x_1166_, v_moreLeancArgs_1162_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lake_Module_leancArgs(v_self_1169_);
lean_dec_ref(v_self_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1171_){
_start:
{
lean_object* v_lib_1172_; lean_object* v_pkg_1173_; lean_object* v_config_1174_; lean_object* v_toLeanConfig_1175_; lean_object* v_config_1176_; lean_object* v_toLeanConfig_1177_; lean_object* v_weakLeancArgs_1178_; lean_object* v_weakLeancArgs_1179_; lean_object* v___x_1180_; 
v_lib_1172_ = lean_ctor_get(v_self_1171_, 0);
lean_inc_ref(v_lib_1172_);
lean_dec_ref(v_self_1171_);
v_pkg_1173_ = lean_ctor_get(v_lib_1172_, 0);
v_config_1174_ = lean_ctor_get(v_pkg_1173_, 6);
v_toLeanConfig_1175_ = lean_ctor_get(v_config_1174_, 1);
lean_inc_ref(v_toLeanConfig_1175_);
v_config_1176_ = lean_ctor_get(v_lib_1172_, 2);
lean_inc(v_config_1176_);
lean_dec_ref(v_lib_1172_);
v_toLeanConfig_1177_ = lean_ctor_get(v_config_1176_, 0);
lean_inc_ref(v_toLeanConfig_1177_);
lean_dec(v_config_1176_);
v_weakLeancArgs_1178_ = lean_ctor_get(v_toLeanConfig_1175_, 5);
lean_inc_ref(v_weakLeancArgs_1178_);
lean_dec_ref(v_toLeanConfig_1175_);
v_weakLeancArgs_1179_ = lean_ctor_get(v_toLeanConfig_1177_, 5);
lean_inc_ref(v_weakLeancArgs_1179_);
lean_dec_ref(v_toLeanConfig_1177_);
v___x_1180_ = l_Array_append___redArg(v_weakLeancArgs_1178_, v_weakLeancArgs_1179_);
lean_dec_ref(v_weakLeancArgs_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1181_){
_start:
{
lean_object* v_lib_1182_; lean_object* v_pkg_1183_; lean_object* v_config_1184_; lean_object* v_toLeanConfig_1185_; lean_object* v_config_1186_; lean_object* v_toLeanConfig_1187_; lean_object* v_moreLinkArgs_1188_; lean_object* v_moreLinkArgs_1189_; lean_object* v___x_1190_; 
v_lib_1182_ = lean_ctor_get(v_self_1181_, 0);
lean_inc_ref(v_lib_1182_);
lean_dec_ref(v_self_1181_);
v_pkg_1183_ = lean_ctor_get(v_lib_1182_, 0);
v_config_1184_ = lean_ctor_get(v_pkg_1183_, 6);
v_toLeanConfig_1185_ = lean_ctor_get(v_config_1184_, 1);
lean_inc_ref(v_toLeanConfig_1185_);
v_config_1186_ = lean_ctor_get(v_lib_1182_, 2);
lean_inc(v_config_1186_);
lean_dec_ref(v_lib_1182_);
v_toLeanConfig_1187_ = lean_ctor_get(v_config_1186_, 0);
lean_inc_ref(v_toLeanConfig_1187_);
lean_dec(v_config_1186_);
v_moreLinkArgs_1188_ = lean_ctor_get(v_toLeanConfig_1185_, 8);
lean_inc_ref(v_moreLinkArgs_1188_);
lean_dec_ref(v_toLeanConfig_1185_);
v_moreLinkArgs_1189_ = lean_ctor_get(v_toLeanConfig_1187_, 8);
lean_inc_ref(v_moreLinkArgs_1189_);
lean_dec_ref(v_toLeanConfig_1187_);
v___x_1190_ = l_Array_append___redArg(v_moreLinkArgs_1188_, v_moreLinkArgs_1189_);
lean_dec_ref(v_moreLinkArgs_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1191_){
_start:
{
lean_object* v_lib_1192_; lean_object* v_pkg_1193_; lean_object* v_config_1194_; lean_object* v_toLeanConfig_1195_; lean_object* v_config_1196_; lean_object* v_toLeanConfig_1197_; lean_object* v_weakLinkArgs_1198_; lean_object* v_weakLinkArgs_1199_; lean_object* v___x_1200_; 
v_lib_1192_ = lean_ctor_get(v_self_1191_, 0);
lean_inc_ref(v_lib_1192_);
lean_dec_ref(v_self_1191_);
v_pkg_1193_ = lean_ctor_get(v_lib_1192_, 0);
v_config_1194_ = lean_ctor_get(v_pkg_1193_, 6);
v_toLeanConfig_1195_ = lean_ctor_get(v_config_1194_, 1);
lean_inc_ref(v_toLeanConfig_1195_);
v_config_1196_ = lean_ctor_get(v_lib_1192_, 2);
lean_inc(v_config_1196_);
lean_dec_ref(v_lib_1192_);
v_toLeanConfig_1197_ = lean_ctor_get(v_config_1196_, 0);
lean_inc_ref(v_toLeanConfig_1197_);
lean_dec(v_config_1196_);
v_weakLinkArgs_1198_ = lean_ctor_get(v_toLeanConfig_1195_, 9);
lean_inc_ref(v_weakLinkArgs_1198_);
lean_dec_ref(v_toLeanConfig_1195_);
v_weakLinkArgs_1199_ = lean_ctor_get(v_toLeanConfig_1197_, 9);
lean_inc_ref(v_weakLinkArgs_1199_);
lean_dec_ref(v_toLeanConfig_1197_);
v___x_1200_ = l_Array_append___redArg(v_weakLinkArgs_1198_, v_weakLinkArgs_1199_);
lean_dec_ref(v_weakLinkArgs_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1202_){
_start:
{
lean_object* v_lib_1203_; lean_object* v_pkg_1204_; lean_object* v_config_1205_; uint8_t v_bootstrap_1206_; 
v_lib_1203_ = lean_ctor_get(v_self_1202_, 0);
lean_inc_ref(v_lib_1203_);
lean_dec_ref(v_self_1202_);
v_pkg_1204_ = lean_ctor_get(v_lib_1203_, 0);
lean_inc_ref(v_pkg_1204_);
lean_dec_ref(v_lib_1203_);
v_config_1205_ = lean_ctor_get(v_pkg_1204_, 6);
lean_inc_ref(v_config_1205_);
v_bootstrap_1206_ = lean_ctor_get_uint8(v_config_1205_, sizeof(void*)*28);
if (v_bootstrap_1206_ == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref(v_config_1205_);
lean_dec_ref(v_pkg_1204_);
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v_dir_1208_; lean_object* v_buildDir_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_dir_1208_ = lean_ctor_get(v_pkg_1204_, 4);
lean_inc_ref(v_dir_1208_);
lean_dec_ref(v_pkg_1204_);
v_buildDir_1209_ = lean_ctor_get(v_config_1205_, 5);
lean_inc_ref(v_buildDir_1209_);
lean_dec_ref(v_config_1205_);
v___x_1210_ = l_System_FilePath_normalize(v_buildDir_1209_);
v___x_1211_ = l_Lake_joinRelative(v_dir_1208_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1213_ = l_Lake_joinRelative(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1215_){
_start:
{
lean_object* v_lib_1216_; lean_object* v_config_1217_; lean_object* v_toLeanConfig_1218_; lean_object* v_platformIndependent_1219_; 
v_lib_1216_ = lean_ctor_get(v_self_1215_, 0);
v_config_1217_ = lean_ctor_get(v_lib_1216_, 2);
v_toLeanConfig_1218_ = lean_ctor_get(v_config_1217_, 0);
v_platformIndependent_1219_ = lean_ctor_get(v_toLeanConfig_1218_, 10);
if (lean_obj_tag(v_platformIndependent_1219_) == 0)
{
lean_object* v_pkg_1220_; lean_object* v_config_1221_; lean_object* v_toLeanConfig_1222_; lean_object* v_platformIndependent_1223_; 
v_pkg_1220_ = lean_ctor_get(v_lib_1216_, 0);
v_config_1221_ = lean_ctor_get(v_pkg_1220_, 6);
v_toLeanConfig_1222_ = lean_ctor_get(v_config_1221_, 1);
v_platformIndependent_1223_ = lean_ctor_get(v_toLeanConfig_1222_, 10);
lean_inc(v_platformIndependent_1223_);
return v_platformIndependent_1223_;
}
else
{
lean_inc_ref(v_platformIndependent_1219_);
return v_platformIndependent_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lake_Module_platformIndependent(v_self_1224_);
lean_dec_ref(v_self_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompileImports(lean_object* v_self_1226_){
_start:
{
lean_object* v_lib_1227_; lean_object* v_pkg_1228_; lean_object* v_config_1229_; uint8_t v_precompileModules_1230_; 
v_lib_1227_ = lean_ctor_get(v_self_1226_, 0);
v_pkg_1228_ = lean_ctor_get(v_lib_1227_, 0);
v_config_1229_ = lean_ctor_get(v_pkg_1228_, 6);
v_precompileModules_1230_ = lean_ctor_get_uint8(v_config_1229_, sizeof(void*)*28 + 1);
if (v_precompileModules_1230_ == 0)
{
lean_object* v_config_1231_; uint8_t v_precompileModules_1232_; 
v_config_1231_ = lean_ctor_get(v_lib_1227_, 2);
v_precompileModules_1232_ = lean_ctor_get_uint8(v_config_1231_, sizeof(void*)*9 + 2);
if (v_precompileModules_1232_ == 0)
{
lean_object* v_toLeanConfig_1233_; uint8_t v_precompileImports_1234_; 
v_toLeanConfig_1233_ = lean_ctor_get(v_config_1229_, 1);
v_precompileImports_1234_ = lean_ctor_get_uint8(v_toLeanConfig_1233_, sizeof(void*)*13 + 2);
if (v_precompileImports_1234_ == 0)
{
lean_object* v_toLeanConfig_1235_; uint8_t v_precompileImports_1236_; 
v_toLeanConfig_1235_ = lean_ctor_get(v_config_1231_, 0);
v_precompileImports_1236_ = lean_ctor_get_uint8(v_toLeanConfig_1235_, sizeof(void*)*13 + 2);
return v_precompileImports_1236_;
}
else
{
return v_precompileImports_1234_;
}
}
else
{
return v_precompileModules_1232_;
}
}
else
{
return v_precompileModules_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompileImports___boxed(lean_object* v_self_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Lake_Module_shouldPrecompileImports(v_self_1237_);
lean_dec_ref(v_self_1237_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1240_){
_start:
{
lean_object* v_lib_1241_; lean_object* v_pkg_1242_; lean_object* v_config_1243_; uint8_t v_precompileModules_1244_; 
v_lib_1241_ = lean_ctor_get(v_self_1240_, 0);
v_pkg_1242_ = lean_ctor_get(v_lib_1241_, 0);
v_config_1243_ = lean_ctor_get(v_pkg_1242_, 6);
v_precompileModules_1244_ = lean_ctor_get_uint8(v_config_1243_, sizeof(void*)*28 + 1);
if (v_precompileModules_1244_ == 0)
{
lean_object* v_config_1245_; uint8_t v_precompileModules_1246_; 
v_config_1245_ = lean_ctor_get(v_lib_1241_, 2);
v_precompileModules_1246_ = lean_ctor_get_uint8(v_config_1245_, sizeof(void*)*9 + 2);
return v_precompileModules_1246_;
}
else
{
return v_precompileModules_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Lake_Module_shouldPrecompile(v_self_1247_);
lean_dec_ref(v_self_1247_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1250_, uint8_t v_shouldExport_1251_){
_start:
{
lean_object* v_lib_1252_; lean_object* v_config_1253_; lean_object* v_nativeFacets_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_lib_1252_ = lean_ctor_get(v_self_1250_, 0);
lean_inc_ref(v_lib_1252_);
lean_dec_ref(v_self_1250_);
v_config_1253_ = lean_ctor_get(v_lib_1252_, 2);
lean_inc(v_config_1253_);
lean_dec_ref(v_lib_1252_);
v_nativeFacets_1254_ = lean_ctor_get(v_config_1253_, 8);
lean_inc_ref(v_nativeFacets_1254_);
lean_dec(v_config_1253_);
v___x_1255_ = lean_box(v_shouldExport_1251_);
v___x_1256_ = lean_apply_1(v_nativeFacets_1254_, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1257_, lean_object* v_shouldExport_1258_){
_start:
{
uint8_t v_shouldExport_boxed_1259_; lean_object* v_res_1260_; 
v_shouldExport_boxed_1259_ = lean_unbox(v_shouldExport_1258_);
v_res_1260_ = l_Lake_Module_nativeFacets(v_self_1257_, v_shouldExport_boxed_1259_);
return v_res_1260_;
}
}
lean_object* runtime_initialize_Lake_Config_LeanLib(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
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
res = runtime_initialize_Lean_Compiler_Options(builtin);
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
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_LeanLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
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
