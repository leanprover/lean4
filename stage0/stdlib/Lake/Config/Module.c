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
uint64_t l_Lake_instHashableModule___lam__0(lean_object* v_m_18_){
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
LEAN_EXPORT void l_Lake_instHashableModule___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_18_ = stack[0].m_obj;
uint64_t v_res_22_;
v_res_22_ = l_Lake_instHashableModule___lam__0(v_m_18_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lake_instHashableModule___lam__0___boxed(lean_object* v_m_23_){
_start:
{
uint64_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lake_instHashableModule___lam__0(v_m_23_);
lean_dec_ref(v_m_23_);
v_r_25_ = lean_box_uint64(v_res_24_);
return v_r_25_;
}
}
uint8_t l_Lake_instBEqModule___lam__0(lean_object* v_m_28_, lean_object* v_n_29_){
_start:
{
lean_object* v_name_30_; lean_object* v_name_31_; uint8_t v___x_32_; 
v_name_30_ = lean_ctor_get(v_m_28_, 1);
v_name_31_ = lean_ctor_get(v_n_29_, 1);
v___x_32_ = lean_name_eq(v_name_30_, v_name_31_);
return v___x_32_;
}
}
LEAN_EXPORT void l_Lake_instBEqModule___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_28_ = stack[0].m_obj;
lean_object* v_n_29_ = stack[1].m_obj;
uint8_t v_res_33_;
v_res_33_ = l_Lake_instBEqModule___lam__0(v_m_28_, v_n_29_);
stack->m_num = v_res_33_;
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
lean_object* v___x_47_; 
v___x_47_ = l_Lake_OrdHashSet_empty___redArg();
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
lean_object* l_Lake_ModuleMap_empty___redArg(){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(1);
return v___x_50_;
}
}
LEAN_EXPORT void l_Lake_ModuleMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_51_;
v_res_51_ = l_Lake_ModuleMap_empty___redArg();
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty___redArg___boxed(lean_object* v___dummy_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lake_ModuleMap_empty___redArg();
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleMap_empty(lean_object* v_00_u03b1_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(1);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModule_x3f(lean_object* v_mod_56_, lean_object* v_self_57_){
_start:
{
lean_object* v_config_58_; uint8_t v___x_59_; 
v_config_58_ = lean_ctor_get(v_self_57_, 2);
v___x_59_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_56_, v_config_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec_ref(v_self_57_);
lean_dec(v_mod_56_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_self_57_);
lean_ctor_set(v___x_61_, 1, v_mod_56_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(lean_object* v___x_63_, lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_string_utf8_byte_size(v_s_64_);
v___x_66_ = lean_string_utf8_byte_size(v___x_63_);
v___x_67_ = lean_nat_dec_le(v___x_66_, v___x_65_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_s_64_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_string_memcmp(v_s_64_, v___x_63_, v___x_69_, v___x_69_, v___x_66_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec_ref(v_s_64_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc_ref(v_s_64_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_s_64_);
lean_ctor_set(v___x_72_, 1, v___x_69_);
lean_ctor_set(v___x_72_, 2, v___x_65_);
v___x_73_ = l_String_Slice_pos_x21(v___x_72_, v___x_66_);
lean_dec_ref_known(v___x_72_, 3);
v___x_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_74_, 0, v_s_64_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
lean_ctor_set(v___x_74_, 2, v___x_65_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg___boxed(lean_object* v___x_76_, lean_object* v_s_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_76_, v_s_77_);
lean_dec_ref(v___x_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(lean_object* v___x_79_, lean_object* v_s_80_, lean_object* v_pat_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_79_, v_s_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___boxed(lean_object* v___x_83_, lean_object* v_s_84_, lean_object* v_pat_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(v___x_83_, v_s_84_, v_pat_85_);
lean_dec_ref(v_pat_85_);
lean_dec_ref(v___x_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(lean_object* v_s_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_89_ = lean_string_utf8_byte_size(v_s_88_);
v___x_90_ = lean_unsigned_to_nat(5u);
v___x_91_ = lean_nat_dec_le(v___x_90_, v___x_89_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v_s_88_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0));
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_sub(v___x_89_, v___x_90_);
v___x_96_ = lean_string_memcmp(v_s_88_, v___x_93_, v___x_95_, v___x_94_, v___x_90_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec(v___x_95_);
lean_dec_ref(v_s_88_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
lean_inc_ref(v_s_88_);
v___x_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_98_, 0, v_s_88_);
lean_ctor_set(v___x_98_, 1, v___x_94_);
lean_ctor_set(v___x_98_, 2, v___x_89_);
v___x_99_ = l_String_Slice_pos_x21(v___x_98_, v___x_95_);
lean_dec(v___x_95_);
lean_dec_ref_known(v___x_98_, 3);
v___x_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_100_, 0, v_s_88_);
lean_ctor_set(v___x_100_, 1, v___x_94_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(lean_object* v_s_102_, lean_object* v_pat_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v_s_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___boxed(lean_object* v_s_105_, lean_object* v_pat_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(v_s_105_, v_pat_106_);
lean_dec_ref(v_pat_106_);
return v_res_107_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1(void){
_start:
{
uint32_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = l_System_FilePath_pathSeparator;
v___x_110_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_111_ = lean_string_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
v___x_113_ = lean_string_utf8_byte_size(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(lean_object* v_s_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_115_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
v___x_116_ = lean_string_utf8_byte_size(v_s_114_);
v___x_117_ = lean_obj_once(&l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2, &l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once, _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2);
v___x_118_ = lean_nat_dec_le(v___x_117_, v___x_116_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_dec_ref(v_s_114_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_nat_sub(v___x_116_, v___x_117_);
v___x_122_ = lean_string_memcmp(v_s_114_, v___x_115_, v___x_121_, v___x_120_, v___x_117_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec(v___x_121_);
lean_dec_ref(v_s_114_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_inc_ref(v_s_114_);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v_s_114_);
lean_ctor_set(v___x_124_, 1, v___x_120_);
lean_ctor_set(v___x_124_, 2, v___x_116_);
v___x_125_ = l_String_Slice_pos_x21(v___x_124_, v___x_121_);
lean_dec(v___x_121_);
lean_dec_ref_known(v___x_124_, 3);
v___x_126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_126_, 0, v_s_114_);
lean_ctor_set(v___x_126_, 1, v___x_120_);
lean_ctor_set(v___x_126_, 2, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(lean_object* v_s_128_, lean_object* v_pat_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v_s_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___boxed(lean_object* v_s_131_, lean_object* v_pat_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(v_s_131_, v_pat_132_);
lean_dec_ref(v_pat_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
return v_x_134_;
}
else
{
lean_object* v_head_136_; lean_object* v_tail_137_; lean_object* v___x_138_; 
v_head_136_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_head_136_);
v_tail_137_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_tail_137_);
lean_dec_ref_known(v_x_135_, 2);
v___x_138_ = l_Lean_Name_str___override(v_x_134_, v_head_136_);
v_x_134_ = v___x_138_;
v_x_135_ = v_tail_137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_findModuleBySrc_x3f(lean_object* v_path_140_, lean_object* v_self_141_){
_start:
{
lean_object* v___y_143_; lean_object* v_pkg_151_; lean_object* v_config_152_; lean_object* v_config_153_; lean_object* v_dir_154_; lean_object* v_srcDir_155_; lean_object* v_srcDir_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_pkg_151_ = lean_ctor_get(v_self_141_, 0);
v_config_152_ = lean_ctor_get(v_pkg_151_, 6);
v_config_153_ = lean_ctor_get(v_self_141_, 2);
v_dir_154_ = lean_ctor_get(v_pkg_151_, 4);
v_srcDir_155_ = lean_ctor_get(v_config_152_, 4);
v_srcDir_156_ = lean_ctor_get(v_config_153_, 1);
lean_inc_ref(v_srcDir_155_);
v___x_157_ = l_System_FilePath_normalize(v_srcDir_155_);
lean_inc_ref(v_dir_154_);
v___x_158_ = l_Lake_joinRelative(v_dir_154_, v___x_157_);
lean_inc_ref(v_srcDir_156_);
v___x_159_ = l_System_FilePath_normalize(v_srcDir_156_);
v___x_160_ = l_Lake_joinRelative(v___x_158_, v___x_159_);
v___x_161_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_160_, v_path_140_);
lean_dec_ref(v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; 
lean_dec_ref(v_self_141_);
v___x_162_ = lean_box(0);
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v_str_164_; lean_object* v_startInclusive_165_; lean_object* v_endExclusive_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_180_; 
v_val_163_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v___x_161_, 1);
v_str_164_ = lean_ctor_get(v_val_163_, 0);
lean_inc_ref(v_str_164_);
v_startInclusive_165_ = lean_ctor_get(v_val_163_, 1);
lean_inc(v_startInclusive_165_);
v_endExclusive_166_ = lean_ctor_get(v_val_163_, 2);
lean_inc(v_endExclusive_166_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_String_Slice_Pos_nextn(v_val_163_, v___x_168_, v___x_167_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_val_163_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_181_ = lean_ctor_get(v_val_163_, 2);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_val_163_, 1);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_val_163_, 0);
lean_dec(v_unused_183_);
v___x_171_ = v_val_163_;
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_val_163_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_nat_add(v_startInclusive_165_, v___x_169_);
lean_dec(v___x_169_);
lean_dec(v_startInclusive_165_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_str_164_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_endExclusive_166_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l_String_Slice_toString(v___x_175_);
lean_dec_ref(v___x_175_);
lean_inc_ref(v___x_176_);
v___x_177_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v___x_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v___x_178_; 
v___x_178_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v___x_176_);
v___y_143_ = v___x_178_;
goto v___jp_142_;
}
else
{
lean_dec_ref(v___x_176_);
v___y_143_ = v___x_177_;
goto v___jp_142_;
}
}
}
}
v___jp_142_:
{
if (lean_obj_tag(v___y_143_) == 0)
{
lean_object* v___x_144_; 
lean_dec_ref(v_self_141_);
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
lean_object* v_val_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_val_145_ = lean_ctor_get(v___y_143_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v___y_143_, 1);
v___x_146_ = lean_box(0);
v___x_147_ = l_String_Slice_toString(v_val_145_);
lean_dec(v_val_145_);
v___x_148_ = l_System_FilePath_components(v___x_147_);
v___x_149_ = l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(v___x_146_, v___x_148_);
v___x_150_ = l_Lake_LeanLib_findModule_x3f(v___x_149_, v_self_141_);
return v___x_150_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(lean_object* v_self_187_, lean_object* v_as_188_, size_t v_i_189_, size_t v_stop_190_, lean_object* v_b_191_){
_start:
{
lean_object* v___y_193_; uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_189_, v_stop_190_);
if (v___x_197_ == 0)
{
lean_object* v_toConfigDecl_198_; lean_object* v_name_199_; lean_object* v_kind_200_; lean_object* v_config_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_toConfigDecl_198_ = lean_array_uget_borrowed(v_as_188_, v_i_189_);
v_name_199_ = lean_ctor_get(v_toConfigDecl_198_, 1);
v_kind_200_ = lean_ctor_get(v_toConfigDecl_198_, 2);
v_config_201_ = lean_ctor_get(v_toConfigDecl_198_, 3);
v___x_202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1));
v___x_203_ = lean_name_eq(v_kind_200_, v___x_202_);
if (v___x_203_ == 0)
{
v___y_193_ = v_b_191_;
goto v___jp_192_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc(v_config_201_);
lean_inc(v_name_199_);
lean_inc_ref(v_self_187_);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v_self_187_);
lean_ctor_set(v___x_204_, 1, v_name_199_);
lean_ctor_set(v___x_204_, 2, v_config_201_);
v___x_205_ = lean_array_push(v_b_191_, v___x_204_);
v___y_193_ = v___x_205_;
goto v___jp_192_;
}
}
else
{
lean_dec_ref(v_self_187_);
return v_b_191_;
}
v___jp_192_:
{
size_t v___x_194_; size_t v___x_195_; 
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_189_, v___x_194_);
v_i_189_ = v___x_195_;
v_b_191_ = v___y_193_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_187_ = stack[0].m_obj;
lean_object* v_as_188_ = stack[1].m_obj;
size_t v_i_189_ = stack[2].m_num;
size_t v_stop_190_ = stack[3].m_num;
lean_object* v_b_191_ = stack[4].m_obj;
lean_object* v_res_206_;
v_res_206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_187_, v_as_188_, v_i_189_, v_stop_190_, v_b_191_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___boxed(lean_object* v_self_207_, lean_object* v_as_208_, lean_object* v_i_209_, lean_object* v_stop_210_, lean_object* v_b_211_){
_start:
{
size_t v_i_boxed_212_; size_t v_stop_boxed_213_; lean_object* v_res_214_; 
v_i_boxed_212_ = lean_unbox_usize(v_i_209_);
lean_dec(v_i_209_);
v_stop_boxed_213_ = lean_unbox_usize(v_stop_210_);
lean_dec(v_stop_210_);
v_res_214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_207_, v_as_208_, v_i_boxed_212_, v_stop_boxed_213_, v_b_211_);
lean_dec_ref(v_as_208_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(lean_object* v_mod_215_, lean_object* v_as_216_, lean_object* v_i_217_){
_start:
{
lean_object* v_zero_218_; uint8_t v_isZero_219_; 
v_zero_218_ = lean_unsigned_to_nat(0u);
v_isZero_219_ = lean_nat_dec_eq(v_i_217_, v_zero_218_);
if (v_isZero_219_ == 1)
{
lean_object* v___x_220_; 
lean_dec(v_i_217_);
lean_dec(v_mod_215_);
v___x_220_ = lean_box(0);
return v___x_220_;
}
else
{
lean_object* v_one_221_; lean_object* v_n_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_one_221_ = lean_unsigned_to_nat(1u);
v_n_222_ = lean_nat_sub(v_i_217_, v_one_221_);
lean_dec(v_i_217_);
v___x_223_ = lean_array_fget_borrowed(v_as_216_, v_n_222_);
lean_inc(v___x_223_);
lean_inc(v_mod_215_);
v___x_224_ = l_Lake_LeanLib_findModule_x3f(v_mod_215_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
v_i_217_ = v_n_222_;
goto _start;
}
else
{
lean_dec(v_n_222_);
lean_dec(v_mod_215_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_226_, lean_object* v_as_227_, lean_object* v_i_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_226_, v_as_227_, v_i_228_);
lean_dec_ref(v_as_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object* v_mod_232_, lean_object* v_self_233_){
_start:
{
lean_object* v___y_235_; lean_object* v_targetDecls_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_targetDecls_238_ = lean_ctor_get(v_self_233_, 15);
lean_inc_ref(v_targetDecls_238_);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = ((lean_object*)(l_Lake_Package_findModule_x3f___closed__0));
v___x_241_ = lean_array_get_size(v_targetDecls_238_);
v___x_242_ = lean_nat_dec_lt(v___x_239_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec_ref(v_targetDecls_238_);
lean_dec_ref(v_self_233_);
v___y_235_ = v___x_240_;
goto v___jp_234_;
}
else
{
size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((size_t)0ULL);
v___x_244_ = lean_usize_of_nat(v___x_241_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_233_, v_targetDecls_238_, v___x_243_, v___x_244_, v___x_240_);
lean_dec_ref(v_targetDecls_238_);
v___y_235_ = v___x_245_;
goto v___jp_234_;
}
v___jp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_array_get_size(v___y_235_);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_232_, v___y_235_, v___x_236_);
lean_dec_ref(v___y_235_);
return v___x_237_;
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
uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object* v_x_256_, lean_object* v_x_257_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_256_ = stack[0].m_obj;
lean_object* v_x_257_ = stack[1].m_obj;
uint8_t v_res_264_;
v_res_264_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_256_, v_x_257_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_265_, v_x_266_);
lean_dec(v_x_266_);
lean_dec(v_x_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object* v___x_269_, lean_object* v_f_270_, lean_object* v_x_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_Lean_Name_append(v___x_269_, v_x_271_);
v___x_275_ = lean_apply_3(v_f_270_, v___x_274_, v___y_272_, lean_box(0));
return v___x_275_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_269_ = stack[0].m_obj;
lean_object* v_f_270_ = stack[1].m_obj;
lean_object* v_x_271_ = stack[2].m_obj;
lean_object* v___y_272_ = stack[3].m_obj;
lean_object* v_res_276_;
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_269_, v_f_270_, v_x_271_, v___y_272_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object* v___x_277_, lean_object* v_f_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_277_, v_f_278_, v_x_279_, v___y_280_);
return v_res_282_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object* v_f_286_, lean_object* v_as_287_, size_t v_sz_288_, size_t v_i_289_, lean_object* v_b_290_, lean_object* v___y_291_){
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
lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_302_ = lean_box(0);
v_a_303_ = lean_array_uget_borrowed(v_as_287_, v_i_289_);
lean_inc(v_a_303_);
v___x_304_ = l_IO_FS_DirEntry_path(v_a_303_);
v___x_305_ = l_System_FilePath_isDir(v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = l_System_FilePath_extension(v___x_304_);
v___x_307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1));
v___x_308_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
if (v___x_308_ == 0)
{
v_a_294_ = v___x_302_;
v_snd_295_ = v___y_291_;
goto v___jp_293_;
}
else
{
lean_object* v_fileName_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_fileName_309_ = lean_ctor_get(v_a_303_, 1);
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
v_a_294_ = v___x_302_;
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
v_fileName_317_ = lean_ctor_get(v_a_303_, 1);
v___x_318_ = lean_box(0);
lean_inc_ref(v_fileName_317_);
v___x_319_ = l_Lean_Name_str___override(v___x_318_, v_fileName_317_);
lean_inc_ref(v_f_286_);
v___f_320_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_320_, 0, v___x_319_);
lean_closure_set(v___f_320_, 1, v_f_286_);
v___x_321_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_304_, v___f_320_, v___y_291_);
lean_dec_ref(v___x_304_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_snd_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v_snd_323_ = lean_ctor_get(v_a_322_, 1);
lean_inc(v_snd_323_);
lean_dec(v_a_322_);
v_a_294_ = v___x_302_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_286_ = stack[0].m_obj;
lean_object* v_as_287_ = stack[1].m_obj;
size_t v_sz_288_ = stack[2].m_num;
size_t v_i_289_ = stack[3].m_num;
lean_object* v_b_290_ = stack[4].m_obj;
lean_object* v___y_291_ = stack[5].m_obj;
lean_object* v_res_324_;
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_286_, v_as_287_, v_sz_288_, v_i_289_, v_b_290_, v___y_291_);
stack->m_obj
 = v_res_324_;
}
lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object* v_dir_325_, lean_object* v_f_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_io_read_dir(v_dir_325_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; size_t v_sz_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = lean_box(0);
v_sz_332_ = lean_array_size(v_a_330_);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_326_, v_a_330_, v_sz_332_, v___x_333_, v___x_331_, v___y_327_);
lean_dec(v_a_330_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_351_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_351_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_351_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_351_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_snd_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_349_; 
v_snd_339_ = lean_ctor_get(v_a_335_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_335_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_a_335_, 0);
lean_dec(v_unused_350_);
v___x_341_ = v_a_335_;
v_isShared_342_ = v_isSharedCheck_349_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_339_);
lean_dec(v_a_335_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_349_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_331_);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_snd_339_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_344_);
v___x_346_ = v___x_337_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
else
{
return v___x_334_;
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___y_327_);
lean_dec_ref(v_f_326_);
v_a_352_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_329_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_329_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_dir_325_ = stack[0].m_obj;
lean_object* v_f_326_ = stack[1].m_obj;
lean_object* v___y_327_ = stack[2].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_325_, v_f_326_, v___y_327_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object* v_dir_361_, lean_object* v_f_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_361_, v_f_362_, v___y_363_);
lean_dec_ref(v_dir_361_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object* v_f_366_, lean_object* v_as_367_, lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_b_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_374_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_366_, v_as_367_, v_sz_boxed_373_, v_i_boxed_374_, v_b_370_, v___y_371_);
lean_dec_ref(v_as_367_);
return v_res_375_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object* v_self_376_, lean_object* v_mod_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_self_376_);
lean_ctor_set(v___x_381_, 1, v_mod_377_);
v___x_382_ = lean_array_push(v___y_378_, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_380_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_376_ = stack[0].m_obj;
lean_object* v_mod_377_ = stack[1].m_obj;
lean_object* v___y_378_ = stack[2].m_obj;
lean_object* v_res_385_;
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_376_, v_mod_377_, v___y_378_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object* v_self_386_, lean_object* v_mod_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_386_, v_mod_387_, v___y_388_);
return v_res_390_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object* v_a_391_, lean_object* v___f_392_, lean_object* v_x_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l_Lean_Name_append(v_a_391_, v_x_393_);
v___x_397_ = lean_apply_3(v___f_392_, v___x_396_, v___y_394_, lean_box(0));
return v___x_397_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_391_ = stack[0].m_obj;
lean_object* v___f_392_ = stack[1].m_obj;
lean_object* v_x_393_ = stack[2].m_obj;
lean_object* v___y_394_ = stack[3].m_obj;
lean_object* v_res_398_;
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_391_, v___f_392_, v_x_393_, v___y_394_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object* v_a_399_, lean_object* v___f_400_, lean_object* v_x_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_399_, v___f_400_, v_x_401_, v___y_402_);
return v_res_404_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object* v_self_405_, lean_object* v_as_406_, size_t v_i_407_, size_t v_stop_408_, lean_object* v_b_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___y_413_; uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_eq(v_i_407_, v_stop_408_);
if (v___x_420_ == 0)
{
lean_object* v_pkg_421_; lean_object* v_config_422_; lean_object* v_config_423_; lean_object* v_dir_424_; lean_object* v_srcDir_425_; lean_object* v_srcDir_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_pkg_421_ = lean_ctor_get(v_self_405_, 0);
v_config_422_ = lean_ctor_get(v_pkg_421_, 6);
v_config_423_ = lean_ctor_get(v_self_405_, 2);
v_dir_424_ = lean_ctor_get(v_pkg_421_, 4);
v_srcDir_425_ = lean_ctor_get(v_config_422_, 4);
v_srcDir_426_ = lean_ctor_get(v_config_423_, 1);
lean_inc_ref(v_self_405_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(v___f_427_, 0, v_self_405_);
v___x_428_ = lean_array_uget_borrowed(v_as_406_, v_i_407_);
lean_inc_ref(v_srcDir_425_);
v___x_429_ = l_System_FilePath_normalize(v_srcDir_425_);
lean_inc_ref(v_dir_424_);
v___x_430_ = l_Lake_joinRelative(v_dir_424_, v___x_429_);
lean_inc_ref(v_srcDir_426_);
v___x_431_ = l_System_FilePath_normalize(v_srcDir_426_);
v___x_432_ = l_Lake_joinRelative(v___x_430_, v___x_431_);
switch(lean_obj_tag(v___x_428_))
{
case 0:
{
lean_object* v_a_433_; lean_object* v___x_434_; 
lean_dec_ref(v___x_432_);
lean_dec_ref(v___f_427_);
v_a_433_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_433_);
lean_inc_ref(v_self_405_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_405_, v_a_433_, v___y_410_);
v___y_413_ = v___x_434_;
goto v___jp_412_;
}
case 1:
{
lean_object* v_a_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_435_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_435_, 2);
v___f_436_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_436_, 0, v_a_435_);
lean_closure_set(v___f_436_, 1, v___f_427_);
v___x_437_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_438_ = l_Lean_modToFilePath(v___x_432_, v_a_435_, v___x_437_);
lean_dec_ref(v___x_432_);
v___x_439_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_438_, v___f_436_, v___y_410_);
lean_dec_ref(v___x_438_);
v___y_413_ = v___x_439_;
goto v___jp_412_;
}
default: 
{
lean_object* v_a_440_; lean_object* v___f_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_440_, 2);
v___f_441_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_441_, 0, v_a_440_);
lean_closure_set(v___f_441_, 1, v___f_427_);
lean_inc_ref(v_self_405_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_405_, v_a_440_, v___y_410_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v_snd_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v_snd_444_ = lean_ctor_get(v_a_443_, 1);
lean_inc(v_snd_444_);
lean_dec(v_a_443_);
v___x_445_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc(v_a_440_);
v___x_446_ = l_Lean_modToFilePath(v___x_432_, v_a_440_, v___x_445_);
lean_dec_ref(v___x_432_);
v___x_447_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_446_, v___f_441_, v_snd_444_);
lean_dec_ref(v___x_446_);
v___y_413_ = v___x_447_;
goto v___jp_412_;
}
else
{
lean_dec_ref(v___f_441_);
lean_dec_ref(v___x_432_);
lean_dec_ref(v_self_405_);
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v_self_405_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_b_409_);
lean_ctor_set(v___x_448_, 1, v___y_410_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
v___jp_412_:
{
if (lean_obj_tag(v___y_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; size_t v___x_417_; size_t v___x_418_; 
v_a_414_ = lean_ctor_get(v___y_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___y_413_, 1);
v_fst_415_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_fst_415_);
v_snd_416_ = lean_ctor_get(v_a_414_, 1);
lean_inc(v_snd_416_);
lean_dec(v_a_414_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_407_, v___x_417_);
v_i_407_ = v___x_418_;
v_b_409_ = v_fst_415_;
v___y_410_ = v_snd_416_;
goto _start;
}
else
{
lean_dec_ref(v_self_405_);
return v___y_413_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_405_ = stack[0].m_obj;
lean_object* v_as_406_ = stack[1].m_obj;
size_t v_i_407_ = stack[2].m_num;
size_t v_stop_408_ = stack[3].m_num;
lean_object* v_b_409_ = stack[4].m_obj;
lean_object* v___y_410_ = stack[5].m_obj;
lean_object* v_res_450_;
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_405_, v_as_406_, v_i_407_, v_stop_408_, v_b_409_, v___y_410_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object* v_self_451_, lean_object* v_as_452_, lean_object* v_i_453_, lean_object* v_stop_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; lean_object* v_res_460_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_451_, v_as_452_, v_i_boxed_458_, v_stop_boxed_459_, v_b_455_, v___y_456_);
lean_dec_ref(v_as_452_);
return v_res_460_;
}
}
lean_object* l_Lake_LeanLib_getModuleArray(lean_object* v_self_463_){
_start:
{
lean_object* v___y_466_; lean_object* v_config_484_; lean_object* v_globs_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_config_484_ = lean_ctor_get(v_self_463_, 2);
v_globs_485_ = lean_ctor_get(v_config_484_, 3);
lean_inc_ref(v_globs_485_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_array_get_size(v_globs_485_);
v___x_488_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_489_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v_globs_485_);
lean_dec_ref(v_self_463_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_nat_dec_le(v___x_487_, v___x_487_);
if (v___x_492_ == 0)
{
if (v___x_489_ == 0)
{
lean_object* v___x_493_; 
lean_dec_ref(v_globs_485_);
lean_dec_ref(v_self_463_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_488_);
return v___x_493_;
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_usize_of_nat(v___x_487_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_463_, v_globs_485_, v___x_494_, v___x_495_, v___x_491_, v___x_488_);
lean_dec_ref(v_globs_485_);
v___y_466_ = v___x_496_;
goto v___jp_465_;
}
}
else
{
size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v___x_497_ = ((size_t)0ULL);
v___x_498_ = lean_usize_of_nat(v___x_487_);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_463_, v_globs_485_, v___x_497_, v___x_498_, v___x_491_, v___x_488_);
lean_dec_ref(v_globs_485_);
v___y_466_ = v___x_499_;
goto v___jp_465_;
}
}
v___jp_465_:
{
if (lean_obj_tag(v___y_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_a_467_ = lean_ctor_get(v___y_466_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___y_466_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v___y_466_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___y_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_snd_471_; lean_object* v___x_473_; 
v_snd_471_ = lean_ctor_get(v_a_467_, 1);
lean_inc(v_snd_471_);
lean_dec(v_a_467_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_snd_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_snd_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_a_476_ = lean_ctor_get(v___y_466_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___y_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___y_466_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___y_466_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_LeanLib_getModuleArray_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_463_ = stack[0].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Lake_LeanLib_getModuleArray(v_self_463_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object* v_self_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_LeanLib_getModuleArray(v_self_501_);
return v_res_503_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object* v_self_504_, lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_, lean_object* v_b_508_){
_start:
{
lean_object* v___y_510_; uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
lean_inc_ref(v_self_504_);
lean_inc(v___x_515_);
v___x_516_ = l_Lake_LeanLib_findModule_x3f(v___x_515_, v_self_504_);
if (lean_obj_tag(v___x_516_) == 0)
{
v___y_510_ = v_b_508_;
goto v___jp_509_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_518_; 
v_val_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = lean_array_push(v_b_508_, v_val_517_);
v___y_510_ = v___x_518_;
goto v___jp_509_;
}
}
else
{
lean_dec_ref(v_self_504_);
return v_b_508_;
}
v___jp_509_:
{
size_t v___x_511_; size_t v___x_512_; 
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_506_, v___x_511_);
v_i_506_ = v___x_512_;
v_b_508_ = v___y_510_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_504_ = stack[0].m_obj;
lean_object* v_as_505_ = stack[1].m_obj;
size_t v_i_506_ = stack[2].m_num;
size_t v_stop_507_ = stack[3].m_num;
lean_object* v_b_508_ = stack[4].m_obj;
lean_object* v_res_519_;
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_504_, v_as_505_, v_i_506_, v_stop_507_, v_b_508_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object* v_self_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_){
_start:
{
size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_520_, v_as_521_, v_i_boxed_525_, v_stop_boxed_526_, v_b_524_);
lean_dec_ref(v_as_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object* v_self_528_, lean_object* v_as_529_, lean_object* v_start_530_, lean_object* v_stop_531_){
_start:
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_533_ = lean_nat_dec_lt(v_start_530_, v_stop_531_);
if (v___x_533_ == 0)
{
lean_dec_ref(v_self_528_);
return v___x_532_;
}
else
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_array_get_size(v_as_529_);
v___x_535_ = lean_nat_dec_le(v_stop_531_, v___x_534_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = lean_nat_dec_lt(v_start_530_, v___x_534_);
if (v___x_536_ == 0)
{
lean_dec_ref(v_self_528_);
return v___x_532_;
}
else
{
size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_usize_of_nat(v_start_530_);
v___x_538_ = lean_usize_of_nat(v___x_534_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_528_, v_as_529_, v___x_537_, v___x_538_, v___x_532_);
return v___x_539_;
}
}
else
{
size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_usize_of_nat(v_start_530_);
v___x_541_ = lean_usize_of_nat(v_stop_531_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_528_, v_as_529_, v___x_540_, v___x_541_, v___x_532_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object* v_self_543_, lean_object* v_as_544_, lean_object* v_start_545_, lean_object* v_stop_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_543_, v_as_544_, v_start_545_, v_stop_546_);
lean_dec(v_stop_546_);
lean_dec(v_start_545_);
lean_dec_ref(v_as_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* v_self_548_){
_start:
{
lean_object* v_config_549_; lean_object* v_roots_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_config_549_ = lean_ctor_get(v_self_548_, 2);
v_roots_550_ = lean_ctor_get(v_config_549_, 2);
lean_inc_ref(v_roots_550_);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_array_get_size(v_roots_550_);
v___x_553_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_548_, v_roots_550_, v___x_551_, v___x_552_);
lean_dec_ref(v_roots_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* v_self_554_){
_start:
{
lean_object* v_lib_555_; lean_object* v_pkg_556_; 
v_lib_555_ = lean_ctor_get(v_self_554_, 0);
v_pkg_556_ = lean_ctor_get(v_lib_555_, 0);
lean_inc_ref(v_pkg_556_);
return v_pkg_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* v_self_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lake_Module_pkg(v_self_557_);
lean_dec_ref(v_self_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* v_self_559_){
_start:
{
lean_object* v_lib_560_; lean_object* v_pkg_561_; lean_object* v_config_562_; lean_object* v_config_563_; lean_object* v_dir_564_; lean_object* v_srcDir_565_; lean_object* v_srcDir_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_lib_560_ = lean_ctor_get(v_self_559_, 0);
lean_inc_ref(v_lib_560_);
lean_dec_ref(v_self_559_);
v_pkg_561_ = lean_ctor_get(v_lib_560_, 0);
lean_inc_ref(v_pkg_561_);
v_config_562_ = lean_ctor_get(v_pkg_561_, 6);
lean_inc_ref(v_config_562_);
v_config_563_ = lean_ctor_get(v_lib_560_, 2);
lean_inc(v_config_563_);
lean_dec_ref(v_lib_560_);
v_dir_564_ = lean_ctor_get(v_pkg_561_, 4);
lean_inc_ref(v_dir_564_);
lean_dec_ref(v_pkg_561_);
v_srcDir_565_ = lean_ctor_get(v_config_562_, 4);
lean_inc_ref(v_srcDir_565_);
lean_dec_ref(v_config_562_);
v_srcDir_566_ = lean_ctor_get(v_config_563_, 1);
lean_inc_ref(v_srcDir_566_);
lean_dec(v_config_563_);
v___x_567_ = l_System_FilePath_normalize(v_srcDir_565_);
v___x_568_ = l_Lake_joinRelative(v_dir_564_, v___x_567_);
v___x_569_ = l_System_FilePath_normalize(v_srcDir_566_);
v___x_570_ = l_Lake_joinRelative(v___x_568_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object* v_ext_571_, lean_object* v_self_572_){
_start:
{
lean_object* v_name_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_name_573_ = lean_ctor_get(v_self_572_, 1);
v___x_574_ = l_Lean_Name_getString_x21(v_name_573_);
v___x_575_ = l_System_FilePath_addExtension(v___x_574_, v_ext_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object* v_ext_576_, lean_object* v_self_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lake_Module_fileName(v_ext_576_, v_self_577_);
lean_dec_ref(v_self_577_);
lean_dec_ref(v_ext_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_579_, lean_object* v_ext_580_, lean_object* v_self_581_){
_start:
{
lean_object* v_name_582_; lean_object* v___x_583_; 
v_name_582_ = lean_ctor_get(v_self_581_, 1);
lean_inc(v_name_582_);
lean_dec_ref(v_self_581_);
v___x_583_ = l_Lean_modToFilePath(v_dir_579_, v_name_582_, v_ext_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_584_, lean_object* v_ext_585_, lean_object* v_self_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lake_Module_filePath(v_dir_584_, v_ext_585_, v_self_586_);
lean_dec_ref(v_ext_585_);
lean_dec_ref(v_dir_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_588_, lean_object* v_self_589_){
_start:
{
lean_object* v_lib_590_; lean_object* v_pkg_591_; lean_object* v_config_592_; lean_object* v_config_593_; lean_object* v_name_594_; lean_object* v_dir_595_; lean_object* v_srcDir_596_; lean_object* v_srcDir_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_lib_590_ = lean_ctor_get(v_self_589_, 0);
v_pkg_591_ = lean_ctor_get(v_lib_590_, 0);
lean_inc_ref(v_pkg_591_);
v_config_592_ = lean_ctor_get(v_pkg_591_, 6);
lean_inc_ref(v_config_592_);
v_config_593_ = lean_ctor_get(v_lib_590_, 2);
lean_inc(v_config_593_);
v_name_594_ = lean_ctor_get(v_self_589_, 1);
lean_inc(v_name_594_);
lean_dec_ref(v_self_589_);
v_dir_595_ = lean_ctor_get(v_pkg_591_, 4);
lean_inc_ref(v_dir_595_);
lean_dec_ref(v_pkg_591_);
v_srcDir_596_ = lean_ctor_get(v_config_592_, 4);
lean_inc_ref(v_srcDir_596_);
lean_dec_ref(v_config_592_);
v_srcDir_597_ = lean_ctor_get(v_config_593_, 1);
lean_inc_ref(v_srcDir_597_);
lean_dec(v_config_593_);
v___x_598_ = l_System_FilePath_normalize(v_srcDir_596_);
v___x_599_ = l_Lake_joinRelative(v_dir_595_, v___x_598_);
v___x_600_ = l_System_FilePath_normalize(v_srcDir_597_);
v___x_601_ = l_Lake_joinRelative(v___x_599_, v___x_600_);
v___x_602_ = l_Lean_modToFilePath(v___x_601_, v_name_594_, v_ext_588_);
lean_dec_ref(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_603_, lean_object* v_self_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lake_Module_srcPath(v_ext_603_, v_self_604_);
lean_dec_ref(v_ext_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_606_){
_start:
{
lean_object* v_lib_607_; lean_object* v_pkg_608_; lean_object* v_config_609_; lean_object* v_config_610_; lean_object* v_name_611_; lean_object* v_dir_612_; lean_object* v_srcDir_613_; lean_object* v_srcDir_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
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
v_srcDir_613_ = lean_ctor_get(v_config_609_, 4);
lean_inc_ref(v_srcDir_613_);
lean_dec_ref(v_config_609_);
v_srcDir_614_ = lean_ctor_get(v_config_610_, 1);
lean_inc_ref(v_srcDir_614_);
lean_dec(v_config_610_);
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_616_ = l_System_FilePath_normalize(v_srcDir_613_);
v___x_617_ = l_Lake_joinRelative(v_dir_612_, v___x_616_);
v___x_618_ = l_System_FilePath_normalize(v_srcDir_614_);
v___x_619_ = l_Lake_joinRelative(v___x_617_, v___x_618_);
v___x_620_ = l_Lean_modToFilePath(v___x_619_, v_name_611_, v___x_615_);
lean_dec_ref(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_621_){
_start:
{
lean_object* v_lib_622_; lean_object* v_pkg_623_; lean_object* v_config_624_; lean_object* v_config_625_; lean_object* v_name_626_; lean_object* v_dir_627_; lean_object* v_srcDir_628_; lean_object* v_srcDir_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_lib_622_ = lean_ctor_get(v_self_621_, 0);
v_pkg_623_ = lean_ctor_get(v_lib_622_, 0);
lean_inc_ref(v_pkg_623_);
v_config_624_ = lean_ctor_get(v_pkg_623_, 6);
lean_inc_ref(v_config_624_);
v_config_625_ = lean_ctor_get(v_lib_622_, 2);
lean_inc(v_config_625_);
v_name_626_ = lean_ctor_get(v_self_621_, 1);
lean_inc(v_name_626_);
lean_dec_ref(v_self_621_);
v_dir_627_ = lean_ctor_get(v_pkg_623_, 4);
lean_inc_ref_n(v_dir_627_, 2);
lean_dec_ref(v_pkg_623_);
v_srcDir_628_ = lean_ctor_get(v_config_624_, 4);
lean_inc_ref(v_srcDir_628_);
lean_dec_ref(v_config_624_);
v_srcDir_629_ = lean_ctor_get(v_config_625_, 1);
lean_inc_ref(v_srcDir_629_);
lean_dec(v_config_625_);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_631_ = l_System_FilePath_normalize(v_srcDir_628_);
v___x_632_ = l_Lake_joinRelative(v_dir_627_, v___x_631_);
v___x_633_ = l_System_FilePath_normalize(v_srcDir_629_);
v___x_634_ = l_Lake_joinRelative(v___x_632_, v___x_633_);
v___x_635_ = l_Lean_modToFilePath(v___x_634_, v_name_626_, v___x_630_);
lean_dec_ref(v___x_634_);
v___x_636_ = l_Lake_relPathFrom(v_dir_627_, v___x_635_);
lean_dec_ref(v_dir_627_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_637_, lean_object* v_self_638_){
_start:
{
lean_object* v_lib_639_; lean_object* v_pkg_640_; lean_object* v_config_641_; lean_object* v_name_642_; lean_object* v_dir_643_; lean_object* v_buildDir_644_; lean_object* v_leanLibDir_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_lib_639_ = lean_ctor_get(v_self_638_, 0);
v_pkg_640_ = lean_ctor_get(v_lib_639_, 0);
lean_inc_ref(v_pkg_640_);
v_config_641_ = lean_ctor_get(v_pkg_640_, 6);
lean_inc_ref(v_config_641_);
v_name_642_ = lean_ctor_get(v_self_638_, 1);
lean_inc(v_name_642_);
lean_dec_ref(v_self_638_);
v_dir_643_ = lean_ctor_get(v_pkg_640_, 4);
lean_inc_ref(v_dir_643_);
lean_dec_ref(v_pkg_640_);
v_buildDir_644_ = lean_ctor_get(v_config_641_, 5);
lean_inc_ref(v_buildDir_644_);
v_leanLibDir_645_ = lean_ctor_get(v_config_641_, 6);
lean_inc_ref(v_leanLibDir_645_);
lean_dec_ref(v_config_641_);
v___x_646_ = l_System_FilePath_normalize(v_buildDir_644_);
v___x_647_ = l_Lake_joinRelative(v_dir_643_, v___x_646_);
v___x_648_ = l_System_FilePath_normalize(v_leanLibDir_645_);
v___x_649_ = l_Lake_joinRelative(v___x_647_, v___x_648_);
v___x_650_ = l_Lean_modToFilePath(v___x_649_, v_name_642_, v_ext_637_);
lean_dec_ref(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_651_, lean_object* v_self_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lake_Module_leanLibPath(v_ext_651_, v_self_652_);
lean_dec_ref(v_ext_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object* v_self_654_){
_start:
{
lean_object* v_lib_655_; lean_object* v_pkg_656_; lean_object* v_config_657_; lean_object* v_name_658_; lean_object* v_dir_659_; lean_object* v_buildDir_660_; lean_object* v_leanLibDir_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_lib_655_ = lean_ctor_get(v_self_654_, 0);
v_pkg_656_ = lean_ctor_get(v_lib_655_, 0);
lean_inc_ref(v_pkg_656_);
v_config_657_ = lean_ctor_get(v_pkg_656_, 6);
lean_inc_ref(v_config_657_);
v_name_658_ = lean_ctor_get(v_self_654_, 1);
lean_inc(v_name_658_);
lean_dec_ref(v_self_654_);
v_dir_659_ = lean_ctor_get(v_pkg_656_, 4);
lean_inc_ref(v_dir_659_);
lean_dec_ref(v_pkg_656_);
v_buildDir_660_ = lean_ctor_get(v_config_657_, 5);
lean_inc_ref(v_buildDir_660_);
v_leanLibDir_661_ = lean_ctor_get(v_config_657_, 6);
lean_inc_ref(v_leanLibDir_661_);
lean_dec_ref(v_config_657_);
v___x_662_ = l_System_FilePath_normalize(v_buildDir_660_);
v___x_663_ = l_Lake_joinRelative(v_dir_659_, v___x_662_);
v___x_664_ = l_System_FilePath_normalize(v_leanLibDir_661_);
v___x_665_ = l_Lake_joinRelative(v___x_663_, v___x_664_);
v___x_666_ = l_Lean_Name_getPrefix(v_name_658_);
lean_dec(v_name_658_);
v___x_667_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_668_ = l_Lean_modToFilePath(v___x_665_, v___x_666_, v___x_667_);
lean_dec_ref(v___x_665_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_670_){
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
v_buildDir_676_ = lean_ctor_get(v_config_673_, 5);
lean_inc_ref(v_buildDir_676_);
v_leanLibDir_677_ = lean_ctor_get(v_config_673_, 6);
lean_inc_ref(v_leanLibDir_677_);
lean_dec_ref(v_config_673_);
v___x_678_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_679_ = l_System_FilePath_normalize(v_buildDir_676_);
v___x_680_ = l_Lake_joinRelative(v_dir_675_, v___x_679_);
v___x_681_ = l_System_FilePath_normalize(v_leanLibDir_677_);
v___x_682_ = l_Lake_joinRelative(v___x_680_, v___x_681_);
v___x_683_ = l_Lean_modToFilePath(v___x_682_, v_name_674_, v___x_678_);
lean_dec_ref(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_685_){
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
v_buildDir_691_ = lean_ctor_get(v_config_688_, 5);
lean_inc_ref(v_buildDir_691_);
v_leanLibDir_692_ = lean_ctor_get(v_config_688_, 6);
lean_inc_ref(v_leanLibDir_692_);
lean_dec_ref(v_config_688_);
v___x_693_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_694_ = l_System_FilePath_normalize(v_buildDir_691_);
v___x_695_ = l_Lake_joinRelative(v_dir_690_, v___x_694_);
v___x_696_ = l_System_FilePath_normalize(v_leanLibDir_692_);
v___x_697_ = l_Lake_joinRelative(v___x_695_, v___x_696_);
v___x_698_ = l_Lean_modToFilePath(v___x_697_, v_name_689_, v___x_693_);
lean_dec_ref(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_700_){
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
v_buildDir_706_ = lean_ctor_get(v_config_703_, 5);
lean_inc_ref(v_buildDir_706_);
v_leanLibDir_707_ = lean_ctor_get(v_config_703_, 6);
lean_inc_ref(v_leanLibDir_707_);
lean_dec_ref(v_config_703_);
v___x_708_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_709_ = l_System_FilePath_normalize(v_buildDir_706_);
v___x_710_ = l_Lake_joinRelative(v_dir_705_, v___x_709_);
v___x_711_ = l_System_FilePath_normalize(v_leanLibDir_707_);
v___x_712_ = l_Lake_joinRelative(v___x_710_, v___x_711_);
v___x_713_ = l_Lean_modToFilePath(v___x_712_, v_name_704_, v___x_708_);
lean_dec_ref(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_715_){
_start:
{
lean_object* v_lib_716_; lean_object* v_pkg_717_; lean_object* v_config_718_; lean_object* v_name_719_; lean_object* v_dir_720_; lean_object* v_buildDir_721_; lean_object* v_leanLibDir_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
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
v_buildDir_721_ = lean_ctor_get(v_config_718_, 5);
lean_inc_ref(v_buildDir_721_);
v_leanLibDir_722_ = lean_ctor_get(v_config_718_, 6);
lean_inc_ref(v_leanLibDir_722_);
lean_dec_ref(v_config_718_);
v___x_723_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_724_ = l_System_FilePath_normalize(v_buildDir_721_);
v___x_725_ = l_Lake_joinRelative(v_dir_720_, v___x_724_);
v___x_726_ = l_System_FilePath_normalize(v_leanLibDir_722_);
v___x_727_ = l_Lake_joinRelative(v___x_725_, v___x_726_);
v___x_728_ = l_Lean_modToFilePath(v___x_727_, v_name_719_, v___x_723_);
lean_dec_ref(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object* v_self_730_){
_start:
{
lean_object* v_lib_731_; lean_object* v_pkg_732_; lean_object* v_config_733_; lean_object* v_name_734_; lean_object* v_dir_735_; lean_object* v_buildDir_736_; lean_object* v_leanLibDir_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_lib_731_ = lean_ctor_get(v_self_730_, 0);
v_pkg_732_ = lean_ctor_get(v_lib_731_, 0);
lean_inc_ref(v_pkg_732_);
v_config_733_ = lean_ctor_get(v_pkg_732_, 6);
lean_inc_ref(v_config_733_);
v_name_734_ = lean_ctor_get(v_self_730_, 1);
lean_inc(v_name_734_);
lean_dec_ref(v_self_730_);
v_dir_735_ = lean_ctor_get(v_pkg_732_, 4);
lean_inc_ref(v_dir_735_);
lean_dec_ref(v_pkg_732_);
v_buildDir_736_ = lean_ctor_get(v_config_733_, 5);
lean_inc_ref(v_buildDir_736_);
v_leanLibDir_737_ = lean_ctor_get(v_config_733_, 6);
lean_inc_ref(v_leanLibDir_737_);
lean_dec_ref(v_config_733_);
v___x_738_ = ((lean_object*)(l_Lake_Module_irSigFile___closed__0));
v___x_739_ = l_System_FilePath_normalize(v_buildDir_736_);
v___x_740_ = l_Lake_joinRelative(v_dir_735_, v___x_739_);
v___x_741_ = l_System_FilePath_normalize(v_leanLibDir_737_);
v___x_742_ = l_Lake_joinRelative(v___x_740_, v___x_741_);
v___x_743_ = l_Lean_modToFilePath(v___x_742_, v_name_734_, v___x_738_);
lean_dec_ref(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_745_){
_start:
{
lean_object* v_lib_746_; lean_object* v_pkg_747_; lean_object* v_config_748_; lean_object* v_name_749_; lean_object* v_dir_750_; lean_object* v_buildDir_751_; lean_object* v_leanLibDir_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_lib_746_ = lean_ctor_get(v_self_745_, 0);
v_pkg_747_ = lean_ctor_get(v_lib_746_, 0);
lean_inc_ref(v_pkg_747_);
v_config_748_ = lean_ctor_get(v_pkg_747_, 6);
lean_inc_ref(v_config_748_);
v_name_749_ = lean_ctor_get(v_self_745_, 1);
lean_inc(v_name_749_);
lean_dec_ref(v_self_745_);
v_dir_750_ = lean_ctor_get(v_pkg_747_, 4);
lean_inc_ref(v_dir_750_);
lean_dec_ref(v_pkg_747_);
v_buildDir_751_ = lean_ctor_get(v_config_748_, 5);
lean_inc_ref(v_buildDir_751_);
v_leanLibDir_752_ = lean_ctor_get(v_config_748_, 6);
lean_inc_ref(v_leanLibDir_752_);
lean_dec_ref(v_config_748_);
v___x_753_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_754_ = l_System_FilePath_normalize(v_buildDir_751_);
v___x_755_ = l_Lake_joinRelative(v_dir_750_, v___x_754_);
v___x_756_ = l_System_FilePath_normalize(v_leanLibDir_752_);
v___x_757_ = l_Lake_joinRelative(v___x_755_, v___x_756_);
v___x_758_ = l_Lean_modToFilePath(v___x_757_, v_name_749_, v___x_753_);
lean_dec_ref(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_760_){
_start:
{
lean_object* v_lib_761_; lean_object* v_pkg_762_; lean_object* v_config_763_; lean_object* v_name_764_; lean_object* v_dir_765_; lean_object* v_buildDir_766_; lean_object* v_leanLibDir_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_lib_761_ = lean_ctor_get(v_self_760_, 0);
v_pkg_762_ = lean_ctor_get(v_lib_761_, 0);
lean_inc_ref(v_pkg_762_);
v_config_763_ = lean_ctor_get(v_pkg_762_, 6);
lean_inc_ref(v_config_763_);
v_name_764_ = lean_ctor_get(v_self_760_, 1);
lean_inc(v_name_764_);
lean_dec_ref(v_self_760_);
v_dir_765_ = lean_ctor_get(v_pkg_762_, 4);
lean_inc_ref(v_dir_765_);
lean_dec_ref(v_pkg_762_);
v_buildDir_766_ = lean_ctor_get(v_config_763_, 5);
lean_inc_ref(v_buildDir_766_);
v_leanLibDir_767_ = lean_ctor_get(v_config_763_, 6);
lean_inc_ref(v_leanLibDir_767_);
lean_dec_ref(v_config_763_);
v___x_768_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_769_ = l_System_FilePath_normalize(v_buildDir_766_);
v___x_770_ = l_Lake_joinRelative(v_dir_765_, v___x_769_);
v___x_771_ = l_System_FilePath_normalize(v_leanLibDir_767_);
v___x_772_ = l_Lake_joinRelative(v___x_770_, v___x_771_);
v___x_773_ = l_Lean_modToFilePath(v___x_772_, v_name_764_, v___x_768_);
lean_dec_ref(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irTraceFile(lean_object* v_self_775_){
_start:
{
lean_object* v_lib_776_; lean_object* v_pkg_777_; lean_object* v_config_778_; lean_object* v_name_779_; lean_object* v_dir_780_; lean_object* v_buildDir_781_; lean_object* v_leanLibDir_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_lib_776_ = lean_ctor_get(v_self_775_, 0);
v_pkg_777_ = lean_ctor_get(v_lib_776_, 0);
lean_inc_ref(v_pkg_777_);
v_config_778_ = lean_ctor_get(v_pkg_777_, 6);
lean_inc_ref(v_config_778_);
v_name_779_ = lean_ctor_get(v_self_775_, 1);
lean_inc(v_name_779_);
lean_dec_ref(v_self_775_);
v_dir_780_ = lean_ctor_get(v_pkg_777_, 4);
lean_inc_ref(v_dir_780_);
lean_dec_ref(v_pkg_777_);
v_buildDir_781_ = lean_ctor_get(v_config_778_, 5);
lean_inc_ref(v_buildDir_781_);
v_leanLibDir_782_ = lean_ctor_get(v_config_778_, 6);
lean_inc_ref(v_leanLibDir_782_);
lean_dec_ref(v_config_778_);
v___x_783_ = ((lean_object*)(l_Lake_Module_irTraceFile___closed__0));
v___x_784_ = l_System_FilePath_normalize(v_buildDir_781_);
v___x_785_ = l_Lake_joinRelative(v_dir_780_, v___x_784_);
v___x_786_ = l_System_FilePath_normalize(v_leanLibDir_782_);
v___x_787_ = l_Lake_joinRelative(v___x_785_, v___x_786_);
v___x_788_ = l_Lean_modToFilePath(v___x_787_, v_name_779_, v___x_783_);
lean_dec_ref(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_789_, lean_object* v_self_790_){
_start:
{
lean_object* v_lib_791_; lean_object* v_pkg_792_; lean_object* v_config_793_; lean_object* v_name_794_; lean_object* v_dir_795_; lean_object* v_buildDir_796_; lean_object* v_irDir_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_lib_791_ = lean_ctor_get(v_self_790_, 0);
v_pkg_792_ = lean_ctor_get(v_lib_791_, 0);
lean_inc_ref(v_pkg_792_);
v_config_793_ = lean_ctor_get(v_pkg_792_, 6);
lean_inc_ref(v_config_793_);
v_name_794_ = lean_ctor_get(v_self_790_, 1);
lean_inc(v_name_794_);
lean_dec_ref(v_self_790_);
v_dir_795_ = lean_ctor_get(v_pkg_792_, 4);
lean_inc_ref(v_dir_795_);
lean_dec_ref(v_pkg_792_);
v_buildDir_796_ = lean_ctor_get(v_config_793_, 5);
lean_inc_ref(v_buildDir_796_);
v_irDir_797_ = lean_ctor_get(v_config_793_, 9);
lean_inc_ref(v_irDir_797_);
lean_dec_ref(v_config_793_);
v___x_798_ = l_System_FilePath_normalize(v_buildDir_796_);
v___x_799_ = l_Lake_joinRelative(v_dir_795_, v___x_798_);
v___x_800_ = l_System_FilePath_normalize(v_irDir_797_);
v___x_801_ = l_Lake_joinRelative(v___x_799_, v___x_800_);
v___x_802_ = l_Lean_modToFilePath(v___x_801_, v_name_794_, v_ext_789_);
lean_dec_ref(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_803_, lean_object* v_self_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lake_Module_irPath(v_ext_803_, v_self_804_);
lean_dec_ref(v_ext_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_806_){
_start:
{
lean_object* v_lib_807_; lean_object* v_pkg_808_; lean_object* v_config_809_; lean_object* v_name_810_; lean_object* v_dir_811_; lean_object* v_buildDir_812_; lean_object* v_irDir_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_lib_807_ = lean_ctor_get(v_self_806_, 0);
v_pkg_808_ = lean_ctor_get(v_lib_807_, 0);
lean_inc_ref(v_pkg_808_);
v_config_809_ = lean_ctor_get(v_pkg_808_, 6);
lean_inc_ref(v_config_809_);
v_name_810_ = lean_ctor_get(v_self_806_, 1);
lean_inc(v_name_810_);
lean_dec_ref(v_self_806_);
v_dir_811_ = lean_ctor_get(v_pkg_808_, 4);
lean_inc_ref(v_dir_811_);
lean_dec_ref(v_pkg_808_);
v_buildDir_812_ = lean_ctor_get(v_config_809_, 5);
lean_inc_ref(v_buildDir_812_);
v_irDir_813_ = lean_ctor_get(v_config_809_, 9);
lean_inc_ref(v_irDir_813_);
lean_dec_ref(v_config_809_);
v___x_814_ = l_System_FilePath_normalize(v_buildDir_812_);
v___x_815_ = l_Lake_joinRelative(v_dir_811_, v___x_814_);
v___x_816_ = l_System_FilePath_normalize(v_irDir_813_);
v___x_817_ = l_Lake_joinRelative(v___x_815_, v___x_816_);
v___x_818_ = l_Lean_Name_getPrefix(v_name_810_);
lean_dec(v_name_810_);
v___x_819_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_820_ = l_Lean_modToFilePath(v___x_817_, v___x_818_, v___x_819_);
lean_dec_ref(v___x_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_822_){
_start:
{
lean_object* v_lib_823_; lean_object* v_pkg_824_; lean_object* v_config_825_; lean_object* v_name_826_; lean_object* v_dir_827_; lean_object* v_buildDir_828_; lean_object* v_irDir_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_lib_823_ = lean_ctor_get(v_self_822_, 0);
v_pkg_824_ = lean_ctor_get(v_lib_823_, 0);
lean_inc_ref(v_pkg_824_);
v_config_825_ = lean_ctor_get(v_pkg_824_, 6);
lean_inc_ref(v_config_825_);
v_name_826_ = lean_ctor_get(v_self_822_, 1);
lean_inc(v_name_826_);
lean_dec_ref(v_self_822_);
v_dir_827_ = lean_ctor_get(v_pkg_824_, 4);
lean_inc_ref(v_dir_827_);
lean_dec_ref(v_pkg_824_);
v_buildDir_828_ = lean_ctor_get(v_config_825_, 5);
lean_inc_ref(v_buildDir_828_);
v_irDir_829_ = lean_ctor_get(v_config_825_, 9);
lean_inc_ref(v_irDir_829_);
lean_dec_ref(v_config_825_);
v___x_830_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_831_ = l_System_FilePath_normalize(v_buildDir_828_);
v___x_832_ = l_Lake_joinRelative(v_dir_827_, v___x_831_);
v___x_833_ = l_System_FilePath_normalize(v_irDir_829_);
v___x_834_ = l_Lake_joinRelative(v___x_832_, v___x_833_);
v___x_835_ = l_Lean_modToFilePath(v___x_834_, v_name_826_, v___x_830_);
lean_dec_ref(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSetupFile(lean_object* v_self_837_){
_start:
{
lean_object* v_lib_838_; lean_object* v_pkg_839_; lean_object* v_config_840_; lean_object* v_name_841_; lean_object* v_dir_842_; lean_object* v_buildDir_843_; lean_object* v_irDir_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_lib_838_ = lean_ctor_get(v_self_837_, 0);
v_pkg_839_ = lean_ctor_get(v_lib_838_, 0);
lean_inc_ref(v_pkg_839_);
v_config_840_ = lean_ctor_get(v_pkg_839_, 6);
lean_inc_ref(v_config_840_);
v_name_841_ = lean_ctor_get(v_self_837_, 1);
lean_inc(v_name_841_);
lean_dec_ref(v_self_837_);
v_dir_842_ = lean_ctor_get(v_pkg_839_, 4);
lean_inc_ref(v_dir_842_);
lean_dec_ref(v_pkg_839_);
v_buildDir_843_ = lean_ctor_get(v_config_840_, 5);
lean_inc_ref(v_buildDir_843_);
v_irDir_844_ = lean_ctor_get(v_config_840_, 9);
lean_inc_ref(v_irDir_844_);
lean_dec_ref(v_config_840_);
v___x_845_ = ((lean_object*)(l_Lake_Module_irSetupFile___closed__0));
v___x_846_ = l_System_FilePath_normalize(v_buildDir_843_);
v___x_847_ = l_Lake_joinRelative(v_dir_842_, v___x_846_);
v___x_848_ = l_System_FilePath_normalize(v_irDir_844_);
v___x_849_ = l_Lake_joinRelative(v___x_847_, v___x_848_);
v___x_850_ = l_Lean_modToFilePath(v___x_849_, v_name_841_, v___x_845_);
lean_dec_ref(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_852_){
_start:
{
lean_object* v_lib_853_; lean_object* v_pkg_854_; lean_object* v_config_855_; lean_object* v_name_856_; lean_object* v_dir_857_; lean_object* v_buildDir_858_; lean_object* v_irDir_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_lib_853_ = lean_ctor_get(v_self_852_, 0);
v_pkg_854_ = lean_ctor_get(v_lib_853_, 0);
lean_inc_ref(v_pkg_854_);
v_config_855_ = lean_ctor_get(v_pkg_854_, 6);
lean_inc_ref(v_config_855_);
v_name_856_ = lean_ctor_get(v_self_852_, 1);
lean_inc(v_name_856_);
lean_dec_ref(v_self_852_);
v_dir_857_ = lean_ctor_get(v_pkg_854_, 4);
lean_inc_ref(v_dir_857_);
lean_dec_ref(v_pkg_854_);
v_buildDir_858_ = lean_ctor_get(v_config_855_, 5);
lean_inc_ref(v_buildDir_858_);
v_irDir_859_ = lean_ctor_get(v_config_855_, 9);
lean_inc_ref(v_irDir_859_);
lean_dec_ref(v_config_855_);
v___x_860_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_861_ = l_System_FilePath_normalize(v_buildDir_858_);
v___x_862_ = l_Lake_joinRelative(v_dir_857_, v___x_861_);
v___x_863_ = l_System_FilePath_normalize(v_irDir_859_);
v___x_864_ = l_Lake_joinRelative(v___x_862_, v___x_863_);
v___x_865_ = l_Lean_modToFilePath(v___x_864_, v_name_856_, v___x_860_);
lean_dec_ref(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_867_){
_start:
{
lean_object* v_lib_868_; lean_object* v_pkg_869_; lean_object* v_config_870_; lean_object* v_name_871_; lean_object* v_dir_872_; lean_object* v_buildDir_873_; lean_object* v_irDir_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_lib_868_ = lean_ctor_get(v_self_867_, 0);
v_pkg_869_ = lean_ctor_get(v_lib_868_, 0);
lean_inc_ref(v_pkg_869_);
v_config_870_ = lean_ctor_get(v_pkg_869_, 6);
lean_inc_ref(v_config_870_);
v_name_871_ = lean_ctor_get(v_self_867_, 1);
lean_inc(v_name_871_);
lean_dec_ref(v_self_867_);
v_dir_872_ = lean_ctor_get(v_pkg_869_, 4);
lean_inc_ref(v_dir_872_);
lean_dec_ref(v_pkg_869_);
v_buildDir_873_ = lean_ctor_get(v_config_870_, 5);
lean_inc_ref(v_buildDir_873_);
v_irDir_874_ = lean_ctor_get(v_config_870_, 9);
lean_inc_ref(v_irDir_874_);
lean_dec_ref(v_config_870_);
v___x_875_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_876_ = l_System_FilePath_normalize(v_buildDir_873_);
v___x_877_ = l_Lake_joinRelative(v_dir_872_, v___x_876_);
v___x_878_ = l_System_FilePath_normalize(v_irDir_874_);
v___x_879_ = l_Lake_joinRelative(v___x_877_, v___x_878_);
v___x_880_ = l_Lean_modToFilePath(v___x_879_, v_name_871_, v___x_875_);
lean_dec_ref(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_882_){
_start:
{
lean_object* v_lib_883_; lean_object* v_pkg_884_; lean_object* v_config_885_; lean_object* v_name_886_; lean_object* v_dir_887_; lean_object* v_buildDir_888_; lean_object* v_irDir_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_lib_883_ = lean_ctor_get(v_self_882_, 0);
v_pkg_884_ = lean_ctor_get(v_lib_883_, 0);
lean_inc_ref(v_pkg_884_);
v_config_885_ = lean_ctor_get(v_pkg_884_, 6);
lean_inc_ref(v_config_885_);
v_name_886_ = lean_ctor_get(v_self_882_, 1);
lean_inc(v_name_886_);
lean_dec_ref(v_self_882_);
v_dir_887_ = lean_ctor_get(v_pkg_884_, 4);
lean_inc_ref(v_dir_887_);
lean_dec_ref(v_pkg_884_);
v_buildDir_888_ = lean_ctor_get(v_config_885_, 5);
lean_inc_ref(v_buildDir_888_);
v_irDir_889_ = lean_ctor_get(v_config_885_, 9);
lean_inc_ref(v_irDir_889_);
lean_dec_ref(v_config_885_);
v___x_890_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_891_ = l_System_FilePath_normalize(v_buildDir_888_);
v___x_892_ = l_Lake_joinRelative(v_dir_887_, v___x_891_);
v___x_893_ = l_System_FilePath_normalize(v_irDir_889_);
v___x_894_ = l_Lake_joinRelative(v___x_892_, v___x_893_);
v___x_895_ = l_Lean_modToFilePath(v___x_894_, v_name_886_, v___x_890_);
lean_dec_ref(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_897_){
_start:
{
lean_object* v_lib_898_; lean_object* v_pkg_899_; lean_object* v_config_900_; lean_object* v_name_901_; lean_object* v_dir_902_; lean_object* v_buildDir_903_; lean_object* v_irDir_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_lib_898_ = lean_ctor_get(v_self_897_, 0);
v_pkg_899_ = lean_ctor_get(v_lib_898_, 0);
lean_inc_ref(v_pkg_899_);
v_config_900_ = lean_ctor_get(v_pkg_899_, 6);
lean_inc_ref(v_config_900_);
v_name_901_ = lean_ctor_get(v_self_897_, 1);
lean_inc(v_name_901_);
lean_dec_ref(v_self_897_);
v_dir_902_ = lean_ctor_get(v_pkg_899_, 4);
lean_inc_ref(v_dir_902_);
lean_dec_ref(v_pkg_899_);
v_buildDir_903_ = lean_ctor_get(v_config_900_, 5);
lean_inc_ref(v_buildDir_903_);
v_irDir_904_ = lean_ctor_get(v_config_900_, 9);
lean_inc_ref(v_irDir_904_);
lean_dec_ref(v_config_900_);
v___x_905_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_906_ = l_System_FilePath_normalize(v_buildDir_903_);
v___x_907_ = l_Lake_joinRelative(v_dir_902_, v___x_906_);
v___x_908_ = l_System_FilePath_normalize(v_irDir_904_);
v___x_909_ = l_Lake_joinRelative(v___x_907_, v___x_908_);
v___x_910_ = l_Lean_modToFilePath(v___x_909_, v_name_901_, v___x_905_);
lean_dec_ref(v___x_909_);
return v___x_910_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_internal_has_llvm_backend(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec_ref(v_self_913_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
else
{
lean_object* v_lib_916_; lean_object* v_pkg_917_; lean_object* v_config_918_; lean_object* v_name_919_; lean_object* v_dir_920_; lean_object* v_buildDir_921_; lean_object* v_irDir_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_lib_916_ = lean_ctor_get(v_self_913_, 0);
v_pkg_917_ = lean_ctor_get(v_lib_916_, 0);
lean_inc_ref(v_pkg_917_);
v_config_918_ = lean_ctor_get(v_pkg_917_, 6);
lean_inc_ref(v_config_918_);
v_name_919_ = lean_ctor_get(v_self_913_, 1);
lean_inc(v_name_919_);
lean_dec_ref(v_self_913_);
v_dir_920_ = lean_ctor_get(v_pkg_917_, 4);
lean_inc_ref(v_dir_920_);
lean_dec_ref(v_pkg_917_);
v_buildDir_921_ = lean_ctor_get(v_config_918_, 5);
lean_inc_ref(v_buildDir_921_);
v_irDir_922_ = lean_ctor_get(v_config_918_, 9);
lean_inc_ref(v_irDir_922_);
lean_dec_ref(v_config_918_);
v___x_923_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_924_ = l_System_FilePath_normalize(v_buildDir_921_);
v___x_925_ = l_Lake_joinRelative(v_dir_920_, v___x_924_);
v___x_926_ = l_System_FilePath_normalize(v_irDir_922_);
v___x_927_ = l_Lake_joinRelative(v___x_925_, v___x_926_);
v___x_928_ = l_Lean_modToFilePath(v___x_927_, v_name_919_, v___x_923_);
lean_dec_ref(v___x_927_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_931_){
_start:
{
lean_object* v_lib_932_; lean_object* v_pkg_933_; lean_object* v_config_934_; lean_object* v_name_935_; lean_object* v_dir_936_; lean_object* v_buildDir_937_; lean_object* v_irDir_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_lib_932_ = lean_ctor_get(v_self_931_, 0);
v_pkg_933_ = lean_ctor_get(v_lib_932_, 0);
lean_inc_ref(v_pkg_933_);
v_config_934_ = lean_ctor_get(v_pkg_933_, 6);
lean_inc_ref(v_config_934_);
v_name_935_ = lean_ctor_get(v_self_931_, 1);
lean_inc(v_name_935_);
lean_dec_ref(v_self_931_);
v_dir_936_ = lean_ctor_get(v_pkg_933_, 4);
lean_inc_ref(v_dir_936_);
lean_dec_ref(v_pkg_933_);
v_buildDir_937_ = lean_ctor_get(v_config_934_, 5);
lean_inc_ref(v_buildDir_937_);
v_irDir_938_ = lean_ctor_get(v_config_934_, 9);
lean_inc_ref(v_irDir_938_);
lean_dec_ref(v_config_934_);
v___x_939_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_940_ = l_System_FilePath_normalize(v_buildDir_937_);
v___x_941_ = l_Lake_joinRelative(v_dir_936_, v___x_940_);
v___x_942_ = l_System_FilePath_normalize(v_irDir_938_);
v___x_943_ = l_Lake_joinRelative(v___x_941_, v___x_942_);
v___x_944_ = l_Lean_modToFilePath(v___x_943_, v_name_935_, v___x_939_);
lean_dec_ref(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_946_){
_start:
{
lean_object* v_lib_947_; lean_object* v_pkg_948_; lean_object* v_config_949_; lean_object* v_name_950_; lean_object* v_dir_951_; lean_object* v_buildDir_952_; lean_object* v_irDir_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_lib_947_ = lean_ctor_get(v_self_946_, 0);
v_pkg_948_ = lean_ctor_get(v_lib_947_, 0);
lean_inc_ref(v_pkg_948_);
v_config_949_ = lean_ctor_get(v_pkg_948_, 6);
lean_inc_ref(v_config_949_);
v_name_950_ = lean_ctor_get(v_self_946_, 1);
lean_inc(v_name_950_);
lean_dec_ref(v_self_946_);
v_dir_951_ = lean_ctor_get(v_pkg_948_, 4);
lean_inc_ref(v_dir_951_);
lean_dec_ref(v_pkg_948_);
v_buildDir_952_ = lean_ctor_get(v_config_949_, 5);
lean_inc_ref(v_buildDir_952_);
v_irDir_953_ = lean_ctor_get(v_config_949_, 9);
lean_inc_ref(v_irDir_953_);
lean_dec_ref(v_config_949_);
v___x_954_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_955_ = l_System_FilePath_normalize(v_buildDir_952_);
v___x_956_ = l_Lake_joinRelative(v_dir_951_, v___x_955_);
v___x_957_ = l_System_FilePath_normalize(v_irDir_953_);
v___x_958_ = l_Lake_joinRelative(v___x_956_, v___x_957_);
v___x_959_ = l_Lean_modToFilePath(v___x_958_, v_name_950_, v___x_954_);
lean_dec_ref(v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_962_){
_start:
{
lean_object* v_lib_963_; lean_object* v_name_964_; lean_object* v_pkg_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_lib_963_ = lean_ctor_get(v_self_962_, 0);
lean_inc_ref(v_lib_963_);
v_name_964_ = lean_ctor_get(v_self_962_, 1);
lean_inc(v_name_964_);
lean_dec_ref(v_self_962_);
v_pkg_965_ = lean_ctor_get(v_lib_963_, 0);
lean_inc_ref(v_pkg_965_);
lean_dec_ref(v_lib_963_);
v___x_966_ = l_Lake_Package_id_x3f(v_pkg_965_);
v___x_967_ = l_Lean_mkModuleInitializationStem(v_name_964_, v___x_966_);
lean_dec(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_969_){
_start:
{
lean_object* v_lib_970_; lean_object* v_pkg_971_; lean_object* v_config_972_; lean_object* v_name_973_; lean_object* v_dir_974_; lean_object* v_buildDir_975_; lean_object* v_leanLibDir_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_lib_970_ = lean_ctor_get(v_self_969_, 0);
v_pkg_971_ = lean_ctor_get(v_lib_970_, 0);
lean_inc_ref(v_pkg_971_);
v_config_972_ = lean_ctor_get(v_pkg_971_, 6);
v_name_973_ = lean_ctor_get(v_self_969_, 1);
lean_inc(v_name_973_);
lean_dec_ref(v_self_969_);
v_dir_974_ = lean_ctor_get(v_pkg_971_, 4);
v_buildDir_975_ = lean_ctor_get(v_config_972_, 5);
v_leanLibDir_976_ = lean_ctor_get(v_config_972_, 6);
lean_inc_ref(v_buildDir_975_);
v___x_977_ = l_System_FilePath_normalize(v_buildDir_975_);
lean_inc_ref(v_dir_974_);
v___x_978_ = l_Lake_joinRelative(v_dir_974_, v___x_977_);
lean_inc_ref(v_leanLibDir_976_);
v___x_979_ = l_System_FilePath_normalize(v_leanLibDir_976_);
v___x_980_ = l_Lake_joinRelative(v___x_978_, v___x_979_);
v___x_981_ = l_Lake_Package_id_x3f(v_pkg_971_);
v___x_982_ = l_Lean_mkModuleInitializationStem(v_name_973_, v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
v___x_985_ = l_Lake_sharedLibExt;
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
v___x_987_ = l_Lake_joinRelative(v___x_980_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_988_){
_start:
{
lean_object* v_lib_989_; lean_object* v_pkg_990_; lean_object* v_config_991_; lean_object* v_toLeanConfig_992_; lean_object* v_config_993_; lean_object* v_toLeanConfig_994_; uint8_t v_buildType_995_; lean_object* v_leanOptions_996_; lean_object* v_moreServerOptions_997_; uint8_t v_buildType_998_; lean_object* v_leanOptions_999_; lean_object* v_moreServerOptions_1000_; lean_object* v___x_1001_; uint8_t v___y_1003_; uint8_t v___x_1011_; 
v_lib_989_ = lean_ctor_get(v_self_988_, 0);
v_pkg_990_ = lean_ctor_get(v_lib_989_, 0);
v_config_991_ = lean_ctor_get(v_pkg_990_, 6);
v_toLeanConfig_992_ = lean_ctor_get(v_config_991_, 1);
v_config_993_ = lean_ctor_get(v_lib_989_, 2);
v_toLeanConfig_994_ = lean_ctor_get(v_config_993_, 0);
v_buildType_995_ = lean_ctor_get_uint8(v_toLeanConfig_992_, sizeof(void*)*13);
v_leanOptions_996_ = lean_ctor_get(v_toLeanConfig_992_, 0);
v_moreServerOptions_997_ = lean_ctor_get(v_toLeanConfig_992_, 4);
v_buildType_998_ = lean_ctor_get_uint8(v_toLeanConfig_994_, sizeof(void*)*13);
v_leanOptions_999_ = lean_ctor_get(v_toLeanConfig_994_, 0);
v_moreServerOptions_1000_ = lean_ctor_get(v_toLeanConfig_994_, 4);
v___x_1001_ = lean_box(1);
v___x_1011_ = l_Lake_instOrdBuildType_ord(v_buildType_995_, v_buildType_998_);
if (v___x_1011_ == 2)
{
v___y_1003_ = v_buildType_998_;
goto v___jp_1002_;
}
else
{
v___y_1003_ = v_buildType_995_;
goto v___jp_1002_;
}
v___jp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1004_ = l_Lake_BuildType_leanOptions(v___y_1003_);
v___x_1005_ = l_Lean_LeanOptions_append(v___x_1001_, v___x_1004_);
v___x_1006_ = l_Lean_LeanOptions_ofArray(v_leanOptions_996_);
v___x_1007_ = l_Lean_LeanOptions_appendArray(v___x_1006_, v_moreServerOptions_997_);
v___x_1008_ = l_Lean_LeanOptions_append(v___x_1005_, v___x_1007_);
v___x_1009_ = l_Lean_LeanOptions_appendArray(v___x_1008_, v_leanOptions_999_);
v___x_1010_ = l_Lean_LeanOptions_appendArray(v___x_1009_, v_moreServerOptions_1000_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lake_Module_serverOptions(v_self_1012_);
lean_dec_ref(v_self_1012_);
return v_res_1013_;
}
}
uint8_t l_Lake_Module_buildType(lean_object* v_self_1014_){
_start:
{
lean_object* v_lib_1015_; lean_object* v_pkg_1016_; lean_object* v_config_1017_; lean_object* v_toLeanConfig_1018_; lean_object* v_config_1019_; lean_object* v_toLeanConfig_1020_; uint8_t v_buildType_1021_; uint8_t v_buildType_1022_; uint8_t v___x_1023_; 
v_lib_1015_ = lean_ctor_get(v_self_1014_, 0);
v_pkg_1016_ = lean_ctor_get(v_lib_1015_, 0);
v_config_1017_ = lean_ctor_get(v_pkg_1016_, 6);
v_toLeanConfig_1018_ = lean_ctor_get(v_config_1017_, 1);
v_config_1019_ = lean_ctor_get(v_lib_1015_, 2);
v_toLeanConfig_1020_ = lean_ctor_get(v_config_1019_, 0);
v_buildType_1021_ = lean_ctor_get_uint8(v_toLeanConfig_1018_, sizeof(void*)*13);
v_buildType_1022_ = lean_ctor_get_uint8(v_toLeanConfig_1020_, sizeof(void*)*13);
v___x_1023_ = l_Lake_instOrdBuildType_ord(v_buildType_1021_, v_buildType_1022_);
if (v___x_1023_ == 2)
{
return v_buildType_1022_;
}
else
{
return v_buildType_1021_;
}
}
}
LEAN_EXPORT void l_Lake_Module_buildType_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1014_ = stack[0].m_obj;
uint8_t v_res_1024_;
v_res_1024_ = l_Lake_Module_buildType(v_self_1014_);
stack->m_num = v_res_1024_;
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lake_Module_buildType(v_self_1025_);
lean_dec_ref(v_self_1025_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
uint8_t l_Lake_Module_backend(lean_object* v_self_1028_){
_start:
{
lean_object* v_lib_1029_; lean_object* v_config_1030_; lean_object* v_toLeanConfig_1031_; lean_object* v_pkg_1032_; lean_object* v_config_1033_; lean_object* v_toLeanConfig_1034_; uint8_t v_backend_1035_; uint8_t v_backend_1036_; uint8_t v___x_1037_; 
v_lib_1029_ = lean_ctor_get(v_self_1028_, 0);
v_config_1030_ = lean_ctor_get(v_lib_1029_, 2);
v_toLeanConfig_1031_ = lean_ctor_get(v_config_1030_, 0);
v_pkg_1032_ = lean_ctor_get(v_lib_1029_, 0);
v_config_1033_ = lean_ctor_get(v_pkg_1032_, 6);
v_toLeanConfig_1034_ = lean_ctor_get(v_config_1033_, 1);
v_backend_1035_ = lean_ctor_get_uint8(v_toLeanConfig_1031_, sizeof(void*)*13 + 1);
v_backend_1036_ = lean_ctor_get_uint8(v_toLeanConfig_1034_, sizeof(void*)*13 + 1);
v___x_1037_ = l_Lake_Backend_orPreferLeft(v_backend_1035_, v_backend_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT void l_Lake_Module_backend_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1028_ = stack[0].m_obj;
uint8_t v_res_1038_;
v_res_1038_ = l_Lake_Module_backend(v_self_1028_);
stack->m_num = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Lake_Module_backend(v_self_1039_);
lean_dec_ref(v_self_1039_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_1042_){
_start:
{
lean_object* v_lib_1043_; lean_object* v_config_1044_; uint8_t v_allowImportAll_1045_; 
v_lib_1043_ = lean_ctor_get(v_self_1042_, 0);
v_config_1044_ = lean_ctor_get(v_lib_1043_, 2);
v_allowImportAll_1045_ = lean_ctor_get_uint8(v_config_1044_, sizeof(void*)*9 + 3);
if (v_allowImportAll_1045_ == 0)
{
lean_object* v_pkg_1046_; lean_object* v_config_1047_; uint8_t v_allowImportAll_1048_; 
v_pkg_1046_ = lean_ctor_get(v_lib_1043_, 0);
v_config_1047_ = lean_ctor_get(v_pkg_1046_, 6);
v_allowImportAll_1048_ = lean_ctor_get_uint8(v_config_1047_, sizeof(void*)*28 + 5);
return v_allowImportAll_1048_;
}
else
{
return v_allowImportAll_1045_;
}
}
}
LEAN_EXPORT void l_Lake_Module_allowImportAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1042_ = stack[0].m_obj;
uint8_t v_res_1049_;
v_res_1049_ = l_Lake_Module_allowImportAll(v_self_1042_);
stack->m_num = v_res_1049_;
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Lake_Module_allowImportAll(v_self_1050_);
lean_dec_ref(v_self_1050_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
uint8_t l_Lake_Module_requiresModuleSystem(lean_object* v_self_1053_){
_start:
{
lean_object* v_lib_1054_; lean_object* v_config_1055_; lean_object* v_toLeanConfig_1056_; uint8_t v_requiresModuleSystem_1057_; 
v_lib_1054_ = lean_ctor_get(v_self_1053_, 0);
v_config_1055_ = lean_ctor_get(v_lib_1054_, 2);
v_toLeanConfig_1056_ = lean_ctor_get(v_config_1055_, 0);
v_requiresModuleSystem_1057_ = lean_ctor_get_uint8(v_toLeanConfig_1056_, sizeof(void*)*13 + 3);
if (v_requiresModuleSystem_1057_ == 0)
{
lean_object* v_pkg_1058_; lean_object* v_config_1059_; lean_object* v_toLeanConfig_1060_; uint8_t v_requiresModuleSystem_1061_; 
v_pkg_1058_ = lean_ctor_get(v_lib_1054_, 0);
v_config_1059_ = lean_ctor_get(v_pkg_1058_, 6);
v_toLeanConfig_1060_ = lean_ctor_get(v_config_1059_, 1);
v_requiresModuleSystem_1061_ = lean_ctor_get_uint8(v_toLeanConfig_1060_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_1061_;
}
else
{
return v_requiresModuleSystem_1057_;
}
}
}
LEAN_EXPORT void l_Lake_Module_requiresModuleSystem_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1053_ = stack[0].m_obj;
uint8_t v_res_1062_;
v_res_1062_ = l_Lake_Module_requiresModuleSystem(v_self_1053_);
stack->m_num = v_res_1062_;
}
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object* v_self_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lake_Module_requiresModuleSystem(v_self_1063_);
lean_dec_ref(v_self_1063_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
uint8_t l_Lake_Module_allowNonModules(lean_object* v_self_1066_){
_start:
{
lean_object* v_lib_1067_; lean_object* v_config_1068_; lean_object* v_toLeanConfig_1069_; uint8_t v_allowNonModules_1070_; 
v_lib_1067_ = lean_ctor_get(v_self_1066_, 0);
v_config_1068_ = lean_ctor_get(v_lib_1067_, 2);
v_toLeanConfig_1069_ = lean_ctor_get(v_config_1068_, 0);
v_allowNonModules_1070_ = lean_ctor_get_uint8(v_toLeanConfig_1069_, sizeof(void*)*13 + 4);
if (v_allowNonModules_1070_ == 0)
{
lean_object* v_pkg_1071_; lean_object* v_config_1072_; lean_object* v_toLeanConfig_1073_; uint8_t v_allowNonModules_1074_; 
v_pkg_1071_ = lean_ctor_get(v_lib_1067_, 0);
v_config_1072_ = lean_ctor_get(v_pkg_1071_, 6);
v_toLeanConfig_1073_ = lean_ctor_get(v_config_1072_, 1);
v_allowNonModules_1074_ = lean_ctor_get_uint8(v_toLeanConfig_1073_, sizeof(void*)*13 + 4);
return v_allowNonModules_1074_;
}
else
{
return v_allowNonModules_1070_;
}
}
}
LEAN_EXPORT void l_Lake_Module_allowNonModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1066_ = stack[0].m_obj;
uint8_t v_res_1075_;
v_res_1075_ = l_Lake_Module_allowNonModules(v_self_1066_);
stack->m_num = v_res_1075_;
}
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object* v_self_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l_Lake_Module_allowNonModules(v_self_1076_);
lean_dec_ref(v_self_1076_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_1079_){
_start:
{
lean_object* v_lib_1080_; lean_object* v_pkg_1081_; lean_object* v_config_1082_; lean_object* v_toLeanConfig_1083_; lean_object* v_config_1084_; lean_object* v_toLeanConfig_1085_; lean_object* v_dynlibs_1086_; lean_object* v_dynlibs_1087_; lean_object* v___x_1088_; 
v_lib_1080_ = lean_ctor_get(v_self_1079_, 0);
lean_inc_ref(v_lib_1080_);
lean_dec_ref(v_self_1079_);
v_pkg_1081_ = lean_ctor_get(v_lib_1080_, 0);
v_config_1082_ = lean_ctor_get(v_pkg_1081_, 6);
v_toLeanConfig_1083_ = lean_ctor_get(v_config_1082_, 1);
lean_inc_ref(v_toLeanConfig_1083_);
v_config_1084_ = lean_ctor_get(v_lib_1080_, 2);
lean_inc(v_config_1084_);
lean_dec_ref(v_lib_1080_);
v_toLeanConfig_1085_ = lean_ctor_get(v_config_1084_, 0);
lean_inc_ref(v_toLeanConfig_1085_);
lean_dec(v_config_1084_);
v_dynlibs_1086_ = lean_ctor_get(v_toLeanConfig_1083_, 11);
lean_inc_ref(v_dynlibs_1086_);
lean_dec_ref(v_toLeanConfig_1083_);
v_dynlibs_1087_ = lean_ctor_get(v_toLeanConfig_1085_, 11);
lean_inc_ref(v_dynlibs_1087_);
lean_dec_ref(v_toLeanConfig_1085_);
v___x_1088_ = l_Array_append___redArg(v_dynlibs_1086_, v_dynlibs_1087_);
lean_dec_ref(v_dynlibs_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1089_){
_start:
{
lean_object* v_lib_1090_; lean_object* v_pkg_1091_; lean_object* v_config_1092_; lean_object* v_toLeanConfig_1093_; lean_object* v_config_1094_; lean_object* v_toLeanConfig_1095_; lean_object* v_plugins_1096_; lean_object* v_plugins_1097_; lean_object* v___x_1098_; 
v_lib_1090_ = lean_ctor_get(v_self_1089_, 0);
lean_inc_ref(v_lib_1090_);
lean_dec_ref(v_self_1089_);
v_pkg_1091_ = lean_ctor_get(v_lib_1090_, 0);
v_config_1092_ = lean_ctor_get(v_pkg_1091_, 6);
v_toLeanConfig_1093_ = lean_ctor_get(v_config_1092_, 1);
lean_inc_ref(v_toLeanConfig_1093_);
v_config_1094_ = lean_ctor_get(v_lib_1090_, 2);
lean_inc(v_config_1094_);
lean_dec_ref(v_lib_1090_);
v_toLeanConfig_1095_ = lean_ctor_get(v_config_1094_, 0);
lean_inc_ref(v_toLeanConfig_1095_);
lean_dec(v_config_1094_);
v_plugins_1096_ = lean_ctor_get(v_toLeanConfig_1093_, 12);
lean_inc_ref(v_plugins_1096_);
lean_dec_ref(v_toLeanConfig_1093_);
v_plugins_1097_ = lean_ctor_get(v_toLeanConfig_1095_, 12);
lean_inc_ref(v_plugins_1097_);
lean_dec_ref(v_toLeanConfig_1095_);
v___x_1098_ = l_Array_append___redArg(v_plugins_1096_, v_plugins_1097_);
lean_dec_ref(v_plugins_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1099_){
_start:
{
lean_object* v_lib_1100_; lean_object* v_pkg_1101_; lean_object* v_config_1102_; lean_object* v_toLeanConfig_1103_; lean_object* v_config_1104_; lean_object* v_toLeanConfig_1105_; uint8_t v_buildType_1106_; lean_object* v_leanOptions_1107_; uint8_t v_buildType_1108_; lean_object* v_leanOptions_1109_; uint8_t v___y_1111_; uint8_t v___x_1116_; 
v_lib_1100_ = lean_ctor_get(v_self_1099_, 0);
v_pkg_1101_ = lean_ctor_get(v_lib_1100_, 0);
v_config_1102_ = lean_ctor_get(v_pkg_1101_, 6);
v_toLeanConfig_1103_ = lean_ctor_get(v_config_1102_, 1);
v_config_1104_ = lean_ctor_get(v_lib_1100_, 2);
v_toLeanConfig_1105_ = lean_ctor_get(v_config_1104_, 0);
v_buildType_1106_ = lean_ctor_get_uint8(v_toLeanConfig_1103_, sizeof(void*)*13);
v_leanOptions_1107_ = lean_ctor_get(v_toLeanConfig_1103_, 0);
v_buildType_1108_ = lean_ctor_get_uint8(v_toLeanConfig_1105_, sizeof(void*)*13);
v_leanOptions_1109_ = lean_ctor_get(v_toLeanConfig_1105_, 0);
v___x_1116_ = l_Lake_instOrdBuildType_ord(v_buildType_1106_, v_buildType_1108_);
if (v___x_1116_ == 2)
{
v___y_1111_ = v_buildType_1108_;
goto v___jp_1110_;
}
else
{
v___y_1111_ = v_buildType_1106_;
goto v___jp_1110_;
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = l_Lake_BuildType_leanOptions(v___y_1111_);
v___x_1113_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1107_);
v___x_1114_ = l_Lean_LeanOptions_append(v___x_1112_, v___x_1113_);
v___x_1115_ = l_Lean_LeanOptions_appendArray(v___x_1114_, v_leanOptions_1109_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lake_Module_leanOptions(v_self_1117_);
lean_dec_ref(v_self_1117_);
return v_res_1118_;
}
}
uint8_t l_Lake_Module_postponeCompile(lean_object* v_self_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v_lib_1121_; lean_object* v_pkg_1122_; lean_object* v_config_1123_; lean_object* v_toLeanConfig_1124_; lean_object* v_config_1125_; lean_object* v_toLeanConfig_1126_; uint8_t v_buildType_1127_; lean_object* v_leanOptions_1128_; uint8_t v_buildType_1129_; lean_object* v_leanOptions_1130_; uint8_t v___y_1132_; uint8_t v___x_1141_; 
v___x_1120_ = l_Lean_KVMap_instValueBool;
v_lib_1121_ = lean_ctor_get(v_self_1119_, 0);
v_pkg_1122_ = lean_ctor_get(v_lib_1121_, 0);
v_config_1123_ = lean_ctor_get(v_pkg_1122_, 6);
v_toLeanConfig_1124_ = lean_ctor_get(v_config_1123_, 1);
v_config_1125_ = lean_ctor_get(v_lib_1121_, 2);
v_toLeanConfig_1126_ = lean_ctor_get(v_config_1125_, 0);
v_buildType_1127_ = lean_ctor_get_uint8(v_toLeanConfig_1124_, sizeof(void*)*13);
v_leanOptions_1128_ = lean_ctor_get(v_toLeanConfig_1124_, 0);
v_buildType_1129_ = lean_ctor_get_uint8(v_toLeanConfig_1126_, sizeof(void*)*13);
v_leanOptions_1130_ = lean_ctor_get(v_toLeanConfig_1126_, 0);
v___x_1141_ = l_Lake_instOrdBuildType_ord(v_buildType_1127_, v_buildType_1129_);
if (v___x_1141_ == 2)
{
v___y_1132_ = v_buildType_1129_;
goto v___jp_1131_;
}
else
{
v___y_1132_ = v_buildType_1127_;
goto v___jp_1131_;
}
v___jp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1133_ = l_Lake_BuildType_leanOptions(v___y_1132_);
v___x_1134_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1128_);
v___x_1135_ = l_Lean_LeanOptions_append(v___x_1133_, v___x_1134_);
v___x_1136_ = l_Lean_LeanOptions_appendArray(v___x_1135_, v_leanOptions_1130_);
v___x_1137_ = l_Lean_LeanOptions_toOptions(v___x_1136_);
v___x_1138_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1139_ = l_Lean_Option_get___redArg(v___x_1120_, v___x_1137_, v___x_1138_);
lean_dec_ref(v___x_1137_);
v___x_1140_ = lean_unbox(v___x_1139_);
lean_dec(v___x_1139_);
return v___x_1140_;
}
}
}
LEAN_EXPORT void l_Lake_Module_postponeCompile_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1119_ = stack[0].m_obj;
uint8_t v_res_1142_;
v_res_1142_ = l_Lake_Module_postponeCompile(v_self_1119_);
stack->m_num = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lake_Module_postponeCompile___boxed(lean_object* v_self_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Lake_Module_postponeCompile(v_self_1143_);
lean_dec_ref(v_self_1143_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
static lean_object* _init_l_Lake_Module_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1147_){
_start:
{
lean_object* v_lib_1148_; lean_object* v_pkg_1149_; lean_object* v_config_1150_; lean_object* v_toLeanConfig_1151_; lean_object* v_config_1152_; lean_object* v_toLeanConfig_1153_; lean_object* v_moreLeanArgs_1154_; lean_object* v_moreLeanArgs_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_lib_1148_ = lean_ctor_get(v_self_1147_, 0);
v_pkg_1149_ = lean_ctor_get(v_lib_1148_, 0);
v_config_1150_ = lean_ctor_get(v_pkg_1149_, 6);
v_toLeanConfig_1151_ = lean_ctor_get(v_config_1150_, 1);
v_config_1152_ = lean_ctor_get(v_lib_1148_, 2);
v_toLeanConfig_1153_ = lean_ctor_get(v_config_1152_, 0);
v_moreLeanArgs_1154_ = lean_ctor_get(v_toLeanConfig_1151_, 1);
v_moreLeanArgs_1155_ = lean_ctor_get(v_toLeanConfig_1153_, 1);
v___x_1156_ = lean_obj_once(&l_Lake_Module_leanArgs___closed__0, &l_Lake_Module_leanArgs___closed__0_once, _init_l_Lake_Module_leanArgs___closed__0);
v___x_1157_ = l_Array_append___redArg(v___x_1156_, v_moreLeanArgs_1154_);
v___x_1158_ = l_Array_append___redArg(v___x_1157_, v_moreLeanArgs_1155_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lake_Module_leanArgs(v_self_1159_);
lean_dec_ref(v_self_1159_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1161_){
_start:
{
lean_object* v_lib_1162_; lean_object* v_pkg_1163_; lean_object* v_config_1164_; lean_object* v_toLeanConfig_1165_; lean_object* v_config_1166_; lean_object* v_toLeanConfig_1167_; lean_object* v_weakLeanArgs_1168_; lean_object* v_weakLeanArgs_1169_; lean_object* v___x_1170_; 
v_lib_1162_ = lean_ctor_get(v_self_1161_, 0);
lean_inc_ref(v_lib_1162_);
lean_dec_ref(v_self_1161_);
v_pkg_1163_ = lean_ctor_get(v_lib_1162_, 0);
v_config_1164_ = lean_ctor_get(v_pkg_1163_, 6);
v_toLeanConfig_1165_ = lean_ctor_get(v_config_1164_, 1);
lean_inc_ref(v_toLeanConfig_1165_);
v_config_1166_ = lean_ctor_get(v_lib_1162_, 2);
lean_inc(v_config_1166_);
lean_dec_ref(v_lib_1162_);
v_toLeanConfig_1167_ = lean_ctor_get(v_config_1166_, 0);
lean_inc_ref(v_toLeanConfig_1167_);
lean_dec(v_config_1166_);
v_weakLeanArgs_1168_ = lean_ctor_get(v_toLeanConfig_1165_, 2);
lean_inc_ref(v_weakLeanArgs_1168_);
lean_dec_ref(v_toLeanConfig_1165_);
v_weakLeanArgs_1169_ = lean_ctor_get(v_toLeanConfig_1167_, 2);
lean_inc_ref(v_weakLeanArgs_1169_);
lean_dec_ref(v_toLeanConfig_1167_);
v___x_1170_ = l_Array_append___redArg(v_weakLeanArgs_1168_, v_weakLeanArgs_1169_);
lean_dec_ref(v_weakLeanArgs_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1171_){
_start:
{
lean_object* v_lib_1172_; lean_object* v_pkg_1173_; lean_object* v_config_1174_; lean_object* v_toLeanConfig_1175_; lean_object* v_config_1176_; lean_object* v_toLeanConfig_1177_; uint8_t v_buildType_1178_; lean_object* v_moreLeancArgs_1179_; uint8_t v_buildType_1180_; lean_object* v_moreLeancArgs_1181_; uint8_t v___y_1183_; uint8_t v___x_1187_; 
v_lib_1172_ = lean_ctor_get(v_self_1171_, 0);
v_pkg_1173_ = lean_ctor_get(v_lib_1172_, 0);
v_config_1174_ = lean_ctor_get(v_pkg_1173_, 6);
v_toLeanConfig_1175_ = lean_ctor_get(v_config_1174_, 1);
v_config_1176_ = lean_ctor_get(v_lib_1172_, 2);
v_toLeanConfig_1177_ = lean_ctor_get(v_config_1176_, 0);
v_buildType_1178_ = lean_ctor_get_uint8(v_toLeanConfig_1175_, sizeof(void*)*13);
v_moreLeancArgs_1179_ = lean_ctor_get(v_toLeanConfig_1175_, 3);
v_buildType_1180_ = lean_ctor_get_uint8(v_toLeanConfig_1177_, sizeof(void*)*13);
v_moreLeancArgs_1181_ = lean_ctor_get(v_toLeanConfig_1177_, 3);
v___x_1187_ = l_Lake_instOrdBuildType_ord(v_buildType_1178_, v_buildType_1180_);
if (v___x_1187_ == 2)
{
v___y_1183_ = v_buildType_1180_;
goto v___jp_1182_;
}
else
{
v___y_1183_ = v_buildType_1178_;
goto v___jp_1182_;
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = l_Lake_BuildType_leancArgs(v___y_1183_);
v___x_1185_ = l_Array_append___redArg(v___x_1184_, v_moreLeancArgs_1179_);
v___x_1186_ = l_Array_append___redArg(v___x_1185_, v_moreLeancArgs_1181_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lake_Module_leancArgs(v_self_1188_);
lean_dec_ref(v_self_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1190_){
_start:
{
lean_object* v_lib_1191_; lean_object* v_pkg_1192_; lean_object* v_config_1193_; lean_object* v_toLeanConfig_1194_; lean_object* v_config_1195_; lean_object* v_toLeanConfig_1196_; lean_object* v_weakLeancArgs_1197_; lean_object* v_weakLeancArgs_1198_; lean_object* v___x_1199_; 
v_lib_1191_ = lean_ctor_get(v_self_1190_, 0);
lean_inc_ref(v_lib_1191_);
lean_dec_ref(v_self_1190_);
v_pkg_1192_ = lean_ctor_get(v_lib_1191_, 0);
v_config_1193_ = lean_ctor_get(v_pkg_1192_, 6);
v_toLeanConfig_1194_ = lean_ctor_get(v_config_1193_, 1);
lean_inc_ref(v_toLeanConfig_1194_);
v_config_1195_ = lean_ctor_get(v_lib_1191_, 2);
lean_inc(v_config_1195_);
lean_dec_ref(v_lib_1191_);
v_toLeanConfig_1196_ = lean_ctor_get(v_config_1195_, 0);
lean_inc_ref(v_toLeanConfig_1196_);
lean_dec(v_config_1195_);
v_weakLeancArgs_1197_ = lean_ctor_get(v_toLeanConfig_1194_, 5);
lean_inc_ref(v_weakLeancArgs_1197_);
lean_dec_ref(v_toLeanConfig_1194_);
v_weakLeancArgs_1198_ = lean_ctor_get(v_toLeanConfig_1196_, 5);
lean_inc_ref(v_weakLeancArgs_1198_);
lean_dec_ref(v_toLeanConfig_1196_);
v___x_1199_ = l_Array_append___redArg(v_weakLeancArgs_1197_, v_weakLeancArgs_1198_);
lean_dec_ref(v_weakLeancArgs_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1200_){
_start:
{
lean_object* v_lib_1201_; lean_object* v_pkg_1202_; lean_object* v_config_1203_; lean_object* v_toLeanConfig_1204_; lean_object* v_config_1205_; lean_object* v_toLeanConfig_1206_; lean_object* v_moreLinkArgs_1207_; lean_object* v_moreLinkArgs_1208_; lean_object* v___x_1209_; 
v_lib_1201_ = lean_ctor_get(v_self_1200_, 0);
lean_inc_ref(v_lib_1201_);
lean_dec_ref(v_self_1200_);
v_pkg_1202_ = lean_ctor_get(v_lib_1201_, 0);
v_config_1203_ = lean_ctor_get(v_pkg_1202_, 6);
v_toLeanConfig_1204_ = lean_ctor_get(v_config_1203_, 1);
lean_inc_ref(v_toLeanConfig_1204_);
v_config_1205_ = lean_ctor_get(v_lib_1201_, 2);
lean_inc(v_config_1205_);
lean_dec_ref(v_lib_1201_);
v_toLeanConfig_1206_ = lean_ctor_get(v_config_1205_, 0);
lean_inc_ref(v_toLeanConfig_1206_);
lean_dec(v_config_1205_);
v_moreLinkArgs_1207_ = lean_ctor_get(v_toLeanConfig_1204_, 8);
lean_inc_ref(v_moreLinkArgs_1207_);
lean_dec_ref(v_toLeanConfig_1204_);
v_moreLinkArgs_1208_ = lean_ctor_get(v_toLeanConfig_1206_, 8);
lean_inc_ref(v_moreLinkArgs_1208_);
lean_dec_ref(v_toLeanConfig_1206_);
v___x_1209_ = l_Array_append___redArg(v_moreLinkArgs_1207_, v_moreLinkArgs_1208_);
lean_dec_ref(v_moreLinkArgs_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1210_){
_start:
{
lean_object* v_lib_1211_; lean_object* v_pkg_1212_; lean_object* v_config_1213_; lean_object* v_toLeanConfig_1214_; lean_object* v_config_1215_; lean_object* v_toLeanConfig_1216_; lean_object* v_weakLinkArgs_1217_; lean_object* v_weakLinkArgs_1218_; lean_object* v___x_1219_; 
v_lib_1211_ = lean_ctor_get(v_self_1210_, 0);
lean_inc_ref(v_lib_1211_);
lean_dec_ref(v_self_1210_);
v_pkg_1212_ = lean_ctor_get(v_lib_1211_, 0);
v_config_1213_ = lean_ctor_get(v_pkg_1212_, 6);
v_toLeanConfig_1214_ = lean_ctor_get(v_config_1213_, 1);
lean_inc_ref(v_toLeanConfig_1214_);
v_config_1215_ = lean_ctor_get(v_lib_1211_, 2);
lean_inc(v_config_1215_);
lean_dec_ref(v_lib_1211_);
v_toLeanConfig_1216_ = lean_ctor_get(v_config_1215_, 0);
lean_inc_ref(v_toLeanConfig_1216_);
lean_dec(v_config_1215_);
v_weakLinkArgs_1217_ = lean_ctor_get(v_toLeanConfig_1214_, 9);
lean_inc_ref(v_weakLinkArgs_1217_);
lean_dec_ref(v_toLeanConfig_1214_);
v_weakLinkArgs_1218_ = lean_ctor_get(v_toLeanConfig_1216_, 9);
lean_inc_ref(v_weakLinkArgs_1218_);
lean_dec_ref(v_toLeanConfig_1216_);
v___x_1219_ = l_Array_append___redArg(v_weakLinkArgs_1217_, v_weakLinkArgs_1218_);
lean_dec_ref(v_weakLinkArgs_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1221_){
_start:
{
lean_object* v_lib_1222_; lean_object* v_pkg_1223_; lean_object* v_config_1224_; uint8_t v_bootstrap_1225_; 
v_lib_1222_ = lean_ctor_get(v_self_1221_, 0);
lean_inc_ref(v_lib_1222_);
lean_dec_ref(v_self_1221_);
v_pkg_1223_ = lean_ctor_get(v_lib_1222_, 0);
lean_inc_ref(v_pkg_1223_);
lean_dec_ref(v_lib_1222_);
v_config_1224_ = lean_ctor_get(v_pkg_1223_, 6);
lean_inc_ref(v_config_1224_);
v_bootstrap_1225_ = lean_ctor_get_uint8(v_config_1224_, sizeof(void*)*28);
if (v_bootstrap_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_config_1224_);
lean_dec_ref(v_pkg_1223_);
v___x_1226_ = lean_box(0);
return v___x_1226_;
}
else
{
lean_object* v_dir_1227_; lean_object* v_buildDir_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_dir_1227_ = lean_ctor_get(v_pkg_1223_, 4);
lean_inc_ref(v_dir_1227_);
lean_dec_ref(v_pkg_1223_);
v_buildDir_1228_ = lean_ctor_get(v_config_1224_, 5);
lean_inc_ref(v_buildDir_1228_);
lean_dec_ref(v_config_1224_);
v___x_1229_ = l_System_FilePath_normalize(v_buildDir_1228_);
v___x_1230_ = l_Lake_joinRelative(v_dir_1227_, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1232_ = l_Lake_joinRelative(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1234_){
_start:
{
lean_object* v_lib_1235_; lean_object* v_config_1236_; lean_object* v_toLeanConfig_1237_; lean_object* v_platformIndependent_1238_; 
v_lib_1235_ = lean_ctor_get(v_self_1234_, 0);
v_config_1236_ = lean_ctor_get(v_lib_1235_, 2);
v_toLeanConfig_1237_ = lean_ctor_get(v_config_1236_, 0);
v_platformIndependent_1238_ = lean_ctor_get(v_toLeanConfig_1237_, 10);
if (lean_obj_tag(v_platformIndependent_1238_) == 0)
{
lean_object* v_pkg_1239_; lean_object* v_config_1240_; lean_object* v_toLeanConfig_1241_; lean_object* v_platformIndependent_1242_; 
v_pkg_1239_ = lean_ctor_get(v_lib_1235_, 0);
v_config_1240_ = lean_ctor_get(v_pkg_1239_, 6);
v_toLeanConfig_1241_ = lean_ctor_get(v_config_1240_, 1);
v_platformIndependent_1242_ = lean_ctor_get(v_toLeanConfig_1241_, 10);
lean_inc(v_platformIndependent_1242_);
return v_platformIndependent_1242_;
}
else
{
lean_inc_ref(v_platformIndependent_1238_);
return v_platformIndependent_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lake_Module_platformIndependent(v_self_1243_);
lean_dec_ref(v_self_1243_);
return v_res_1244_;
}
}
uint8_t l_Lake_Module_shouldPrecompileImports(lean_object* v_self_1245_){
_start:
{
lean_object* v_lib_1246_; lean_object* v_pkg_1247_; lean_object* v_config_1248_; uint8_t v_precompileModules_1249_; 
v_lib_1246_ = lean_ctor_get(v_self_1245_, 0);
v_pkg_1247_ = lean_ctor_get(v_lib_1246_, 0);
v_config_1248_ = lean_ctor_get(v_pkg_1247_, 6);
v_precompileModules_1249_ = lean_ctor_get_uint8(v_config_1248_, sizeof(void*)*28 + 1);
if (v_precompileModules_1249_ == 0)
{
lean_object* v_config_1250_; uint8_t v_precompileModules_1251_; 
v_config_1250_ = lean_ctor_get(v_lib_1246_, 2);
v_precompileModules_1251_ = lean_ctor_get_uint8(v_config_1250_, sizeof(void*)*9 + 2);
if (v_precompileModules_1251_ == 0)
{
lean_object* v_toLeanConfig_1252_; uint8_t v_precompileImports_1253_; 
v_toLeanConfig_1252_ = lean_ctor_get(v_config_1248_, 1);
v_precompileImports_1253_ = lean_ctor_get_uint8(v_toLeanConfig_1252_, sizeof(void*)*13 + 2);
if (v_precompileImports_1253_ == 0)
{
lean_object* v_toLeanConfig_1254_; uint8_t v_precompileImports_1255_; 
v_toLeanConfig_1254_ = lean_ctor_get(v_config_1250_, 0);
v_precompileImports_1255_ = lean_ctor_get_uint8(v_toLeanConfig_1254_, sizeof(void*)*13 + 2);
return v_precompileImports_1255_;
}
else
{
return v_precompileImports_1253_;
}
}
else
{
return v_precompileModules_1251_;
}
}
else
{
return v_precompileModules_1249_;
}
}
}
LEAN_EXPORT void l_Lake_Module_shouldPrecompileImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1245_ = stack[0].m_obj;
uint8_t v_res_1256_;
v_res_1256_ = l_Lake_Module_shouldPrecompileImports(v_self_1245_);
stack->m_num = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompileImports___boxed(lean_object* v_self_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Lake_Module_shouldPrecompileImports(v_self_1257_);
lean_dec_ref(v_self_1257_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1260_){
_start:
{
lean_object* v_lib_1261_; lean_object* v_pkg_1262_; lean_object* v_config_1263_; uint8_t v_precompileModules_1264_; 
v_lib_1261_ = lean_ctor_get(v_self_1260_, 0);
v_pkg_1262_ = lean_ctor_get(v_lib_1261_, 0);
v_config_1263_ = lean_ctor_get(v_pkg_1262_, 6);
v_precompileModules_1264_ = lean_ctor_get_uint8(v_config_1263_, sizeof(void*)*28 + 1);
if (v_precompileModules_1264_ == 0)
{
lean_object* v_config_1265_; uint8_t v_precompileModules_1266_; 
v_config_1265_ = lean_ctor_get(v_lib_1261_, 2);
v_precompileModules_1266_ = lean_ctor_get_uint8(v_config_1265_, sizeof(void*)*9 + 2);
return v_precompileModules_1266_;
}
else
{
return v_precompileModules_1264_;
}
}
}
LEAN_EXPORT void l_Lake_Module_shouldPrecompile_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1260_ = stack[0].m_obj;
uint8_t v_res_1267_;
v_res_1267_ = l_Lake_Module_shouldPrecompile(v_self_1260_);
stack->m_num = v_res_1267_;
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Lake_Module_shouldPrecompile(v_self_1268_);
lean_dec_ref(v_self_1268_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1271_, uint8_t v_shouldExport_1272_){
_start:
{
lean_object* v_lib_1273_; lean_object* v_config_1274_; lean_object* v_nativeFacets_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_lib_1273_ = lean_ctor_get(v_self_1271_, 0);
lean_inc_ref(v_lib_1273_);
lean_dec_ref(v_self_1271_);
v_config_1274_ = lean_ctor_get(v_lib_1273_, 2);
lean_inc(v_config_1274_);
lean_dec_ref(v_lib_1273_);
v_nativeFacets_1275_ = lean_ctor_get(v_config_1274_, 8);
lean_inc_ref(v_nativeFacets_1275_);
lean_dec(v_config_1274_);
v___x_1276_ = lean_box(v_shouldExport_1272_);
v___x_1277_ = lean_apply_1(v_nativeFacets_1275_, v___x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT void l_Lake_Module_nativeFacets_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1271_ = stack[0].m_obj;
uint8_t v_shouldExport_1272_ = stack[1].m_num;
lean_object* v_res_1278_;
v_res_1278_ = l_Lake_Module_nativeFacets(v_self_1271_, v_shouldExport_1272_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1279_, lean_object* v_shouldExport_1280_){
_start:
{
uint8_t v_shouldExport_boxed_1281_; lean_object* v_res_1282_; 
v_shouldExport_boxed_1281_ = lean_unbox(v_shouldExport_1280_);
v_res_1282_ = l_Lake_Module_nativeFacets(v_self_1279_, v_shouldExport_boxed_1281_);
return v_res_1282_;
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
