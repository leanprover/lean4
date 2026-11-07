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
lean_object* v_val_140_; lean_object* v_pkg_146_; lean_object* v_config_147_; lean_object* v_config_148_; lean_object* v_dir_149_; lean_object* v_srcDir_150_; lean_object* v_srcDir_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_pkg_146_ = lean_ctor_get(v_self_138_, 0);
v_config_147_ = lean_ctor_get(v_pkg_146_, 6);
v_config_148_ = lean_ctor_get(v_self_138_, 2);
v_dir_149_ = lean_ctor_get(v_pkg_146_, 4);
v_srcDir_150_ = lean_ctor_get(v_config_147_, 4);
v_srcDir_151_ = lean_ctor_get(v_config_148_, 1);
lean_inc_ref(v_srcDir_150_);
v___x_152_ = l_System_FilePath_normalize(v_srcDir_150_);
lean_inc_ref(v_dir_149_);
v___x_153_ = l_Lake_joinRelative(v_dir_149_, v___x_152_);
lean_inc_ref(v_srcDir_151_);
v___x_154_ = l_System_FilePath_normalize(v_srcDir_151_);
v___x_155_ = l_Lake_joinRelative(v___x_153_, v___x_154_);
v___x_156_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_155_, v_path_137_);
lean_dec_ref(v___x_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_self_138_);
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v_str_159_; lean_object* v_startInclusive_160_; lean_object* v_endExclusive_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_178_; 
v_val_158_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_val_158_);
lean_dec_ref_known(v___x_156_, 1);
v_str_159_ = lean_ctor_get(v_val_158_, 0);
lean_inc_ref(v_str_159_);
v_startInclusive_160_ = lean_ctor_get(v_val_158_, 1);
lean_inc(v_startInclusive_160_);
v_endExclusive_161_ = lean_ctor_get(v_val_158_, 2);
lean_inc(v_endExclusive_161_);
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = l_String_Slice_Pos_nextn(v_val_158_, v___x_163_, v___x_162_);
v_isSharedCheck_178_ = !lean_is_exclusive(v_val_158_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_179_ = lean_ctor_get(v_val_158_, 2);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_val_158_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_val_158_, 0);
lean_dec(v_unused_181_);
v___x_166_ = v_val_158_;
v_isShared_167_ = v_isSharedCheck_178_;
goto v_resetjp_165_;
}
else
{
lean_dec(v_val_158_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_178_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_nat_add(v_startInclusive_160_, v___x_164_);
lean_dec(v___x_164_);
lean_dec(v_startInclusive_160_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_str_159_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_endExclusive_161_);
v___x_170_ = v_reuseFailAlloc_177_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = l_String_Slice_toString(v___x_170_);
lean_dec_ref(v___x_170_);
lean_inc_ref(v___x_171_);
v___x_172_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v___x_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v___x_173_; 
v___x_173_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v___x_171_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_174_; 
lean_dec_ref(v_self_138_);
v___x_174_ = lean_box(0);
return v___x_174_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_173_, 1);
v_val_140_ = v_val_175_;
goto v___jp_139_;
}
}
else
{
lean_object* v_val_176_; 
lean_dec_ref(v___x_171_);
v_val_176_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_172_, 1);
v_val_140_ = v_val_176_;
goto v___jp_139_;
}
}
}
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_141_ = lean_box(0);
v___x_142_ = l_String_Slice_toString(v_val_140_);
lean_dec_ref(v_val_140_);
v___x_143_ = l_System_FilePath_components(v___x_142_);
v___x_144_ = l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(v___x_141_, v___x_143_);
v___x_145_ = l_Lake_LeanLib_findModule_x3f(v___x_144_, v_self_138_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(lean_object* v_self_185_, lean_object* v_as_186_, size_t v_i_187_, size_t v_stop_188_, lean_object* v_b_189_){
_start:
{
lean_object* v___y_191_; uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_eq(v_i_187_, v_stop_188_);
if (v___x_195_ == 0)
{
lean_object* v_toConfigDecl_196_; lean_object* v_name_197_; lean_object* v_kind_198_; lean_object* v_config_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_toConfigDecl_196_ = lean_array_uget_borrowed(v_as_186_, v_i_187_);
v_name_197_ = lean_ctor_get(v_toConfigDecl_196_, 1);
v_kind_198_ = lean_ctor_get(v_toConfigDecl_196_, 2);
v_config_199_ = lean_ctor_get(v_toConfigDecl_196_, 3);
v___x_200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1));
v___x_201_ = lean_name_eq(v_kind_198_, v___x_200_);
if (v___x_201_ == 0)
{
v___y_191_ = v_b_189_;
goto v___jp_190_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_inc(v_config_199_);
lean_inc(v_name_197_);
lean_inc_ref(v_self_185_);
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_self_185_);
lean_ctor_set(v___x_202_, 1, v_name_197_);
lean_ctor_set(v___x_202_, 2, v_config_199_);
v___x_203_ = lean_array_push(v_b_189_, v___x_202_);
v___y_191_ = v___x_203_;
goto v___jp_190_;
}
}
else
{
lean_dec_ref(v_self_185_);
return v_b_189_;
}
v___jp_190_:
{
size_t v___x_192_; size_t v___x_193_; 
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_add(v_i_187_, v___x_192_);
v_i_187_ = v___x_193_;
v_b_189_ = v___y_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___boxed(lean_object* v_self_204_, lean_object* v_as_205_, lean_object* v_i_206_, lean_object* v_stop_207_, lean_object* v_b_208_){
_start:
{
size_t v_i_boxed_209_; size_t v_stop_boxed_210_; lean_object* v_res_211_; 
v_i_boxed_209_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_stop_boxed_210_ = lean_unbox_usize(v_stop_207_);
lean_dec(v_stop_207_);
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_204_, v_as_205_, v_i_boxed_209_, v_stop_boxed_210_, v_b_208_);
lean_dec_ref(v_as_205_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(lean_object* v_mod_212_, lean_object* v_as_213_, lean_object* v_i_214_){
_start:
{
lean_object* v_zero_215_; uint8_t v_isZero_216_; 
v_zero_215_ = lean_unsigned_to_nat(0u);
v_isZero_216_ = lean_nat_dec_eq(v_i_214_, v_zero_215_);
if (v_isZero_216_ == 1)
{
lean_object* v___x_217_; 
lean_dec(v_i_214_);
lean_dec(v_mod_212_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_one_218_; lean_object* v_n_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_one_218_ = lean_unsigned_to_nat(1u);
v_n_219_ = lean_nat_sub(v_i_214_, v_one_218_);
lean_dec(v_i_214_);
v___x_220_ = lean_array_fget_borrowed(v_as_213_, v_n_219_);
lean_inc(v___x_220_);
lean_inc(v_mod_212_);
v___x_221_ = l_Lake_LeanLib_findModule_x3f(v_mod_212_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
v_i_214_ = v_n_219_;
goto _start;
}
else
{
lean_dec(v_n_219_);
lean_dec(v_mod_212_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(lean_object* v_mod_223_, lean_object* v_as_224_, lean_object* v_i_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_223_, v_as_224_, v_i_225_);
lean_dec_ref(v_as_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findModule_x3f(lean_object* v_mod_229_, lean_object* v_self_230_){
_start:
{
lean_object* v___y_232_; lean_object* v_targetDecls_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_targetDecls_235_ = lean_ctor_get(v_self_230_, 15);
lean_inc_ref(v_targetDecls_235_);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = ((lean_object*)(l_Lake_Package_findModule_x3f___closed__0));
v___x_238_ = lean_array_get_size(v_targetDecls_235_);
v___x_239_ = lean_nat_dec_lt(v___x_236_, v___x_238_);
if (v___x_239_ == 0)
{
lean_dec_ref(v_targetDecls_235_);
lean_dec_ref(v_self_230_);
v___y_232_ = v___x_237_;
goto v___jp_231_;
}
else
{
size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_usize_of_nat(v___x_238_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_230_, v_targetDecls_235_, v___x_240_, v___x_241_, v___x_237_);
lean_dec_ref(v_targetDecls_235_);
v___y_232_ = v___x_242_;
goto v___jp_231_;
}
v___jp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_array_get_size(v___y_232_);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_229_, v___y_232_, v___x_233_);
lean_dec_ref(v___y_232_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(lean_object* v_mod_243_, lean_object* v_as_244_, lean_object* v_i_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_243_, v_as_244_, v_i_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(lean_object* v_mod_248_, lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_248_, v_as_249_, v_i_250_, v_a_251_);
lean_dec_ref(v_as_249_);
return v_res_252_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
if (lean_obj_tag(v_x_254_) == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
else
{
if (lean_obj_tag(v_x_254_) == 0)
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
else
{
lean_object* v_val_258_; lean_object* v_val_259_; uint8_t v___x_260_; 
v_val_258_ = lean_ctor_get(v_x_253_, 0);
v_val_259_ = lean_ctor_get(v_x_254_, 0);
v___x_260_ = lean_string_dec_eq(v_val_258_, v_val_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_261_, v_x_262_);
lean_dec(v_x_262_);
lean_dec(v_x_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(lean_object* v___x_265_, lean_object* v_f_266_, lean_object* v_x_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = l_Lean_Name_append(v___x_265_, v_x_267_);
v___x_271_ = lean_apply_3(v_f_266_, v___x_270_, v___y_268_, lean_box(0));
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(lean_object* v___x_272_, lean_object* v_f_273_, lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_272_, v_f_273_, v_x_274_, v___y_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(lean_object* v_f_281_, lean_object* v_as_282_, size_t v_sz_283_, size_t v_i_284_, lean_object* v_b_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_a_289_; lean_object* v_snd_290_; uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_lt(v_i_284_, v_sz_283_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_f_281_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_b_285_);
lean_ctor_set(v___x_295_, 1, v___y_286_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_297_ = lean_box(0);
v_a_298_ = lean_array_uget_borrowed(v_as_282_, v_i_284_);
lean_inc(v_a_298_);
v___x_299_ = l_IO_FS_DirEntry_path(v_a_298_);
v___x_300_ = l_System_FilePath_isDir(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_System_FilePath_extension(v___x_299_);
v___x_302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1));
v___x_303_ = l_instBEqOption_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
if (v___x_303_ == 0)
{
v_a_289_ = v___x_297_;
v_snd_290_ = v___y_286_;
goto v___jp_288_;
}
else
{
lean_object* v_fileName_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_fileName_304_ = lean_ctor_get(v_a_298_, 1);
v___x_305_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc_ref(v_fileName_304_);
v___x_306_ = l_System_FilePath_withExtension(v_fileName_304_, v___x_305_);
v___x_307_ = lean_box(0);
v___x_308_ = l_Lean_Name_str___override(v___x_307_, v___x_306_);
lean_inc_ref(v_f_281_);
v___x_309_ = lean_apply_3(v_f_281_, v___x_308_, v___y_286_, lean_box(0));
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_snd_311_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_snd_311_ = lean_ctor_get(v_a_310_, 1);
lean_inc(v_snd_311_);
lean_dec(v_a_310_);
v_a_289_ = v___x_297_;
v_snd_290_ = v_snd_311_;
goto v___jp_288_;
}
else
{
lean_dec_ref(v_f_281_);
return v___x_309_;
}
}
}
else
{
lean_object* v_fileName_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___x_316_; 
v_fileName_312_ = lean_ctor_get(v_a_298_, 1);
v___x_313_ = lean_box(0);
lean_inc_ref(v_fileName_312_);
v___x_314_ = l_Lean_Name_str___override(v___x_313_, v_fileName_312_);
lean_inc_ref(v_f_281_);
v___f_315_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed), 5, 2);
lean_closure_set(v___f_315_, 0, v___x_314_);
lean_closure_set(v___f_315_, 1, v_f_281_);
v___x_316_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_299_, v___f_315_, v___y_286_);
lean_dec_ref(v___x_299_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v_snd_318_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v_snd_318_ = lean_ctor_get(v_a_317_, 1);
lean_inc(v_snd_318_);
lean_dec(v_a_317_);
v_a_289_ = v___x_297_;
v_snd_290_ = v_snd_318_;
goto v___jp_288_;
}
else
{
lean_dec_ref(v_f_281_);
return v___x_316_;
}
}
}
v___jp_288_:
{
size_t v___x_291_; size_t v___x_292_; 
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_284_, v___x_291_);
v_i_284_ = v___x_292_;
v_b_285_ = v_a_289_;
v___y_286_ = v_snd_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(lean_object* v_dir_319_, lean_object* v_f_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_io_read_dir(v_dir_319_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_325_; size_t v_sz_326_; size_t v___x_327_; lean_object* v___x_328_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
v___x_325_ = lean_box(0);
v_sz_326_ = lean_array_size(v_a_324_);
v___x_327_ = ((size_t)0ULL);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_320_, v_a_324_, v_sz_326_, v___x_327_, v___x_325_, v___y_321_);
lean_dec(v_a_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_345_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_345_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_snd_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_343_; 
v_snd_333_ = lean_ctor_get(v_a_329_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_a_329_, 0);
lean_dec(v_unused_344_);
v___x_335_ = v_a_329_;
v_isShared_336_ = v_isSharedCheck_343_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_snd_333_);
lean_dec(v_a_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_343_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_325_);
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_snd_333_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_338_);
v___x_340_ = v___x_331_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
else
{
return v___x_328_;
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___y_321_);
lean_dec_ref(v_f_320_);
v_a_346_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_323_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_323_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(lean_object* v_dir_354_, lean_object* v_f_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v_dir_354_, v_f_355_, v___y_356_);
lean_dec_ref(v_dir_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(lean_object* v_f_359_, lean_object* v_as_360_, lean_object* v_sz_361_, lean_object* v_i_362_, lean_object* v_b_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
size_t v_sz_boxed_366_; size_t v_i_boxed_367_; lean_object* v_res_368_; 
v_sz_boxed_366_ = lean_unbox_usize(v_sz_361_);
lean_dec(v_sz_361_);
v_i_boxed_367_ = lean_unbox_usize(v_i_362_);
lean_dec(v_i_362_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_359_, v_as_360_, v_sz_boxed_366_, v_i_boxed_367_, v_b_363_, v___y_364_);
lean_dec_ref(v_as_360_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(lean_object* v_self_369_, lean_object* v_mod_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_self_369_);
lean_ctor_set(v___x_374_, 1, v_mod_370_);
v___x_375_ = lean_array_push(v___y_371_, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_373_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(lean_object* v_self_378_, lean_object* v_mod_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_378_, v_mod_379_, v___y_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(lean_object* v_a_383_, lean_object* v___f_384_, lean_object* v_x_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = l_Lean_Name_append(v_a_383_, v_x_385_);
v___x_389_ = lean_apply_3(v___f_384_, v___x_388_, v___y_386_, lean_box(0));
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(lean_object* v_a_390_, lean_object* v___f_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_390_, v___f_391_, v_x_392_, v___y_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(lean_object* v_self_396_, lean_object* v_as_397_, size_t v_i_398_, size_t v_stop_399_, lean_object* v_b_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___y_404_; uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_eq(v_i_398_, v_stop_399_);
if (v___x_411_ == 0)
{
lean_object* v_pkg_412_; lean_object* v_config_413_; lean_object* v_config_414_; lean_object* v_dir_415_; lean_object* v_srcDir_416_; lean_object* v_srcDir_417_; lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_pkg_412_ = lean_ctor_get(v_self_396_, 0);
v_config_413_ = lean_ctor_get(v_pkg_412_, 6);
v_config_414_ = lean_ctor_get(v_self_396_, 2);
v_dir_415_ = lean_ctor_get(v_pkg_412_, 4);
v_srcDir_416_ = lean_ctor_get(v_config_413_, 4);
v_srcDir_417_ = lean_ctor_get(v_config_414_, 1);
lean_inc_ref(v_self_396_);
v___f_418_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed), 4, 1);
lean_closure_set(v___f_418_, 0, v_self_396_);
v___x_419_ = lean_array_uget_borrowed(v_as_397_, v_i_398_);
lean_inc_ref(v_srcDir_416_);
v___x_420_ = l_System_FilePath_normalize(v_srcDir_416_);
lean_inc_ref(v_dir_415_);
v___x_421_ = l_Lake_joinRelative(v_dir_415_, v___x_420_);
lean_inc_ref(v_srcDir_417_);
v___x_422_ = l_System_FilePath_normalize(v_srcDir_417_);
v___x_423_ = l_Lake_joinRelative(v___x_421_, v___x_422_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_a_424_; lean_object* v___x_425_; 
lean_dec_ref(v___x_423_);
lean_dec_ref(v___f_418_);
v_a_424_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_424_);
lean_inc_ref(v_self_396_);
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_396_, v_a_424_, v___y_401_);
v___y_404_ = v___x_425_;
goto v___jp_403_;
}
case 1:
{
lean_object* v_a_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_426_ = lean_ctor_get(v___x_419_, 0);
lean_inc_n(v_a_426_, 2);
v___f_427_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_427_, 0, v_a_426_);
lean_closure_set(v___f_427_, 1, v___f_418_);
v___x_428_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_429_ = l_Lean_modToFilePath(v___x_423_, v_a_426_, v___x_428_);
lean_dec_ref(v___x_423_);
v___x_430_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_429_, v___f_427_, v___y_401_);
lean_dec_ref(v___x_429_);
v___y_404_ = v___x_430_;
goto v___jp_403_;
}
default: 
{
lean_object* v_a_431_; lean_object* v___f_432_; lean_object* v___x_433_; 
v_a_431_ = lean_ctor_get(v___x_419_, 0);
lean_inc_n(v_a_431_, 2);
v___f_432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed), 5, 2);
lean_closure_set(v___f_432_, 0, v_a_431_);
lean_closure_set(v___f_432_, 1, v___f_418_);
lean_inc_ref(v_self_396_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_396_, v_a_431_, v___y_401_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_snd_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v_snd_435_ = lean_ctor_get(v_a_434_, 1);
lean_inc(v_snd_435_);
lean_dec(v_a_434_);
v___x_436_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
lean_inc(v_a_431_);
v___x_437_ = l_Lean_modToFilePath(v___x_423_, v_a_431_, v___x_436_);
lean_dec_ref(v___x_423_);
v___x_438_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_437_, v___f_432_, v_snd_435_);
lean_dec_ref(v___x_437_);
v___y_404_ = v___x_438_;
goto v___jp_403_;
}
else
{
lean_dec_ref(v___f_432_);
lean_dec_ref(v___x_423_);
lean_dec_ref(v_self_396_);
return v___x_433_;
}
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_self_396_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_b_400_);
lean_ctor_set(v___x_439_, 1, v___y_401_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
v___jp_403_:
{
if (lean_obj_tag(v___y_404_) == 0)
{
lean_object* v_a_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; size_t v___x_408_; size_t v___x_409_; 
v_a_405_ = lean_ctor_get(v___y_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___y_404_, 1);
v_fst_406_ = lean_ctor_get(v_a_405_, 0);
lean_inc(v_fst_406_);
v_snd_407_ = lean_ctor_get(v_a_405_, 1);
lean_inc(v_snd_407_);
lean_dec(v_a_405_);
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_398_, v___x_408_);
v_i_398_ = v___x_409_;
v_b_400_ = v_fst_406_;
v___y_401_ = v_snd_407_;
goto _start;
}
else
{
lean_dec_ref(v_self_396_);
return v___y_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(lean_object* v_self_441_, lean_object* v_as_442_, lean_object* v_i_443_, lean_object* v_stop_444_, lean_object* v_b_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
size_t v_i_boxed_448_; size_t v_stop_boxed_449_; lean_object* v_res_450_; 
v_i_boxed_448_ = lean_unbox_usize(v_i_443_);
lean_dec(v_i_443_);
v_stop_boxed_449_ = lean_unbox_usize(v_stop_444_);
lean_dec(v_stop_444_);
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_441_, v_as_442_, v_i_boxed_448_, v_stop_boxed_449_, v_b_445_, v___y_446_);
lean_dec_ref(v_as_442_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray(lean_object* v_self_453_){
_start:
{
lean_object* v_config_455_; lean_object* v_globs_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_config_455_ = lean_ctor_get(v_self_453_, 2);
v_globs_456_ = lean_ctor_get(v_config_455_, 3);
lean_inc_ref(v_globs_456_);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_array_get_size(v_globs_456_);
v___x_459_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_460_ = lean_nat_dec_lt(v___x_457_, v___x_458_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec_ref(v_globs_456_);
lean_dec_ref(v_self_453_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_box(0);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_458_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_453_, v_globs_456_, v___x_463_, v___x_464_, v___x_462_, v___x_459_);
lean_dec_ref(v_globs_456_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_snd_470_; lean_object* v___x_472_; 
v_snd_470_ = lean_ctor_get(v_a_466_, 1);
lean_inc(v_snd_470_);
lean_dec(v_a_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v_snd_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_snd_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_465_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_465_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_getModuleArray___boxed(lean_object* v_self_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lake_LeanLib_getModuleArray(v_self_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(lean_object* v_self_486_, lean_object* v_as_487_, size_t v_i_488_, size_t v_stop_489_, lean_object* v_b_490_){
_start:
{
lean_object* v___y_492_; uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_eq(v_i_488_, v_stop_489_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_array_uget_borrowed(v_as_487_, v_i_488_);
lean_inc_ref(v_self_486_);
lean_inc(v___x_497_);
v___x_498_ = l_Lake_LeanLib_findModule_x3f(v___x_497_, v_self_486_);
if (lean_obj_tag(v___x_498_) == 0)
{
v___y_492_ = v_b_490_;
goto v___jp_491_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_500_; 
v_val_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = lean_array_push(v_b_490_, v_val_499_);
v___y_492_ = v___x_500_;
goto v___jp_491_;
}
}
else
{
lean_dec_ref(v_self_486_);
return v_b_490_;
}
v___jp_491_:
{
size_t v___x_493_; size_t v___x_494_; 
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_488_, v___x_493_);
v_i_488_ = v___x_494_;
v_b_490_ = v___y_492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(lean_object* v_self_501_, lean_object* v_as_502_, lean_object* v_i_503_, lean_object* v_stop_504_, lean_object* v_b_505_){
_start:
{
size_t v_i_boxed_506_; size_t v_stop_boxed_507_; lean_object* v_res_508_; 
v_i_boxed_506_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_stop_boxed_507_ = lean_unbox_usize(v_stop_504_);
lean_dec(v_stop_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_501_, v_as_502_, v_i_boxed_506_, v_stop_boxed_507_, v_b_505_);
lean_dec_ref(v_as_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(lean_object* v_self_509_, lean_object* v_as_510_, lean_object* v_start_511_, lean_object* v_stop_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lake_LeanLib_getModuleArray___closed__0));
v___x_514_ = lean_nat_dec_lt(v_start_511_, v_stop_512_);
if (v___x_514_ == 0)
{
lean_dec_ref(v_self_509_);
return v___x_513_;
}
else
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_get_size(v_as_510_);
v___x_516_ = lean_nat_dec_le(v_stop_512_, v___x_515_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v_start_511_, v___x_515_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_self_509_);
return v___x_513_;
}
else
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_usize_of_nat(v_start_511_);
v___x_519_ = lean_usize_of_nat(v___x_515_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_509_, v_as_510_, v___x_518_, v___x_519_, v___x_513_);
return v___x_520_;
}
}
else
{
size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_usize_of_nat(v_start_511_);
v___x_522_ = lean_usize_of_nat(v_stop_512_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_509_, v_as_510_, v___x_521_, v___x_522_, v___x_513_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(lean_object* v_self_524_, lean_object* v_as_525_, lean_object* v_start_526_, lean_object* v_stop_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_524_, v_as_525_, v_start_526_, v_stop_527_);
lean_dec(v_stop_527_);
lean_dec(v_start_526_);
lean_dec_ref(v_as_525_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_rootModules(lean_object* v_self_529_){
_start:
{
lean_object* v_config_530_; lean_object* v_roots_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_config_530_ = lean_ctor_get(v_self_529_, 2);
v_roots_531_ = lean_ctor_get(v_config_530_, 2);
lean_inc_ref(v_roots_531_);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_array_get_size(v_roots_531_);
v___x_534_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(v_self_529_, v_roots_531_, v___x_532_, v___x_533_);
lean_dec_ref(v_roots_531_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg(lean_object* v_self_535_){
_start:
{
lean_object* v_lib_536_; lean_object* v_pkg_537_; 
v_lib_536_ = lean_ctor_get(v_self_535_, 0);
v_pkg_537_ = lean_ctor_get(v_lib_536_, 0);
lean_inc_ref(v_pkg_537_);
return v_pkg_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_pkg___boxed(lean_object* v_self_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_Module_pkg(v_self_538_);
lean_dec_ref(v_self_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_rootDir(lean_object* v_self_540_){
_start:
{
lean_object* v_lib_541_; lean_object* v_pkg_542_; lean_object* v_config_543_; lean_object* v_config_544_; lean_object* v_dir_545_; lean_object* v_srcDir_546_; lean_object* v_srcDir_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_lib_541_ = lean_ctor_get(v_self_540_, 0);
lean_inc_ref(v_lib_541_);
lean_dec_ref(v_self_540_);
v_pkg_542_ = lean_ctor_get(v_lib_541_, 0);
lean_inc_ref(v_pkg_542_);
v_config_543_ = lean_ctor_get(v_pkg_542_, 6);
lean_inc_ref(v_config_543_);
v_config_544_ = lean_ctor_get(v_lib_541_, 2);
lean_inc(v_config_544_);
lean_dec_ref(v_lib_541_);
v_dir_545_ = lean_ctor_get(v_pkg_542_, 4);
lean_inc_ref(v_dir_545_);
lean_dec_ref(v_pkg_542_);
v_srcDir_546_ = lean_ctor_get(v_config_543_, 4);
lean_inc_ref(v_srcDir_546_);
lean_dec_ref(v_config_543_);
v_srcDir_547_ = lean_ctor_get(v_config_544_, 1);
lean_inc_ref(v_srcDir_547_);
lean_dec(v_config_544_);
v___x_548_ = l_System_FilePath_normalize(v_srcDir_546_);
v___x_549_ = l_Lake_joinRelative(v_dir_545_, v___x_548_);
v___x_550_ = l_System_FilePath_normalize(v_srcDir_547_);
v___x_551_ = l_Lake_joinRelative(v___x_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName(lean_object* v_ext_552_, lean_object* v_self_553_){
_start:
{
lean_object* v_name_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_name_554_ = lean_ctor_get(v_self_553_, 1);
v___x_555_ = l_Lean_Name_getString_x21(v_name_554_);
v___x_556_ = l_System_FilePath_addExtension(v___x_555_, v_ext_552_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_fileName___boxed(lean_object* v_ext_557_, lean_object* v_self_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lake_Module_fileName(v_ext_557_, v_self_558_);
lean_dec_ref(v_self_558_);
lean_dec_ref(v_ext_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath(lean_object* v_dir_560_, lean_object* v_ext_561_, lean_object* v_self_562_){
_start:
{
lean_object* v_name_563_; lean_object* v___x_564_; 
v_name_563_ = lean_ctor_get(v_self_562_, 1);
lean_inc(v_name_563_);
lean_dec_ref(v_self_562_);
v___x_564_ = l_Lean_modToFilePath(v_dir_560_, v_name_563_, v_ext_561_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_filePath___boxed(lean_object* v_dir_565_, lean_object* v_ext_566_, lean_object* v_self_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lake_Module_filePath(v_dir_565_, v_ext_566_, v_self_567_);
lean_dec_ref(v_ext_566_);
lean_dec_ref(v_dir_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath(lean_object* v_ext_569_, lean_object* v_self_570_){
_start:
{
lean_object* v_lib_571_; lean_object* v_pkg_572_; lean_object* v_config_573_; lean_object* v_config_574_; lean_object* v_name_575_; lean_object* v_dir_576_; lean_object* v_srcDir_577_; lean_object* v_srcDir_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_lib_571_ = lean_ctor_get(v_self_570_, 0);
v_pkg_572_ = lean_ctor_get(v_lib_571_, 0);
lean_inc_ref(v_pkg_572_);
v_config_573_ = lean_ctor_get(v_pkg_572_, 6);
lean_inc_ref(v_config_573_);
v_config_574_ = lean_ctor_get(v_lib_571_, 2);
lean_inc(v_config_574_);
v_name_575_ = lean_ctor_get(v_self_570_, 1);
lean_inc(v_name_575_);
lean_dec_ref(v_self_570_);
v_dir_576_ = lean_ctor_get(v_pkg_572_, 4);
lean_inc_ref(v_dir_576_);
lean_dec_ref(v_pkg_572_);
v_srcDir_577_ = lean_ctor_get(v_config_573_, 4);
lean_inc_ref(v_srcDir_577_);
lean_dec_ref(v_config_573_);
v_srcDir_578_ = lean_ctor_get(v_config_574_, 1);
lean_inc_ref(v_srcDir_578_);
lean_dec(v_config_574_);
v___x_579_ = l_System_FilePath_normalize(v_srcDir_577_);
v___x_580_ = l_Lake_joinRelative(v_dir_576_, v___x_579_);
v___x_581_ = l_System_FilePath_normalize(v_srcDir_578_);
v___x_582_ = l_Lake_joinRelative(v___x_580_, v___x_581_);
v___x_583_ = l_Lean_modToFilePath(v___x_582_, v_name_575_, v_ext_569_);
lean_dec_ref(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_srcPath___boxed(lean_object* v_ext_584_, lean_object* v_self_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lake_Module_srcPath(v_ext_584_, v_self_585_);
lean_dec_ref(v_ext_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanFile(lean_object* v_self_587_){
_start:
{
lean_object* v_lib_588_; lean_object* v_pkg_589_; lean_object* v_config_590_; lean_object* v_config_591_; lean_object* v_name_592_; lean_object* v_dir_593_; lean_object* v_srcDir_594_; lean_object* v_srcDir_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_lib_588_ = lean_ctor_get(v_self_587_, 0);
v_pkg_589_ = lean_ctor_get(v_lib_588_, 0);
lean_inc_ref(v_pkg_589_);
v_config_590_ = lean_ctor_get(v_pkg_589_, 6);
lean_inc_ref(v_config_590_);
v_config_591_ = lean_ctor_get(v_lib_588_, 2);
lean_inc(v_config_591_);
v_name_592_ = lean_ctor_get(v_self_587_, 1);
lean_inc(v_name_592_);
lean_dec_ref(v_self_587_);
v_dir_593_ = lean_ctor_get(v_pkg_589_, 4);
lean_inc_ref(v_dir_593_);
lean_dec_ref(v_pkg_589_);
v_srcDir_594_ = lean_ctor_get(v_config_590_, 4);
lean_inc_ref(v_srcDir_594_);
lean_dec_ref(v_config_590_);
v_srcDir_595_ = lean_ctor_get(v_config_591_, 1);
lean_inc_ref(v_srcDir_595_);
lean_dec(v_config_591_);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_597_ = l_System_FilePath_normalize(v_srcDir_594_);
v___x_598_ = l_Lake_joinRelative(v_dir_593_, v___x_597_);
v___x_599_ = l_System_FilePath_normalize(v_srcDir_595_);
v___x_600_ = l_Lake_joinRelative(v___x_598_, v___x_599_);
v___x_601_ = l_Lean_modToFilePath(v___x_600_, v_name_592_, v___x_596_);
lean_dec_ref(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_relLeanFile(lean_object* v_self_602_){
_start:
{
lean_object* v_lib_603_; lean_object* v_pkg_604_; lean_object* v_config_605_; lean_object* v_config_606_; lean_object* v_name_607_; lean_object* v_dir_608_; lean_object* v_srcDir_609_; lean_object* v_srcDir_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_lib_603_ = lean_ctor_get(v_self_602_, 0);
v_pkg_604_ = lean_ctor_get(v_lib_603_, 0);
lean_inc_ref(v_pkg_604_);
v_config_605_ = lean_ctor_get(v_pkg_604_, 6);
lean_inc_ref(v_config_605_);
v_config_606_ = lean_ctor_get(v_lib_603_, 2);
lean_inc(v_config_606_);
v_name_607_ = lean_ctor_get(v_self_602_, 1);
lean_inc(v_name_607_);
lean_dec_ref(v_self_602_);
v_dir_608_ = lean_ctor_get(v_pkg_604_, 4);
lean_inc_ref_n(v_dir_608_, 2);
lean_dec_ref(v_pkg_604_);
v_srcDir_609_ = lean_ctor_get(v_config_605_, 4);
lean_inc_ref(v_srcDir_609_);
lean_dec_ref(v_config_605_);
v_srcDir_610_ = lean_ctor_get(v_config_606_, 1);
lean_inc_ref(v_srcDir_610_);
lean_dec(v_config_606_);
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0));
v___x_612_ = l_System_FilePath_normalize(v_srcDir_609_);
v___x_613_ = l_Lake_joinRelative(v_dir_608_, v___x_612_);
v___x_614_ = l_System_FilePath_normalize(v_srcDir_610_);
v___x_615_ = l_Lake_joinRelative(v___x_613_, v___x_614_);
v___x_616_ = l_Lean_modToFilePath(v___x_615_, v_name_607_, v___x_611_);
lean_dec_ref(v___x_615_);
v___x_617_ = l_Lake_relPathFrom(v_dir_608_, v___x_616_);
lean_dec_ref(v_dir_608_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath(lean_object* v_ext_618_, lean_object* v_self_619_){
_start:
{
lean_object* v_lib_620_; lean_object* v_pkg_621_; lean_object* v_config_622_; lean_object* v_name_623_; lean_object* v_dir_624_; lean_object* v_buildDir_625_; lean_object* v_leanLibDir_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_lib_620_ = lean_ctor_get(v_self_619_, 0);
v_pkg_621_ = lean_ctor_get(v_lib_620_, 0);
lean_inc_ref(v_pkg_621_);
v_config_622_ = lean_ctor_get(v_pkg_621_, 6);
lean_inc_ref(v_config_622_);
v_name_623_ = lean_ctor_get(v_self_619_, 1);
lean_inc(v_name_623_);
lean_dec_ref(v_self_619_);
v_dir_624_ = lean_ctor_get(v_pkg_621_, 4);
lean_inc_ref(v_dir_624_);
lean_dec_ref(v_pkg_621_);
v_buildDir_625_ = lean_ctor_get(v_config_622_, 5);
lean_inc_ref(v_buildDir_625_);
v_leanLibDir_626_ = lean_ctor_get(v_config_622_, 6);
lean_inc_ref(v_leanLibDir_626_);
lean_dec_ref(v_config_622_);
v___x_627_ = l_System_FilePath_normalize(v_buildDir_625_);
v___x_628_ = l_Lake_joinRelative(v_dir_624_, v___x_627_);
v___x_629_ = l_System_FilePath_normalize(v_leanLibDir_626_);
v___x_630_ = l_Lake_joinRelative(v___x_628_, v___x_629_);
v___x_631_ = l_Lean_modToFilePath(v___x_630_, v_name_623_, v_ext_618_);
lean_dec_ref(v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibPath___boxed(lean_object* v_ext_632_, lean_object* v_self_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lake_Module_leanLibPath(v_ext_632_, v_self_633_);
lean_dec_ref(v_ext_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanLibDir(lean_object* v_self_635_){
_start:
{
lean_object* v_lib_636_; lean_object* v_pkg_637_; lean_object* v_config_638_; lean_object* v_name_639_; lean_object* v_dir_640_; lean_object* v_buildDir_641_; lean_object* v_leanLibDir_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_lib_636_ = lean_ctor_get(v_self_635_, 0);
v_pkg_637_ = lean_ctor_get(v_lib_636_, 0);
lean_inc_ref(v_pkg_637_);
v_config_638_ = lean_ctor_get(v_pkg_637_, 6);
lean_inc_ref(v_config_638_);
v_name_639_ = lean_ctor_get(v_self_635_, 1);
lean_inc(v_name_639_);
lean_dec_ref(v_self_635_);
v_dir_640_ = lean_ctor_get(v_pkg_637_, 4);
lean_inc_ref(v_dir_640_);
lean_dec_ref(v_pkg_637_);
v_buildDir_641_ = lean_ctor_get(v_config_638_, 5);
lean_inc_ref(v_buildDir_641_);
v_leanLibDir_642_ = lean_ctor_get(v_config_638_, 6);
lean_inc_ref(v_leanLibDir_642_);
lean_dec_ref(v_config_638_);
v___x_643_ = l_System_FilePath_normalize(v_buildDir_641_);
v___x_644_ = l_Lake_joinRelative(v_dir_640_, v___x_643_);
v___x_645_ = l_System_FilePath_normalize(v_leanLibDir_642_);
v___x_646_ = l_Lake_joinRelative(v___x_644_, v___x_645_);
v___x_647_ = l_Lean_Name_getPrefix(v_name_639_);
lean_dec(v_name_639_);
v___x_648_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_649_ = l_Lean_modToFilePath(v___x_646_, v___x_647_, v___x_648_);
lean_dec_ref(v___x_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanFile(lean_object* v_self_651_){
_start:
{
lean_object* v_lib_652_; lean_object* v_pkg_653_; lean_object* v_config_654_; lean_object* v_name_655_; lean_object* v_dir_656_; lean_object* v_buildDir_657_; lean_object* v_leanLibDir_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_lib_652_ = lean_ctor_get(v_self_651_, 0);
v_pkg_653_ = lean_ctor_get(v_lib_652_, 0);
lean_inc_ref(v_pkg_653_);
v_config_654_ = lean_ctor_get(v_pkg_653_, 6);
lean_inc_ref(v_config_654_);
v_name_655_ = lean_ctor_get(v_self_651_, 1);
lean_inc(v_name_655_);
lean_dec_ref(v_self_651_);
v_dir_656_ = lean_ctor_get(v_pkg_653_, 4);
lean_inc_ref(v_dir_656_);
lean_dec_ref(v_pkg_653_);
v_buildDir_657_ = lean_ctor_get(v_config_654_, 5);
lean_inc_ref(v_buildDir_657_);
v_leanLibDir_658_ = lean_ctor_get(v_config_654_, 6);
lean_inc_ref(v_leanLibDir_658_);
lean_dec_ref(v_config_654_);
v___x_659_ = ((lean_object*)(l_Lake_Module_oleanFile___closed__0));
v___x_660_ = l_System_FilePath_normalize(v_buildDir_657_);
v___x_661_ = l_Lake_joinRelative(v_dir_656_, v___x_660_);
v___x_662_ = l_System_FilePath_normalize(v_leanLibDir_658_);
v___x_663_ = l_Lake_joinRelative(v___x_661_, v___x_662_);
v___x_664_ = l_Lean_modToFilePath(v___x_663_, v_name_655_, v___x_659_);
lean_dec_ref(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanServerFile(lean_object* v_self_666_){
_start:
{
lean_object* v_lib_667_; lean_object* v_pkg_668_; lean_object* v_config_669_; lean_object* v_name_670_; lean_object* v_dir_671_; lean_object* v_buildDir_672_; lean_object* v_leanLibDir_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_lib_667_ = lean_ctor_get(v_self_666_, 0);
v_pkg_668_ = lean_ctor_get(v_lib_667_, 0);
lean_inc_ref(v_pkg_668_);
v_config_669_ = lean_ctor_get(v_pkg_668_, 6);
lean_inc_ref(v_config_669_);
v_name_670_ = lean_ctor_get(v_self_666_, 1);
lean_inc(v_name_670_);
lean_dec_ref(v_self_666_);
v_dir_671_ = lean_ctor_get(v_pkg_668_, 4);
lean_inc_ref(v_dir_671_);
lean_dec_ref(v_pkg_668_);
v_buildDir_672_ = lean_ctor_get(v_config_669_, 5);
lean_inc_ref(v_buildDir_672_);
v_leanLibDir_673_ = lean_ctor_get(v_config_669_, 6);
lean_inc_ref(v_leanLibDir_673_);
lean_dec_ref(v_config_669_);
v___x_674_ = ((lean_object*)(l_Lake_Module_oleanServerFile___closed__0));
v___x_675_ = l_System_FilePath_normalize(v_buildDir_672_);
v___x_676_ = l_Lake_joinRelative(v_dir_671_, v___x_675_);
v___x_677_ = l_System_FilePath_normalize(v_leanLibDir_673_);
v___x_678_ = l_Lake_joinRelative(v___x_676_, v___x_677_);
v___x_679_ = l_Lean_modToFilePath(v___x_678_, v_name_670_, v___x_674_);
lean_dec_ref(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_oleanPrivateFile(lean_object* v_self_681_){
_start:
{
lean_object* v_lib_682_; lean_object* v_pkg_683_; lean_object* v_config_684_; lean_object* v_name_685_; lean_object* v_dir_686_; lean_object* v_buildDir_687_; lean_object* v_leanLibDir_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_lib_682_ = lean_ctor_get(v_self_681_, 0);
v_pkg_683_ = lean_ctor_get(v_lib_682_, 0);
lean_inc_ref(v_pkg_683_);
v_config_684_ = lean_ctor_get(v_pkg_683_, 6);
lean_inc_ref(v_config_684_);
v_name_685_ = lean_ctor_get(v_self_681_, 1);
lean_inc(v_name_685_);
lean_dec_ref(v_self_681_);
v_dir_686_ = lean_ctor_get(v_pkg_683_, 4);
lean_inc_ref(v_dir_686_);
lean_dec_ref(v_pkg_683_);
v_buildDir_687_ = lean_ctor_get(v_config_684_, 5);
lean_inc_ref(v_buildDir_687_);
v_leanLibDir_688_ = lean_ctor_get(v_config_684_, 6);
lean_inc_ref(v_leanLibDir_688_);
lean_dec_ref(v_config_684_);
v___x_689_ = ((lean_object*)(l_Lake_Module_oleanPrivateFile___closed__0));
v___x_690_ = l_System_FilePath_normalize(v_buildDir_687_);
v___x_691_ = l_Lake_joinRelative(v_dir_686_, v___x_690_);
v___x_692_ = l_System_FilePath_normalize(v_leanLibDir_688_);
v___x_693_ = l_Lake_joinRelative(v___x_691_, v___x_692_);
v___x_694_ = l_Lean_modToFilePath(v___x_693_, v_name_685_, v___x_689_);
lean_dec_ref(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ileanFile(lean_object* v_self_696_){
_start:
{
lean_object* v_lib_697_; lean_object* v_pkg_698_; lean_object* v_config_699_; lean_object* v_name_700_; lean_object* v_dir_701_; lean_object* v_buildDir_702_; lean_object* v_leanLibDir_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_lib_697_ = lean_ctor_get(v_self_696_, 0);
v_pkg_698_ = lean_ctor_get(v_lib_697_, 0);
lean_inc_ref(v_pkg_698_);
v_config_699_ = lean_ctor_get(v_pkg_698_, 6);
lean_inc_ref(v_config_699_);
v_name_700_ = lean_ctor_get(v_self_696_, 1);
lean_inc(v_name_700_);
lean_dec_ref(v_self_696_);
v_dir_701_ = lean_ctor_get(v_pkg_698_, 4);
lean_inc_ref(v_dir_701_);
lean_dec_ref(v_pkg_698_);
v_buildDir_702_ = lean_ctor_get(v_config_699_, 5);
lean_inc_ref(v_buildDir_702_);
v_leanLibDir_703_ = lean_ctor_get(v_config_699_, 6);
lean_inc_ref(v_leanLibDir_703_);
lean_dec_ref(v_config_699_);
v___x_704_ = ((lean_object*)(l_Lake_Module_ileanFile___closed__0));
v___x_705_ = l_System_FilePath_normalize(v_buildDir_702_);
v___x_706_ = l_Lake_joinRelative(v_dir_701_, v___x_705_);
v___x_707_ = l_System_FilePath_normalize(v_leanLibDir_703_);
v___x_708_ = l_Lake_joinRelative(v___x_706_, v___x_707_);
v___x_709_ = l_Lean_modToFilePath(v___x_708_, v_name_700_, v___x_704_);
lean_dec_ref(v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSigFile(lean_object* v_self_711_){
_start:
{
lean_object* v_lib_712_; lean_object* v_pkg_713_; lean_object* v_config_714_; lean_object* v_name_715_; lean_object* v_dir_716_; lean_object* v_buildDir_717_; lean_object* v_leanLibDir_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_lib_712_ = lean_ctor_get(v_self_711_, 0);
v_pkg_713_ = lean_ctor_get(v_lib_712_, 0);
lean_inc_ref(v_pkg_713_);
v_config_714_ = lean_ctor_get(v_pkg_713_, 6);
lean_inc_ref(v_config_714_);
v_name_715_ = lean_ctor_get(v_self_711_, 1);
lean_inc(v_name_715_);
lean_dec_ref(v_self_711_);
v_dir_716_ = lean_ctor_get(v_pkg_713_, 4);
lean_inc_ref(v_dir_716_);
lean_dec_ref(v_pkg_713_);
v_buildDir_717_ = lean_ctor_get(v_config_714_, 5);
lean_inc_ref(v_buildDir_717_);
v_leanLibDir_718_ = lean_ctor_get(v_config_714_, 6);
lean_inc_ref(v_leanLibDir_718_);
lean_dec_ref(v_config_714_);
v___x_719_ = ((lean_object*)(l_Lake_Module_irSigFile___closed__0));
v___x_720_ = l_System_FilePath_normalize(v_buildDir_717_);
v___x_721_ = l_Lake_joinRelative(v_dir_716_, v___x_720_);
v___x_722_ = l_System_FilePath_normalize(v_leanLibDir_718_);
v___x_723_ = l_Lake_joinRelative(v___x_721_, v___x_722_);
v___x_724_ = l_Lean_modToFilePath(v___x_723_, v_name_715_, v___x_719_);
lean_dec_ref(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irFile(lean_object* v_self_726_){
_start:
{
lean_object* v_lib_727_; lean_object* v_pkg_728_; lean_object* v_config_729_; lean_object* v_name_730_; lean_object* v_dir_731_; lean_object* v_buildDir_732_; lean_object* v_leanLibDir_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_lib_727_ = lean_ctor_get(v_self_726_, 0);
v_pkg_728_ = lean_ctor_get(v_lib_727_, 0);
lean_inc_ref(v_pkg_728_);
v_config_729_ = lean_ctor_get(v_pkg_728_, 6);
lean_inc_ref(v_config_729_);
v_name_730_ = lean_ctor_get(v_self_726_, 1);
lean_inc(v_name_730_);
lean_dec_ref(v_self_726_);
v_dir_731_ = lean_ctor_get(v_pkg_728_, 4);
lean_inc_ref(v_dir_731_);
lean_dec_ref(v_pkg_728_);
v_buildDir_732_ = lean_ctor_get(v_config_729_, 5);
lean_inc_ref(v_buildDir_732_);
v_leanLibDir_733_ = lean_ctor_get(v_config_729_, 6);
lean_inc_ref(v_leanLibDir_733_);
lean_dec_ref(v_config_729_);
v___x_734_ = ((lean_object*)(l_Lake_Module_irFile___closed__0));
v___x_735_ = l_System_FilePath_normalize(v_buildDir_732_);
v___x_736_ = l_Lake_joinRelative(v_dir_731_, v___x_735_);
v___x_737_ = l_System_FilePath_normalize(v_leanLibDir_733_);
v___x_738_ = l_Lake_joinRelative(v___x_736_, v___x_737_);
v___x_739_ = l_Lean_modToFilePath(v___x_738_, v_name_730_, v___x_734_);
lean_dec_ref(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_traceFile(lean_object* v_self_741_){
_start:
{
lean_object* v_lib_742_; lean_object* v_pkg_743_; lean_object* v_config_744_; lean_object* v_name_745_; lean_object* v_dir_746_; lean_object* v_buildDir_747_; lean_object* v_leanLibDir_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_lib_742_ = lean_ctor_get(v_self_741_, 0);
v_pkg_743_ = lean_ctor_get(v_lib_742_, 0);
lean_inc_ref(v_pkg_743_);
v_config_744_ = lean_ctor_get(v_pkg_743_, 6);
lean_inc_ref(v_config_744_);
v_name_745_ = lean_ctor_get(v_self_741_, 1);
lean_inc(v_name_745_);
lean_dec_ref(v_self_741_);
v_dir_746_ = lean_ctor_get(v_pkg_743_, 4);
lean_inc_ref(v_dir_746_);
lean_dec_ref(v_pkg_743_);
v_buildDir_747_ = lean_ctor_get(v_config_744_, 5);
lean_inc_ref(v_buildDir_747_);
v_leanLibDir_748_ = lean_ctor_get(v_config_744_, 6);
lean_inc_ref(v_leanLibDir_748_);
lean_dec_ref(v_config_744_);
v___x_749_ = ((lean_object*)(l_Lake_Module_traceFile___closed__0));
v___x_750_ = l_System_FilePath_normalize(v_buildDir_747_);
v___x_751_ = l_Lake_joinRelative(v_dir_746_, v___x_750_);
v___x_752_ = l_System_FilePath_normalize(v_leanLibDir_748_);
v___x_753_ = l_Lake_joinRelative(v___x_751_, v___x_752_);
v___x_754_ = l_Lean_modToFilePath(v___x_753_, v_name_745_, v___x_749_);
lean_dec_ref(v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irTraceFile(lean_object* v_self_756_){
_start:
{
lean_object* v_lib_757_; lean_object* v_pkg_758_; lean_object* v_config_759_; lean_object* v_name_760_; lean_object* v_dir_761_; lean_object* v_buildDir_762_; lean_object* v_leanLibDir_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_lib_757_ = lean_ctor_get(v_self_756_, 0);
v_pkg_758_ = lean_ctor_get(v_lib_757_, 0);
lean_inc_ref(v_pkg_758_);
v_config_759_ = lean_ctor_get(v_pkg_758_, 6);
lean_inc_ref(v_config_759_);
v_name_760_ = lean_ctor_get(v_self_756_, 1);
lean_inc(v_name_760_);
lean_dec_ref(v_self_756_);
v_dir_761_ = lean_ctor_get(v_pkg_758_, 4);
lean_inc_ref(v_dir_761_);
lean_dec_ref(v_pkg_758_);
v_buildDir_762_ = lean_ctor_get(v_config_759_, 5);
lean_inc_ref(v_buildDir_762_);
v_leanLibDir_763_ = lean_ctor_get(v_config_759_, 6);
lean_inc_ref(v_leanLibDir_763_);
lean_dec_ref(v_config_759_);
v___x_764_ = ((lean_object*)(l_Lake_Module_irTraceFile___closed__0));
v___x_765_ = l_System_FilePath_normalize(v_buildDir_762_);
v___x_766_ = l_Lake_joinRelative(v_dir_761_, v___x_765_);
v___x_767_ = l_System_FilePath_normalize(v_leanLibDir_763_);
v___x_768_ = l_Lake_joinRelative(v___x_766_, v___x_767_);
v___x_769_ = l_Lean_modToFilePath(v___x_768_, v_name_760_, v___x_764_);
lean_dec_ref(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath(lean_object* v_ext_770_, lean_object* v_self_771_){
_start:
{
lean_object* v_lib_772_; lean_object* v_pkg_773_; lean_object* v_config_774_; lean_object* v_name_775_; lean_object* v_dir_776_; lean_object* v_buildDir_777_; lean_object* v_irDir_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_lib_772_ = lean_ctor_get(v_self_771_, 0);
v_pkg_773_ = lean_ctor_get(v_lib_772_, 0);
lean_inc_ref(v_pkg_773_);
v_config_774_ = lean_ctor_get(v_pkg_773_, 6);
lean_inc_ref(v_config_774_);
v_name_775_ = lean_ctor_get(v_self_771_, 1);
lean_inc(v_name_775_);
lean_dec_ref(v_self_771_);
v_dir_776_ = lean_ctor_get(v_pkg_773_, 4);
lean_inc_ref(v_dir_776_);
lean_dec_ref(v_pkg_773_);
v_buildDir_777_ = lean_ctor_get(v_config_774_, 5);
lean_inc_ref(v_buildDir_777_);
v_irDir_778_ = lean_ctor_get(v_config_774_, 9);
lean_inc_ref(v_irDir_778_);
lean_dec_ref(v_config_774_);
v___x_779_ = l_System_FilePath_normalize(v_buildDir_777_);
v___x_780_ = l_Lake_joinRelative(v_dir_776_, v___x_779_);
v___x_781_ = l_System_FilePath_normalize(v_irDir_778_);
v___x_782_ = l_Lake_joinRelative(v___x_780_, v___x_781_);
v___x_783_ = l_Lean_modToFilePath(v___x_782_, v_name_775_, v_ext_770_);
lean_dec_ref(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irPath___boxed(lean_object* v_ext_784_, lean_object* v_self_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lake_Module_irPath(v_ext_784_, v_self_785_);
lean_dec_ref(v_ext_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irDir(lean_object* v_self_787_){
_start:
{
lean_object* v_lib_788_; lean_object* v_pkg_789_; lean_object* v_config_790_; lean_object* v_name_791_; lean_object* v_dir_792_; lean_object* v_buildDir_793_; lean_object* v_irDir_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_lib_788_ = lean_ctor_get(v_self_787_, 0);
v_pkg_789_ = lean_ctor_get(v_lib_788_, 0);
lean_inc_ref(v_pkg_789_);
v_config_790_ = lean_ctor_get(v_pkg_789_, 6);
lean_inc_ref(v_config_790_);
v_name_791_ = lean_ctor_get(v_self_787_, 1);
lean_inc(v_name_791_);
lean_dec_ref(v_self_787_);
v_dir_792_ = lean_ctor_get(v_pkg_789_, 4);
lean_inc_ref(v_dir_792_);
lean_dec_ref(v_pkg_789_);
v_buildDir_793_ = lean_ctor_get(v_config_790_, 5);
lean_inc_ref(v_buildDir_793_);
v_irDir_794_ = lean_ctor_get(v_config_790_, 9);
lean_inc_ref(v_irDir_794_);
lean_dec_ref(v_config_790_);
v___x_795_ = l_System_FilePath_normalize(v_buildDir_793_);
v___x_796_ = l_Lake_joinRelative(v_dir_792_, v___x_795_);
v___x_797_ = l_System_FilePath_normalize(v_irDir_794_);
v___x_798_ = l_Lake_joinRelative(v___x_796_, v___x_797_);
v___x_799_ = l_Lean_Name_getPrefix(v_name_791_);
lean_dec(v_name_791_);
v___x_800_ = ((lean_object*)(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0));
v___x_801_ = l_Lean_modToFilePath(v___x_798_, v___x_799_, v___x_800_);
lean_dec_ref(v___x_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_setupFile(lean_object* v_self_803_){
_start:
{
lean_object* v_lib_804_; lean_object* v_pkg_805_; lean_object* v_config_806_; lean_object* v_name_807_; lean_object* v_dir_808_; lean_object* v_buildDir_809_; lean_object* v_irDir_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_lib_804_ = lean_ctor_get(v_self_803_, 0);
v_pkg_805_ = lean_ctor_get(v_lib_804_, 0);
lean_inc_ref(v_pkg_805_);
v_config_806_ = lean_ctor_get(v_pkg_805_, 6);
lean_inc_ref(v_config_806_);
v_name_807_ = lean_ctor_get(v_self_803_, 1);
lean_inc(v_name_807_);
lean_dec_ref(v_self_803_);
v_dir_808_ = lean_ctor_get(v_pkg_805_, 4);
lean_inc_ref(v_dir_808_);
lean_dec_ref(v_pkg_805_);
v_buildDir_809_ = lean_ctor_get(v_config_806_, 5);
lean_inc_ref(v_buildDir_809_);
v_irDir_810_ = lean_ctor_get(v_config_806_, 9);
lean_inc_ref(v_irDir_810_);
lean_dec_ref(v_config_806_);
v___x_811_ = ((lean_object*)(l_Lake_Module_setupFile___closed__0));
v___x_812_ = l_System_FilePath_normalize(v_buildDir_809_);
v___x_813_ = l_Lake_joinRelative(v_dir_808_, v___x_812_);
v___x_814_ = l_System_FilePath_normalize(v_irDir_810_);
v___x_815_ = l_Lake_joinRelative(v___x_813_, v___x_814_);
v___x_816_ = l_Lean_modToFilePath(v___x_815_, v_name_807_, v___x_811_);
lean_dec_ref(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_irSetupFile(lean_object* v_self_818_){
_start:
{
lean_object* v_lib_819_; lean_object* v_pkg_820_; lean_object* v_config_821_; lean_object* v_name_822_; lean_object* v_dir_823_; lean_object* v_buildDir_824_; lean_object* v_irDir_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_lib_819_ = lean_ctor_get(v_self_818_, 0);
v_pkg_820_ = lean_ctor_get(v_lib_819_, 0);
lean_inc_ref(v_pkg_820_);
v_config_821_ = lean_ctor_get(v_pkg_820_, 6);
lean_inc_ref(v_config_821_);
v_name_822_ = lean_ctor_get(v_self_818_, 1);
lean_inc(v_name_822_);
lean_dec_ref(v_self_818_);
v_dir_823_ = lean_ctor_get(v_pkg_820_, 4);
lean_inc_ref(v_dir_823_);
lean_dec_ref(v_pkg_820_);
v_buildDir_824_ = lean_ctor_get(v_config_821_, 5);
lean_inc_ref(v_buildDir_824_);
v_irDir_825_ = lean_ctor_get(v_config_821_, 9);
lean_inc_ref(v_irDir_825_);
lean_dec_ref(v_config_821_);
v___x_826_ = ((lean_object*)(l_Lake_Module_irSetupFile___closed__0));
v___x_827_ = l_System_FilePath_normalize(v_buildDir_824_);
v___x_828_ = l_Lake_joinRelative(v_dir_823_, v___x_827_);
v___x_829_ = l_System_FilePath_normalize(v_irDir_825_);
v___x_830_ = l_Lake_joinRelative(v___x_828_, v___x_829_);
v___x_831_ = l_Lean_modToFilePath(v___x_830_, v_name_822_, v___x_826_);
lean_dec_ref(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_cFile(lean_object* v_self_833_){
_start:
{
lean_object* v_lib_834_; lean_object* v_pkg_835_; lean_object* v_config_836_; lean_object* v_name_837_; lean_object* v_dir_838_; lean_object* v_buildDir_839_; lean_object* v_irDir_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_lib_834_ = lean_ctor_get(v_self_833_, 0);
v_pkg_835_ = lean_ctor_get(v_lib_834_, 0);
lean_inc_ref(v_pkg_835_);
v_config_836_ = lean_ctor_get(v_pkg_835_, 6);
lean_inc_ref(v_config_836_);
v_name_837_ = lean_ctor_get(v_self_833_, 1);
lean_inc(v_name_837_);
lean_dec_ref(v_self_833_);
v_dir_838_ = lean_ctor_get(v_pkg_835_, 4);
lean_inc_ref(v_dir_838_);
lean_dec_ref(v_pkg_835_);
v_buildDir_839_ = lean_ctor_get(v_config_836_, 5);
lean_inc_ref(v_buildDir_839_);
v_irDir_840_ = lean_ctor_get(v_config_836_, 9);
lean_inc_ref(v_irDir_840_);
lean_dec_ref(v_config_836_);
v___x_841_ = ((lean_object*)(l_Lake_Module_cFile___closed__0));
v___x_842_ = l_System_FilePath_normalize(v_buildDir_839_);
v___x_843_ = l_Lake_joinRelative(v_dir_838_, v___x_842_);
v___x_844_ = l_System_FilePath_normalize(v_irDir_840_);
v___x_845_ = l_Lake_joinRelative(v___x_843_, v___x_844_);
v___x_846_ = l_Lean_modToFilePath(v___x_845_, v_name_837_, v___x_841_);
lean_dec_ref(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coExportFile(lean_object* v_self_848_){
_start:
{
lean_object* v_lib_849_; lean_object* v_pkg_850_; lean_object* v_config_851_; lean_object* v_name_852_; lean_object* v_dir_853_; lean_object* v_buildDir_854_; lean_object* v_irDir_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_lib_849_ = lean_ctor_get(v_self_848_, 0);
v_pkg_850_ = lean_ctor_get(v_lib_849_, 0);
lean_inc_ref(v_pkg_850_);
v_config_851_ = lean_ctor_get(v_pkg_850_, 6);
lean_inc_ref(v_config_851_);
v_name_852_ = lean_ctor_get(v_self_848_, 1);
lean_inc(v_name_852_);
lean_dec_ref(v_self_848_);
v_dir_853_ = lean_ctor_get(v_pkg_850_, 4);
lean_inc_ref(v_dir_853_);
lean_dec_ref(v_pkg_850_);
v_buildDir_854_ = lean_ctor_get(v_config_851_, 5);
lean_inc_ref(v_buildDir_854_);
v_irDir_855_ = lean_ctor_get(v_config_851_, 9);
lean_inc_ref(v_irDir_855_);
lean_dec_ref(v_config_851_);
v___x_856_ = ((lean_object*)(l_Lake_Module_coExportFile___closed__0));
v___x_857_ = l_System_FilePath_normalize(v_buildDir_854_);
v___x_858_ = l_Lake_joinRelative(v_dir_853_, v___x_857_);
v___x_859_ = l_System_FilePath_normalize(v_irDir_855_);
v___x_860_ = l_Lake_joinRelative(v___x_858_, v___x_859_);
v___x_861_ = l_Lean_modToFilePath(v___x_860_, v_name_852_, v___x_856_);
lean_dec_ref(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFile(lean_object* v_self_863_){
_start:
{
lean_object* v_lib_864_; lean_object* v_pkg_865_; lean_object* v_config_866_; lean_object* v_name_867_; lean_object* v_dir_868_; lean_object* v_buildDir_869_; lean_object* v_irDir_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_lib_864_ = lean_ctor_get(v_self_863_, 0);
v_pkg_865_ = lean_ctor_get(v_lib_864_, 0);
lean_inc_ref(v_pkg_865_);
v_config_866_ = lean_ctor_get(v_pkg_865_, 6);
lean_inc_ref(v_config_866_);
v_name_867_ = lean_ctor_get(v_self_863_, 1);
lean_inc(v_name_867_);
lean_dec_ref(v_self_863_);
v_dir_868_ = lean_ctor_get(v_pkg_865_, 4);
lean_inc_ref(v_dir_868_);
lean_dec_ref(v_pkg_865_);
v_buildDir_869_ = lean_ctor_get(v_config_866_, 5);
lean_inc_ref(v_buildDir_869_);
v_irDir_870_ = lean_ctor_get(v_config_866_, 9);
lean_inc_ref(v_irDir_870_);
lean_dec_ref(v_config_866_);
v___x_871_ = ((lean_object*)(l_Lake_Module_coNoExportFile___closed__0));
v___x_872_ = l_System_FilePath_normalize(v_buildDir_869_);
v___x_873_ = l_Lake_joinRelative(v_dir_868_, v___x_872_);
v___x_874_ = l_System_FilePath_normalize(v_irDir_870_);
v___x_875_ = l_Lake_joinRelative(v___x_873_, v___x_874_);
v___x_876_ = l_Lean_modToFilePath(v___x_875_, v_name_867_, v___x_871_);
lean_dec_ref(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile(lean_object* v_self_878_){
_start:
{
lean_object* v_lib_879_; lean_object* v_pkg_880_; lean_object* v_config_881_; lean_object* v_name_882_; lean_object* v_dir_883_; lean_object* v_buildDir_884_; lean_object* v_irDir_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_lib_879_ = lean_ctor_get(v_self_878_, 0);
v_pkg_880_ = lean_ctor_get(v_lib_879_, 0);
lean_inc_ref(v_pkg_880_);
v_config_881_ = lean_ctor_get(v_pkg_880_, 6);
lean_inc_ref(v_config_881_);
v_name_882_ = lean_ctor_get(v_self_878_, 1);
lean_inc(v_name_882_);
lean_dec_ref(v_self_878_);
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
return v___x_891_;
}
}
static uint8_t _init_l_Lake_Module_bcFile_x3f___closed__0(void){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_box(0);
v___x_893_ = lean_internal_has_llvm_backend(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcFile_x3f(lean_object* v_self_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = lean_uint8_once(&l_Lake_Module_bcFile_x3f___closed__0, &l_Lake_Module_bcFile_x3f___closed__0_once, _init_l_Lake_Module_bcFile_x3f___closed__0);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_self_894_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
else
{
lean_object* v_lib_897_; lean_object* v_pkg_898_; lean_object* v_config_899_; lean_object* v_name_900_; lean_object* v_dir_901_; lean_object* v_buildDir_902_; lean_object* v_irDir_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_lib_897_ = lean_ctor_get(v_self_894_, 0);
v_pkg_898_ = lean_ctor_get(v_lib_897_, 0);
lean_inc_ref(v_pkg_898_);
v_config_899_ = lean_ctor_get(v_pkg_898_, 6);
lean_inc_ref(v_config_899_);
v_name_900_ = lean_ctor_get(v_self_894_, 1);
lean_inc(v_name_900_);
lean_dec_ref(v_self_894_);
v_dir_901_ = lean_ctor_get(v_pkg_898_, 4);
lean_inc_ref(v_dir_901_);
lean_dec_ref(v_pkg_898_);
v_buildDir_902_ = lean_ctor_get(v_config_899_, 5);
lean_inc_ref(v_buildDir_902_);
v_irDir_903_ = lean_ctor_get(v_config_899_, 9);
lean_inc_ref(v_irDir_903_);
lean_dec_ref(v_config_899_);
v___x_904_ = ((lean_object*)(l_Lake_Module_bcFile___closed__0));
v___x_905_ = l_System_FilePath_normalize(v_buildDir_902_);
v___x_906_ = l_Lake_joinRelative(v_dir_901_, v___x_905_);
v___x_907_ = l_System_FilePath_normalize(v_irDir_903_);
v___x_908_ = l_Lake_joinRelative(v___x_906_, v___x_907_);
v___x_909_ = l_Lean_modToFilePath(v___x_908_, v_name_900_, v___x_904_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_bcoFile(lean_object* v_self_912_){
_start:
{
lean_object* v_lib_913_; lean_object* v_pkg_914_; lean_object* v_config_915_; lean_object* v_name_916_; lean_object* v_dir_917_; lean_object* v_buildDir_918_; lean_object* v_irDir_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_lib_913_ = lean_ctor_get(v_self_912_, 0);
v_pkg_914_ = lean_ctor_get(v_lib_913_, 0);
lean_inc_ref(v_pkg_914_);
v_config_915_ = lean_ctor_get(v_pkg_914_, 6);
lean_inc_ref(v_config_915_);
v_name_916_ = lean_ctor_get(v_self_912_, 1);
lean_inc(v_name_916_);
lean_dec_ref(v_self_912_);
v_dir_917_ = lean_ctor_get(v_pkg_914_, 4);
lean_inc_ref(v_dir_917_);
lean_dec_ref(v_pkg_914_);
v_buildDir_918_ = lean_ctor_get(v_config_915_, 5);
lean_inc_ref(v_buildDir_918_);
v_irDir_919_ = lean_ctor_get(v_config_915_, 9);
lean_inc_ref(v_irDir_919_);
lean_dec_ref(v_config_915_);
v___x_920_ = ((lean_object*)(l_Lake_Module_bcoFile___closed__0));
v___x_921_ = l_System_FilePath_normalize(v_buildDir_918_);
v___x_922_ = l_Lake_joinRelative(v_dir_917_, v___x_921_);
v___x_923_ = l_System_FilePath_normalize(v_irDir_919_);
v___x_924_ = l_Lake_joinRelative(v___x_922_, v___x_923_);
v___x_925_ = l_Lean_modToFilePath(v___x_924_, v_name_916_, v___x_920_);
lean_dec_ref(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_ltarFile(lean_object* v_self_927_){
_start:
{
lean_object* v_lib_928_; lean_object* v_pkg_929_; lean_object* v_config_930_; lean_object* v_name_931_; lean_object* v_dir_932_; lean_object* v_buildDir_933_; lean_object* v_irDir_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_lib_928_ = lean_ctor_get(v_self_927_, 0);
v_pkg_929_ = lean_ctor_get(v_lib_928_, 0);
lean_inc_ref(v_pkg_929_);
v_config_930_ = lean_ctor_get(v_pkg_929_, 6);
lean_inc_ref(v_config_930_);
v_name_931_ = lean_ctor_get(v_self_927_, 1);
lean_inc(v_name_931_);
lean_dec_ref(v_self_927_);
v_dir_932_ = lean_ctor_get(v_pkg_929_, 4);
lean_inc_ref(v_dir_932_);
lean_dec_ref(v_pkg_929_);
v_buildDir_933_ = lean_ctor_get(v_config_930_, 5);
lean_inc_ref(v_buildDir_933_);
v_irDir_934_ = lean_ctor_get(v_config_930_, 9);
lean_inc_ref(v_irDir_934_);
lean_dec_ref(v_config_930_);
v___x_935_ = ((lean_object*)(l_Lake_Module_ltarFile___closed__0));
v___x_936_ = l_System_FilePath_normalize(v_buildDir_933_);
v___x_937_ = l_Lake_joinRelative(v_dir_932_, v___x_936_);
v___x_938_ = l_System_FilePath_normalize(v_irDir_934_);
v___x_939_ = l_Lake_joinRelative(v___x_937_, v___x_938_);
v___x_940_ = l_Lean_modToFilePath(v___x_939_, v_name_931_, v___x_935_);
lean_dec_ref(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibName(lean_object* v_self_943_){
_start:
{
lean_object* v_lib_944_; lean_object* v_name_945_; lean_object* v_pkg_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_lib_944_ = lean_ctor_get(v_self_943_, 0);
lean_inc_ref(v_lib_944_);
v_name_945_ = lean_ctor_get(v_self_943_, 1);
lean_inc(v_name_945_);
lean_dec_ref(v_self_943_);
v_pkg_946_ = lean_ctor_get(v_lib_944_, 0);
lean_inc_ref(v_pkg_946_);
lean_dec_ref(v_lib_944_);
v___x_947_ = l_Lake_Package_id_x3f(v_pkg_946_);
v___x_948_ = l_Lean_mkModuleInitializationStem(v_name_945_, v___x_947_);
lean_dec(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibFile(lean_object* v_self_950_){
_start:
{
lean_object* v_lib_951_; lean_object* v_pkg_952_; lean_object* v_config_953_; lean_object* v_name_954_; lean_object* v_dir_955_; lean_object* v_buildDir_956_; lean_object* v_leanLibDir_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_lib_951_ = lean_ctor_get(v_self_950_, 0);
v_pkg_952_ = lean_ctor_get(v_lib_951_, 0);
lean_inc_ref(v_pkg_952_);
v_config_953_ = lean_ctor_get(v_pkg_952_, 6);
v_name_954_ = lean_ctor_get(v_self_950_, 1);
lean_inc(v_name_954_);
lean_dec_ref(v_self_950_);
v_dir_955_ = lean_ctor_get(v_pkg_952_, 4);
v_buildDir_956_ = lean_ctor_get(v_config_953_, 5);
v_leanLibDir_957_ = lean_ctor_get(v_config_953_, 6);
lean_inc_ref(v_buildDir_956_);
v___x_958_ = l_System_FilePath_normalize(v_buildDir_956_);
lean_inc_ref(v_dir_955_);
v___x_959_ = l_Lake_joinRelative(v_dir_955_, v___x_958_);
lean_inc_ref(v_leanLibDir_957_);
v___x_960_ = l_System_FilePath_normalize(v_leanLibDir_957_);
v___x_961_ = l_Lake_joinRelative(v___x_959_, v___x_960_);
v___x_962_ = l_Lake_Package_id_x3f(v_pkg_952_);
v___x_963_ = l_Lean_mkModuleInitializationStem(v_name_954_, v___x_962_);
lean_dec(v___x_962_);
v___x_964_ = ((lean_object*)(l_Lake_Module_dynlibFile___closed__0));
v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
v___x_966_ = l_Lake_sharedLibExt;
v___x_967_ = lean_string_append(v___x_965_, v___x_966_);
v___x_968_ = l_Lake_joinRelative(v___x_961_, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions(lean_object* v_self_969_){
_start:
{
lean_object* v_lib_970_; lean_object* v_pkg_971_; lean_object* v_config_972_; lean_object* v_toLeanConfig_973_; lean_object* v_config_974_; lean_object* v_toLeanConfig_975_; uint8_t v_buildType_976_; lean_object* v_leanOptions_977_; lean_object* v_moreServerOptions_978_; uint8_t v_buildType_979_; lean_object* v_leanOptions_980_; lean_object* v_moreServerOptions_981_; lean_object* v___x_982_; uint8_t v___y_984_; uint8_t v___x_992_; 
v_lib_970_ = lean_ctor_get(v_self_969_, 0);
v_pkg_971_ = lean_ctor_get(v_lib_970_, 0);
v_config_972_ = lean_ctor_get(v_pkg_971_, 6);
v_toLeanConfig_973_ = lean_ctor_get(v_config_972_, 1);
v_config_974_ = lean_ctor_get(v_lib_970_, 2);
v_toLeanConfig_975_ = lean_ctor_get(v_config_974_, 0);
v_buildType_976_ = lean_ctor_get_uint8(v_toLeanConfig_973_, sizeof(void*)*13);
v_leanOptions_977_ = lean_ctor_get(v_toLeanConfig_973_, 0);
v_moreServerOptions_978_ = lean_ctor_get(v_toLeanConfig_973_, 4);
v_buildType_979_ = lean_ctor_get_uint8(v_toLeanConfig_975_, sizeof(void*)*13);
v_leanOptions_980_ = lean_ctor_get(v_toLeanConfig_975_, 0);
v_moreServerOptions_981_ = lean_ctor_get(v_toLeanConfig_975_, 4);
v___x_982_ = lean_box(1);
v___x_992_ = l_Lake_instOrdBuildType_ord(v_buildType_976_, v_buildType_979_);
if (v___x_992_ == 2)
{
v___y_984_ = v_buildType_979_;
goto v___jp_983_;
}
else
{
v___y_984_ = v_buildType_976_;
goto v___jp_983_;
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_985_ = l_Lake_BuildType_leanOptions(v___y_984_);
v___x_986_ = l_Lean_LeanOptions_append(v___x_982_, v___x_985_);
v___x_987_ = l_Lean_LeanOptions_ofArray(v_leanOptions_977_);
v___x_988_ = l_Lean_LeanOptions_appendArray(v___x_987_, v_moreServerOptions_978_);
v___x_989_ = l_Lean_LeanOptions_append(v___x_986_, v___x_988_);
v___x_990_ = l_Lean_LeanOptions_appendArray(v___x_989_, v_leanOptions_980_);
v___x_991_ = l_Lean_LeanOptions_appendArray(v___x_990_, v_moreServerOptions_981_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_serverOptions___boxed(lean_object* v_self_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lake_Module_serverOptions(v_self_993_);
lean_dec_ref(v_self_993_);
return v_res_994_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_buildType(lean_object* v_self_995_){
_start:
{
lean_object* v_lib_996_; lean_object* v_pkg_997_; lean_object* v_config_998_; lean_object* v_toLeanConfig_999_; lean_object* v_config_1000_; lean_object* v_toLeanConfig_1001_; uint8_t v_buildType_1002_; uint8_t v_buildType_1003_; uint8_t v___x_1004_; 
v_lib_996_ = lean_ctor_get(v_self_995_, 0);
v_pkg_997_ = lean_ctor_get(v_lib_996_, 0);
v_config_998_ = lean_ctor_get(v_pkg_997_, 6);
v_toLeanConfig_999_ = lean_ctor_get(v_config_998_, 1);
v_config_1000_ = lean_ctor_get(v_lib_996_, 2);
v_toLeanConfig_1001_ = lean_ctor_get(v_config_1000_, 0);
v_buildType_1002_ = lean_ctor_get_uint8(v_toLeanConfig_999_, sizeof(void*)*13);
v_buildType_1003_ = lean_ctor_get_uint8(v_toLeanConfig_1001_, sizeof(void*)*13);
v___x_1004_ = l_Lake_instOrdBuildType_ord(v_buildType_1002_, v_buildType_1003_);
if (v___x_1004_ == 2)
{
return v_buildType_1003_;
}
else
{
return v_buildType_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_buildType___boxed(lean_object* v_self_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lake_Module_buildType(v_self_1005_);
lean_dec_ref(v_self_1005_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_backend(lean_object* v_self_1008_){
_start:
{
lean_object* v_lib_1009_; lean_object* v_config_1010_; lean_object* v_toLeanConfig_1011_; lean_object* v_pkg_1012_; lean_object* v_config_1013_; lean_object* v_toLeanConfig_1014_; uint8_t v_backend_1015_; uint8_t v_backend_1016_; uint8_t v___x_1017_; 
v_lib_1009_ = lean_ctor_get(v_self_1008_, 0);
v_config_1010_ = lean_ctor_get(v_lib_1009_, 2);
v_toLeanConfig_1011_ = lean_ctor_get(v_config_1010_, 0);
v_pkg_1012_ = lean_ctor_get(v_lib_1009_, 0);
v_config_1013_ = lean_ctor_get(v_pkg_1012_, 6);
v_toLeanConfig_1014_ = lean_ctor_get(v_config_1013_, 1);
v_backend_1015_ = lean_ctor_get_uint8(v_toLeanConfig_1011_, sizeof(void*)*13 + 1);
v_backend_1016_ = lean_ctor_get_uint8(v_toLeanConfig_1014_, sizeof(void*)*13 + 1);
v___x_1017_ = l_Lake_Backend_orPreferLeft(v_backend_1015_, v_backend_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_backend___boxed(lean_object* v_self_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lake_Module_backend(v_self_1018_);
lean_dec_ref(v_self_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowImportAll(lean_object* v_self_1021_){
_start:
{
lean_object* v_lib_1022_; lean_object* v_config_1023_; uint8_t v_allowImportAll_1024_; 
v_lib_1022_ = lean_ctor_get(v_self_1021_, 0);
v_config_1023_ = lean_ctor_get(v_lib_1022_, 2);
v_allowImportAll_1024_ = lean_ctor_get_uint8(v_config_1023_, sizeof(void*)*9 + 3);
if (v_allowImportAll_1024_ == 0)
{
lean_object* v_pkg_1025_; lean_object* v_config_1026_; uint8_t v_allowImportAll_1027_; 
v_pkg_1025_ = lean_ctor_get(v_lib_1022_, 0);
v_config_1026_ = lean_ctor_get(v_pkg_1025_, 6);
v_allowImportAll_1027_ = lean_ctor_get_uint8(v_config_1026_, sizeof(void*)*28 + 5);
return v_allowImportAll_1027_;
}
else
{
return v_allowImportAll_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowImportAll___boxed(lean_object* v_self_1028_){
_start:
{
uint8_t v_res_1029_; lean_object* v_r_1030_; 
v_res_1029_ = l_Lake_Module_allowImportAll(v_self_1028_);
lean_dec_ref(v_self_1028_);
v_r_1030_ = lean_box(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_requiresModuleSystem(lean_object* v_self_1031_){
_start:
{
lean_object* v_lib_1032_; lean_object* v_config_1033_; lean_object* v_toLeanConfig_1034_; uint8_t v_requiresModuleSystem_1035_; 
v_lib_1032_ = lean_ctor_get(v_self_1031_, 0);
v_config_1033_ = lean_ctor_get(v_lib_1032_, 2);
v_toLeanConfig_1034_ = lean_ctor_get(v_config_1033_, 0);
v_requiresModuleSystem_1035_ = lean_ctor_get_uint8(v_toLeanConfig_1034_, sizeof(void*)*13 + 3);
if (v_requiresModuleSystem_1035_ == 0)
{
lean_object* v_pkg_1036_; lean_object* v_config_1037_; lean_object* v_toLeanConfig_1038_; uint8_t v_requiresModuleSystem_1039_; 
v_pkg_1036_ = lean_ctor_get(v_lib_1032_, 0);
v_config_1037_ = lean_ctor_get(v_pkg_1036_, 6);
v_toLeanConfig_1038_ = lean_ctor_get(v_config_1037_, 1);
v_requiresModuleSystem_1039_ = lean_ctor_get_uint8(v_toLeanConfig_1038_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_1039_;
}
else
{
return v_requiresModuleSystem_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_requiresModuleSystem___boxed(lean_object* v_self_1040_){
_start:
{
uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_res_1041_ = l_Lake_Module_requiresModuleSystem(v_self_1040_);
lean_dec_ref(v_self_1040_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_allowNonModules(lean_object* v_self_1043_){
_start:
{
lean_object* v_lib_1044_; lean_object* v_config_1045_; lean_object* v_toLeanConfig_1046_; uint8_t v_allowNonModules_1047_; 
v_lib_1044_ = lean_ctor_get(v_self_1043_, 0);
v_config_1045_ = lean_ctor_get(v_lib_1044_, 2);
v_toLeanConfig_1046_ = lean_ctor_get(v_config_1045_, 0);
v_allowNonModules_1047_ = lean_ctor_get_uint8(v_toLeanConfig_1046_, sizeof(void*)*13 + 4);
if (v_allowNonModules_1047_ == 0)
{
lean_object* v_pkg_1048_; lean_object* v_config_1049_; lean_object* v_toLeanConfig_1050_; uint8_t v_allowNonModules_1051_; 
v_pkg_1048_ = lean_ctor_get(v_lib_1044_, 0);
v_config_1049_ = lean_ctor_get(v_pkg_1048_, 6);
v_toLeanConfig_1050_ = lean_ctor_get(v_config_1049_, 1);
v_allowNonModules_1051_ = lean_ctor_get_uint8(v_toLeanConfig_1050_, sizeof(void*)*13 + 4);
return v_allowNonModules_1051_;
}
else
{
return v_allowNonModules_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_allowNonModules___boxed(lean_object* v_self_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l_Lake_Module_allowNonModules(v_self_1052_);
lean_dec_ref(v_self_1052_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_dynlibs(lean_object* v_self_1055_){
_start:
{
lean_object* v_lib_1056_; lean_object* v_pkg_1057_; lean_object* v_config_1058_; lean_object* v_toLeanConfig_1059_; lean_object* v_config_1060_; lean_object* v_toLeanConfig_1061_; lean_object* v_dynlibs_1062_; lean_object* v_dynlibs_1063_; lean_object* v___x_1064_; 
v_lib_1056_ = lean_ctor_get(v_self_1055_, 0);
lean_inc_ref(v_lib_1056_);
lean_dec_ref(v_self_1055_);
v_pkg_1057_ = lean_ctor_get(v_lib_1056_, 0);
v_config_1058_ = lean_ctor_get(v_pkg_1057_, 6);
v_toLeanConfig_1059_ = lean_ctor_get(v_config_1058_, 1);
lean_inc_ref(v_toLeanConfig_1059_);
v_config_1060_ = lean_ctor_get(v_lib_1056_, 2);
lean_inc(v_config_1060_);
lean_dec_ref(v_lib_1056_);
v_toLeanConfig_1061_ = lean_ctor_get(v_config_1060_, 0);
lean_inc_ref(v_toLeanConfig_1061_);
lean_dec(v_config_1060_);
v_dynlibs_1062_ = lean_ctor_get(v_toLeanConfig_1059_, 11);
lean_inc_ref(v_dynlibs_1062_);
lean_dec_ref(v_toLeanConfig_1059_);
v_dynlibs_1063_ = lean_ctor_get(v_toLeanConfig_1061_, 11);
lean_inc_ref(v_dynlibs_1063_);
lean_dec_ref(v_toLeanConfig_1061_);
v___x_1064_ = l_Array_append___redArg(v_dynlibs_1062_, v_dynlibs_1063_);
lean_dec_ref(v_dynlibs_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_plugins(lean_object* v_self_1065_){
_start:
{
lean_object* v_lib_1066_; lean_object* v_pkg_1067_; lean_object* v_config_1068_; lean_object* v_toLeanConfig_1069_; lean_object* v_config_1070_; lean_object* v_toLeanConfig_1071_; lean_object* v_plugins_1072_; lean_object* v_plugins_1073_; lean_object* v___x_1074_; 
v_lib_1066_ = lean_ctor_get(v_self_1065_, 0);
lean_inc_ref(v_lib_1066_);
lean_dec_ref(v_self_1065_);
v_pkg_1067_ = lean_ctor_get(v_lib_1066_, 0);
v_config_1068_ = lean_ctor_get(v_pkg_1067_, 6);
v_toLeanConfig_1069_ = lean_ctor_get(v_config_1068_, 1);
lean_inc_ref(v_toLeanConfig_1069_);
v_config_1070_ = lean_ctor_get(v_lib_1066_, 2);
lean_inc(v_config_1070_);
lean_dec_ref(v_lib_1066_);
v_toLeanConfig_1071_ = lean_ctor_get(v_config_1070_, 0);
lean_inc_ref(v_toLeanConfig_1071_);
lean_dec(v_config_1070_);
v_plugins_1072_ = lean_ctor_get(v_toLeanConfig_1069_, 12);
lean_inc_ref(v_plugins_1072_);
lean_dec_ref(v_toLeanConfig_1069_);
v_plugins_1073_ = lean_ctor_get(v_toLeanConfig_1071_, 12);
lean_inc_ref(v_plugins_1073_);
lean_dec_ref(v_toLeanConfig_1071_);
v___x_1074_ = l_Array_append___redArg(v_plugins_1072_, v_plugins_1073_);
lean_dec_ref(v_plugins_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions(lean_object* v_self_1075_){
_start:
{
lean_object* v_lib_1076_; lean_object* v_pkg_1077_; lean_object* v_config_1078_; lean_object* v_toLeanConfig_1079_; lean_object* v_config_1080_; lean_object* v_toLeanConfig_1081_; uint8_t v_buildType_1082_; lean_object* v_leanOptions_1083_; uint8_t v_buildType_1084_; lean_object* v_leanOptions_1085_; uint8_t v___y_1087_; uint8_t v___x_1092_; 
v_lib_1076_ = lean_ctor_get(v_self_1075_, 0);
v_pkg_1077_ = lean_ctor_get(v_lib_1076_, 0);
v_config_1078_ = lean_ctor_get(v_pkg_1077_, 6);
v_toLeanConfig_1079_ = lean_ctor_get(v_config_1078_, 1);
v_config_1080_ = lean_ctor_get(v_lib_1076_, 2);
v_toLeanConfig_1081_ = lean_ctor_get(v_config_1080_, 0);
v_buildType_1082_ = lean_ctor_get_uint8(v_toLeanConfig_1079_, sizeof(void*)*13);
v_leanOptions_1083_ = lean_ctor_get(v_toLeanConfig_1079_, 0);
v_buildType_1084_ = lean_ctor_get_uint8(v_toLeanConfig_1081_, sizeof(void*)*13);
v_leanOptions_1085_ = lean_ctor_get(v_toLeanConfig_1081_, 0);
v___x_1092_ = l_Lake_instOrdBuildType_ord(v_buildType_1082_, v_buildType_1084_);
if (v___x_1092_ == 2)
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
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = l_Lake_BuildType_leanOptions(v___y_1087_);
v___x_1089_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1083_);
v___x_1090_ = l_Lean_LeanOptions_append(v___x_1088_, v___x_1089_);
v___x_1091_ = l_Lean_LeanOptions_appendArray(v___x_1090_, v_leanOptions_1085_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanOptions___boxed(lean_object* v_self_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lake_Module_leanOptions(v_self_1093_);
lean_dec_ref(v_self_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_postponeCompile(lean_object* v_self_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v_lib_1097_; lean_object* v_pkg_1098_; lean_object* v_config_1099_; lean_object* v_toLeanConfig_1100_; lean_object* v_config_1101_; lean_object* v_toLeanConfig_1102_; uint8_t v_buildType_1103_; lean_object* v_leanOptions_1104_; uint8_t v_buildType_1105_; lean_object* v_leanOptions_1106_; uint8_t v___y_1108_; uint8_t v___x_1117_; 
v___x_1096_ = l_Lean_KVMap_instValueBool;
v_lib_1097_ = lean_ctor_get(v_self_1095_, 0);
v_pkg_1098_ = lean_ctor_get(v_lib_1097_, 0);
v_config_1099_ = lean_ctor_get(v_pkg_1098_, 6);
v_toLeanConfig_1100_ = lean_ctor_get(v_config_1099_, 1);
v_config_1101_ = lean_ctor_get(v_lib_1097_, 2);
v_toLeanConfig_1102_ = lean_ctor_get(v_config_1101_, 0);
v_buildType_1103_ = lean_ctor_get_uint8(v_toLeanConfig_1100_, sizeof(void*)*13);
v_leanOptions_1104_ = lean_ctor_get(v_toLeanConfig_1100_, 0);
v_buildType_1105_ = lean_ctor_get_uint8(v_toLeanConfig_1102_, sizeof(void*)*13);
v_leanOptions_1106_ = lean_ctor_get(v_toLeanConfig_1102_, 0);
v___x_1117_ = l_Lake_instOrdBuildType_ord(v_buildType_1103_, v_buildType_1105_);
if (v___x_1117_ == 2)
{
v___y_1108_ = v_buildType_1105_;
goto v___jp_1107_;
}
else
{
v___y_1108_ = v_buildType_1103_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1109_ = l_Lake_BuildType_leanOptions(v___y_1108_);
v___x_1110_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1104_);
v___x_1111_ = l_Lean_LeanOptions_append(v___x_1109_, v___x_1110_);
v___x_1112_ = l_Lean_LeanOptions_appendArray(v___x_1111_, v_leanOptions_1106_);
v___x_1113_ = l_Lean_LeanOptions_toOptions(v___x_1112_);
v___x_1114_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1115_ = l_Lean_Option_get___redArg(v___x_1096_, v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1113_);
v___x_1116_ = lean_unbox(v___x_1115_);
lean_dec(v___x_1115_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_postponeCompile___boxed(lean_object* v_self_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Lake_Module_postponeCompile(v_self_1118_);
lean_dec_ref(v_self_1118_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
static lean_object* _init_l_Lake_Module_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs(lean_object* v_self_1122_){
_start:
{
lean_object* v_lib_1123_; lean_object* v_pkg_1124_; lean_object* v_config_1125_; lean_object* v_toLeanConfig_1126_; lean_object* v_config_1127_; lean_object* v_toLeanConfig_1128_; lean_object* v_moreLeanArgs_1129_; lean_object* v_moreLeanArgs_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_lib_1123_ = lean_ctor_get(v_self_1122_, 0);
v_pkg_1124_ = lean_ctor_get(v_lib_1123_, 0);
v_config_1125_ = lean_ctor_get(v_pkg_1124_, 6);
v_toLeanConfig_1126_ = lean_ctor_get(v_config_1125_, 1);
v_config_1127_ = lean_ctor_get(v_lib_1123_, 2);
v_toLeanConfig_1128_ = lean_ctor_get(v_config_1127_, 0);
v_moreLeanArgs_1129_ = lean_ctor_get(v_toLeanConfig_1126_, 1);
v_moreLeanArgs_1130_ = lean_ctor_get(v_toLeanConfig_1128_, 1);
v___x_1131_ = lean_obj_once(&l_Lake_Module_leanArgs___closed__0, &l_Lake_Module_leanArgs___closed__0_once, _init_l_Lake_Module_leanArgs___closed__0);
v___x_1132_ = l_Array_append___redArg(v___x_1131_, v_moreLeanArgs_1129_);
v___x_1133_ = l_Array_append___redArg(v___x_1132_, v_moreLeanArgs_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanArgs___boxed(lean_object* v_self_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lake_Module_leanArgs(v_self_1134_);
lean_dec_ref(v_self_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeanArgs(lean_object* v_self_1136_){
_start:
{
lean_object* v_lib_1137_; lean_object* v_pkg_1138_; lean_object* v_config_1139_; lean_object* v_toLeanConfig_1140_; lean_object* v_config_1141_; lean_object* v_toLeanConfig_1142_; lean_object* v_weakLeanArgs_1143_; lean_object* v_weakLeanArgs_1144_; lean_object* v___x_1145_; 
v_lib_1137_ = lean_ctor_get(v_self_1136_, 0);
lean_inc_ref(v_lib_1137_);
lean_dec_ref(v_self_1136_);
v_pkg_1138_ = lean_ctor_get(v_lib_1137_, 0);
v_config_1139_ = lean_ctor_get(v_pkg_1138_, 6);
v_toLeanConfig_1140_ = lean_ctor_get(v_config_1139_, 1);
lean_inc_ref(v_toLeanConfig_1140_);
v_config_1141_ = lean_ctor_get(v_lib_1137_, 2);
lean_inc(v_config_1141_);
lean_dec_ref(v_lib_1137_);
v_toLeanConfig_1142_ = lean_ctor_get(v_config_1141_, 0);
lean_inc_ref(v_toLeanConfig_1142_);
lean_dec(v_config_1141_);
v_weakLeanArgs_1143_ = lean_ctor_get(v_toLeanConfig_1140_, 2);
lean_inc_ref(v_weakLeanArgs_1143_);
lean_dec_ref(v_toLeanConfig_1140_);
v_weakLeanArgs_1144_ = lean_ctor_get(v_toLeanConfig_1142_, 2);
lean_inc_ref(v_weakLeanArgs_1144_);
lean_dec_ref(v_toLeanConfig_1142_);
v___x_1145_ = l_Array_append___redArg(v_weakLeanArgs_1143_, v_weakLeanArgs_1144_);
lean_dec_ref(v_weakLeanArgs_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs(lean_object* v_self_1146_){
_start:
{
lean_object* v_lib_1147_; lean_object* v_pkg_1148_; lean_object* v_config_1149_; lean_object* v_toLeanConfig_1150_; lean_object* v_config_1151_; lean_object* v_toLeanConfig_1152_; uint8_t v_buildType_1153_; lean_object* v_moreLeancArgs_1154_; uint8_t v_buildType_1155_; lean_object* v_moreLeancArgs_1156_; uint8_t v___y_1158_; uint8_t v___x_1162_; 
v_lib_1147_ = lean_ctor_get(v_self_1146_, 0);
v_pkg_1148_ = lean_ctor_get(v_lib_1147_, 0);
v_config_1149_ = lean_ctor_get(v_pkg_1148_, 6);
v_toLeanConfig_1150_ = lean_ctor_get(v_config_1149_, 1);
v_config_1151_ = lean_ctor_get(v_lib_1147_, 2);
v_toLeanConfig_1152_ = lean_ctor_get(v_config_1151_, 0);
v_buildType_1153_ = lean_ctor_get_uint8(v_toLeanConfig_1150_, sizeof(void*)*13);
v_moreLeancArgs_1154_ = lean_ctor_get(v_toLeanConfig_1150_, 3);
v_buildType_1155_ = lean_ctor_get_uint8(v_toLeanConfig_1152_, sizeof(void*)*13);
v_moreLeancArgs_1156_ = lean_ctor_get(v_toLeanConfig_1152_, 3);
v___x_1162_ = l_Lake_instOrdBuildType_ord(v_buildType_1153_, v_buildType_1155_);
if (v___x_1162_ == 2)
{
v___y_1158_ = v_buildType_1155_;
goto v___jp_1157_;
}
else
{
v___y_1158_ = v_buildType_1153_;
goto v___jp_1157_;
}
v___jp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = l_Lake_BuildType_leancArgs(v___y_1158_);
v___x_1160_ = l_Array_append___redArg(v___x_1159_, v_moreLeancArgs_1154_);
v___x_1161_ = l_Array_append___redArg(v___x_1160_, v_moreLeancArgs_1156_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leancArgs___boxed(lean_object* v_self_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lake_Module_leancArgs(v_self_1163_);
lean_dec_ref(v_self_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLeancArgs(lean_object* v_self_1165_){
_start:
{
lean_object* v_lib_1166_; lean_object* v_pkg_1167_; lean_object* v_config_1168_; lean_object* v_toLeanConfig_1169_; lean_object* v_config_1170_; lean_object* v_toLeanConfig_1171_; lean_object* v_weakLeancArgs_1172_; lean_object* v_weakLeancArgs_1173_; lean_object* v___x_1174_; 
v_lib_1166_ = lean_ctor_get(v_self_1165_, 0);
lean_inc_ref(v_lib_1166_);
lean_dec_ref(v_self_1165_);
v_pkg_1167_ = lean_ctor_get(v_lib_1166_, 0);
v_config_1168_ = lean_ctor_get(v_pkg_1167_, 6);
v_toLeanConfig_1169_ = lean_ctor_get(v_config_1168_, 1);
lean_inc_ref(v_toLeanConfig_1169_);
v_config_1170_ = lean_ctor_get(v_lib_1166_, 2);
lean_inc(v_config_1170_);
lean_dec_ref(v_lib_1166_);
v_toLeanConfig_1171_ = lean_ctor_get(v_config_1170_, 0);
lean_inc_ref(v_toLeanConfig_1171_);
lean_dec(v_config_1170_);
v_weakLeancArgs_1172_ = lean_ctor_get(v_toLeanConfig_1169_, 5);
lean_inc_ref(v_weakLeancArgs_1172_);
lean_dec_ref(v_toLeanConfig_1169_);
v_weakLeancArgs_1173_ = lean_ctor_get(v_toLeanConfig_1171_, 5);
lean_inc_ref(v_weakLeancArgs_1173_);
lean_dec_ref(v_toLeanConfig_1171_);
v___x_1174_ = l_Array_append___redArg(v_weakLeancArgs_1172_, v_weakLeancArgs_1173_);
lean_dec_ref(v_weakLeancArgs_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_linkArgs(lean_object* v_self_1175_){
_start:
{
lean_object* v_lib_1176_; lean_object* v_pkg_1177_; lean_object* v_config_1178_; lean_object* v_toLeanConfig_1179_; lean_object* v_config_1180_; lean_object* v_toLeanConfig_1181_; lean_object* v_moreLinkArgs_1182_; lean_object* v_moreLinkArgs_1183_; lean_object* v___x_1184_; 
v_lib_1176_ = lean_ctor_get(v_self_1175_, 0);
lean_inc_ref(v_lib_1176_);
lean_dec_ref(v_self_1175_);
v_pkg_1177_ = lean_ctor_get(v_lib_1176_, 0);
v_config_1178_ = lean_ctor_get(v_pkg_1177_, 6);
v_toLeanConfig_1179_ = lean_ctor_get(v_config_1178_, 1);
lean_inc_ref(v_toLeanConfig_1179_);
v_config_1180_ = lean_ctor_get(v_lib_1176_, 2);
lean_inc(v_config_1180_);
lean_dec_ref(v_lib_1176_);
v_toLeanConfig_1181_ = lean_ctor_get(v_config_1180_, 0);
lean_inc_ref(v_toLeanConfig_1181_);
lean_dec(v_config_1180_);
v_moreLinkArgs_1182_ = lean_ctor_get(v_toLeanConfig_1179_, 8);
lean_inc_ref(v_moreLinkArgs_1182_);
lean_dec_ref(v_toLeanConfig_1179_);
v_moreLinkArgs_1183_ = lean_ctor_get(v_toLeanConfig_1181_, 8);
lean_inc_ref(v_moreLinkArgs_1183_);
lean_dec_ref(v_toLeanConfig_1181_);
v___x_1184_ = l_Array_append___redArg(v_moreLinkArgs_1182_, v_moreLinkArgs_1183_);
lean_dec_ref(v_moreLinkArgs_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_weakLinkArgs(lean_object* v_self_1185_){
_start:
{
lean_object* v_lib_1186_; lean_object* v_pkg_1187_; lean_object* v_config_1188_; lean_object* v_toLeanConfig_1189_; lean_object* v_config_1190_; lean_object* v_toLeanConfig_1191_; lean_object* v_weakLinkArgs_1192_; lean_object* v_weakLinkArgs_1193_; lean_object* v___x_1194_; 
v_lib_1186_ = lean_ctor_get(v_self_1185_, 0);
lean_inc_ref(v_lib_1186_);
lean_dec_ref(v_self_1185_);
v_pkg_1187_ = lean_ctor_get(v_lib_1186_, 0);
v_config_1188_ = lean_ctor_get(v_pkg_1187_, 6);
v_toLeanConfig_1189_ = lean_ctor_get(v_config_1188_, 1);
lean_inc_ref(v_toLeanConfig_1189_);
v_config_1190_ = lean_ctor_get(v_lib_1186_, 2);
lean_inc(v_config_1190_);
lean_dec_ref(v_lib_1186_);
v_toLeanConfig_1191_ = lean_ctor_get(v_config_1190_, 0);
lean_inc_ref(v_toLeanConfig_1191_);
lean_dec(v_config_1190_);
v_weakLinkArgs_1192_ = lean_ctor_get(v_toLeanConfig_1189_, 9);
lean_inc_ref(v_weakLinkArgs_1192_);
lean_dec_ref(v_toLeanConfig_1189_);
v_weakLinkArgs_1193_ = lean_ctor_get(v_toLeanConfig_1191_, 9);
lean_inc_ref(v_weakLinkArgs_1193_);
lean_dec_ref(v_toLeanConfig_1191_);
v___x_1194_ = l_Array_append___redArg(v_weakLinkArgs_1192_, v_weakLinkArgs_1193_);
lean_dec_ref(v_weakLinkArgs_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_leanIncludeDir_x3f(lean_object* v_self_1196_){
_start:
{
lean_object* v_lib_1197_; lean_object* v_pkg_1198_; lean_object* v_config_1199_; uint8_t v_bootstrap_1200_; 
v_lib_1197_ = lean_ctor_get(v_self_1196_, 0);
lean_inc_ref(v_lib_1197_);
lean_dec_ref(v_self_1196_);
v_pkg_1198_ = lean_ctor_get(v_lib_1197_, 0);
lean_inc_ref(v_pkg_1198_);
lean_dec_ref(v_lib_1197_);
v_config_1199_ = lean_ctor_get(v_pkg_1198_, 6);
lean_inc_ref(v_config_1199_);
v_bootstrap_1200_ = lean_ctor_get_uint8(v_config_1199_, sizeof(void*)*28);
if (v_bootstrap_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v_config_1199_);
lean_dec_ref(v_pkg_1198_);
v___x_1201_ = lean_box(0);
return v___x_1201_;
}
else
{
lean_object* v_dir_1202_; lean_object* v_buildDir_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_dir_1202_ = lean_ctor_get(v_pkg_1198_, 4);
lean_inc_ref(v_dir_1202_);
lean_dec_ref(v_pkg_1198_);
v_buildDir_1203_ = lean_ctor_get(v_config_1199_, 5);
lean_inc_ref(v_buildDir_1203_);
lean_dec_ref(v_config_1199_);
v___x_1204_ = l_System_FilePath_normalize(v_buildDir_1203_);
v___x_1205_ = l_Lake_joinRelative(v_dir_1202_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lake_Module_leanIncludeDir_x3f___closed__0));
v___x_1207_ = l_Lake_joinRelative(v___x_1205_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent(lean_object* v_self_1209_){
_start:
{
lean_object* v_lib_1210_; lean_object* v_config_1211_; lean_object* v_toLeanConfig_1212_; lean_object* v_platformIndependent_1213_; 
v_lib_1210_ = lean_ctor_get(v_self_1209_, 0);
v_config_1211_ = lean_ctor_get(v_lib_1210_, 2);
v_toLeanConfig_1212_ = lean_ctor_get(v_config_1211_, 0);
v_platformIndependent_1213_ = lean_ctor_get(v_toLeanConfig_1212_, 10);
if (lean_obj_tag(v_platformIndependent_1213_) == 0)
{
lean_object* v_pkg_1214_; lean_object* v_config_1215_; lean_object* v_toLeanConfig_1216_; lean_object* v_platformIndependent_1217_; 
v_pkg_1214_ = lean_ctor_get(v_lib_1210_, 0);
v_config_1215_ = lean_ctor_get(v_pkg_1214_, 6);
v_toLeanConfig_1216_ = lean_ctor_get(v_config_1215_, 1);
v_platformIndependent_1217_ = lean_ctor_get(v_toLeanConfig_1216_, 10);
lean_inc(v_platformIndependent_1217_);
return v_platformIndependent_1217_;
}
else
{
lean_inc_ref(v_platformIndependent_1213_);
return v_platformIndependent_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_platformIndependent___boxed(lean_object* v_self_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lake_Module_platformIndependent(v_self_1218_);
lean_dec_ref(v_self_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompileImports(lean_object* v_self_1220_){
_start:
{
lean_object* v_lib_1221_; lean_object* v_pkg_1222_; lean_object* v_config_1223_; uint8_t v_precompileModules_1224_; 
v_lib_1221_ = lean_ctor_get(v_self_1220_, 0);
v_pkg_1222_ = lean_ctor_get(v_lib_1221_, 0);
v_config_1223_ = lean_ctor_get(v_pkg_1222_, 6);
v_precompileModules_1224_ = lean_ctor_get_uint8(v_config_1223_, sizeof(void*)*28 + 1);
if (v_precompileModules_1224_ == 0)
{
lean_object* v_config_1225_; uint8_t v_precompileModules_1226_; 
v_config_1225_ = lean_ctor_get(v_lib_1221_, 2);
v_precompileModules_1226_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*9 + 2);
if (v_precompileModules_1226_ == 0)
{
lean_object* v_toLeanConfig_1227_; uint8_t v_precompileImports_1228_; 
v_toLeanConfig_1227_ = lean_ctor_get(v_config_1223_, 1);
v_precompileImports_1228_ = lean_ctor_get_uint8(v_toLeanConfig_1227_, sizeof(void*)*13 + 2);
if (v_precompileImports_1228_ == 0)
{
lean_object* v_toLeanConfig_1229_; uint8_t v_precompileImports_1230_; 
v_toLeanConfig_1229_ = lean_ctor_get(v_config_1225_, 0);
v_precompileImports_1230_ = lean_ctor_get_uint8(v_toLeanConfig_1229_, sizeof(void*)*13 + 2);
return v_precompileImports_1230_;
}
else
{
return v_precompileImports_1228_;
}
}
else
{
return v_precompileModules_1226_;
}
}
else
{
return v_precompileModules_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompileImports___boxed(lean_object* v_self_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Lake_Module_shouldPrecompileImports(v_self_1231_);
lean_dec_ref(v_self_1231_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l_Lake_Module_shouldPrecompile(lean_object* v_self_1234_){
_start:
{
lean_object* v_lib_1235_; lean_object* v_pkg_1236_; lean_object* v_config_1237_; uint8_t v_precompileModules_1238_; 
v_lib_1235_ = lean_ctor_get(v_self_1234_, 0);
v_pkg_1236_ = lean_ctor_get(v_lib_1235_, 0);
v_config_1237_ = lean_ctor_get(v_pkg_1236_, 6);
v_precompileModules_1238_ = lean_ctor_get_uint8(v_config_1237_, sizeof(void*)*28 + 1);
if (v_precompileModules_1238_ == 0)
{
lean_object* v_config_1239_; uint8_t v_precompileModules_1240_; 
v_config_1239_ = lean_ctor_get(v_lib_1235_, 2);
v_precompileModules_1240_ = lean_ctor_get_uint8(v_config_1239_, sizeof(void*)*9 + 2);
return v_precompileModules_1240_;
}
else
{
return v_precompileModules_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Module_shouldPrecompile___boxed(lean_object* v_self_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lake_Module_shouldPrecompile(v_self_1241_);
lean_dec_ref(v_self_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets(lean_object* v_self_1244_, uint8_t v_shouldExport_1245_){
_start:
{
lean_object* v_lib_1246_; lean_object* v_config_1247_; lean_object* v_nativeFacets_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_lib_1246_ = lean_ctor_get(v_self_1244_, 0);
lean_inc_ref(v_lib_1246_);
lean_dec_ref(v_self_1244_);
v_config_1247_ = lean_ctor_get(v_lib_1246_, 2);
lean_inc(v_config_1247_);
lean_dec_ref(v_lib_1246_);
v_nativeFacets_1248_ = lean_ctor_get(v_config_1247_, 8);
lean_inc_ref(v_nativeFacets_1248_);
lean_dec(v_config_1247_);
v___x_1249_ = lean_box(v_shouldExport_1245_);
v___x_1250_ = lean_apply_1(v_nativeFacets_1248_, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Module_nativeFacets___boxed(lean_object* v_self_1251_, lean_object* v_shouldExport_1252_){
_start:
{
uint8_t v_shouldExport_boxed_1253_; lean_object* v_res_1254_; 
v_shouldExport_boxed_1253_ = lean_unbox(v_shouldExport_1252_);
v_res_1254_ = l_Lake_Module_nativeFacets(v_self_1251_, v_shouldExport_boxed_1253_);
return v_res_1254_;
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
