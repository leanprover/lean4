// Lean compiler output
// Module: Lake.Load.Lean.Elab
// Imports: public import Lake.Load.Config import Lean.Compiler.IR.CompilerM import Lean.Elab.Frontend import Lake.DSL.Extensions import Lake.Util.JsonObject import Init.System.Platform import Lake.DSL.AttributesCore
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqImport_beq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_LogEntry_ofMessage(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableImport_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_mkExtNameMap(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lake_nameExt;
extern lean_object* l_Lake_dirExt;
extern lean_object* l_Lake_optsExt;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_unlock(lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* l_System_FilePath_fileName(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*);
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_importModulesUsingCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_importModulesUsingCache___closed__0 = (const lean_object*)&l_Lake_importModulesUsingCache___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_configModuleName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lakefile"};
static const lean_object* l_Lake_configModuleName___closed__0 = (const lean_object*)&l_Lake_configModuleName___closed__0_value;
static const lean_ctor_object l_Lake_configModuleName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_configModuleName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 28, 93, 140, 254, 254, 56, 70)}};
static const lean_object* l_Lake_configModuleName___closed__1 = (const lean_object*)&l_Lake_configModuleName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_configModuleName = (const lean_object*)&l_Lake_configModuleName___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = ": package configuration has errors"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lake_environment_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "packageAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 216, 234, 151, 184, 29, 39, 9)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageDepAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__4_value),LEAN_SCALAR_PTR_LITERAL(45, 68, 99, 181, 205, 9, 187, 35)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__7_value),LEAN_SCALAR_PTR_LITERAL(85, 79, 83, 54, 241, 232, 152, 172)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 29, 82, 124, 109, 105, 242, 204)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "defaultScriptAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(102, 220, 227, 87, 142, 243, 134, 10)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanLibAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value),LEAN_SCALAR_PTR_LITERAL(32, 216, 106, 32, 231, 39, 130, 108)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanExeAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value),LEAN_SCALAR_PTR_LITERAL(188, 182, 7, 15, 47, 104, 138, 158)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "externLibAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value),LEAN_SCALAR_PTR_LITERAL(101, 0, 33, 72, 82, 211, 54, 104)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "targetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value),LEAN_SCALAR_PTR_LITERAL(230, 170, 78, 40, 161, 217, 169, 127)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "defaultTargetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value),LEAN_SCALAR_PTR_LITERAL(136, 50, 195, 92, 10, 179, 138, 115)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value),LEAN_SCALAR_PTR_LITERAL(145, 171, 145, 31, 167, 29, 89, 20)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value),LEAN_SCALAR_PTR_LITERAL(162, 200, 112, 121, 111, 252, 78, 167)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "moduleFacetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value),LEAN_SCALAR_PTR_LITERAL(184, 177, 55, 179, 152, 236, 7, 155)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageFacetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value),LEAN_SCALAR_PTR_LITERAL(30, 214, 121, 146, 170, 223, 202, 251)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libraryFacetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value),LEAN_SCALAR_PTR_LITERAL(68, 159, 200, 109, 254, 124, 216, 54)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(225, 220, 115, 150, 240, 139, 111, 12)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value_aux_1),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value),LEAN_SCALAR_PTR_LITERAL(176, 236, 150, 45, 29, 146, 124, 106)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "platform"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "leanHash"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configHash"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "options"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5_value;
static const lean_array_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__1_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Load"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__2_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(220, 161, 253, 19, 127, 236, 68, 167)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value),LEAN_SCALAR_PTR_LITERAL(253, 154, 30, 39, 33, 163, 227, 110)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(203, 94, 47, 233, 25, 155, 207, 4)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(182, 71, 227, 32, 192, 195, 122, 155)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__8_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 249, 1, 41, 61, 175, 29, 187)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ConfigTrace"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__9_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(112, 234, 7, 233, 55, 68, 23, 133)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 160, 71, 192, 5, 128, 186)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 42, 147, 74, 160, 173, 203, 244)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(240, 241, 210, 157, 244, 84, 172, 19)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(226, 162, 205, 82, 193, 115, 8, 28)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(15, 45, 121, 141, 112, 165, 100, 9)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object*);
static const lean_closure_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace___closed__0_value;
static const lean_string_object l_Lake_importConfigFile___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "could not acquire an exclusive configuration lock; another process may already be reconfiguring the package"};
static const lean_object* l_Lake_importConfigFile___lam__0___closed__0 = (const lean_object*)&l_Lake_importConfigFile___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_importConfigFile___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_importConfigFile___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_importConfigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid configuration file name"};
static const lean_object* l_Lake_importConfigFile___closed__0 = (const lean_object*)&l_Lake_importConfigFile___closed__0_value;
static const lean_ctor_object l_Lake_importConfigFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_importConfigFile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_importConfigFile___closed__1 = (const lean_object*)&l_Lake_importConfigFile___closed__1_value;
static const lean_string_object l_Lake_importConfigFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l_Lake_importConfigFile___closed__2 = (const lean_object*)&l_Lake_importConfigFile___closed__2_value;
static const lean_string_object l_Lake_importConfigFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_Lake_importConfigFile___closed__3 = (const lean_object*)&l_Lake_importConfigFile___closed__3_value;
static const lean_string_object l_Lake_importConfigFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "olean.trace"};
static const lean_object* l_Lake_importConfigFile___closed__4 = (const lean_object*)&l_Lake_importConfigFile___closed__4_value;
static const lean_string_object l_Lake_importConfigFile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "olean.lock"};
static const lean_object* l_Lake_importConfigFile___closed__5 = (const lean_object*)&l_Lake_importConfigFile___closed__5_value;
static const lean_string_object l_Lake_importConfigFile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "compiled configuration is invalid; run with '-R' to reconfigure"};
static const lean_object* l_Lake_importConfigFile___closed__6 = (const lean_object*)&l_Lake_importConfigFile___closed__6_value;
static const lean_ctor_object l_Lake_importConfigFile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_importConfigFile___closed__6_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_importConfigFile___closed__7 = (const lean_object*)&l_Lake_importConfigFile___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
v___x_9_ = lean_st_mk_ref(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2____boxed(lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4(){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_enable_initializer_execution();
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4___boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
return v_res_16_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(lean_object* v_xs_17_, lean_object* v_ys_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_zero_20_; uint8_t v_isZero_21_; 
v_zero_20_ = lean_unsigned_to_nat(0u);
v_isZero_21_ = lean_nat_dec_eq(v_x_19_, v_zero_20_);
if (v_isZero_21_ == 1)
{
lean_dec(v_x_19_);
return v_isZero_21_;
}
else
{
lean_object* v_one_22_; lean_object* v_n_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v_one_22_ = lean_unsigned_to_nat(1u);
v_n_23_ = lean_nat_sub(v_x_19_, v_one_22_);
lean_dec(v_x_19_);
v___x_24_ = lean_array_fget_borrowed(v_xs_17_, v_n_23_);
v___x_25_ = lean_array_fget_borrowed(v_ys_18_, v_n_23_);
v___x_26_ = l_Lean_instBEqImport_beq(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_dec(v_n_23_);
return v___x_26_;
}
else
{
v_x_19_ = v_n_23_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_xs_28_, lean_object* v_ys_29_, lean_object* v_x_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_28_, v_ys_29_, v_x_30_);
lean_dec_ref(v_ys_29_);
lean_dec_ref(v_xs_28_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(lean_object* v_a_33_, lean_object* v_b_34_, lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
lean_dec(v_b_34_);
lean_dec_ref(v_a_33_);
return v_x_35_;
}
else
{
lean_object* v_key_36_; lean_object* v_value_37_; lean_object* v_tail_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_52_; 
v_key_36_ = lean_ctor_get(v_x_35_, 0);
v_value_37_ = lean_ctor_get(v_x_35_, 1);
v_tail_38_ = lean_ctor_get(v_x_35_, 2);
v_isSharedCheck_52_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_52_ == 0)
{
v___x_40_ = v_x_35_;
v_isShared_41_ = v_isSharedCheck_52_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_tail_38_);
lean_inc(v_value_37_);
lean_inc(v_key_36_);
lean_dec(v_x_35_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_52_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_array_get_size(v_key_36_);
v___x_48_ = lean_array_get_size(v_a_33_);
v___x_49_ = lean_nat_dec_eq(v___x_47_, v___x_48_);
if (v___x_49_ == 0)
{
goto v___jp_42_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_36_, v_a_33_, v___x_47_);
if (v___x_50_ == 0)
{
goto v___jp_42_;
}
else
{
lean_object* v___x_51_; 
lean_del_object(v___x_40_);
lean_dec(v_value_37_);
lean_dec(v_key_36_);
v___x_51_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_51_, 0, v_a_33_);
lean_ctor_set(v___x_51_, 1, v_b_34_);
lean_ctor_set(v___x_51_, 2, v_tail_38_);
return v___x_51_;
}
}
v___jp_42_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_33_, v_b_34_, v_tail_38_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 2, v___x_43_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_key_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_value_37_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(lean_object* v_a_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
else
{
lean_object* v_key_56_; lean_object* v_tail_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_key_56_ = lean_ctor_get(v_x_54_, 0);
v_tail_57_ = lean_ctor_get(v_x_54_, 2);
v___x_58_ = lean_array_get_size(v_key_56_);
v___x_59_ = lean_array_get_size(v_a_53_);
v___x_60_ = lean_nat_dec_eq(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
v_x_54_ = v_tail_57_;
goto _start;
}
else
{
uint8_t v___x_62_; 
v___x_62_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_56_, v_a_53_, v___x_58_);
if (v___x_62_ == 0)
{
v_x_54_ = v_tail_57_;
goto _start;
}
else
{
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg___boxed(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec_ref(v_a_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(lean_object* v_as_68_, size_t v_i_69_, size_t v_stop_70_, uint64_t v_b_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_usize_dec_eq(v_i_69_, v_stop_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; size_t v___x_76_; size_t v___x_77_; 
v___x_73_ = lean_array_uget_borrowed(v_as_68_, v_i_69_);
v___x_74_ = l_Lean_instHashableImport_hash(v___x_73_);
v___x_75_ = lean_uint64_mix_hash(v_b_71_, v___x_74_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_69_, v___x_76_);
v_i_69_ = v___x_77_;
v_b_71_ = v___x_75_;
goto _start;
}
else
{
return v_b_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1___boxed(lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v_b_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; uint64_t v_b_boxed_85_; uint64_t v_res_86_; lean_object* v_r_87_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_b_boxed_85_ = lean_unbox_uint64(v_b_82_);
lean_dec_ref(v_b_82_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_as_79_, v_i_boxed_83_, v_stop_boxed_84_, v_b_boxed_85_);
lean_dec_ref(v_as_79_);
v_r_87_ = lean_box_uint64(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
return v_x_88_;
}
else
{
lean_object* v_key_90_; lean_object* v_value_91_; lean_object* v_tail_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_127_; 
v_key_90_ = lean_ctor_get(v_x_89_, 0);
v_value_91_ = lean_ctor_get(v_x_89_, 1);
v_tail_92_ = lean_ctor_get(v_x_89_, 2);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_127_ == 0)
{
v___x_94_ = v_x_89_;
v_isShared_95_ = v_isSharedCheck_127_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_tail_92_);
lean_inc(v_value_91_);
lean_inc(v_key_90_);
lean_dec(v_x_89_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_127_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; uint64_t v___y_98_; uint64_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_96_ = lean_array_get_size(v_x_88_);
v___x_116_ = 7ULL;
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_array_get_size(v_key_90_);
v___x_119_ = lean_nat_dec_lt(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
v___y_98_ = v___x_116_;
goto v___jp_97_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_le(v___x_118_, v___x_118_);
if (v___x_120_ == 0)
{
if (v___x_119_ == 0)
{
v___y_98_ = v___x_116_;
goto v___jp_97_;
}
else
{
size_t v___x_121_; size_t v___x_122_; uint64_t v___x_123_; 
v___x_121_ = ((size_t)0ULL);
v___x_122_ = lean_usize_of_nat(v___x_118_);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_key_90_, v___x_121_, v___x_122_, v___x_116_);
v___y_98_ = v___x_123_;
goto v___jp_97_;
}
}
else
{
size_t v___x_124_; size_t v___x_125_; uint64_t v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_118_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_key_90_, v___x_124_, v___x_125_, v___x_116_);
v___y_98_ = v___x_126_;
goto v___jp_97_;
}
}
v___jp_97_:
{
uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v_fold_101_; uint64_t v___x_102_; uint64_t v___x_103_; uint64_t v___x_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_99_ = 32ULL;
v___x_100_ = lean_uint64_shift_right(v___y_98_, v___x_99_);
v_fold_101_ = lean_uint64_xor(v___y_98_, v___x_100_);
v___x_102_ = 16ULL;
v___x_103_ = lean_uint64_shift_right(v_fold_101_, v___x_102_);
v___x_104_ = lean_uint64_xor(v_fold_101_, v___x_103_);
v___x_105_ = lean_uint64_to_usize(v___x_104_);
v___x_106_ = lean_usize_of_nat(v___x_96_);
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_sub(v___x_106_, v___x_107_);
v___x_109_ = lean_usize_land(v___x_105_, v___x_108_);
v___x_110_ = lean_array_uget_borrowed(v_x_88_, v___x_109_);
lean_inc(v___x_110_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 2, v___x_110_);
v___x_112_ = v___x_94_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_key_90_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_value_91_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v___x_110_);
v___x_112_ = v_reuseFailAlloc_115_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; 
v___x_113_ = lean_array_uset(v_x_88_, v___x_109_, v___x_112_);
v_x_88_ = v___x_113_;
v_x_89_ = v_tail_92_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(lean_object* v_i_128_, lean_object* v_source_129_, lean_object* v_target_130_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_array_get_size(v_source_129_);
v___x_132_ = lean_nat_dec_lt(v_i_128_, v___x_131_);
if (v___x_132_ == 0)
{
lean_dec_ref(v_source_129_);
lean_dec(v_i_128_);
return v_target_130_;
}
else
{
lean_object* v_es_133_; lean_object* v___x_134_; lean_object* v_source_135_; lean_object* v_target_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_es_133_ = lean_array_fget(v_source_129_, v_i_128_);
v___x_134_ = lean_box(0);
v_source_135_ = lean_array_fset(v_source_129_, v_i_128_, v___x_134_);
v_target_136_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_target_130_, v_es_133_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_i_128_, v___x_137_);
lean_dec(v_i_128_);
v_i_128_ = v___x_138_;
v_source_129_ = v_source_135_;
v_target_130_ = v_target_136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(lean_object* v_data_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_nbuckets_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_141_ = lean_array_get_size(v_data_140_);
v___x_142_ = lean_unsigned_to_nat(2u);
v_nbuckets_143_ = lean_nat_mul(v___x_141_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_box(0);
v___x_146_ = lean_mk_array(v_nbuckets_143_, v___x_145_);
v___x_147_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v___x_144_, v_data_140_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object* v_m_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v_size_151_; lean_object* v_buckets_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_207_; 
v_size_151_ = lean_ctor_get(v_m_148_, 0);
v_buckets_152_ = lean_ctor_get(v_m_148_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_m_148_);
if (v_isSharedCheck_207_ == 0)
{
v___x_154_ = v_m_148_;
v_isShared_155_ = v_isSharedCheck_207_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_buckets_152_);
lean_inc(v_size_151_);
lean_dec(v_m_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_207_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; uint64_t v___y_158_; uint64_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_156_ = lean_array_get_size(v_buckets_152_);
v___x_196_ = 7ULL;
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_array_get_size(v_a_149_);
v___x_199_ = lean_nat_dec_lt(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
v___y_158_ = v___x_196_;
goto v___jp_157_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = lean_nat_dec_le(v___x_198_, v___x_198_);
if (v___x_200_ == 0)
{
if (v___x_199_ == 0)
{
v___y_158_ = v___x_196_;
goto v___jp_157_;
}
else
{
size_t v___x_201_; size_t v___x_202_; uint64_t v___x_203_; 
v___x_201_ = ((size_t)0ULL);
v___x_202_ = lean_usize_of_nat(v___x_198_);
v___x_203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_149_, v___x_201_, v___x_202_, v___x_196_);
v___y_158_ = v___x_203_;
goto v___jp_157_;
}
}
else
{
size_t v___x_204_; size_t v___x_205_; uint64_t v___x_206_; 
v___x_204_ = ((size_t)0ULL);
v___x_205_ = lean_usize_of_nat(v___x_198_);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_149_, v___x_204_, v___x_205_, v___x_196_);
v___y_158_ = v___x_206_;
goto v___jp_157_;
}
}
v___jp_157_:
{
uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v_fold_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; lean_object* v_bkt_170_; uint8_t v___x_171_; 
v___x_159_ = 32ULL;
v___x_160_ = lean_uint64_shift_right(v___y_158_, v___x_159_);
v_fold_161_ = lean_uint64_xor(v___y_158_, v___x_160_);
v___x_162_ = 16ULL;
v___x_163_ = lean_uint64_shift_right(v_fold_161_, v___x_162_);
v___x_164_ = lean_uint64_xor(v_fold_161_, v___x_163_);
v___x_165_ = lean_uint64_to_usize(v___x_164_);
v___x_166_ = lean_usize_of_nat(v___x_156_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_sub(v___x_166_, v___x_167_);
v___x_169_ = lean_usize_land(v___x_165_, v___x_168_);
v_bkt_170_ = lean_array_uget_borrowed(v_buckets_152_, v___x_169_);
v___x_171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_149_, v_bkt_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v_size_x27_173_; lean_object* v___x_174_; lean_object* v_buckets_x27_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v_size_x27_173_ = lean_nat_add(v_size_151_, v___x_172_);
lean_dec(v_size_151_);
lean_inc(v_bkt_170_);
v___x_174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_174_, 0, v_a_149_);
lean_ctor_set(v___x_174_, 1, v_b_150_);
lean_ctor_set(v___x_174_, 2, v_bkt_170_);
v_buckets_x27_175_ = lean_array_uset(v_buckets_152_, v___x_169_, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(4u);
v___x_177_ = lean_nat_mul(v_size_x27_173_, v___x_176_);
v___x_178_ = lean_unsigned_to_nat(3u);
v___x_179_ = lean_nat_div(v___x_177_, v___x_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_array_get_size(v_buckets_x27_175_);
v___x_181_ = lean_nat_dec_le(v___x_179_, v___x_180_);
lean_dec(v___x_179_);
if (v___x_181_ == 0)
{
lean_object* v_val_182_; lean_object* v___x_184_; 
v_val_182_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_buckets_x27_175_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_val_182_);
lean_ctor_set(v___x_154_, 0, v_size_x27_173_);
v___x_184_ = v___x_154_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_size_x27_173_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_val_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v___x_187_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_buckets_x27_175_);
lean_ctor_set(v___x_154_, 0, v_size_x27_173_);
v___x_187_ = v___x_154_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_size_x27_173_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_buckets_x27_175_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v___x_189_; lean_object* v_buckets_x27_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
lean_inc(v_bkt_170_);
v___x_189_ = lean_box(0);
v_buckets_x27_190_ = lean_array_uset(v_buckets_152_, v___x_169_, v___x_189_);
v___x_191_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_149_, v_b_150_, v_bkt_170_);
v___x_192_ = lean_array_uset(v_buckets_x27_190_, v___x_169_, v___x_191_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_192_);
v___x_194_ = v___x_154_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_151_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object* v_a_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v_key_211_; lean_object* v_value_212_; lean_object* v_tail_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_key_211_ = lean_ctor_get(v_x_209_, 0);
v_value_212_ = lean_ctor_get(v_x_209_, 1);
v_tail_213_ = lean_ctor_get(v_x_209_, 2);
v___x_214_ = lean_array_get_size(v_key_211_);
v___x_215_ = lean_array_get_size(v_a_208_);
v___x_216_ = lean_nat_dec_eq(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
v_x_209_ = v_tail_213_;
goto _start;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_211_, v_a_208_, v___x_214_);
if (v___x_218_ == 0)
{
v_x_209_ = v_tail_213_;
goto _start;
}
else
{
lean_object* v___x_220_; 
lean_inc(v_value_212_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_value_212_);
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_221_, v_x_222_);
lean_dec(v_x_222_);
lean_dec_ref(v_a_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object* v_m_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_buckets_226_; lean_object* v___x_227_; uint64_t v___y_229_; uint64_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_buckets_226_ = lean_ctor_get(v_m_224_, 1);
v___x_227_ = lean_array_get_size(v_buckets_226_);
v___x_243_ = 7ULL;
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_array_get_size(v_a_225_);
v___x_246_ = lean_nat_dec_lt(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = lean_nat_dec_le(v___x_245_, v___x_245_);
if (v___x_247_ == 0)
{
if (v___x_246_ == 0)
{
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
else
{
size_t v___x_248_; size_t v___x_249_; uint64_t v___x_250_; 
v___x_248_ = ((size_t)0ULL);
v___x_249_ = lean_usize_of_nat(v___x_245_);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_225_, v___x_248_, v___x_249_, v___x_243_);
v___y_229_ = v___x_250_;
goto v___jp_228_;
}
}
else
{
size_t v___x_251_; size_t v___x_252_; uint64_t v___x_253_; 
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_245_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_225_, v___x_251_, v___x_252_, v___x_243_);
v___y_229_ = v___x_253_;
goto v___jp_228_;
}
}
v___jp_228_:
{
uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v_fold_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_230_ = 32ULL;
v___x_231_ = lean_uint64_shift_right(v___y_229_, v___x_230_);
v_fold_232_ = lean_uint64_xor(v___y_229_, v___x_231_);
v___x_233_ = 16ULL;
v___x_234_ = lean_uint64_shift_right(v_fold_232_, v___x_233_);
v___x_235_ = lean_uint64_xor(v_fold_232_, v___x_234_);
v___x_236_ = lean_uint64_to_usize(v___x_235_);
v___x_237_ = lean_usize_of_nat(v___x_227_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_sub(v___x_237_, v___x_238_);
v___x_240_ = lean_usize_land(v___x_236_, v___x_239_);
v___x_241_ = lean_array_uget_borrowed(v_buckets_226_, v___x_240_);
v___x_242_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_225_, v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object* v_m_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_254_, v_a_255_);
lean_dec_ref(v_a_255_);
lean_dec_ref(v_m_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* v_imports_259_, lean_object* v_opts_260_, uint32_t v_trustLevel_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
v___x_264_ = lean_st_ref_get(v___x_263_);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v___x_264_, v_imports_259_);
lean_dec(v___x_264_);
if (lean_obj_tag(v___x_265_) == 1)
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_opts_260_);
lean_dec_ref(v_imports_259_);
v_val_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_val_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v___x_274_; 
lean_dec(v___x_265_);
v___x_274_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; uint8_t v___x_276_; uint8_t v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v___x_274_);
v___x_275_ = ((lean_object*)(l_Lake_importModulesUsingCache___closed__0));
v___x_276_ = 0;
v___x_277_ = 1;
v___x_278_ = 2;
v___x_279_ = lean_box(1);
lean_inc_ref(v_imports_259_);
v___x_280_ = l_Lean_importModules(v_imports_259_, v_opts_260_, v_trustLevel_261_, v___x_275_, v___x_276_, v___x_277_, v___x_278_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_291_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_291_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_285_ = lean_st_ref_take(v___x_263_);
lean_inc(v_a_281_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_285_, v_imports_259_, v_a_281_);
v___x_287_ = lean_st_ref_set(v___x_263_, v___x_286_);
if (v_isShared_284_ == 0)
{
v___x_289_ = v___x_283_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_281_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_dec_ref(v_imports_259_);
return v___x_280_;
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_opts_260_);
lean_dec_ref(v_imports_259_);
v_a_292_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_274_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_274_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* v_imports_300_, lean_object* v_opts_301_, lean_object* v_trustLevel_302_, lean_object* v_a_303_){
_start:
{
uint32_t v_trustLevel_boxed_304_; lean_object* v_res_305_; 
v_trustLevel_boxed_304_ = lean_unbox_uint32(v_trustLevel_302_);
lean_dec(v_trustLevel_302_);
v_res_305_ = l_Lake_importModulesUsingCache(v_imports_300_, v_opts_301_, v_trustLevel_boxed_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_307_, v_a_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object* v_00_u03b2_310_, lean_object* v_m_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_310_, v_m_311_, v_a_312_);
lean_dec_ref(v_a_312_);
lean_dec_ref(v_m_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(lean_object* v_00_u03b2_314_, lean_object* v_m_315_, lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_315_, v_a_316_, v_b_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_320_, v_x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_a_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_323_, v_a_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object* v_00_u03b2_327_, lean_object* v_a_328_, lean_object* v_x_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_328_, v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_00_u03b2_331_, v_a_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_a_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(lean_object* v_00_u03b2_336_, lean_object* v_data_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_data_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(lean_object* v_00_u03b2_339_, lean_object* v_a_340_, lean_object* v_b_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_340_, v_b_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(lean_object* v_xs_344_, lean_object* v_ys_345_, lean_object* v_hsz_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_344_, v_ys_345_, v_x_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_350_, lean_object* v_ys_351_, lean_object* v_hsz_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_350_, v_ys_351_, v_hsz_352_, v_x_353_, v_x_354_);
lean_dec_ref(v_ys_351_);
lean_dec_ref(v_xs_350_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_357_, lean_object* v_i_358_, lean_object* v_source_359_, lean_object* v_target_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v_i_358_, v_source_359_, v_target_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_x_363_, v_x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object* v_header_367_, lean_object* v_opts_368_, lean_object* v_inputCtx_369_, lean_object* v_a_370_){
_start:
{
uint8_t v___x_372_; lean_object* v_imports_373_; uint32_t v___x_374_; lean_object* v___x_375_; 
v___x_372_ = 1;
lean_inc(v_header_367_);
v_imports_373_ = l_Lean_Elab_HeaderSyntax_imports(v_header_367_, v___x_372_);
v___x_374_ = 1024;
v___x_375_ = l_Lake_importModulesUsingCache(v_imports_373_, v_opts_368_, v___x_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_inputCtx_369_);
lean_dec(v_header_367_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_a_376_);
lean_ctor_set(v___x_380_, 1, v_a_370_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v_fileName_386_; lean_object* v_fileMap_387_; uint8_t v___x_388_; lean_object* v___y_390_; lean_object* v___x_419_; 
v_a_385_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_375_);
v_fileName_386_ = lean_ctor_get(v_inputCtx_369_, 1);
lean_inc_ref(v_fileName_386_);
v_fileMap_387_ = lean_ctor_get(v_inputCtx_369_, 2);
lean_inc_ref(v_fileMap_387_);
lean_dec_ref(v_inputCtx_369_);
v___x_388_ = 0;
v___x_419_ = l_Lean_Syntax_getPos_x3f(v_header_367_, v___x_388_);
lean_dec(v_header_367_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___y_390_ = v___x_420_;
goto v___jp_389_;
}
else
{
lean_object* v_val_421_; 
v_val_421_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_val_421_);
lean_dec_ref(v___x_419_);
v___y_390_ = v_val_421_;
goto v___jp_389_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint32_t v___x_399_; lean_object* v___x_400_; 
v___x_391_ = l_Lean_FileMap_toPosition(v_fileMap_387_, v___y_390_);
lean_dec(v___y_390_);
v___x_392_ = lean_box(0);
v___x_393_ = 2;
v___x_394_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0));
v___x_395_ = lean_io_error_to_string(v_a_385_);
v___x_396_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
v___x_397_ = l_Lean_MessageData_ofFormat(v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_398_, 0, v_fileName_386_);
lean_ctor_set(v___x_398_, 1, v___x_391_);
lean_ctor_set(v___x_398_, 2, v___x_392_);
lean_ctor_set(v___x_398_, 3, v___x_394_);
lean_ctor_set(v___x_398_, 4, v___x_397_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*5, v___x_388_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*5 + 1, v___x_393_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*5 + 2, v___x_388_);
v___x_399_ = 0;
v___x_400_ = lean_mk_empty_environment(v___x_399_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_410_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = l_Lean_MessageLog_add(v___x_398_, v_a_370_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_a_401_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v___x_398_);
lean_dec_ref(v_a_370_);
v_a_411_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_400_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_400_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object* v_header_422_, lean_object* v_opts_423_, lean_object* v_inputCtx_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_422_, v_opts_423_, v_inputCtx_424_, v_a_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object* v_x_432_, lean_object* v___y_433_){
_start:
{
uint8_t v_isSilent_435_; 
v_isSilent_435_ = lean_ctor_get_uint8(v_x_432_, sizeof(void*)*5 + 2);
if (v_isSilent_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = l_Lake_LogEntry_ofMessage(v_x_432_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_array_push(v___y_433_, v___x_436_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref(v_x_432_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___y_433_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object* v_x_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_442_, v___y_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_446_, lean_object* v_as_447_, size_t v_i_448_, size_t v_stop_449_, lean_object* v_b_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_eq(v_i_448_, v_stop_449_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_array_uget_borrowed(v_as_447_, v_i_448_);
lean_inc_ref(v_f_446_);
lean_inc(v___x_454_);
v___x_455_ = lean_apply_3(v_f_446_, v___x_454_, v___y_451_, lean_box(0));
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v_a_457_; size_t v___x_458_; size_t v___x_459_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
v_a_457_ = lean_ctor_get(v___x_455_, 1);
lean_inc(v_a_457_);
lean_dec_ref(v___x_455_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_448_, v___x_458_);
v_i_448_ = v___x_459_;
v_b_450_ = v_a_456_;
v___y_451_ = v_a_457_;
goto _start;
}
else
{
lean_dec_ref(v_f_446_);
return v___x_455_;
}
}
else
{
lean_object* v___x_461_; 
lean_dec_ref(v_f_446_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_b_450_);
lean_ctor_set(v___x_461_, 1, v___y_451_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_462_, lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_stop_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
size_t v_i_boxed_469_; size_t v_stop_boxed_470_; lean_object* v_res_471_; 
v_i_boxed_469_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_stop_boxed_470_ = lean_unbox_usize(v_stop_465_);
lean_dec(v_stop_465_);
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_462_, v_as_463_, v_i_boxed_469_, v_stop_boxed_470_, v_b_466_, v___y_467_);
lean_dec_ref(v_as_463_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_472_, lean_object* v_x_473_, lean_object* v___y_474_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v_cs_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_cs_476_ = lean_ctor_get(v_x_473_, 0);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_array_get_size(v_cs_476_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_nat_dec_lt(v___x_477_, v___x_478_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v_f_472_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___y_474_);
return v___x_481_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_le(v___x_478_, v___x_478_);
if (v___x_482_ == 0)
{
if (v___x_480_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_f_472_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_479_);
lean_ctor_set(v___x_483_, 1, v___y_474_);
return v___x_483_;
}
else
{
size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((size_t)0ULL);
v___x_485_ = lean_usize_of_nat(v___x_478_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_472_, v_cs_476_, v___x_484_, v___x_485_, v___x_479_, v___y_474_);
return v___x_486_;
}
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_478_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_472_, v_cs_476_, v___x_487_, v___x_488_, v___x_479_, v___y_474_);
return v___x_489_;
}
}
}
else
{
lean_object* v_vs_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_vs_490_ = lean_ctor_get(v_x_473_, 0);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_array_get_size(v_vs_490_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_nat_dec_lt(v___x_491_, v___x_492_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec_ref(v_f_472_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___y_474_);
return v___x_495_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_le(v___x_492_, v___x_492_);
if (v___x_496_ == 0)
{
if (v___x_494_ == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v_f_472_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_493_);
lean_ctor_set(v___x_497_, 1, v___y_474_);
return v___x_497_;
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((size_t)0ULL);
v___x_499_ = lean_usize_of_nat(v___x_492_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_472_, v_vs_490_, v___x_498_, v___x_499_, v___x_493_, v___y_474_);
return v___x_500_;
}
}
else
{
size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((size_t)0ULL);
v___x_502_ = lean_usize_of_nat(v___x_492_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_472_, v_vs_490_, v___x_501_, v___x_502_, v___x_493_, v___y_474_);
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_504_, lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_, lean_object* v_b_508_, lean_object* v___y_509_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
lean_inc_ref(v_f_504_);
v___x_513_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_504_, v___x_512_, v___y_509_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v_a_515_; size_t v___x_516_; size_t v___x_517_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
v_a_515_ = lean_ctor_get(v___x_513_, 1);
lean_inc(v_a_515_);
lean_dec_ref(v___x_513_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_506_, v___x_516_);
v_i_506_ = v___x_517_;
v_b_508_ = v_a_514_;
v___y_509_ = v_a_515_;
goto _start;
}
else
{
lean_dec_ref(v_f_504_);
return v___x_513_;
}
}
else
{
lean_object* v___x_519_; 
lean_dec_ref(v_f_504_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_b_508_);
lean_ctor_set(v___x_519_, 1, v___y_509_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
size_t v_i_boxed_527_; size_t v_stop_boxed_528_; lean_object* v_res_529_; 
v_i_boxed_527_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_528_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_520_, v_as_521_, v_i_boxed_527_, v_stop_boxed_528_, v_b_524_, v___y_525_);
lean_dec_ref(v_as_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_530_, v_x_531_, v___y_532_);
lean_dec_ref(v_x_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_535_, lean_object* v_t_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_root_539_; lean_object* v_tail_540_; lean_object* v___x_541_; 
v_root_539_ = lean_ctor_get(v_t_536_, 0);
v_tail_540_ = lean_ctor_get(v_t_536_, 1);
lean_inc_ref(v_f_535_);
v___x_541_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_535_, v_root_539_, v___y_537_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_563_; 
v_a_542_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_564_);
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_563_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_563_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_array_get_size(v_tail_540_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_nat_dec_lt(v___x_546_, v___x_547_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v_f_535_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_548_);
v___x_551_ = v___x_544_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_a_542_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
uint8_t v___x_553_; 
v___x_553_ = lean_nat_dec_le(v___x_547_, v___x_547_);
if (v___x_553_ == 0)
{
if (v___x_549_ == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v_f_535_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_548_);
v___x_555_ = v___x_544_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_a_542_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
else
{
size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; 
lean_del_object(v___x_544_);
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_547_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_535_, v_tail_540_, v___x_557_, v___x_558_, v___x_548_, v_a_542_);
return v___x_559_;
}
}
else
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
lean_del_object(v___x_544_);
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_547_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_535_, v_tail_540_, v___x_560_, v___x_561_, v___x_548_, v_a_542_);
return v___x_562_;
}
}
}
}
else
{
lean_dec_ref(v_f_535_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_565_, lean_object* v_t_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_565_, v_t_566_, v___y_567_);
lean_dec_ref(v_t_566_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_571_, lean_object* v_x_572_, size_t v_x_573_, size_t v_x_574_, lean_object* v___y_575_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_object* v_cs_577_; lean_object* v___x_578_; size_t v___x_579_; lean_object* v_j_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v_cs_577_ = lean_ctor_get(v_x_572_, 0);
v___x_578_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_579_ = lean_usize_shift_right(v_x_573_, v_x_574_);
v_j_580_ = lean_usize_to_nat(v___x_579_);
v___x_581_ = lean_array_get_borrowed(v___x_578_, v_cs_577_, v_j_580_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_shift_left(v___x_582_, v_x_574_);
v___x_584_ = lean_usize_sub(v___x_583_, v___x_582_);
v___x_585_ = lean_usize_land(v_x_573_, v___x_584_);
v___x_586_ = ((size_t)5ULL);
v___x_587_ = lean_usize_sub(v_x_574_, v___x_586_);
lean_inc_ref(v_f_571_);
v___x_588_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_571_, v___x_581_, v___x_585_, v___x_587_, v___y_575_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_611_; 
v_a_589_ = lean_ctor_get(v___x_588_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_612_);
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_611_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_611_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_j_580_, v___x_593_);
lean_dec(v_j_580_);
v___x_595_ = lean_array_get_size(v_cs_577_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_nat_dec_lt(v___x_594_, v___x_595_);
if (v___x_597_ == 0)
{
lean_object* v___x_599_; 
lean_dec(v___x_594_);
lean_dec_ref(v_f_571_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_596_);
v___x_599_ = v___x_591_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_a_589_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
uint8_t v___x_601_; 
v___x_601_ = lean_nat_dec_le(v___x_595_, v___x_595_);
if (v___x_601_ == 0)
{
if (v___x_597_ == 0)
{
lean_object* v___x_603_; 
lean_dec(v___x_594_);
lean_dec_ref(v_f_571_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_596_);
v___x_603_ = v___x_591_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_589_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
lean_del_object(v___x_591_);
v___x_605_ = lean_usize_of_nat(v___x_594_);
lean_dec(v___x_594_);
v___x_606_ = lean_usize_of_nat(v___x_595_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_571_, v_cs_577_, v___x_605_, v___x_606_, v___x_596_, v_a_589_);
return v___x_607_;
}
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_591_);
v___x_608_ = lean_usize_of_nat(v___x_594_);
lean_dec(v___x_594_);
v___x_609_ = lean_usize_of_nat(v___x_595_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_571_, v_cs_577_, v___x_608_, v___x_609_, v___x_596_, v_a_589_);
return v___x_610_;
}
}
}
}
else
{
lean_dec(v_j_580_);
lean_dec_ref(v_f_571_);
return v___x_588_;
}
}
else
{
lean_object* v_vs_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_vs_613_ = lean_ctor_get(v_x_572_, 0);
v___x_614_ = lean_usize_to_nat(v_x_573_);
v___x_615_ = lean_array_get_size(v_vs_613_);
v___x_616_ = lean_box(0);
v___x_617_ = lean_nat_dec_lt(v___x_614_, v___x_615_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v___x_614_);
lean_dec_ref(v_f_571_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___y_575_);
return v___x_618_;
}
else
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_le(v___x_615_, v___x_615_);
if (v___x_619_ == 0)
{
if (v___x_617_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v___x_614_);
lean_dec_ref(v_f_571_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_616_);
lean_ctor_set(v___x_620_, 1, v___y_575_);
return v___x_620_;
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_usize_of_nat(v___x_614_);
lean_dec(v___x_614_);
v___x_622_ = lean_usize_of_nat(v___x_615_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_571_, v_vs_613_, v___x_621_, v___x_622_, v___x_616_, v___y_575_);
return v___x_623_;
}
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_usize_of_nat(v___x_614_);
lean_dec(v___x_614_);
v___x_625_ = lean_usize_of_nat(v___x_615_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_571_, v_vs_613_, v___x_624_, v___x_625_, v___x_616_, v___y_575_);
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
size_t v_x_13978__boxed_633_; size_t v_x_13979__boxed_634_; lean_object* v_res_635_; 
v_x_13978__boxed_633_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_x_13979__boxed_634_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_635_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_627_, v_x_628_, v_x_13978__boxed_633_, v_x_13979__boxed_634_, v___y_631_);
lean_dec_ref(v_x_628_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_636_, lean_object* v_t_637_, lean_object* v_start_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_nat_dec_eq(v_start_638_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v_root_643_; lean_object* v_tail_644_; size_t v_shift_645_; lean_object* v_tailOff_646_; uint8_t v___x_647_; 
v_root_643_ = lean_ctor_get(v_t_637_, 0);
v_tail_644_ = lean_ctor_get(v_t_637_, 1);
v_shift_645_ = lean_ctor_get_usize(v_t_637_, 4);
v_tailOff_646_ = lean_ctor_get(v_t_637_, 3);
v___x_647_ = lean_nat_dec_le(v_tailOff_646_, v_start_638_);
if (v___x_647_ == 0)
{
size_t v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_usize_of_nat(v_start_638_);
lean_inc_ref(v_f_636_);
v___x_649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_636_, v_root_643_, v___x_648_, v_shift_645_, v___y_639_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_670_; 
v_a_650_ = lean_ctor_get(v___x_649_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_671_);
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_670_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_670_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_array_get_size(v_tail_644_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_nat_dec_lt(v___x_641_, v___x_654_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_f_636_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_655_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_a_650_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_le(v___x_654_, v___x_654_);
if (v___x_660_ == 0)
{
if (v___x_656_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_f_636_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_655_);
v___x_662_ = v___x_652_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_a_650_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
lean_del_object(v___x_652_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_654_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_636_, v_tail_644_, v___x_664_, v___x_665_, v___x_655_, v_a_650_);
return v___x_666_;
}
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_652_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_654_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_636_, v_tail_644_, v___x_667_, v___x_668_, v___x_655_, v_a_650_);
return v___x_669_;
}
}
}
}
else
{
lean_dec_ref(v_f_636_);
return v___x_649_;
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_672_ = lean_nat_sub(v_start_638_, v_tailOff_646_);
v___x_673_ = lean_array_get_size(v_tail_644_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec(v___x_672_);
lean_dec_ref(v_f_636_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___y_639_);
return v___x_676_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_le(v___x_673_, v___x_673_);
if (v___x_677_ == 0)
{
if (v___x_675_ == 0)
{
lean_object* v___x_678_; 
lean_dec(v___x_672_);
lean_dec_ref(v_f_636_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_674_);
lean_ctor_set(v___x_678_, 1, v___y_639_);
return v___x_678_;
}
else
{
size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_usize_of_nat(v___x_672_);
lean_dec(v___x_672_);
v___x_680_ = lean_usize_of_nat(v___x_673_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_636_, v_tail_644_, v___x_679_, v___x_680_, v___x_674_, v___y_639_);
return v___x_681_;
}
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_usize_of_nat(v___x_672_);
lean_dec(v___x_672_);
v___x_683_ = lean_usize_of_nat(v___x_673_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_636_, v_tail_644_, v___x_682_, v___x_683_, v___x_674_, v___y_639_);
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_636_, v_t_637_, v___y_639_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_686_, lean_object* v_t_687_, lean_object* v_start_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_686_, v_t_687_, v_start_688_, v___y_689_);
lean_dec(v_start_688_);
lean_dec_ref(v_t_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_692_, lean_object* v_f_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_unreported_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_unreported_696_ = lean_ctor_get(v_log_692_, 1);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_693_, v_unreported_696_, v___x_697_, v___y_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_699_, lean_object* v_f_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_699_, v_f_700_, v___y_701_);
lean_dec_ref(v_log_699_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_706_, lean_object* v_pkgName_707_, lean_object* v_pkgDir_708_, lean_object* v_lakeOpts_709_, lean_object* v_leanOpts_710_, lean_object* v_configFile_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_IO_FS_readFile(v_configFile_711_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v___x_716_ = 1;
v___x_717_ = lean_string_utf8_byte_size(v_a_715_);
lean_inc_ref(v_configFile_711_);
v___x_718_ = l_Lean_Parser_mkInputContext___redArg(v_a_715_, v_configFile_711_, v___x_716_, v___x_717_);
lean_inc_ref(v___x_718_);
v___x_719_ = l_Lean_Parser_parseHeader(v___x_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_818_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_818_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_818_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_818_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_snd_724_; lean_object* v_fst_725_; lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_817_; 
v_snd_724_ = lean_ctor_get(v_a_720_, 1);
lean_inc(v_snd_724_);
v_fst_725_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_fst_725_);
lean_dec(v_a_720_);
v_fst_726_ = lean_ctor_get(v_snd_724_, 0);
v_snd_727_ = lean_ctor_get(v_snd_724_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_snd_724_);
if (v_isSharedCheck_817_ == 0)
{
v___x_729_ = v_snd_724_;
v_isShared_730_ = v_isSharedCheck_817_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_snd_724_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_817_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; 
lean_inc_ref(v___x_718_);
lean_inc_ref(v_leanOpts_710_);
v___x_731_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_725_, v_leanOpts_710_, v___x_718_, v_snd_727_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_807_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_807_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_807_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_807_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_806_; 
v_fst_736_ = lean_ctor_get(v_a_732_, 0);
v_snd_737_ = lean_ctor_get(v_a_732_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_806_ == 0)
{
v___x_739_ = v_a_732_;
v_isShared_740_ = v_isSharedCheck_806_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v_a_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_806_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v_asyncMode_742_; lean_object* v___x_743_; lean_object* v_asyncMode_744_; lean_object* v___x_745_; lean_object* v_asyncMode_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_741_ = l_Lake_nameExt;
v_asyncMode_742_ = lean_ctor_get(v___x_741_, 2);
v___x_743_ = l_Lake_dirExt;
v_asyncMode_744_ = lean_ctor_get(v___x_743_, 2);
v___x_745_ = l_Lake_optsExt;
v_asyncMode_746_ = lean_ctor_get(v___x_745_, 2);
v___x_747_ = ((lean_object*)(l_Lake_configModuleName));
v___x_748_ = l_Lean_Environment_setMainModule(v_fst_736_, v___x_747_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v_pkgName_707_);
lean_ctor_set(v___x_739_, 0, v_pkgIdx_706_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_pkgIdx_706_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_pkgName_707_);
v___x_750_ = v_reuseFailAlloc_805_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_Lean_EnvExtension_setState___redArg(v___x_741_, v___x_748_, v___x_750_, v_asyncMode_742_);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 1);
lean_ctor_set(v___x_734_, 0, v_pkgDir_708_);
v___x_753_ = v___x_734_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_pkgDir_708_);
v___x_753_ = v_reuseFailAlloc_804_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = l_Lean_EnvExtension_setState___redArg(v___x_743_, v___x_751_, v___x_753_, v_asyncMode_744_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
lean_ctor_set(v___x_722_, 0, v_lakeOpts_709_);
v___x_756_ = v___x_722_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_lakeOpts_709_);
v___x_756_ = v_reuseFailAlloc_803_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_EnvExtension_setState___redArg(v___x_745_, v___x_754_, v___x_756_, v_asyncMode_746_);
v___x_758_ = l_Lean_Elab_Command_mkState(v___x_757_, v_snd_737_, v_leanOpts_710_);
v___x_759_ = l_Lean_Elab_IO_processCommands(v___x_718_, v_fst_726_, v___x_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_commandState_761_; lean_object* v_env_762_; lean_object* v_messages_763_; lean_object* v___f_764_; lean_object* v___x_765_; 
lean_del_object(v___x_729_);
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v_commandState_761_ = lean_ctor_get(v_a_760_, 0);
lean_inc_ref(v_commandState_761_);
lean_dec(v_a_760_);
v_env_762_ = lean_ctor_get(v_commandState_761_, 0);
lean_inc_ref(v_env_762_);
v_messages_763_ = lean_ctor_get(v_commandState_761_, 1);
lean_inc_ref(v_messages_763_);
lean_dec_ref(v_commandState_761_);
v___f_764_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_765_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_763_, v___f_764_, v_a_712_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_783_; 
v_a_766_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_784_);
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_783_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_783_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v___x_770_; 
v___x_770_ = l_Lean_MessageLog_hasErrors(v_messages_763_);
lean_dec_ref(v_messages_763_);
if (v___x_770_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v_configFile_711_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v_env_762_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_env_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_a_766_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
lean_dec_ref(v_env_762_);
v___x_774_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1));
v___x_775_ = lean_string_append(v_configFile_711_, v___x_774_);
v___x_776_ = 3;
v___x_777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v___x_776_);
v___x_778_ = lean_array_get_size(v_a_766_);
v___x_779_ = lean_array_push(v_a_766_, v___x_777_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 1, v___x_779_);
lean_ctor_set(v___x_768_, 0, v___x_778_);
v___x_781_ = v___x_768_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_messages_763_);
lean_dec_ref(v_env_762_);
lean_dec_ref(v_configFile_711_);
v_a_785_ = lean_ctor_get(v___x_765_, 0);
v_a_786_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_765_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_inc(v_a_785_);
lean_dec(v___x_765_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_785_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
lean_dec_ref(v_configFile_711_);
v_a_794_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_794_);
lean_dec_ref(v___x_759_);
v___x_795_ = lean_io_error_to_string(v_a_794_);
v___x_796_ = 3;
v___x_797_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*1, v___x_796_);
v___x_798_ = lean_array_get_size(v_a_712_);
v___x_799_ = lean_array_push(v_a_712_, v___x_797_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 1, v___x_799_);
lean_ctor_set(v___x_729_, 0, v___x_798_);
v___x_801_ = v___x_729_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_799_);
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
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec(v_fst_726_);
lean_del_object(v___x_722_);
lean_dec_ref(v___x_718_);
lean_dec_ref(v_configFile_711_);
lean_dec_ref(v_leanOpts_710_);
lean_dec(v_lakeOpts_709_);
lean_dec_ref(v_pkgDir_708_);
lean_dec(v_pkgName_707_);
lean_dec(v_pkgIdx_706_);
v_a_808_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_731_);
v___x_809_ = lean_io_error_to_string(v_a_808_);
v___x_810_ = 3;
v___x_811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1, v___x_810_);
v___x_812_ = lean_array_get_size(v_a_712_);
v___x_813_ = lean_array_push(v_a_712_, v___x_811_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 1, v___x_813_);
lean_ctor_set(v___x_729_, 0, v___x_812_);
v___x_815_ = v___x_729_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v_configFile_711_);
lean_dec_ref(v_leanOpts_710_);
lean_dec(v_lakeOpts_709_);
lean_dec_ref(v_pkgDir_708_);
lean_dec(v_pkgName_707_);
lean_dec(v_pkgIdx_706_);
v_a_819_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v___x_719_);
v___x_820_ = lean_io_error_to_string(v_a_819_);
v___x_821_ = 3;
v___x_822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v___x_821_);
v___x_823_ = lean_array_get_size(v_a_712_);
v___x_824_ = lean_array_push(v_a_712_, v___x_822_);
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref(v_configFile_711_);
lean_dec_ref(v_leanOpts_710_);
lean_dec(v_lakeOpts_709_);
lean_dec_ref(v_pkgDir_708_);
lean_dec(v_pkgName_707_);
lean_dec(v_pkgIdx_706_);
v_a_826_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_826_);
lean_dec_ref(v___x_714_);
v___x_827_ = lean_io_error_to_string(v_a_826_);
v___x_828_ = 3;
v___x_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1, v___x_828_);
v___x_830_ = lean_array_get_size(v_a_712_);
v___x_831_ = lean_array_push(v_a_712_, v___x_829_);
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_833_, lean_object* v_pkgName_834_, lean_object* v_pkgDir_835_, lean_object* v_lakeOpts_836_, lean_object* v_leanOpts_837_, lean_object* v_configFile_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_833_, v_pkgName_834_, v_pkgDir_835_, v_lakeOpts_836_, v_leanOpts_837_, v_configFile_838_, v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_844_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = lake_environment_add(v_env_844_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_845_);
return v_res_846_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_853_ = l_Lean_NameSet_empty;
v___x_854_ = l_Lean_NameSet_insert(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_860_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_861_ = l_Lean_NameSet_insert(v___x_860_, v___x_859_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_867_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_868_ = l_Lean_NameSet_insert(v___x_867_, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_874_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_875_ = l_Lean_NameSet_insert(v___x_874_, v___x_873_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_881_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_882_ = l_Lean_NameSet_insert(v___x_881_, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_888_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_889_ = l_Lean_NameSet_insert(v___x_888_, v___x_887_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_895_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_896_ = l_Lean_NameSet_insert(v___x_895_, v___x_894_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_902_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_903_ = l_Lean_NameSet_insert(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_909_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_910_ = l_Lean_NameSet_insert(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_916_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_917_ = l_Lean_NameSet_insert(v___x_916_, v___x_915_);
return v___x_917_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_923_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_924_ = l_Lean_NameSet_insert(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_930_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_931_ = l_Lean_NameSet_insert(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_937_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_938_ = l_Lean_NameSet_insert(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_944_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_945_ = l_Lean_NameSet_insert(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_951_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_952_ = l_Lean_NameSet_insert(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_959_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_960_ = l_Lean_NameSet_insert(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52));
v___x_968_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_969_ = l_Lean_NameSet_insert(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53);
return v___x_970_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = l_Lean_instInhabitedEnvExtensionState;
v___x_972_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_973_, lean_object* v_val_974_, lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_, lean_object* v_b_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; size_t v___x_986_; size_t v___x_987_; 
v___x_980_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
v___x_981_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_982_ = lean_array_get_borrowed(v___x_981_, v_val_973_, v_val_974_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_box(0);
lean_inc(v___x_980_);
lean_inc(v___x_982_);
v___x_985_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_982_, v_b_978_, v___x_980_, v___x_983_, v___x_984_);
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_976_, v___x_986_);
v_i_976_ = v___x_987_;
v_b_978_ = v___x_985_;
goto _start;
}
else
{
return v_b_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_989_, lean_object* v_val_990_, lean_object* v_as_991_, lean_object* v_i_992_, lean_object* v_stop_993_, lean_object* v_b_994_){
_start:
{
size_t v_i_boxed_995_; size_t v_stop_boxed_996_; lean_object* v_res_997_; 
v_i_boxed_995_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_stop_boxed_996_ = lean_unbox_usize(v_stop_993_);
lean_dec(v_stop_993_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_989_, v_val_990_, v_as_991_, v_i_boxed_995_, v_stop_boxed_996_, v_b_994_);
lean_dec_ref(v_as_991_);
lean_dec(v_val_990_);
lean_dec_ref(v_val_989_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_box(0);
return v___x_1000_;
}
else
{
lean_object* v_key_1001_; lean_object* v_value_1002_; lean_object* v_tail_1003_; uint8_t v___x_1004_; 
v_key_1001_ = lean_ctor_get(v_x_999_, 0);
v_value_1002_ = lean_ctor_get(v_x_999_, 1);
v_tail_1003_ = lean_ctor_get(v_x_999_, 2);
v___x_1004_ = lean_name_eq(v_key_1001_, v_a_998_);
if (v___x_1004_ == 0)
{
v_x_999_ = v_tail_1003_;
goto _start;
}
else
{
lean_object* v___x_1006_; 
lean_inc(v_value_1002_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_value_1002_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1007_, v_x_1008_);
lean_dec(v_x_1008_);
lean_dec(v_a_1007_);
return v_res_1009_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1010_; uint64_t v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1723u);
v___x_1011_ = lean_uint64_of_nat(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_buckets_1014_; lean_object* v___x_1015_; uint64_t v___y_1017_; 
v_buckets_1014_ = lean_ctor_get(v_m_1012_, 1);
v___x_1015_ = lean_array_get_size(v_buckets_1014_);
if (lean_obj_tag(v_a_1013_) == 0)
{
uint64_t v___x_1031_; 
v___x_1031_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0);
v___y_1017_ = v___x_1031_;
goto v___jp_1016_;
}
else
{
uint64_t v_hash_1032_; 
v_hash_1032_ = lean_ctor_get_uint64(v_a_1013_, sizeof(void*)*2);
v___y_1017_ = v_hash_1032_;
goto v___jp_1016_;
}
v___jp_1016_:
{
uint64_t v___x_1018_; uint64_t v___x_1019_; uint64_t v_fold_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; uint64_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1018_ = 32ULL;
v___x_1019_ = lean_uint64_shift_right(v___y_1017_, v___x_1018_);
v_fold_1020_ = lean_uint64_xor(v___y_1017_, v___x_1019_);
v___x_1021_ = 16ULL;
v___x_1022_ = lean_uint64_shift_right(v_fold_1020_, v___x_1021_);
v___x_1023_ = lean_uint64_xor(v_fold_1020_, v___x_1022_);
v___x_1024_ = lean_uint64_to_usize(v___x_1023_);
v___x_1025_ = lean_usize_of_nat(v___x_1015_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_sub(v___x_1025_, v___x_1026_);
v___x_1028_ = lean_usize_land(v___x_1024_, v___x_1027_);
v___x_1029_ = lean_array_uget_borrowed(v_buckets_1014_, v___x_1028_);
v___x_1030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1013_, v___x_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_m_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_1036_, lean_object* v_val_1037_, lean_object* v_as_1038_, size_t v_i_1039_, size_t v_stop_1040_, lean_object* v_b_1041_){
_start:
{
lean_object* v___y_1043_; uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_eq(v_i_1039_, v_stop_1040_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1048_ = lean_array_uget_borrowed(v_as_1038_, v_i_1039_);
v_fst_1049_ = lean_ctor_get(v___x_1048_, 0);
v_snd_1050_ = lean_ctor_get(v___x_1048_, 1);
v___x_1051_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_1052_ = l_Lean_NameSet_contains(v___x_1051_, v_fst_1049_);
if (v___x_1052_ == 0)
{
v___y_1043_ = v_b_1041_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_1036_, v_fst_1049_);
if (lean_obj_tag(v___x_1053_) == 0)
{
v___y_1043_ = v_b_1041_;
goto v___jp_1042_;
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_val_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_val_1054_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_array_get_size(v_snd_1050_);
v___x_1057_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_dec(v_val_1054_);
v___y_1043_ = v_b_1041_;
goto v___jp_1042_;
}
else
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
if (v___x_1058_ == 0)
{
if (v___x_1057_ == 0)
{
lean_dec(v_val_1054_);
v___y_1043_ = v_b_1041_;
goto v___jp_1042_;
}
else
{
size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = lean_usize_of_nat(v___x_1056_);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1037_, v_val_1054_, v_snd_1050_, v___x_1059_, v___x_1060_, v_b_1041_);
lean_dec(v_val_1054_);
v___y_1043_ = v___x_1061_;
goto v___jp_1042_;
}
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1056_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1037_, v_val_1054_, v_snd_1050_, v___x_1062_, v___x_1063_, v_b_1041_);
lean_dec(v_val_1054_);
v___y_1043_ = v___x_1064_;
goto v___jp_1042_;
}
}
}
}
}
else
{
return v_b_1041_;
}
v___jp_1042_:
{
size_t v___x_1044_; size_t v___x_1045_; 
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_1039_, v___x_1044_);
v_i_1039_ = v___x_1045_;
v_b_1041_ = v___y_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1065_, lean_object* v_val_1066_, lean_object* v_as_1067_, lean_object* v_i_1068_, lean_object* v_stop_1069_, lean_object* v_b_1070_){
_start:
{
size_t v_i_boxed_1071_; size_t v_stop_boxed_1072_; lean_object* v_res_1073_; 
v_i_boxed_1071_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_stop_boxed_1072_ = lean_unbox_usize(v_stop_1069_);
lean_dec(v_stop_1069_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1065_, v_val_1066_, v_as_1067_, v_i_boxed_1071_, v_stop_boxed_1072_, v_b_1070_);
lean_dec_ref(v_as_1067_);
lean_dec_ref(v_val_1066_);
lean_dec_ref(v_a_1065_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1074_, size_t v_i_1075_, size_t v_stop_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1075_, v_stop_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1074_, v_i_1075_);
lean_inc(v___x_1079_);
v___x_1080_ = lake_environment_add(v_b_1077_, v___x_1079_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_i_1075_, v___x_1081_);
v_i_1075_ = v___x_1082_;
v_b_1077_ = v___x_1080_;
goto _start;
}
else
{
return v_b_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1084_, lean_object* v_i_1085_, lean_object* v_stop_1086_, lean_object* v_b_1087_){
_start:
{
size_t v_i_boxed_1088_; size_t v_stop_boxed_1089_; lean_object* v_res_1090_; 
v_i_boxed_1088_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_stop_boxed_1089_ = lean_unbox_usize(v_stop_1086_);
lean_dec(v_stop_1086_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1084_, v_i_boxed_1088_, v_stop_boxed_1089_, v_b_1087_);
lean_dec_ref(v_as_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1091_, lean_object* v_leanOpts_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_readModuleData(v_olean_1091_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v_fst_1096_; lean_object* v_imports_1097_; lean_object* v_constants_1098_; lean_object* v_entries_1099_; uint32_t v___x_1100_; lean_object* v___x_1101_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref(v___x_1094_);
v_fst_1096_ = lean_ctor_get(v_a_1095_, 0);
lean_inc(v_fst_1096_);
lean_dec(v_a_1095_);
v_imports_1097_ = lean_ctor_get(v_fst_1096_, 0);
lean_inc_ref(v_imports_1097_);
v_constants_1098_ = lean_ctor_get(v_fst_1096_, 2);
lean_inc_ref(v_constants_1098_);
v_entries_1099_ = lean_ctor_get(v_fst_1096_, 4);
lean_inc_ref(v_entries_1099_);
lean_dec(v_fst_1096_);
v___x_1100_ = 1024;
v___x_1101_ = l_Lake_importModulesUsingCache(v_imports_1097_, v_leanOpts_1092_, v___x_1100_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_array_get_size(v_constants_1098_);
v___x_1144_ = lean_nat_dec_lt(v___x_1103_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec_ref(v_constants_1098_);
v___y_1105_ = v_a_1102_;
goto v___jp_1104_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_le(v___x_1143_, v___x_1143_);
if (v___x_1145_ == 0)
{
if (v___x_1144_ == 0)
{
lean_dec_ref(v_constants_1098_);
v___y_1105_ = v_a_1102_;
goto v___jp_1104_;
}
else
{
size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = lean_usize_of_nat(v___x_1143_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1098_, v___x_1146_, v___x_1147_, v_a_1102_);
lean_dec_ref(v_constants_1098_);
v___y_1105_ = v___x_1148_;
goto v___jp_1104_;
}
}
else
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = lean_usize_of_nat(v___x_1143_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1098_, v___x_1149_, v___x_1150_, v_a_1102_);
lean_dec_ref(v_constants_1098_);
v___y_1105_ = v___x_1151_;
goto v___jp_1104_;
}
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_persistentEnvExtensionsRef;
v___x_1107_ = lean_st_ref_get(v___x_1106_);
v___x_1108_ = l_Lean_mkExtNameMap(v___x_1103_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1134_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1134_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1134_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_array_get_size(v_entries_1099_);
v___x_1114_ = lean_nat_dec_lt(v___x_1103_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1116_; 
lean_dec(v_a_1109_);
lean_dec(v___x_1107_);
lean_dec_ref(v_entries_1099_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___y_1105_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___y_1105_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_le(v___x_1113_, v___x_1113_);
if (v___x_1118_ == 0)
{
if (v___x_1114_ == 0)
{
lean_object* v___x_1120_; 
lean_dec(v_a_1109_);
lean_dec(v___x_1107_);
lean_dec_ref(v_entries_1099_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___y_1105_);
v___x_1120_ = v___x_1111_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___y_1105_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1122_ = ((size_t)0ULL);
v___x_1123_ = lean_usize_of_nat(v___x_1113_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1109_, v___x_1107_, v_entries_1099_, v___x_1122_, v___x_1123_, v___y_1105_);
lean_dec_ref(v_entries_1099_);
lean_dec(v___x_1107_);
lean_dec(v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1124_);
v___x_1126_ = v___x_1111_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = lean_usize_of_nat(v___x_1113_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1109_, v___x_1107_, v_entries_1099_, v___x_1128_, v___x_1129_, v___y_1105_);
lean_dec_ref(v_entries_1099_);
lean_dec(v___x_1107_);
lean_dec(v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1130_);
v___x_1132_ = v___x_1111_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v___x_1107_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_entries_1099_);
v_a_1135_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1108_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1108_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
else
{
lean_dec_ref(v_entries_1099_);
lean_dec_ref(v_constants_1098_);
return v___x_1101_;
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_leanOpts_1092_);
v_a_1152_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1094_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1094_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1160_, lean_object* v_leanOpts_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1160_, v_leanOpts_1161_);
lean_dec_ref(v_olean_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1164_, lean_object* v_m_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1165_, v_a_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1168_, lean_object* v_m_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1168_, v_m_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_m_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1172_, lean_object* v_a_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1173_, v_x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1176_, lean_object* v_a_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1176_, v_a_1177_, v_x_1178_);
lean_dec(v_x_1178_);
lean_dec(v_a_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_box(1);
v___x_1182_ = lean_panic_fn_borrowed(v___x_1181_, v_msg_1180_);
return v___x_1182_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1187_ = lean_unsigned_to_nat(35u);
v___x_1188_ = lean_unsigned_to_nat(276u);
v___x_1189_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1190_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1191_ = l_mkPanicMessageWithDecl(v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_);
return v___x_1191_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1193_ = lean_unsigned_to_nat(21u);
v___x_1194_ = lean_unsigned_to_nat(277u);
v___x_1195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1197_ = l_mkPanicMessageWithDecl(v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_, v___x_1192_);
return v___x_1197_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1201_ = lean_unsigned_to_nat(35u);
v___x_1202_ = lean_unsigned_to_nat(182u);
v___x_1203_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1204_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1205_ = l_mkPanicMessageWithDecl(v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_);
return v___x_1205_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1207_ = lean_unsigned_to_nat(21u);
v___x_1208_ = lean_unsigned_to_nat(183u);
v___x_1209_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1210_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1211_ = l_mkPanicMessageWithDecl(v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1212_, lean_object* v_v_1213_, lean_object* v_t_1214_){
_start:
{
if (lean_obj_tag(v_t_1214_) == 0)
{
lean_object* v_size_1215_; lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v_l_1218_; lean_object* v_r_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1576_; 
v_size_1215_ = lean_ctor_get(v_t_1214_, 0);
v_k_1216_ = lean_ctor_get(v_t_1214_, 1);
v_v_1217_ = lean_ctor_get(v_t_1214_, 2);
v_l_1218_ = lean_ctor_get(v_t_1214_, 3);
v_r_1219_ = lean_ctor_get(v_t_1214_, 4);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_t_1214_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1221_ = v_t_1214_;
v_isShared_1222_ = v_isSharedCheck_1576_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_r_1219_);
lean_inc(v_l_1218_);
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
lean_inc(v_size_1215_);
lean_dec(v_t_1214_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1576_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_string_dec_lt(v_k_1212_, v_k_1216_);
if (v___x_1223_ == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_string_dec_eq(v_k_1212_, v_k_1216_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_size_1215_);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1212_, v_v_1213_, v_r_1219_);
if (lean_obj_tag(v_l_1218_) == 0)
{
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_size_1226_; lean_object* v_size_1227_; lean_object* v_k_1228_; lean_object* v_v_1229_; lean_object* v_l_1230_; lean_object* v_r_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_size_1226_ = lean_ctor_get(v_l_1218_, 0);
v_size_1227_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_size_1227_);
v_k_1228_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_k_1228_);
v_v_1229_ = lean_ctor_get(v___x_1225_, 2);
lean_inc(v_v_1229_);
v_l_1230_ = lean_ctor_get(v___x_1225_, 3);
lean_inc(v_l_1230_);
v_r_1231_ = lean_ctor_get(v___x_1225_, 4);
lean_inc(v_r_1231_);
v___x_1232_ = lean_unsigned_to_nat(3u);
v___x_1233_ = lean_nat_mul(v___x_1232_, v_size_1226_);
v___x_1234_ = lean_nat_dec_lt(v___x_1233_, v_size_1227_);
lean_dec(v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_dec(v_r_1231_);
lean_dec(v_l_1230_);
lean_dec(v_v_1229_);
lean_dec(v_k_1228_);
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v___x_1235_, v_size_1226_);
v___x_1237_ = lean_nat_add(v___x_1236_, v_size_1227_);
lean_dec(v_size_1227_);
lean_dec(v___x_1236_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1225_);
lean_ctor_set(v___x_1221_, 0, v___x_1237_);
v___x_1239_ = v___x_1221_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v___x_1225_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1310_; 
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; 
v_unused_1311_ = lean_ctor_get(v___x_1225_, 4);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v___x_1225_, 3);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v___x_1225_, 2);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v___x_1225_, 1);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1315_);
v___x_1242_ = v___x_1225_;
v_isShared_1243_ = v_isSharedCheck_1310_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v___x_1225_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1310_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
if (lean_obj_tag(v_l_1230_) == 0)
{
if (lean_obj_tag(v_r_1231_) == 0)
{
lean_object* v_size_1244_; lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_l_1247_; lean_object* v_r_1248_; lean_object* v_size_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_size_1244_ = lean_ctor_get(v_l_1230_, 0);
v_k_1245_ = lean_ctor_get(v_l_1230_, 1);
v_v_1246_ = lean_ctor_get(v_l_1230_, 2);
v_l_1247_ = lean_ctor_get(v_l_1230_, 3);
v_r_1248_ = lean_ctor_get(v_l_1230_, 4);
v_size_1249_ = lean_ctor_get(v_r_1231_, 0);
v___x_1250_ = lean_unsigned_to_nat(2u);
v___x_1251_ = lean_nat_mul(v___x_1250_, v_size_1249_);
v___x_1252_ = lean_nat_dec_lt(v_size_1244_, v___x_1251_);
lean_dec(v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1281_; 
lean_inc(v_r_1248_);
lean_inc(v_l_1247_);
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_l_1230_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; lean_object* v_unused_1283_; lean_object* v_unused_1284_; lean_object* v_unused_1285_; lean_object* v_unused_1286_; 
v_unused_1282_ = lean_ctor_get(v_l_1230_, 4);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_l_1230_, 3);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v_l_1230_, 2);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_l_1230_, 1);
lean_dec(v_unused_1285_);
v_unused_1286_ = lean_ctor_get(v_l_1230_, 0);
lean_dec(v_unused_1286_);
v___x_1254_ = v_l_1230_;
v_isShared_1255_ = v_isSharedCheck_1281_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v_l_1230_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1281_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1271_; 
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v___x_1256_, v_size_1226_);
v___x_1258_ = lean_nat_add(v___x_1257_, v_size_1227_);
lean_dec(v_size_1227_);
if (lean_obj_tag(v_l_1247_) == 0)
{
lean_object* v_size_1279_; 
v_size_1279_ = lean_ctor_get(v_l_1247_, 0);
lean_inc(v_size_1279_);
v___y_1271_ = v_size_1279_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_unsigned_to_nat(0u);
v___y_1271_ = v___x_1280_;
goto v___jp_1270_;
}
v___jp_1259_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = lean_nat_add(v___y_1260_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec(v___y_1260_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_r_1231_);
lean_ctor_set(v___x_1254_, 3, v_r_1248_);
lean_ctor_set(v___x_1254_, 2, v_v_1229_);
lean_ctor_set(v___x_1254_, 1, v_k_1228_);
lean_ctor_set(v___x_1254_, 0, v___x_1263_);
v___x_1265_ = v___x_1254_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_r_1231_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___x_1265_);
lean_ctor_set(v___x_1242_, 3, v___y_1261_);
lean_ctor_set(v___x_1242_, 2, v_v_1246_);
lean_ctor_set(v___x_1242_, 1, v_k_1245_);
lean_ctor_set(v___x_1242_, 0, v___x_1258_);
v___x_1267_ = v___x_1242_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v___y_1261_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_nat_add(v___x_1257_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec(v___x_1257_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_l_1247_);
lean_ctor_set(v___x_1221_, 0, v___x_1272_);
v___x_1274_ = v___x_1221_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_l_1247_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_nat_add(v___x_1256_, v_size_1249_);
if (lean_obj_tag(v_r_1248_) == 0)
{
lean_object* v_size_1276_; 
v_size_1276_ = lean_ctor_get(v_r_1248_, 0);
lean_inc(v_size_1276_);
v___y_1260_ = v___x_1275_;
v___y_1261_ = v___x_1274_;
v___y_1262_ = v_size_1276_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___y_1260_ = v___x_1275_;
v___y_1261_ = v___x_1274_;
v___y_1262_ = v___x_1277_;
goto v___jp_1259_;
}
}
}
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
lean_del_object(v___x_1221_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v___x_1287_, v_size_1226_);
v___x_1289_ = lean_nat_add(v___x_1288_, v_size_1227_);
lean_dec(v_size_1227_);
v___x_1290_ = lean_nat_add(v___x_1288_, v_size_1244_);
lean_dec(v___x_1288_);
lean_inc_ref(v_l_1218_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_l_1230_);
lean_ctor_set(v___x_1242_, 3, v_l_1218_);
lean_ctor_set(v___x_1242_, 2, v_v_1217_);
lean_ctor_set(v___x_1242_, 1, v_k_1216_);
lean_ctor_set(v___x_1242_, 0, v___x_1290_);
v___x_1292_ = v___x_1242_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_l_1230_);
v___x_1292_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v_l_1218_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; lean_object* v_unused_1301_; lean_object* v_unused_1302_; lean_object* v_unused_1303_; lean_object* v_unused_1304_; 
v_unused_1300_ = lean_ctor_get(v_l_1218_, 4);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v_l_1218_, 3);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_l_1218_, 2);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_l_1218_, 1);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_l_1218_, 0);
lean_dec(v_unused_1304_);
v___x_1294_ = v_l_1218_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v_l_1218_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 4, v_r_1231_);
lean_ctor_set(v___x_1294_, 3, v___x_1292_);
lean_ctor_set(v___x_1294_, 2, v_v_1229_);
lean_ctor_set(v___x_1294_, 1, v_k_1228_);
lean_ctor_set(v___x_1294_, 0, v___x_1289_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v_r_1231_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref(v_l_1230_);
lean_del_object(v___x_1242_);
lean_dec(v_v_1229_);
lean_dec(v_k_1228_);
lean_dec(v_size_1227_);
lean_dec_ref(v_l_1218_);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1306_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1307_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1306_);
return v___x_1307_;
}
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_del_object(v___x_1242_);
lean_dec(v_r_1231_);
lean_dec(v_v_1229_);
lean_dec(v_k_1228_);
lean_dec(v_size_1227_);
lean_dec_ref(v_l_1218_);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1308_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1309_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1308_);
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_size_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v_size_1316_ = lean_ctor_get(v_l_1218_, 0);
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_add(v___x_1317_, v_size_1316_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1225_);
lean_ctor_set(v___x_1221_, 0, v___x_1318_);
v___x_1320_ = v___x_1221_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v___x_1225_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_l_1322_; 
v_l_1322_ = lean_ctor_get(v___x_1225_, 3);
lean_inc(v_l_1322_);
if (lean_obj_tag(v_l_1322_) == 0)
{
lean_object* v_r_1323_; 
v_r_1323_ = lean_ctor_get(v___x_1225_, 4);
lean_inc(v_r_1323_);
if (lean_obj_tag(v_r_1323_) == 0)
{
lean_object* v_size_1324_; lean_object* v_k_1325_; lean_object* v_v_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1340_; 
v_size_1324_ = lean_ctor_get(v___x_1225_, 0);
v_k_1325_ = lean_ctor_get(v___x_1225_, 1);
v_v_1326_ = lean_ctor_get(v___x_1225_, 2);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; lean_object* v_unused_1342_; 
v_unused_1341_ = lean_ctor_get(v___x_1225_, 4);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v___x_1225_, 3);
lean_dec(v_unused_1342_);
v___x_1328_ = v___x_1225_;
v_isShared_1329_ = v_isSharedCheck_1340_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_v_1326_);
lean_inc(v_k_1325_);
lean_inc(v_size_1324_);
lean_dec(v___x_1225_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1340_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_size_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v_size_1330_ = lean_ctor_get(v_l_1322_, 0);
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v___x_1331_, v_size_1324_);
lean_dec(v_size_1324_);
v___x_1333_ = lean_nat_add(v___x_1331_, v_size_1330_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v_l_1322_);
lean_ctor_set(v___x_1328_, 3, v_l_1218_);
lean_ctor_set(v___x_1328_, 2, v_v_1217_);
lean_ctor_set(v___x_1328_, 1, v_k_1216_);
lean_ctor_set(v___x_1328_, 0, v___x_1333_);
v___x_1335_ = v___x_1328_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_l_1322_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_r_1323_);
lean_ctor_set(v___x_1221_, 3, v___x_1335_);
lean_ctor_set(v___x_1221_, 2, v_v_1326_);
lean_ctor_set(v___x_1221_, 1, v_k_1325_);
lean_ctor_set(v___x_1221_, 0, v___x_1332_);
v___x_1337_ = v___x_1221_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1325_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1326_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_r_1323_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
lean_object* v_k_1343_; lean_object* v_v_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1368_; 
v_k_1343_ = lean_ctor_get(v___x_1225_, 1);
v_v_1344_ = lean_ctor_get(v___x_1225_, 2);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1369_ = lean_ctor_get(v___x_1225_, 4);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v___x_1225_, 3);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1371_);
v___x_1346_ = v___x_1225_;
v_isShared_1347_ = v_isSharedCheck_1368_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_v_1344_);
lean_inc(v_k_1343_);
lean_dec(v___x_1225_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1368_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1364_; 
v_k_1348_ = lean_ctor_get(v_l_1322_, 1);
v_v_1349_ = lean_ctor_get(v_l_1322_, 2);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_l_1322_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1365_ = lean_ctor_get(v_l_1322_, 4);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_l_1322_, 3);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_l_1322_, 0);
lean_dec(v_unused_1367_);
v___x_1351_ = v_l_1322_;
v_isShared_1352_ = v_isSharedCheck_1364_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_v_1349_);
lean_inc(v_k_1348_);
lean_dec(v_l_1322_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1364_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = lean_unsigned_to_nat(3u);
v___x_1354_ = lean_unsigned_to_nat(1u);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 4, v_r_1323_);
lean_ctor_set(v___x_1351_, 3, v_r_1323_);
lean_ctor_set(v___x_1351_, 2, v_v_1217_);
lean_ctor_set(v___x_1351_, 1, v_k_1216_);
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_r_1323_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_r_1323_);
v___x_1356_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 3, v_r_1323_);
lean_ctor_set(v___x_1346_, 0, v___x_1354_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_r_1323_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1323_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1358_);
lean_ctor_set(v___x_1221_, 3, v___x_1356_);
lean_ctor_set(v___x_1221_, 2, v_v_1349_);
lean_ctor_set(v___x_1221_, 1, v_k_1348_);
lean_ctor_set(v___x_1221_, 0, v___x_1353_);
v___x_1360_ = v___x_1221_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1372_; 
v_r_1372_ = lean_ctor_get(v___x_1225_, 4);
lean_inc(v_r_1372_);
if (lean_obj_tag(v_r_1372_) == 0)
{
lean_object* v_k_1373_; lean_object* v_v_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1386_; 
v_k_1373_ = lean_ctor_get(v___x_1225_, 1);
v_v_1374_ = lean_ctor_get(v___x_1225_, 2);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; lean_object* v_unused_1388_; lean_object* v_unused_1389_; 
v_unused_1387_ = lean_ctor_get(v___x_1225_, 4);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v___x_1225_, 3);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1389_);
v___x_1376_ = v___x_1225_;
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_v_1374_);
lean_inc(v_k_1373_);
lean_dec(v___x_1225_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1378_ = lean_unsigned_to_nat(3u);
v___x_1379_ = lean_unsigned_to_nat(1u);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_l_1322_);
lean_ctor_set(v___x_1376_, 2, v_v_1217_);
lean_ctor_set(v___x_1376_, 1, v_k_1216_);
lean_ctor_set(v___x_1376_, 0, v___x_1379_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_l_1322_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_l_1322_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1383_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_r_1372_);
lean_ctor_set(v___x_1221_, 3, v___x_1381_);
lean_ctor_set(v___x_1221_, 2, v_v_1374_);
lean_ctor_set(v___x_1221_, 1, v_k_1373_);
lean_ctor_set(v___x_1221_, 0, v___x_1378_);
v___x_1383_ = v___x_1221_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1373_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1374_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_r_1372_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = lean_unsigned_to_nat(2u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1225_);
lean_ctor_set(v___x_1221_, 3, v_r_1372_);
lean_ctor_set(v___x_1221_, 0, v___x_1390_);
v___x_1392_ = v___x_1221_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_r_1372_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v___x_1225_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = lean_unsigned_to_nat(1u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1225_);
lean_ctor_set(v___x_1221_, 3, v___x_1225_);
lean_ctor_set(v___x_1221_, 0, v___x_1394_);
v___x_1396_ = v___x_1221_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v___x_1225_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v___x_1399_; 
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v_v_1213_);
lean_ctor_set(v___x_1221_, 1, v_k_1212_);
v___x_1399_ = v___x_1221_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_size_1215_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1212_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1213_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_r_1219_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_size_1215_);
v___x_1401_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1212_, v_v_1213_, v_l_1218_);
if (lean_obj_tag(v_r_1219_) == 0)
{
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_size_1402_; lean_object* v_size_1403_; lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v_l_1406_; lean_object* v_r_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_size_1402_ = lean_ctor_get(v_r_1219_, 0);
v_size_1403_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_size_1403_);
v_k_1404_ = lean_ctor_get(v___x_1401_, 1);
lean_inc(v_k_1404_);
v_v_1405_ = lean_ctor_get(v___x_1401_, 2);
lean_inc(v_v_1405_);
v_l_1406_ = lean_ctor_get(v___x_1401_, 3);
lean_inc(v_l_1406_);
v_r_1407_ = lean_ctor_get(v___x_1401_, 4);
lean_inc(v_r_1407_);
v___x_1408_ = lean_unsigned_to_nat(3u);
v___x_1409_ = lean_nat_mul(v___x_1408_, v_size_1402_);
v___x_1410_ = lean_nat_dec_lt(v___x_1409_, v_size_1403_);
lean_dec(v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_dec(v_r_1407_);
lean_dec(v_l_1406_);
lean_dec(v_v_1405_);
lean_dec(v_k_1404_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_add(v___x_1411_, v_size_1403_);
lean_dec(v_size_1403_);
v___x_1413_ = lean_nat_add(v___x_1412_, v_size_1402_);
lean_dec(v___x_1412_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 3, v___x_1401_);
lean_ctor_set(v___x_1221_, 0, v___x_1413_);
v___x_1415_ = v___x_1221_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_r_1219_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1488_; 
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1489_ = lean_ctor_get(v___x_1401_, 4);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v___x_1401_, 3);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v___x_1401_, 2);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v___x_1401_, 1);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1493_);
v___x_1418_ = v___x_1401_;
v_isShared_1419_ = v_isSharedCheck_1488_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v___x_1401_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1488_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
if (lean_obj_tag(v_l_1406_) == 0)
{
if (lean_obj_tag(v_r_1407_) == 0)
{
lean_object* v_size_1420_; lean_object* v_size_1421_; lean_object* v_k_1422_; lean_object* v_v_1423_; lean_object* v_l_1424_; lean_object* v_r_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_size_1420_ = lean_ctor_get(v_l_1406_, 0);
v_size_1421_ = lean_ctor_get(v_r_1407_, 0);
v_k_1422_ = lean_ctor_get(v_r_1407_, 1);
v_v_1423_ = lean_ctor_get(v_r_1407_, 2);
v_l_1424_ = lean_ctor_get(v_r_1407_, 3);
v_r_1425_ = lean_ctor_get(v_r_1407_, 4);
v___x_1426_ = lean_unsigned_to_nat(2u);
v___x_1427_ = lean_nat_mul(v___x_1426_, v_size_1420_);
v___x_1428_ = lean_nat_dec_lt(v_size_1421_, v___x_1427_);
lean_dec(v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1458_; 
lean_inc(v_r_1425_);
lean_inc(v_l_1424_);
lean_inc(v_v_1423_);
lean_inc(v_k_1422_);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_r_1407_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; 
v_unused_1459_ = lean_ctor_get(v_r_1407_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1407_, 3);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_r_1407_, 2);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_r_1407_, 1);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_r_1407_, 0);
lean_dec(v_unused_1463_);
v___x_1430_ = v_r_1407_;
v_isShared_1431_ = v_isSharedCheck_1458_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_r_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1458_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___x_1446_; lean_object* v___y_1448_; 
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_add(v___x_1432_, v_size_1403_);
lean_dec(v_size_1403_);
v___x_1434_ = lean_nat_add(v___x_1433_, v_size_1402_);
lean_dec(v___x_1433_);
v___x_1446_ = lean_nat_add(v___x_1432_, v_size_1420_);
if (lean_obj_tag(v_l_1424_) == 0)
{
lean_object* v_size_1456_; 
v_size_1456_ = lean_ctor_get(v_l_1424_, 0);
lean_inc(v_size_1456_);
v___y_1448_ = v_size_1456_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___y_1448_ = v___x_1457_;
goto v___jp_1447_;
}
v___jp_1435_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_nat_add(v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec(v___y_1437_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_r_1219_);
lean_ctor_set(v___x_1430_, 3, v_r_1425_);
lean_ctor_set(v___x_1430_, 2, v_v_1217_);
lean_ctor_set(v___x_1430_, 1, v_k_1216_);
lean_ctor_set(v___x_1430_, 0, v___x_1439_);
v___x_1441_ = v___x_1430_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_r_1425_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1219_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 4, v___x_1441_);
lean_ctor_set(v___x_1418_, 3, v___y_1436_);
lean_ctor_set(v___x_1418_, 2, v_v_1423_);
lean_ctor_set(v___x_1418_, 1, v_k_1422_);
lean_ctor_set(v___x_1418_, 0, v___x_1434_);
v___x_1443_ = v___x_1418_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1422_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1423_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v___y_1436_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_nat_add(v___x_1446_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec(v___x_1446_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_l_1424_);
lean_ctor_set(v___x_1221_, 3, v_l_1406_);
lean_ctor_set(v___x_1221_, 2, v_v_1405_);
lean_ctor_set(v___x_1221_, 1, v_k_1404_);
lean_ctor_set(v___x_1221_, 0, v___x_1449_);
v___x_1451_ = v___x_1221_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_l_1424_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_nat_add(v___x_1432_, v_size_1402_);
if (lean_obj_tag(v_r_1425_) == 0)
{
lean_object* v_size_1453_; 
v_size_1453_ = lean_ctor_get(v_r_1425_, 0);
lean_inc(v_size_1453_);
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___x_1452_;
v___y_1438_ = v_size_1453_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___y_1436_ = v___x_1451_;
v___y_1437_ = v___x_1452_;
v___y_1438_ = v___x_1454_;
goto v___jp_1435_;
}
}
}
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_del_object(v___x_1221_);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1403_);
lean_dec(v_size_1403_);
v___x_1466_ = lean_nat_add(v___x_1465_, v_size_1402_);
lean_dec(v___x_1465_);
v___x_1467_ = lean_nat_add(v___x_1464_, v_size_1402_);
v___x_1468_ = lean_nat_add(v___x_1467_, v_size_1421_);
lean_dec(v___x_1467_);
lean_inc_ref(v_r_1219_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 4, v_r_1219_);
lean_ctor_set(v___x_1418_, 3, v_r_1407_);
lean_ctor_set(v___x_1418_, 2, v_v_1217_);
lean_ctor_set(v___x_1418_, 1, v_k_1216_);
lean_ctor_set(v___x_1418_, 0, v___x_1468_);
v___x_1470_ = v___x_1418_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_r_1407_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_r_1219_);
v___x_1470_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_isSharedCheck_1477_ = !lean_is_exclusive(v_r_1219_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; 
v_unused_1478_ = lean_ctor_get(v_r_1219_, 4);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_r_1219_, 3);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_r_1219_, 2);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_r_1219_, 1);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_r_1219_, 0);
lean_dec(v_unused_1482_);
v___x_1472_ = v_r_1219_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v_r_1219_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v___x_1470_);
lean_ctor_set(v___x_1472_, 3, v_l_1406_);
lean_ctor_set(v___x_1472_, 2, v_v_1405_);
lean_ctor_set(v___x_1472_, 1, v_k_1404_);
lean_ctor_set(v___x_1472_, 0, v___x_1466_);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_l_1406_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v___x_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_l_1406_);
lean_del_object(v___x_1418_);
lean_dec(v_v_1405_);
lean_dec(v_k_1404_);
lean_dec(v_size_1403_);
lean_dec_ref(v_r_1219_);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1484_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1485_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1484_);
return v___x_1485_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_del_object(v___x_1418_);
lean_dec(v_r_1407_);
lean_dec(v_v_1405_);
lean_dec(v_k_1404_);
lean_dec(v_size_1403_);
lean_dec_ref(v_r_1219_);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1486_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1487_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1486_);
return v___x_1487_;
}
}
}
}
else
{
lean_object* v_size_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v_size_1494_ = lean_ctor_get(v_r_1219_, 0);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_add(v___x_1495_, v_size_1494_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 3, v___x_1401_);
lean_ctor_set(v___x_1221_, 0, v___x_1496_);
v___x_1498_ = v___x_1221_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1219_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
else
{
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_l_1500_; 
v_l_1500_ = lean_ctor_get(v___x_1401_, 3);
lean_inc(v_l_1500_);
if (lean_obj_tag(v_l_1500_) == 0)
{
lean_object* v_r_1501_; 
v_r_1501_ = lean_ctor_get(v___x_1401_, 4);
lean_inc(v_r_1501_);
if (lean_obj_tag(v_r_1501_) == 0)
{
lean_object* v_size_1502_; lean_object* v_k_1503_; lean_object* v_v_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1518_; 
v_size_1502_ = lean_ctor_get(v___x_1401_, 0);
v_k_1503_ = lean_ctor_get(v___x_1401_, 1);
v_v_1504_ = lean_ctor_get(v___x_1401_, 2);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1519_ = lean_ctor_get(v___x_1401_, 4);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v___x_1401_, 3);
lean_dec(v_unused_1520_);
v___x_1506_ = v___x_1401_;
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_v_1504_);
lean_inc(v_k_1503_);
lean_inc(v_size_1502_);
lean_dec(v___x_1401_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_size_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v_size_1508_ = lean_ctor_get(v_r_1501_, 0);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1502_);
lean_dec(v_size_1502_);
v___x_1511_ = lean_nat_add(v___x_1509_, v_size_1508_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v_r_1219_);
lean_ctor_set(v___x_1506_, 3, v_r_1501_);
lean_ctor_set(v___x_1506_, 2, v_v_1217_);
lean_ctor_set(v___x_1506_, 1, v_k_1216_);
lean_ctor_set(v___x_1506_, 0, v___x_1511_);
v___x_1513_ = v___x_1506_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_r_1501_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1219_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1513_);
lean_ctor_set(v___x_1221_, 3, v_l_1500_);
lean_ctor_set(v___x_1221_, 2, v_v_1504_);
lean_ctor_set(v___x_1221_, 1, v_k_1503_);
lean_ctor_set(v___x_1221_, 0, v___x_1510_);
v___x_1515_ = v___x_1221_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1503_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1504_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1500_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1534_; 
v_k_1521_ = lean_ctor_get(v___x_1401_, 1);
v_v_1522_ = lean_ctor_get(v___x_1401_, 2);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; 
v_unused_1535_ = lean_ctor_get(v___x_1401_, 4);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v___x_1401_, 3);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1537_);
v___x_1524_ = v___x_1401_;
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_v_1522_);
lean_inc(v_k_1521_);
lean_dec(v___x_1401_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1526_ = lean_unsigned_to_nat(3u);
v___x_1527_ = lean_unsigned_to_nat(1u);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 3, v_r_1501_);
lean_ctor_set(v___x_1524_, 2, v_v_1217_);
lean_ctor_set(v___x_1524_, 1, v_k_1216_);
lean_ctor_set(v___x_1524_, 0, v___x_1527_);
v___x_1529_ = v___x_1524_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_r_1501_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_r_1501_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1529_);
lean_ctor_set(v___x_1221_, 3, v_l_1500_);
lean_ctor_set(v___x_1221_, 2, v_v_1522_);
lean_ctor_set(v___x_1221_, 1, v_k_1521_);
lean_ctor_set(v___x_1221_, 0, v___x_1526_);
v___x_1531_ = v___x_1221_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1521_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1522_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1500_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_object* v_r_1538_; 
v_r_1538_ = lean_ctor_get(v___x_1401_, 4);
lean_inc(v_r_1538_);
if (lean_obj_tag(v_r_1538_) == 0)
{
lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1564_; 
v_k_1539_ = lean_ctor_get(v___x_1401_, 1);
v_v_1540_ = lean_ctor_get(v___x_1401_, 2);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; lean_object* v_unused_1566_; lean_object* v_unused_1567_; 
v_unused_1565_ = lean_ctor_get(v___x_1401_, 4);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v___x_1401_, 3);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1567_);
v___x_1542_ = v___x_1401_;
v_isShared_1543_ = v_isSharedCheck_1564_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_v_1540_);
lean_inc(v_k_1539_);
lean_dec(v___x_1401_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1564_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1560_; 
v_k_1544_ = lean_ctor_get(v_r_1538_, 1);
v_v_1545_ = lean_ctor_get(v_r_1538_, 2);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_r_1538_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; 
v_unused_1561_ = lean_ctor_get(v_r_1538_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_r_1538_, 3);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_r_1538_, 0);
lean_dec(v_unused_1563_);
v___x_1547_ = v_r_1538_;
v_isShared_1548_ = v_isSharedCheck_1560_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_v_1545_);
lean_inc(v_k_1544_);
lean_dec(v_r_1538_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1560_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = lean_unsigned_to_nat(3u);
v___x_1550_ = lean_unsigned_to_nat(1u);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v_l_1500_);
lean_ctor_set(v___x_1547_, 3, v_l_1500_);
lean_ctor_set(v___x_1547_, 2, v_v_1540_);
lean_ctor_set(v___x_1547_, 1, v_k_1539_);
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_l_1500_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_l_1500_);
v___x_1552_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 4, v_l_1500_);
lean_ctor_set(v___x_1542_, 2, v_v_1217_);
lean_ctor_set(v___x_1542_, 1, v_k_1216_);
lean_ctor_set(v___x_1542_, 0, v___x_1550_);
v___x_1554_ = v___x_1542_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_l_1500_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_l_1500_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1554_);
lean_ctor_set(v___x_1221_, 3, v___x_1552_);
lean_ctor_set(v___x_1221_, 2, v_v_1545_);
lean_ctor_set(v___x_1221_, 1, v_k_1544_);
lean_ctor_set(v___x_1221_, 0, v___x_1549_);
v___x_1556_ = v___x_1221_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_unsigned_to_nat(2u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_r_1538_);
lean_ctor_set(v___x_1221_, 3, v___x_1401_);
lean_ctor_set(v___x_1221_, 0, v___x_1568_);
v___x_1570_ = v___x_1221_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_r_1538_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_unsigned_to_nat(1u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1401_);
lean_ctor_set(v___x_1221_, 3, v___x_1401_);
lean_ctor_set(v___x_1221_, 0, v___x_1572_);
v___x_1574_ = v___x_1221_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v___x_1401_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_k_1212_);
lean_ctor_set(v___x_1578_, 2, v_v_1213_);
lean_ctor_set(v___x_1578_, 3, v_t_1214_);
lean_ctor_set(v___x_1578_, 4, v_t_1214_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1579_, lean_object* v_x_1580_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_l_1583_; lean_object* v_r_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_k_1581_ = lean_ctor_get(v_x_1580_, 1);
lean_inc(v_k_1581_);
v_v_1582_ = lean_ctor_get(v_x_1580_, 2);
lean_inc(v_v_1582_);
v_l_1583_ = lean_ctor_get(v_x_1580_, 3);
lean_inc(v_l_1583_);
v_r_1584_ = lean_ctor_get(v_x_1580_, 4);
lean_inc(v_r_1584_);
lean_dec_ref(v_x_1580_);
v___x_1585_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1579_, v_l_1583_);
v___x_1586_ = 1;
v___x_1587_ = l_Lean_Name_toString(v_k_1581_, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_v_1582_);
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1587_, v___x_1588_, v___x_1585_);
v_init_1579_ = v___x_1589_;
v_x_1580_ = v_r_1584_;
goto _start;
}
else
{
return v_init_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_box(1);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1592_, v_m_1591_);
v___x_1594_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
if (lean_obj_tag(v_a_1595_) == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_array_to_list(v_a_1596_);
return v___x_1597_;
}
else
{
lean_object* v_head_1598_; lean_object* v_tail_1599_; lean_object* v___x_1600_; 
v_head_1598_ = lean_ctor_get(v_a_1595_, 0);
lean_inc(v_head_1598_);
v_tail_1599_ = lean_ctor_get(v_a_1595_, 1);
lean_inc(v_tail_1599_);
lean_dec_ref(v_a_1595_);
v___x_1600_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1596_, v_head_1598_);
v_a_1595_ = v_tail_1599_;
v_a_1596_ = v___x_1600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1610_){
_start:
{
lean_object* v_idx_1611_; lean_object* v_name_1612_; lean_object* v_platform_1613_; lean_object* v_leanHash_1614_; uint64_t v_configHash_1615_; lean_object* v_options_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_idx_1611_ = lean_ctor_get(v_x_1610_, 0);
lean_inc(v_idx_1611_);
v_name_1612_ = lean_ctor_get(v_x_1610_, 1);
lean_inc(v_name_1612_);
v_platform_1613_ = lean_ctor_get(v_x_1610_, 2);
lean_inc_ref(v_platform_1613_);
v_leanHash_1614_ = lean_ctor_get(v_x_1610_, 3);
lean_inc_ref(v_leanHash_1614_);
v_configHash_1615_ = lean_ctor_get_uint64(v_x_1610_, sizeof(void*)*5);
v_options_1616_ = lean_ctor_get(v_x_1610_, 4);
lean_inc(v_options_1616_);
lean_dec_ref(v_x_1610_);
v___x_1617_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1618_ = l_Lean_JsonNumber_fromNat(v_idx_1611_);
v___x_1619_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1624_ = 1;
v___x_1625_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1612_, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1623_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v___x_1621_);
v___x_1629_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_platform_1613_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1621_);
v___x_1633_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_leanHash_1614_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1621_);
v___x_1637_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1638_ = l_Lake_lowerHexUInt64(v_configHash_1615_);
v___x_1639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1637_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1621_);
v___x_1642_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1643_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1616_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1621_);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1621_);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1641_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1636_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1632_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1628_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1622_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1653_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1651_, v___x_1652_);
v___x_1654_ = l_Lean_Json_mkObj(v___x_1653_);
lean_dec(v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1655_, lean_object* v_msg_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1658_, lean_object* v_k_1659_, lean_object* v_v_1660_, lean_object* v_t_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1659_, v_v_1660_, v_t_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1663_, lean_object* v_t_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1663_, v_t_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1668_, lean_object* v_k_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = l_Lean_Json_getObjValD(v_j_1668_, v_k_1669_);
v___x_1671_ = l_Lean_Json_getNat_x3f(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1672_, lean_object* v_k_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1672_, v_k_1673_);
lean_dec_ref(v_k_1673_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1675_, lean_object* v_k_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = l_Lean_Json_getObjValD(v_j_1675_, v_k_1676_);
v___x_1678_ = l_Lean_Name_fromJson_x3f(v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1679_, lean_object* v_k_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1679_, v_k_1680_);
lean_dec_ref(v_k_1680_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1682_, lean_object* v_k_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = l_Lean_Json_getObjValD(v_j_1682_, v_k_1683_);
v___x_1685_ = l_Lean_Json_getStr_x3f(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1686_, lean_object* v_k_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1686_, v_k_1687_);
lean_dec_ref(v_k_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1689_, lean_object* v_k_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = l_Lean_Json_getObjValD(v_j_1689_, v_k_1690_);
v___x_1692_ = l_Lake_Hash_fromJson_x3f(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1693_, v_k_1694_);
lean_dec_ref(v_k_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1699_, lean_object* v_x_1700_){
_start:
{
if (lean_obj_tag(v_x_1700_) == 0)
{
lean_object* v_k_1701_; lean_object* v_v_1702_; lean_object* v_l_1703_; lean_object* v_r_1704_; lean_object* v___x_1705_; 
v_k_1701_ = lean_ctor_get(v_x_1700_, 1);
lean_inc(v_k_1701_);
v_v_1702_ = lean_ctor_get(v_x_1700_, 2);
lean_inc(v_v_1702_);
v_l_1703_ = lean_ctor_get(v_x_1700_, 3);
lean_inc(v_l_1703_);
v_r_1704_ = lean_ctor_get(v_x_1700_, 4);
lean_inc(v_r_1704_);
lean_dec_ref(v_x_1700_);
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1699_, v_l_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec(v_r_1704_);
lean_dec(v_v_1702_);
lean_dec(v_k_1701_);
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1746_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1746_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1746_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1711_ = lean_string_dec_eq(v_k_1701_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v_n_1712_; uint8_t v___x_1713_; 
lean_inc(v_k_1701_);
v_n_1712_ = l_String_toName(v_k_1701_);
v___x_1713_ = l_Lean_Name_isAnonymous(v_n_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_del_object(v___x_1708_);
lean_dec(v_k_1701_);
v___x_1714_ = l_Lean_Json_getStr_x3f(v_v_1702_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_n_1712_);
lean_dec(v_a_1706_);
lean_dec(v_r_1704_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___x_1714_);
v___x_1724_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1712_, v_a_1723_, v_a_1706_);
v_init_1699_ = v___x_1724_;
v_x_1700_ = v_r_1704_;
goto _start;
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_dec(v_n_1712_);
lean_dec(v_a_1706_);
lean_dec(v_r_1704_);
lean_dec(v_v_1702_);
v___x_1726_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1727_ = lean_string_append(v___x_1726_, v_k_1701_);
lean_dec(v_k_1701_);
v___x_1728_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1729_);
v___x_1731_ = v___x_1708_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
lean_object* v___x_1733_; 
lean_del_object(v___x_1708_);
lean_dec(v_k_1701_);
v___x_1733_ = l_Lean_Json_getStr_x3f(v_v_1702_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_a_1706_);
lean_dec(v_r_1704_);
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1733_);
v___x_1743_ = lean_box(0);
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1743_, v_a_1742_, v_a_1706_);
v_init_1699_ = v___x_1744_;
v_x_1700_ = v_r_1704_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_init_1699_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1749_){
_start:
{
if (lean_obj_tag(v_x_1749_) == 5)
{
lean_object* v_kvPairs_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_kvPairs_1750_ = lean_ctor_get(v_x_1749_, 0);
lean_inc(v_kvPairs_1750_);
lean_dec_ref(v_x_1749_);
v___x_1751_ = lean_box(1);
v___x_1752_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1751_, v_kvPairs_1750_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1753_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1754_ = lean_unsigned_to_nat(80u);
v___x_1755_ = l_Lean_Json_pretty(v_x_1749_, v___x_1754_);
v___x_1756_ = lean_string_append(v___x_1753_, v___x_1755_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1760_, lean_object* v_k_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = l_Lean_Json_getObjValD(v_j_1760_, v_k_1761_);
v___x_1763_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1764_, lean_object* v_k_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1764_, v_k_1765_);
lean_dec_ref(v_k_1765_);
return v_res_1766_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = 1;
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1796_, v___x_1795_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1800_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1801_ = lean_string_append(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = 1;
v___x_1805_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1806_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1808_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1809_ = lean_string_append(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1812_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1813_ = lean_string_append(v___x_1812_, v___x_1811_);
return v___x_1813_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = 1;
v___x_1817_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1820_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1821_ = lean_string_append(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1823_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1824_ = lean_string_append(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = 1;
v___x_1828_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1829_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1828_, v___x_1827_);
return v___x_1829_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1831_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1832_ = lean_string_append(v___x_1831_, v___x_1830_);
return v___x_1832_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1834_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1835_ = lean_string_append(v___x_1834_, v___x_1833_);
return v___x_1835_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = 1;
v___x_1839_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1840_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1842_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1843_ = lean_string_append(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1845_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1846_ = lean_string_append(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = 1;
v___x_1850_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1853_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1854_ = lean_string_append(v___x_1853_, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1856_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1857_ = lean_string_append(v___x_1856_, v___x_1855_);
return v___x_1857_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = 1;
v___x_1861_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1861_, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1864_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1865_ = lean_string_append(v___x_1864_, v___x_1863_);
return v___x_1865_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1867_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1868_ = lean_string_append(v___x_1867_, v___x_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1869_);
v___x_1871_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1869_, v___x_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_json_1869_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1881_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1876_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_1877_ = lean_string_append(v___x_1876_, v_a_1872_);
lean_dec(v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_json_1869_);
v_a_1882_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1871_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1871_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 0);
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1890_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1871_);
v___x_1891_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1869_);
v___x_1892_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1869_, v___x_1891_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1897_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_1898_ = lean_string_append(v___x_1897_, v_a_1893_);
lean_dec(v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1903_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1892_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1892_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 0);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_a_1911_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1892_);
v___x_1912_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1869_);
v___x_1913_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1869_, v___x_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1918_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1919_ = lean_string_append(v___x_1918_, v_a_1914_);
lean_dec(v_a_1914_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1919_);
v___x_1921_ = v___x_1916_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
else
{
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1924_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1913_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1913_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 0);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_a_1932_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1913_);
v___x_1933_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1869_);
v___x_1934_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1869_, v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1939_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
v___x_1940_ = lean_string_append(v___x_1939_, v_a_1935_);
lean_dec(v_a_1935_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1940_);
v___x_1942_ = v___x_1937_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1945_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1934_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1934_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 0);
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1953_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1934_);
v___x_1954_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1869_);
v___x_1955_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1869_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1965_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1965_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1960_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
v___x_1961_ = lean_string_append(v___x_1960_, v_a_1956_);
lean_dec(v_a_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1961_);
v___x_1963_ = v___x_1958_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_json_1869_);
v_a_1966_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1955_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1955_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 0);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_a_1974_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1955_);
v___x_1975_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1976_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1869_, v___x_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_a_1974_);
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1981_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_1982_ = lean_string_append(v___x_1981_, v_a_1977_);
lean_dec(v_a_1977_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1982_);
v___x_1984_ = v___x_1979_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_a_1974_);
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
v_a_1987_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1976_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1976_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 0);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2004_; 
v_a_1995_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1997_ = v___x_1976_;
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1976_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; uint64_t v___x_2000_; lean_object* v___x_2002_; 
v___x_1999_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1999_, 0, v_a_1890_);
lean_ctor_set(v___x_1999_, 1, v_a_1911_);
lean_ctor_set(v___x_1999_, 2, v_a_1932_);
lean_ctor_set(v___x_1999_, 3, v_a_1953_);
lean_ctor_set(v___x_1999_, 4, v_a_1995_);
v___x_2000_ = lean_unbox_uint64(v_a_1974_);
lean_dec(v_a_1974_);
lean_ctor_set_uint64(v___x_1999_, sizeof(void*)*5, v___x_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1999_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_importConfigFile___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_2009_ = lean_mk_io_user_error(v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_2010_, lean_object* v___x_2011_, lean_object* v_h_2012_){
_start:
{
uint8_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = 1;
v___x_2015_ = lean_io_prim_handle_mk(v___x_2010_, v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v___x_2017_ = 1;
v___x_2018_ = lean_io_prim_handle_try_lock(v_a_2016_, v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; uint8_t v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = lean_unbox(v_a_2019_);
lean_dec(v_a_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v_a_2016_);
v___x_2021_ = lean_io_prim_handle_unlock(v_h_2012_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2029_; 
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2021_, 0);
lean_dec(v_unused_2030_);
v___x_2023_ = v___x_2021_;
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v___x_2021_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 1);
lean_ctor_set(v___x_2023_, 0, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_a_2031_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2021_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2021_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_io_prim_handle_unlock(v_h_2012_);
if (lean_obj_tag(v___x_2039_) == 0)
{
uint8_t v___x_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v___x_2039_);
v___x_2040_ = 3;
v___x_2041_ = lean_io_prim_handle_mk(v___x_2011_, v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
v___x_2043_ = lean_io_prim_handle_lock(v_a_2042_, v___x_2017_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v___x_2044_; 
lean_dec_ref(v___x_2043_);
v___x_2044_ = lean_io_prim_handle_unlock(v_a_2016_);
lean_dec(v_a_2016_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2052_);
v___x_2046_ = v___x_2044_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v_a_2042_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2042_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2042_);
v_a_2053_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2044_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2044_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_2042_);
lean_dec(v_a_2016_);
v_a_2061_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2043_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2043_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_dec(v_a_2016_);
return v___x_2041_;
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_2016_);
v_a_2069_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2039_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2039_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_2016_);
v_a_2077_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2018_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2018_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2085_, lean_object* v___x_2086_, lean_object* v_h_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lake_importConfigFile___lam__0(v___x_2085_, v___x_2086_, v_h_2087_);
lean_dec(v_h_2087_);
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2085_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2114_; lean_object* v_a_2115_; lean_object* v_lakeEnv_2117_; lean_object* v_pkgIdx_2118_; lean_object* v_pkgName_2119_; lean_object* v_pkgDir_2120_; lean_object* v_configFile_2121_; lean_object* v_lakeOpts_2122_; lean_object* v_leanOpts_2123_; uint8_t v_reconfigure_2124_; lean_object* v___x_2125_; 
v_lakeEnv_2117_ = lean_ctor_get(v_cfg_2102_, 0);
lean_inc_ref(v_lakeEnv_2117_);
v_pkgIdx_2118_ = lean_ctor_get(v_cfg_2102_, 3);
lean_inc(v_pkgIdx_2118_);
v_pkgName_2119_ = lean_ctor_get(v_cfg_2102_, 4);
lean_inc(v_pkgName_2119_);
v_pkgDir_2120_ = lean_ctor_get(v_cfg_2102_, 6);
lean_inc_ref(v_pkgDir_2120_);
v_configFile_2121_ = lean_ctor_get(v_cfg_2102_, 8);
lean_inc_ref_n(v_configFile_2121_, 2);
v_lakeOpts_2122_ = lean_ctor_get(v_cfg_2102_, 12);
lean_inc(v_lakeOpts_2122_);
v_leanOpts_2123_ = lean_ctor_get(v_cfg_2102_, 13);
lean_inc_ref(v_leanOpts_2123_);
v_reconfigure_2124_ = lean_ctor_get_uint8(v_cfg_2102_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2102_);
v___x_2125_ = l_System_FilePath_fileName(v_configFile_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___x_2126_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2127_ = lean_array_get_size(v_a_2103_);
v___x_2128_ = lean_array_push(v_a_2103_, v___x_2126_);
v___x_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v_val_2130_; uint8_t v___x_2131_; lean_object* v_pkgName_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_configDir_2137_; lean_object* v___x_2138_; 
v_val_2130_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2130_);
lean_dec_ref(v___x_2125_);
v___x_2131_ = 0;
lean_inc(v_pkgName_2119_);
v_pkgName_2132_ = l_Lean_Name_toString(v_pkgName_2119_, v___x_2131_);
v___x_2133_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_pkgDir_2120_);
v___x_2134_ = l_Lake_joinRelative(v_pkgDir_2120_, v___x_2133_);
v___x_2135_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
lean_inc_ref(v___x_2134_);
v___x_2136_ = l_Lake_joinRelative(v___x_2134_, v___x_2135_);
v_configDir_2137_ = l_Lake_joinRelative(v___x_2136_, v_pkgName_2132_);
lean_inc_ref(v_configDir_2137_);
v___x_2138_ = l_IO_FS_createDirAll(v_configDir_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref(v___x_2138_);
v___x_2139_ = l_Lake_computeTextFileHash(v_configFile_2121_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_h_2148_; lean_object* v_lakeOpts_2149_; lean_object* v___y_2150_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v_h_2305_; lean_object* v___y_2306_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2130_, 2);
v___x_2142_ = l_System_FilePath_withExtension(v_val_2130_, v___x_2141_);
lean_inc_ref_n(v_configDir_2137_, 2);
v___x_2143_ = l_Lake_joinRelative(v_configDir_2137_, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2145_ = l_System_FilePath_withExtension(v_val_2130_, v___x_2144_);
v___x_2146_ = l_Lake_joinRelative(v_configDir_2137_, v___x_2145_);
v___x_2286_ = l_System_FilePath_pathExists(v___x_2146_);
v___x_2287_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2288_ = l_System_FilePath_withExtension(v_val_2130_, v___x_2287_);
v___x_2289_ = l_Lake_joinRelative(v_configDir_2137_, v___x_2288_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = l_IO_FS_createDirAll(v___x_2134_);
if (lean_obj_tag(v___x_2390_) == 0)
{
uint8_t v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref(v___x_2390_);
v___x_2391_ = 2;
v___x_2392_ = lean_io_prim_handle_mk(v___x_2146_, v___x_2391_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref(v___x_2289_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref(v___x_2392_);
v___x_2394_ = 1;
v___x_2395_ = lean_io_prim_handle_lock(v_a_2393_, v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_dec_ref(v___x_2395_);
v_h_2148_ = v_a_2393_;
v_lakeOpts_2149_ = v_lakeOpts_2122_;
v___y_2150_ = v_a_2103_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec(v_a_2393_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = lean_io_error_to_string(v_a_2396_);
v___x_2398_ = 3;
v___x_2399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1, v___x_2398_);
v___x_2400_ = lean_array_get_size(v_a_2103_);
v___x_2401_ = lean_array_push(v_a_2103_, v___x_2399_);
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
return v___x_2402_;
}
}
else
{
lean_object* v_a_2403_; 
v_a_2403_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2392_);
if (lean_obj_tag(v_a_2403_) == 0)
{
uint8_t v___x_2404_; lean_object* v___x_2405_; 
lean_dec_ref(v_a_2403_);
v___x_2404_ = 0;
v___x_2405_ = lean_io_prim_handle_mk(v___x_2146_, v___x_2404_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref(v___x_2405_);
v_h_2305_ = v_a_2406_;
v___y_2306_ = v_a_2103_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2407_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2405_);
v___x_2408_ = lean_io_error_to_string(v_a_2407_);
v___x_2409_ = 3;
v___x_2410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*1, v___x_2409_);
v___x_2411_ = lean_array_get_size(v_a_2103_);
v___x_2412_ = lean_array_push(v_a_2103_, v___x_2410_);
v___x_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___x_2414_ = lean_io_error_to_string(v_a_2403_);
v___x_2415_ = 3;
v___x_2416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*1, v___x_2415_);
v___x_2417_ = lean_array_get_size(v_a_2103_);
v___x_2418_ = lean_array_push(v_a_2103_, v___x_2416_);
v___x_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2417_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
return v___x_2419_;
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2420_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2420_);
lean_dec_ref(v___x_2390_);
v___x_2421_ = lean_io_error_to_string(v_a_2420_);
v___x_2422_ = 3;
v___x_2423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1, v___x_2422_);
v___x_2424_ = lean_array_get_size(v_a_2103_);
v___x_2425_ = lean_array_push(v_a_2103_, v___x_2423_);
v___x_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
return v___x_2426_;
}
}
else
{
uint8_t v___x_2427_; lean_object* v___x_2428_; 
lean_dec_ref(v___x_2134_);
v___x_2427_ = 0;
v___x_2428_ = lean_io_prim_handle_mk(v___x_2146_, v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2428_);
v_h_2305_ = v_a_2429_;
v___y_2306_ = v_a_2103_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2430_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2428_);
v___x_2431_ = lean_io_error_to_string(v_a_2430_);
v___x_2432_ = 3;
v___x_2433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set_uint8(v___x_2433_, sizeof(void*)*1, v___x_2432_);
v___x_2434_ = lean_array_get_size(v_a_2103_);
v___x_2435_ = lean_array_push(v_a_2103_, v___x_2433_);
v___x_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
return v___x_2436_;
}
}
v___jp_2147_:
{
lean_object* v___x_2151_; 
v___x_2151_ = lean_io_remove_file(v___x_2143_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint64_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v___x_2151_);
lean_dec_ref(v___x_2146_);
v___x_2152_ = l_System_Platform_target;
v___x_2153_ = l_Lake_Env_leanGithash(v_lakeEnv_2117_);
lean_dec_ref(v_lakeEnv_2117_);
lean_inc(v_lakeOpts_2149_);
lean_inc(v_pkgName_2119_);
lean_inc(v_pkgIdx_2118_);
v___x_2154_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2154_, 0, v_pkgIdx_2118_);
lean_ctor_set(v___x_2154_, 1, v_pkgName_2119_);
lean_ctor_set(v___x_2154_, 2, v___x_2152_);
lean_ctor_set(v___x_2154_, 3, v___x_2153_);
lean_ctor_set(v___x_2154_, 4, v_lakeOpts_2149_);
v___x_2155_ = lean_unbox_uint64(v_a_2140_);
lean_dec(v_a_2140_);
lean_ctor_set_uint64(v___x_2154_, sizeof(void*)*5, v___x_2155_);
v___x_2156_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2154_);
v___x_2157_ = lean_unsigned_to_nat(80u);
v___x_2158_ = l_Lean_Json_pretty(v___x_2156_, v___x_2157_);
v___x_2159_ = l_IO_FS_Handle_putStrLn(v_h_2148_, v___x_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref(v___x_2159_);
v___x_2160_ = lean_io_prim_handle_truncate(v_h_2148_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2161_; 
lean_dec_ref(v___x_2160_);
v___x_2161_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2118_, v_pkgName_2119_, v_pkgDir_2120_, v_lakeOpts_2149_, v_leanOpts_2123_, v_configFile_2121_, v___y_2150_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v_a_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
v_a_2163_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_a_2163_);
v___x_2164_ = 1;
v___x_2165_ = l_Lean_writeModule(v_a_2162_, v___x_2143_, v___x_2164_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; 
lean_dec_ref(v___x_2165_);
v___x_2166_ = lean_io_prim_handle_unlock(v_h_2148_);
lean_dec(v_h_2148_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_dec_ref(v___x_2166_);
lean_dec(v_a_2163_);
return v___x_2161_;
}
else
{
lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2179_; 
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; 
v_unused_2180_ = lean_ctor_get(v___x_2161_, 1);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v___x_2161_, 0);
lean_dec(v_unused_2181_);
v___x_2168_ = v___x_2161_;
v_isShared_2169_ = v_isSharedCheck_2179_;
goto v_resetjp_2167_;
}
else
{
lean_dec(v___x_2161_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2179_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_a_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v___x_2166_);
v___x_2171_ = lean_io_error_to_string(v_a_2170_);
v___x_2172_ = 3;
v___x_2173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*1, v___x_2172_);
v___x_2174_ = lean_array_get_size(v_a_2163_);
v___x_2175_ = lean_array_push(v_a_2163_, v___x_2173_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set_tag(v___x_2168_, 1);
lean_ctor_set(v___x_2168_, 1, v___x_2175_);
lean_ctor_set(v___x_2168_, 0, v___x_2174_);
v___x_2177_ = v___x_2168_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_h_2148_);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; lean_object* v_unused_2196_; 
v_unused_2195_ = lean_ctor_get(v___x_2161_, 1);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v___x_2161_, 0);
lean_dec(v_unused_2196_);
v___x_2183_ = v___x_2161_;
v_isShared_2184_ = v_isSharedCheck_2194_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v___x_2161_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2194_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_a_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v_a_2185_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2165_);
v___x_2186_ = lean_io_error_to_string(v_a_2185_);
v___x_2187_ = 3;
v___x_2188_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set_uint8(v___x_2188_, sizeof(void*)*1, v___x_2187_);
v___x_2189_ = lean_array_get_size(v_a_2163_);
v___x_2190_ = lean_array_push(v_a_2163_, v___x_2188_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set_tag(v___x_2183_, 1);
lean_ctor_set(v___x_2183_, 1, v___x_2190_);
lean_ctor_set(v___x_2183_, 0, v___x_2189_);
v___x_2192_ = v___x_2183_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_dec(v_h_2148_);
lean_dec_ref(v___x_2143_);
return v___x_2161_;
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v_lakeOpts_2149_);
lean_dec(v_h_2148_);
lean_dec_ref(v___x_2143_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2197_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2197_);
lean_dec_ref(v___x_2160_);
v___x_2198_ = lean_io_error_to_string(v_a_2197_);
v___x_2199_ = 3;
v___x_2200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*1, v___x_2199_);
v___x_2201_ = lean_array_get_size(v___y_2150_);
v___x_2202_ = lean_array_push(v___y_2150_, v___x_2200_);
v___x_2203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
return v___x_2203_;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec(v_lakeOpts_2149_);
lean_dec(v_h_2148_);
lean_dec_ref(v___x_2143_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2204_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2159_);
v___x_2205_ = lean_io_error_to_string(v_a_2204_);
v___x_2206_ = 3;
v___x_2207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2206_);
v___x_2208_ = lean_array_get_size(v___y_2150_);
v___x_2209_ = lean_array_push(v___y_2150_, v___x_2207_);
v___x_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
return v___x_2210_;
}
}
else
{
lean_object* v_a_2211_; 
v_a_2211_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2151_);
if (lean_obj_tag(v_a_2211_) == 11)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint64_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v_a_2211_);
lean_dec_ref(v___x_2146_);
v___x_2212_ = l_System_Platform_target;
v___x_2213_ = l_Lake_Env_leanGithash(v_lakeEnv_2117_);
lean_dec_ref(v_lakeEnv_2117_);
lean_inc(v_lakeOpts_2149_);
lean_inc(v_pkgName_2119_);
lean_inc(v_pkgIdx_2118_);
v___x_2214_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2214_, 0, v_pkgIdx_2118_);
lean_ctor_set(v___x_2214_, 1, v_pkgName_2119_);
lean_ctor_set(v___x_2214_, 2, v___x_2212_);
lean_ctor_set(v___x_2214_, 3, v___x_2213_);
lean_ctor_set(v___x_2214_, 4, v_lakeOpts_2149_);
v___x_2215_ = lean_unbox_uint64(v_a_2140_);
lean_dec(v_a_2140_);
lean_ctor_set_uint64(v___x_2214_, sizeof(void*)*5, v___x_2215_);
v___x_2216_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2214_);
v___x_2217_ = lean_unsigned_to_nat(80u);
v___x_2218_ = l_Lean_Json_pretty(v___x_2216_, v___x_2217_);
v___x_2219_ = l_IO_FS_Handle_putStrLn(v_h_2148_, v___x_2218_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref(v___x_2219_);
v___x_2220_ = lean_io_prim_handle_truncate(v_h_2148_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref(v___x_2220_);
v___x_2221_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2118_, v_pkgName_2119_, v_pkgDir_2120_, v_lakeOpts_2149_, v_leanOpts_2123_, v_configFile_2121_, v___y_2150_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_a_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
v_a_2223_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_a_2223_);
v___x_2224_ = 1;
v___x_2225_ = l_Lean_writeModule(v_a_2222_, v___x_2143_, v___x_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v___x_2225_);
v___x_2226_ = lean_io_prim_handle_unlock(v_h_2148_);
lean_dec(v_h_2148_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2223_);
return v___x_2221_;
}
else
{
lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2239_; 
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; lean_object* v_unused_2241_; 
v_unused_2240_ = lean_ctor_get(v___x_2221_, 1);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v___x_2221_, 0);
lean_dec(v_unused_2241_);
v___x_2228_ = v___x_2221_;
v_isShared_2229_ = v_isSharedCheck_2239_;
goto v_resetjp_2227_;
}
else
{
lean_dec(v___x_2221_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2239_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_a_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2226_);
v___x_2231_ = lean_io_error_to_string(v_a_2230_);
v___x_2232_ = 3;
v___x_2233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2233_, 0, v___x_2231_);
lean_ctor_set_uint8(v___x_2233_, sizeof(void*)*1, v___x_2232_);
v___x_2234_ = lean_array_get_size(v_a_2223_);
v___x_2235_ = lean_array_push(v_a_2223_, v___x_2233_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set_tag(v___x_2228_, 1);
lean_ctor_set(v___x_2228_, 1, v___x_2235_);
lean_ctor_set(v___x_2228_, 0, v___x_2234_);
v___x_2237_ = v___x_2228_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_h_2148_);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; lean_object* v_unused_2256_; 
v_unused_2255_ = lean_ctor_get(v___x_2221_, 1);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v___x_2221_, 0);
lean_dec(v_unused_2256_);
v___x_2243_ = v___x_2221_;
v_isShared_2244_ = v_isSharedCheck_2254_;
goto v_resetjp_2242_;
}
else
{
lean_dec(v___x_2221_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2254_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_a_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v_a_2245_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2225_);
v___x_2246_ = lean_io_error_to_string(v_a_2245_);
v___x_2247_ = 3;
v___x_2248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1, v___x_2247_);
v___x_2249_ = lean_array_get_size(v_a_2223_);
v___x_2250_ = lean_array_push(v_a_2223_, v___x_2248_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 1);
lean_ctor_set(v___x_2243_, 1, v___x_2250_);
lean_ctor_set(v___x_2243_, 0, v___x_2249_);
v___x_2252_ = v___x_2243_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_dec(v_h_2148_);
lean_dec_ref(v___x_2143_);
return v___x_2221_;
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v_lakeOpts_2149_);
lean_dec(v_h_2148_);
lean_dec_ref(v___x_2143_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2257_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2220_);
v___x_2258_ = lean_io_error_to_string(v_a_2257_);
v___x_2259_ = 3;
v___x_2260_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set_uint8(v___x_2260_, sizeof(void*)*1, v___x_2259_);
v___x_2261_ = lean_array_get_size(v___y_2150_);
v___x_2262_ = lean_array_push(v___y_2150_, v___x_2260_);
v___x_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
return v___x_2263_;
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_lakeOpts_2149_);
lean_dec(v_h_2148_);
lean_dec_ref(v___x_2143_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2264_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2219_);
v___x_2265_ = lean_io_error_to_string(v_a_2264_);
v___x_2266_ = 3;
v___x_2267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*1, v___x_2266_);
v___x_2268_ = lean_array_get_size(v___y_2150_);
v___x_2269_ = lean_array_push(v___y_2150_, v___x_2267_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
return v___x_2270_;
}
}
else
{
lean_object* v___x_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec(v_lakeOpts_2149_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___x_2271_ = lean_io_error_to_string(v_a_2211_);
v___x_2272_ = 3;
v___x_2273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*1, v___x_2272_);
v___x_2274_ = lean_array_get_size(v___y_2150_);
v___x_2275_ = lean_array_push(v___y_2150_, v___x_2273_);
v___x_2276_ = lean_io_prim_handle_unlock(v_h_2148_);
lean_dec(v_h_2148_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; 
lean_dec_ref(v___x_2276_);
v___x_2277_ = lean_io_remove_file(v___x_2146_);
lean_dec_ref(v___x_2146_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref(v___x_2277_);
v___y_2114_ = v___x_2274_;
v_a_2115_ = v___x_2275_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = lean_io_error_to_string(v_a_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set_uint8(v___x_2280_, sizeof(void*)*1, v___x_2272_);
v___x_2281_ = lean_array_push(v___x_2275_, v___x_2280_);
v___y_2114_ = v___x_2274_;
v_a_2115_ = v___x_2281_;
goto v___jp_2113_;
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v___x_2146_);
v_a_2282_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2276_);
v___x_2283_ = lean_io_error_to_string(v_a_2282_);
v___x_2284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*1, v___x_2272_);
v___x_2285_ = lean_array_push(v___x_2275_, v___x_2284_);
v___y_2114_ = v___x_2274_;
v_a_2115_ = v___x_2285_;
goto v___jp_2113_;
}
}
}
}
v___jp_2290_:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lake_importConfigFile___lam__0(v___x_2289_, v___x_2146_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___x_2289_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_options_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v_options_2296_ = lean_ctor_get(v___y_2292_, 4);
lean_inc(v_options_2296_);
lean_dec_ref(v___y_2292_);
v_h_2148_ = v_a_2295_;
v_lakeOpts_2149_ = v_options_2296_;
v___y_2150_ = v___y_2291_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2297_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2294_);
v___x_2298_ = lean_io_error_to_string(v_a_2297_);
v___x_2299_ = 3;
v___x_2300_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1, v___x_2299_);
v___x_2301_ = lean_array_get_size(v___y_2291_);
v___x_2302_ = lean_array_push(v___y_2291_, v___x_2300_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
return v___x_2303_;
}
}
v___jp_2304_:
{
if (v_reconfigure_2124_ == 0)
{
lean_object* v___x_2307_; 
lean_dec(v_lakeOpts_2122_);
v___x_2307_ = lean_io_prim_handle_lock(v_h_2305_, v___x_2131_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2308_; 
lean_dec_ref(v___x_2307_);
v___x_2308_ = l_IO_FS_Handle_readToEnd(v_h_2305_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = ((lean_object*)(l_Lake_importConfigFile___closed__6));
v___x_2311_ = l_Lean_Json_parse(v_a_2309_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v___x_2311_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___x_2312_ = ((lean_object*)(l_Lake_importConfigFile___closed__7));
v___x_2313_ = lean_array_get_size(v___y_2306_);
v___x_2314_ = lean_array_push(v___y_2306_, v___x_2312_);
v___x_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
return v___x_2315_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2311_, 0);
lean_inc_n(v_a_2316_, 2);
lean_dec_ref(v___x_2311_);
v___x_2317_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v___x_2318_; 
lean_dec_ref(v___x_2317_);
v___x_2318_ = l_Lean_Json_getObj_x3f(v_a_2316_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_dec_ref(v___x_2318_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___y_2106_ = v___y_2306_;
v___y_2107_ = v___x_2310_;
goto v___jp_2105_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2321_ = l_Lake_JsonObject_getJson_x3f(v_a_2319_, v___x_2320_);
lean_dec(v_a_2319_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___y_2106_ = v___y_2306_;
v___y_2107_ = v___x_2310_;
goto v___jp_2105_;
}
else
{
lean_object* v_val_2322_; lean_object* v___x_2323_; 
v_val_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_dec_ref(v___x_2323_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___y_2106_ = v___y_2306_;
v___y_2107_ = v___x_2310_;
goto v___jp_2105_;
}
else
{
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_dec_ref(v___x_2323_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___y_2106_ = v___y_2306_;
v___y_2107_ = v___x_2310_;
goto v___jp_2105_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = l_Lake_importConfigFile___lam__0(v___x_2289_, v___x_2146_, v_h_2305_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v_h_2148_ = v_a_2326_;
v_lakeOpts_2149_ = v_a_2324_;
v___y_2150_ = v___y_2306_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec(v_a_2324_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2327_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2325_);
v___x_2328_ = lean_io_error_to_string(v_a_2327_);
v___x_2329_ = 3;
v___x_2330_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*1, v___x_2329_);
v___x_2331_ = lean_array_get_size(v___y_2306_);
v___x_2332_ = lean_array_push(v___y_2306_, v___x_2330_);
v___x_2333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
return v___x_2333_;
}
}
}
}
}
}
else
{
lean_object* v_a_2334_; uint8_t v___x_2335_; 
lean_dec(v_a_2316_);
v_a_2334_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2317_);
v___x_2335_ = l_System_FilePath_pathExists(v___x_2143_);
if (v___x_2335_ == 0)
{
v___y_2291_ = v___y_2306_;
v___y_2292_ = v_a_2334_;
v___y_2293_ = v_h_2305_;
goto v___jp_2290_;
}
else
{
lean_object* v_idx_2336_; lean_object* v_name_2337_; lean_object* v_platform_2338_; lean_object* v_leanHash_2339_; uint64_t v_configHash_2340_; uint8_t v___x_2341_; 
v_idx_2336_ = lean_ctor_get(v_a_2334_, 0);
v_name_2337_ = lean_ctor_get(v_a_2334_, 1);
v_platform_2338_ = lean_ctor_get(v_a_2334_, 2);
v_leanHash_2339_ = lean_ctor_get(v_a_2334_, 3);
v_configHash_2340_ = lean_ctor_get_uint64(v_a_2334_, sizeof(void*)*5);
v___x_2341_ = lean_nat_dec_eq(v_idx_2336_, v_pkgIdx_2118_);
if (v___x_2341_ == 0)
{
v___y_2291_ = v___y_2306_;
v___y_2292_ = v_a_2334_;
v___y_2293_ = v_h_2305_;
goto v___jp_2290_;
}
else
{
uint8_t v___x_2342_; 
v___x_2342_ = lean_name_eq(v_name_2337_, v_pkgName_2119_);
if (v___x_2342_ == 0)
{
v___y_2291_ = v___y_2306_;
v___y_2292_ = v_a_2334_;
v___y_2293_ = v_h_2305_;
goto v___jp_2290_;
}
else
{
uint64_t v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_unbox_uint64(v_a_2140_);
v___x_2344_ = lean_uint64_dec_eq(v_configHash_2340_, v___x_2343_);
if (v___x_2344_ == 0)
{
v___y_2291_ = v___y_2306_;
v___y_2292_ = v_a_2334_;
v___y_2293_ = v_h_2305_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = l_System_Platform_target;
v___x_2346_ = lean_string_dec_eq(v_platform_2338_, v___x_2345_);
if (v___x_2346_ == 0)
{
v___y_2291_ = v___y_2306_;
v___y_2292_ = v_a_2334_;
v___y_2293_ = v_h_2305_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = l_Lake_Env_leanGithash(v_lakeEnv_2117_);
v___x_2348_ = lean_string_dec_eq(v_leanHash_2339_, v___x_2347_);
lean_dec_ref(v___x_2347_);
if (v___x_2348_ == 0)
{
v___y_2291_ = v___y_2306_;
v___y_2292_ = v_a_2334_;
v___y_2293_ = v_h_2305_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2349_; 
lean_dec(v_a_2334_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec(v_a_2140_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v___x_2349_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2143_, v_leanOpts_2123_);
lean_dec_ref(v___x_2143_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = lean_io_prim_handle_unlock(v_h_2305_);
lean_dec(v_h_2305_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref(v___x_2351_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_a_2350_);
lean_ctor_set(v___x_2352_, 1, v___y_2306_);
return v___x_2352_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_a_2350_);
v_a_2353_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2351_);
v___x_2354_ = lean_io_error_to_string(v_a_2353_);
v___x_2355_ = 3;
v___x_2356_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1, v___x_2355_);
v___x_2357_ = lean_array_get_size(v___y_2306_);
v___x_2358_ = lean_array_push(v___y_2306_, v___x_2356_);
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
return v___x_2359_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v_h_2305_);
v_a_2360_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2360_);
lean_dec_ref(v___x_2349_);
v___x_2361_ = lean_io_error_to_string(v_a_2360_);
v___x_2362_ = 3;
v___x_2363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*1, v___x_2362_);
v___x_2364_ = lean_array_get_size(v___y_2306_);
v___x_2365_ = lean_array_push(v___y_2306_, v___x_2363_);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
return v___x_2366_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2367_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2367_);
lean_dec_ref(v___x_2308_);
v___x_2368_ = lean_io_error_to_string(v_a_2367_);
v___x_2369_ = 3;
v___x_2370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set_uint8(v___x_2370_, sizeof(void*)*1, v___x_2369_);
v___x_2371_ = lean_array_get_size(v___y_2306_);
v___x_2372_ = lean_array_push(v___y_2306_, v___x_2370_);
v___x_2373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
return v___x_2373_;
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2374_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2307_);
v___x_2375_ = lean_io_error_to_string(v_a_2374_);
v___x_2376_ = 3;
v___x_2377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*1, v___x_2376_);
v___x_2378_ = lean_array_get_size(v___y_2306_);
v___x_2379_ = lean_array_push(v___y_2306_, v___x_2377_);
v___x_2380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
return v___x_2380_;
}
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lake_importConfigFile___lam__0(v___x_2289_, v___x_2146_, v_h_2305_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2289_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref(v___x_2381_);
v_h_2148_ = v_a_2382_;
v_lakeOpts_2149_ = v_lakeOpts_2122_;
v___y_2150_ = v___y_2306_;
goto v___jp_2147_;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2143_);
lean_dec(v_a_2140_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2383_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2381_);
v___x_2384_ = lean_io_error_to_string(v_a_2383_);
v___x_2385_ = 3;
v___x_2386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1, v___x_2385_);
v___x_2387_ = lean_array_get_size(v___y_2306_);
v___x_2388_ = lean_array_push(v___y_2306_, v___x_2386_);
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec_ref(v_configDir_2137_);
lean_dec_ref(v___x_2134_);
lean_dec(v_val_2130_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2437_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v___x_2139_);
v___x_2438_ = lean_io_error_to_string(v_a_2437_);
v___x_2439_ = 3;
v___x_2440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*1, v___x_2439_);
v___x_2441_ = lean_array_get_size(v_a_2103_);
v___x_2442_ = lean_array_push(v_a_2103_, v___x_2440_);
v___x_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
return v___x_2443_;
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_configDir_2137_);
lean_dec_ref(v___x_2134_);
lean_dec(v_val_2130_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2117_);
v_a_2444_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2444_);
lean_dec_ref(v___x_2138_);
v___x_2445_ = lean_io_error_to_string(v_a_2444_);
v___x_2446_ = 3;
v___x_2447_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set_uint8(v___x_2447_, sizeof(void*)*1, v___x_2446_);
v___x_2448_ = lean_array_get_size(v_a_2103_);
v___x_2449_ = lean_array_push(v_a_2103_, v___x_2447_);
v___x_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
return v___x_2450_;
}
}
v___jp_2105_:
{
uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2108_ = 3;
lean_inc_ref(v___y_2107_);
v___x_2109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2109_, 0, v___y_2107_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1, v___x_2108_);
v___x_2110_ = lean_array_get_size(v___y_2106_);
v___x_2111_ = lean_array_push(v___y_2106_, v___x_2109_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
return v___x_2112_;
}
v___jp_2113_:
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___y_2114_);
lean_ctor_set(v___x_2116_, 1, v_a_2115_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lake_importConfigFile(v_cfg_2451_, v_a_2452_);
return v_res_2454_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_AttributesCore(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Lean_Elab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache);
lean_dec_ref(res);
l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts = _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Lean_Elab(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Lake_DSL_AttributesCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Lean_Elab(builtin);
}
#ifdef __cplusplus
}
#endif
