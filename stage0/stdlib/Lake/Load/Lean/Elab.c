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
uint8_t lean_string_compare(lean_object*, lean_object*);
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
lean_object* l_Nat_reprFast(lean_object*);
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
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
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
lean_dec_ref_known(v___x_274_, 1);
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
lean_dec_ref_known(v___x_375_, 1);
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
lean_dec_ref_known(v___x_419_, 1);
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
lean_dec_ref_known(v___x_398_, 5);
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
lean_dec_ref_known(v___x_455_, 2);
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
lean_dec_ref_known(v___x_513_, 2);
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
lean_dec_ref_known(v___x_714_, 1);
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
lean_dec_ref_known(v___x_759_, 1);
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
lean_dec_ref_known(v___x_759_, 1);
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
lean_dec_ref_known(v___x_731_, 1);
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
lean_dec_ref_known(v___x_719_, 1);
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
lean_dec_ref_known(v___x_714_, 1);
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
lean_dec_ref_known(v___x_1053_, 1);
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
lean_dec_ref_known(v___x_1094_, 1);
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
lean_dec_ref_known(v___x_1101_, 1);
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
v___x_1188_ = lean_unsigned_to_nat(182u);
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
v___x_1194_ = lean_unsigned_to_nat(183u);
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
v___x_1202_ = lean_unsigned_to_nat(276u);
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
v___x_1208_ = lean_unsigned_to_nat(277u);
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
lean_object* v_size_1215_; lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v_l_1218_; lean_object* v_r_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1575_; 
v_size_1215_ = lean_ctor_get(v_t_1214_, 0);
v_k_1216_ = lean_ctor_get(v_t_1214_, 1);
v_v_1217_ = lean_ctor_get(v_t_1214_, 2);
v_l_1218_ = lean_ctor_get(v_t_1214_, 3);
v_r_1219_ = lean_ctor_get(v_t_1214_, 4);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_t_1214_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1221_ = v_t_1214_;
v_isShared_1222_ = v_isSharedCheck_1575_;
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
v_isShared_1222_ = v_isSharedCheck_1575_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_string_compare(v_k_1212_, v_k_1216_);
switch(v___x_1223_)
{
case 0:
{
lean_object* v___x_1224_; 
lean_dec(v_size_1215_);
v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1212_, v_v_1213_, v_l_1218_);
if (lean_obj_tag(v_r_1219_) == 0)
{
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_size_1225_; lean_object* v_size_1226_; lean_object* v_k_1227_; lean_object* v_v_1228_; lean_object* v_l_1229_; lean_object* v_r_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_size_1225_ = lean_ctor_get(v_r_1219_, 0);
v_size_1226_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_size_1226_);
v_k_1227_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_k_1227_);
v_v_1228_ = lean_ctor_get(v___x_1224_, 2);
lean_inc(v_v_1228_);
v_l_1229_ = lean_ctor_get(v___x_1224_, 3);
lean_inc(v_l_1229_);
v_r_1230_ = lean_ctor_get(v___x_1224_, 4);
lean_inc(v_r_1230_);
v___x_1231_ = lean_unsigned_to_nat(3u);
v___x_1232_ = lean_nat_mul(v___x_1231_, v_size_1225_);
v___x_1233_ = lean_nat_dec_lt(v___x_1232_, v_size_1226_);
lean_dec(v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v_r_1230_);
lean_dec(v_l_1229_);
lean_dec(v_v_1228_);
lean_dec(v_k_1227_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v___x_1234_, v_size_1226_);
lean_dec(v_size_1226_);
v___x_1236_ = lean_nat_add(v___x_1235_, v_size_1225_);
lean_dec(v___x_1235_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 3, v___x_1224_);
lean_ctor_set(v___x_1221_, 0, v___x_1236_);
v___x_1238_ = v___x_1221_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_r_1219_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1311_; 
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; lean_object* v_unused_1316_; 
v_unused_1312_ = lean_ctor_get(v___x_1224_, 4);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v___x_1224_, 3);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v___x_1224_, 2);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v___x_1224_, 1);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1316_);
v___x_1241_ = v___x_1224_;
v_isShared_1242_ = v_isSharedCheck_1311_;
goto v_resetjp_1240_;
}
else
{
lean_dec(v___x_1224_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1311_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
if (lean_obj_tag(v_l_1229_) == 0)
{
if (lean_obj_tag(v_r_1230_) == 0)
{
lean_object* v_size_1243_; lean_object* v_size_1244_; lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_l_1247_; lean_object* v_r_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_size_1243_ = lean_ctor_get(v_l_1229_, 0);
v_size_1244_ = lean_ctor_get(v_r_1230_, 0);
v_k_1245_ = lean_ctor_get(v_r_1230_, 1);
v_v_1246_ = lean_ctor_get(v_r_1230_, 2);
v_l_1247_ = lean_ctor_get(v_r_1230_, 3);
v_r_1248_ = lean_ctor_get(v_r_1230_, 4);
v___x_1249_ = lean_unsigned_to_nat(2u);
v___x_1250_ = lean_nat_mul(v___x_1249_, v_size_1243_);
v___x_1251_ = lean_nat_dec_lt(v_size_1244_, v___x_1250_);
lean_dec(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1281_; 
lean_inc(v_r_1248_);
lean_inc(v_l_1247_);
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_r_1230_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; lean_object* v_unused_1283_; lean_object* v_unused_1284_; lean_object* v_unused_1285_; lean_object* v_unused_1286_; 
v_unused_1282_ = lean_ctor_get(v_r_1230_, 4);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_r_1230_, 3);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v_r_1230_, 2);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_r_1230_, 1);
lean_dec(v_unused_1285_);
v_unused_1286_ = lean_ctor_get(v_r_1230_, 0);
lean_dec(v_unused_1286_);
v___x_1253_ = v_r_1230_;
v_isShared_1254_ = v_isSharedCheck_1281_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v_r_1230_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1281_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___x_1269_; lean_object* v___y_1271_; 
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_nat_add(v___x_1255_, v_size_1226_);
lean_dec(v_size_1226_);
v___x_1257_ = lean_nat_add(v___x_1256_, v_size_1225_);
lean_dec(v___x_1256_);
v___x_1269_ = lean_nat_add(v___x_1255_, v_size_1243_);
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
v___jp_1258_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_nat_add(v___y_1259_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec(v___y_1259_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 4, v_r_1219_);
lean_ctor_set(v___x_1253_, 3, v_r_1248_);
lean_ctor_set(v___x_1253_, 2, v_v_1217_);
lean_ctor_set(v___x_1253_, 1, v_k_1216_);
lean_ctor_set(v___x_1253_, 0, v___x_1262_);
v___x_1264_ = v___x_1253_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_r_1219_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 4, v___x_1264_);
lean_ctor_set(v___x_1241_, 3, v___y_1260_);
lean_ctor_set(v___x_1241_, 2, v_v_1246_);
lean_ctor_set(v___x_1241_, 1, v_k_1245_);
lean_ctor_set(v___x_1241_, 0, v___x_1257_);
v___x_1266_ = v___x_1241_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v___y_1260_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_nat_add(v___x_1269_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec(v___x_1269_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_l_1247_);
lean_ctor_set(v___x_1221_, 3, v_l_1229_);
lean_ctor_set(v___x_1221_, 2, v_v_1228_);
lean_ctor_set(v___x_1221_, 1, v_k_1227_);
lean_ctor_set(v___x_1221_, 0, v___x_1272_);
v___x_1274_ = v___x_1221_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1227_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1228_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_l_1229_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_l_1247_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_nat_add(v___x_1255_, v_size_1225_);
if (lean_obj_tag(v_r_1248_) == 0)
{
lean_object* v_size_1276_; 
v_size_1276_ = lean_ctor_get(v_r_1248_, 0);
lean_inc(v_size_1276_);
v___y_1259_ = v___x_1275_;
v___y_1260_ = v___x_1274_;
v___y_1261_ = v_size_1276_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___y_1259_ = v___x_1275_;
v___y_1260_ = v___x_1274_;
v___y_1261_ = v___x_1277_;
goto v___jp_1258_;
}
}
}
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_del_object(v___x_1221_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v___x_1287_, v_size_1226_);
lean_dec(v_size_1226_);
v___x_1289_ = lean_nat_add(v___x_1288_, v_size_1225_);
lean_dec(v___x_1288_);
v___x_1290_ = lean_nat_add(v___x_1287_, v_size_1225_);
v___x_1291_ = lean_nat_add(v___x_1290_, v_size_1244_);
lean_dec(v___x_1290_);
lean_inc_ref(v_r_1219_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 4, v_r_1219_);
lean_ctor_set(v___x_1241_, 3, v_r_1230_);
lean_ctor_set(v___x_1241_, 2, v_v_1217_);
lean_ctor_set(v___x_1241_, 1, v_k_1216_);
lean_ctor_set(v___x_1241_, 0, v___x_1291_);
v___x_1293_ = v___x_1241_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_r_1230_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v_r_1219_);
v___x_1293_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_isSharedCheck_1300_ = !lean_is_exclusive(v_r_1219_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; lean_object* v_unused_1302_; lean_object* v_unused_1303_; lean_object* v_unused_1304_; lean_object* v_unused_1305_; 
v_unused_1301_ = lean_ctor_get(v_r_1219_, 4);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_r_1219_, 3);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_r_1219_, 2);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_r_1219_, 1);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_r_1219_, 0);
lean_dec(v_unused_1305_);
v___x_1295_ = v_r_1219_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v_r_1219_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 4, v___x_1293_);
lean_ctor_set(v___x_1295_, 3, v_l_1229_);
lean_ctor_set(v___x_1295_, 2, v_v_1228_);
lean_ctor_set(v___x_1295_, 1, v_k_1227_);
lean_ctor_set(v___x_1295_, 0, v___x_1289_);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_k_1227_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_v_1228_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_l_1229_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v___x_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref_known(v_l_1229_, 5);
lean_del_object(v___x_1241_);
lean_dec(v_v_1228_);
lean_dec(v_k_1227_);
lean_dec(v_size_1226_);
lean_dec_ref_known(v_r_1219_, 5);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1307_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1308_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1307_);
return v___x_1308_;
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1241_);
lean_dec(v_r_1230_);
lean_dec(v_v_1228_);
lean_dec(v_k_1227_);
lean_dec(v_size_1226_);
lean_dec_ref_known(v_r_1219_, 5);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1309_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1310_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1309_);
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_size_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v_size_1317_ = lean_ctor_get(v_r_1219_, 0);
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_add(v___x_1318_, v_size_1317_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 3, v___x_1224_);
lean_ctor_set(v___x_1221_, 0, v___x_1319_);
v___x_1321_ = v___x_1221_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_r_1219_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_l_1323_; 
v_l_1323_ = lean_ctor_get(v___x_1224_, 3);
lean_inc(v_l_1323_);
if (lean_obj_tag(v_l_1323_) == 0)
{
lean_object* v_r_1324_; 
v_r_1324_ = lean_ctor_get(v___x_1224_, 4);
lean_inc(v_r_1324_);
if (lean_obj_tag(v_r_1324_) == 0)
{
lean_object* v_size_1325_; lean_object* v_k_1326_; lean_object* v_v_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1341_; 
v_size_1325_ = lean_ctor_get(v___x_1224_, 0);
v_k_1326_ = lean_ctor_get(v___x_1224_, 1);
v_v_1327_ = lean_ctor_get(v___x_1224_, 2);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; lean_object* v_unused_1343_; 
v_unused_1342_ = lean_ctor_get(v___x_1224_, 4);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v___x_1224_, 3);
lean_dec(v_unused_1343_);
v___x_1329_ = v___x_1224_;
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_v_1327_);
lean_inc(v_k_1326_);
lean_inc(v_size_1325_);
lean_dec(v___x_1224_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_size_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v_size_1331_ = lean_ctor_get(v_r_1324_, 0);
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_add(v___x_1332_, v_size_1325_);
lean_dec(v_size_1325_);
v___x_1334_ = lean_nat_add(v___x_1332_, v_size_1331_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 4, v_r_1219_);
lean_ctor_set(v___x_1329_, 3, v_r_1324_);
lean_ctor_set(v___x_1329_, 2, v_v_1217_);
lean_ctor_set(v___x_1329_, 1, v_k_1216_);
lean_ctor_set(v___x_1329_, 0, v___x_1334_);
v___x_1336_ = v___x_1329_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_r_1324_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_r_1219_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1336_);
lean_ctor_set(v___x_1221_, 3, v_l_1323_);
lean_ctor_set(v___x_1221_, 2, v_v_1327_);
lean_ctor_set(v___x_1221_, 1, v_k_1326_);
lean_ctor_set(v___x_1221_, 0, v___x_1333_);
v___x_1338_ = v___x_1221_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1326_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1327_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_l_1323_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_k_1344_; lean_object* v_v_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1357_; 
v_k_1344_ = lean_ctor_get(v___x_1224_, 1);
v_v_1345_ = lean_ctor_get(v___x_1224_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; lean_object* v_unused_1360_; 
v_unused_1358_ = lean_ctor_get(v___x_1224_, 4);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v___x_1224_, 3);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1360_);
v___x_1347_ = v___x_1224_;
v_isShared_1348_ = v_isSharedCheck_1357_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_v_1345_);
lean_inc(v_k_1344_);
lean_dec(v___x_1224_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1357_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_unsigned_to_nat(3u);
v___x_1350_ = lean_unsigned_to_nat(1u);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 3, v_r_1324_);
lean_ctor_set(v___x_1347_, 2, v_v_1217_);
lean_ctor_set(v___x_1347_, 1, v_k_1216_);
lean_ctor_set(v___x_1347_, 0, v___x_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_r_1324_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1324_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1352_);
lean_ctor_set(v___x_1221_, 3, v_l_1323_);
lean_ctor_set(v___x_1221_, 2, v_v_1345_);
lean_ctor_set(v___x_1221_, 1, v_k_1344_);
lean_ctor_set(v___x_1221_, 0, v___x_1349_);
v___x_1354_ = v___x_1221_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1344_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1345_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_l_1323_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
else
{
lean_object* v_r_1361_; 
v_r_1361_ = lean_ctor_get(v___x_1224_, 4);
lean_inc(v_r_1361_);
if (lean_obj_tag(v_r_1361_) == 0)
{
lean_object* v_k_1362_; lean_object* v_v_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1387_; 
v_k_1362_ = lean_ctor_get(v___x_1224_, 1);
v_v_1363_ = lean_ctor_get(v___x_1224_, 2);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1388_ = lean_ctor_get(v___x_1224_, 4);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v___x_1224_, 3);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v___x_1224_, 0);
lean_dec(v_unused_1390_);
v___x_1365_ = v___x_1224_;
v_isShared_1366_ = v_isSharedCheck_1387_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_v_1363_);
lean_inc(v_k_1362_);
lean_dec(v___x_1224_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1387_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_k_1367_; lean_object* v_v_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1383_; 
v_k_1367_ = lean_ctor_get(v_r_1361_, 1);
v_v_1368_ = lean_ctor_get(v_r_1361_, 2);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_r_1361_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; 
v_unused_1384_ = lean_ctor_get(v_r_1361_, 4);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_r_1361_, 3);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_r_1361_, 0);
lean_dec(v_unused_1386_);
v___x_1370_ = v_r_1361_;
v_isShared_1371_ = v_isSharedCheck_1383_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_v_1368_);
lean_inc(v_k_1367_);
lean_dec(v_r_1361_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1383_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(3u);
v___x_1373_ = lean_unsigned_to_nat(1u);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_l_1323_);
lean_ctor_set(v___x_1370_, 3, v_l_1323_);
lean_ctor_set(v___x_1370_, 2, v_v_1363_);
lean_ctor_set(v___x_1370_, 1, v_k_1362_);
lean_ctor_set(v___x_1370_, 0, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1362_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1363_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_l_1323_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_l_1323_);
v___x_1375_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 4, v_l_1323_);
lean_ctor_set(v___x_1365_, 2, v_v_1217_);
lean_ctor_set(v___x_1365_, 1, v_k_1216_);
lean_ctor_set(v___x_1365_, 0, v___x_1373_);
v___x_1377_ = v___x_1365_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v_l_1323_);
lean_ctor_set(v_reuseFailAlloc_1381_, 4, v_l_1323_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1379_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1377_);
lean_ctor_set(v___x_1221_, 3, v___x_1375_);
lean_ctor_set(v___x_1221_, 2, v_v_1368_);
lean_ctor_set(v___x_1221_, 1, v_k_1367_);
lean_ctor_set(v___x_1221_, 0, v___x_1372_);
v___x_1379_ = v___x_1221_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_unsigned_to_nat(2u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_r_1361_);
lean_ctor_set(v___x_1221_, 3, v___x_1224_);
lean_ctor_set(v___x_1221_, 0, v___x_1391_);
v___x_1393_ = v___x_1221_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_r_1361_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1224_);
lean_ctor_set(v___x_1221_, 3, v___x_1224_);
lean_ctor_set(v___x_1221_, 0, v___x_1395_);
v___x_1397_ = v___x_1221_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v___x_1224_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
case 1:
{
lean_object* v___x_1400_; 
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v_v_1213_);
lean_ctor_set(v___x_1221_, 1, v_k_1212_);
v___x_1400_ = v___x_1221_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_size_1215_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1212_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1213_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_r_1219_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
default: 
{
lean_object* v___x_1402_; 
lean_dec(v_size_1215_);
v___x_1402_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1212_, v_v_1213_, v_r_1219_);
if (lean_obj_tag(v_l_1218_) == 0)
{
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_size_1403_; lean_object* v_size_1404_; lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v_l_1407_; lean_object* v_r_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v_size_1403_ = lean_ctor_get(v_l_1218_, 0);
v_size_1404_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_size_1404_);
v_k_1405_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_k_1405_);
v_v_1406_ = lean_ctor_get(v___x_1402_, 2);
lean_inc(v_v_1406_);
v_l_1407_ = lean_ctor_get(v___x_1402_, 3);
lean_inc(v_l_1407_);
v_r_1408_ = lean_ctor_get(v___x_1402_, 4);
lean_inc(v_r_1408_);
v___x_1409_ = lean_unsigned_to_nat(3u);
v___x_1410_ = lean_nat_mul(v___x_1409_, v_size_1403_);
v___x_1411_ = lean_nat_dec_lt(v___x_1410_, v_size_1404_);
lean_dec(v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_dec(v_r_1408_);
lean_dec(v_l_1407_);
lean_dec(v_v_1406_);
lean_dec(v_k_1405_);
v___x_1412_ = lean_unsigned_to_nat(1u);
v___x_1413_ = lean_nat_add(v___x_1412_, v_size_1403_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_size_1404_);
lean_dec(v_size_1404_);
lean_dec(v___x_1413_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1402_);
lean_ctor_set(v___x_1221_, 0, v___x_1414_);
v___x_1416_ = v___x_1221_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___x_1402_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1487_; 
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; lean_object* v_unused_1489_; lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; 
v_unused_1488_ = lean_ctor_get(v___x_1402_, 4);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v___x_1402_, 3);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v___x_1402_, 2);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v___x_1402_, 1);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v___x_1402_, 0);
lean_dec(v_unused_1492_);
v___x_1419_ = v___x_1402_;
v_isShared_1420_ = v_isSharedCheck_1487_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v___x_1402_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1487_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
if (lean_obj_tag(v_l_1407_) == 0)
{
if (lean_obj_tag(v_r_1408_) == 0)
{
lean_object* v_size_1421_; lean_object* v_k_1422_; lean_object* v_v_1423_; lean_object* v_l_1424_; lean_object* v_r_1425_; lean_object* v_size_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_size_1421_ = lean_ctor_get(v_l_1407_, 0);
v_k_1422_ = lean_ctor_get(v_l_1407_, 1);
v_v_1423_ = lean_ctor_get(v_l_1407_, 2);
v_l_1424_ = lean_ctor_get(v_l_1407_, 3);
v_r_1425_ = lean_ctor_get(v_l_1407_, 4);
v_size_1426_ = lean_ctor_get(v_r_1408_, 0);
v___x_1427_ = lean_unsigned_to_nat(2u);
v___x_1428_ = lean_nat_mul(v___x_1427_, v_size_1426_);
v___x_1429_ = lean_nat_dec_lt(v_size_1421_, v___x_1428_);
lean_dec(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1458_; 
lean_inc(v_r_1425_);
lean_inc(v_l_1424_);
lean_inc(v_v_1423_);
lean_inc(v_k_1422_);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_l_1407_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; 
v_unused_1459_ = lean_ctor_get(v_l_1407_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_l_1407_, 3);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_l_1407_, 2);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_l_1407_, 1);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_l_1407_, 0);
lean_dec(v_unused_1463_);
v___x_1431_ = v_l_1407_;
v_isShared_1432_ = v_isSharedCheck_1458_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_l_1407_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1458_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1448_; 
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_nat_add(v___x_1433_, v_size_1403_);
v___x_1435_ = lean_nat_add(v___x_1434_, v_size_1404_);
lean_dec(v_size_1404_);
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
v___jp_1436_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_nat_add(v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec(v___y_1438_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 4, v_r_1408_);
lean_ctor_set(v___x_1431_, 3, v_r_1425_);
lean_ctor_set(v___x_1431_, 2, v_v_1406_);
lean_ctor_set(v___x_1431_, 1, v_k_1405_);
lean_ctor_set(v___x_1431_, 0, v___x_1440_);
v___x_1442_ = v___x_1431_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_r_1425_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_r_1408_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 4, v___x_1442_);
lean_ctor_set(v___x_1419_, 3, v___y_1437_);
lean_ctor_set(v___x_1419_, 2, v_v_1423_);
lean_ctor_set(v___x_1419_, 1, v_k_1422_);
lean_ctor_set(v___x_1419_, 0, v___x_1435_);
v___x_1444_ = v___x_1419_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1422_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1423_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v___y_1437_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_nat_add(v___x_1434_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec(v___x_1434_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_l_1424_);
lean_ctor_set(v___x_1221_, 0, v___x_1449_);
v___x_1451_ = v___x_1221_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_l_1424_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_nat_add(v___x_1433_, v_size_1426_);
if (lean_obj_tag(v_r_1425_) == 0)
{
lean_object* v_size_1453_; 
v_size_1453_ = lean_ctor_get(v_r_1425_, 0);
lean_inc(v_size_1453_);
v___y_1437_ = v___x_1451_;
v___y_1438_ = v___x_1452_;
v___y_1439_ = v_size_1453_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___y_1437_ = v___x_1451_;
v___y_1438_ = v___x_1452_;
v___y_1439_ = v___x_1454_;
goto v___jp_1436_;
}
}
}
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
lean_del_object(v___x_1221_);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1403_);
v___x_1466_ = lean_nat_add(v___x_1465_, v_size_1404_);
lean_dec(v_size_1404_);
v___x_1467_ = lean_nat_add(v___x_1465_, v_size_1421_);
lean_dec(v___x_1465_);
lean_inc_ref(v_l_1218_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 4, v_l_1407_);
lean_ctor_set(v___x_1419_, 3, v_l_1218_);
lean_ctor_set(v___x_1419_, 2, v_v_1217_);
lean_ctor_set(v___x_1419_, 1, v_k_1216_);
lean_ctor_set(v___x_1419_, 0, v___x_1467_);
v___x_1469_ = v___x_1419_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_l_1407_);
v___x_1469_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_isSharedCheck_1476_ = !lean_is_exclusive(v_l_1218_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1477_ = lean_ctor_get(v_l_1218_, 4);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_l_1218_, 3);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_l_1218_, 2);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_l_1218_, 1);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1218_, 0);
lean_dec(v_unused_1481_);
v___x_1471_ = v_l_1218_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_l_1218_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v_r_1408_);
lean_ctor_set(v___x_1471_, 3, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v_v_1406_);
lean_ctor_set(v___x_1471_, 1, v_k_1405_);
lean_ctor_set(v___x_1471_, 0, v___x_1466_);
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_r_1408_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref_known(v_l_1407_, 5);
lean_del_object(v___x_1419_);
lean_dec(v_v_1406_);
lean_dec(v_k_1405_);
lean_dec(v_size_1404_);
lean_dec_ref_known(v_l_1218_, 5);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1483_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1484_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1483_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_del_object(v___x_1419_);
lean_dec(v_r_1408_);
lean_dec(v_v_1406_);
lean_dec(v_k_1405_);
lean_dec(v_size_1404_);
lean_dec_ref_known(v_l_1218_, 5);
lean_del_object(v___x_1221_);
lean_dec(v_v_1217_);
lean_dec(v_k_1216_);
v___x_1485_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1486_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1485_);
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_size_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v_size_1493_ = lean_ctor_get(v_l_1218_, 0);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1493_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1402_);
lean_ctor_set(v___x_1221_, 0, v___x_1495_);
v___x_1497_ = v___x_1221_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1402_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_l_1499_; 
v_l_1499_ = lean_ctor_get(v___x_1402_, 3);
lean_inc(v_l_1499_);
if (lean_obj_tag(v_l_1499_) == 0)
{
lean_object* v_r_1500_; 
v_r_1500_ = lean_ctor_get(v___x_1402_, 4);
lean_inc(v_r_1500_);
if (lean_obj_tag(v_r_1500_) == 0)
{
lean_object* v_size_1501_; lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1517_; 
v_size_1501_ = lean_ctor_get(v___x_1402_, 0);
v_k_1502_ = lean_ctor_get(v___x_1402_, 1);
v_v_1503_ = lean_ctor_get(v___x_1402_, 2);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1518_ = lean_ctor_get(v___x_1402_, 4);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v___x_1402_, 3);
lean_dec(v_unused_1519_);
v___x_1505_ = v___x_1402_;
v_isShared_1506_ = v_isSharedCheck_1517_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_v_1503_);
lean_inc(v_k_1502_);
lean_inc(v_size_1501_);
lean_dec(v___x_1402_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1517_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_size_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_size_1507_ = lean_ctor_get(v_l_1499_, 0);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_add(v___x_1508_, v_size_1501_);
lean_dec(v_size_1501_);
v___x_1510_ = lean_nat_add(v___x_1508_, v_size_1507_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_l_1499_);
lean_ctor_set(v___x_1505_, 3, v_l_1218_);
lean_ctor_set(v___x_1505_, 2, v_v_1217_);
lean_ctor_set(v___x_1505_, 1, v_k_1216_);
lean_ctor_set(v___x_1505_, 0, v___x_1510_);
v___x_1512_ = v___x_1505_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_l_1499_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_r_1500_);
lean_ctor_set(v___x_1221_, 3, v___x_1512_);
lean_ctor_set(v___x_1221_, 2, v_v_1503_);
lean_ctor_set(v___x_1221_, 1, v_k_1502_);
lean_ctor_set(v___x_1221_, 0, v___x_1509_);
v___x_1514_ = v___x_1221_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1502_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1503_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_r_1500_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
else
{
lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1545_; 
v_k_1520_ = lean_ctor_get(v___x_1402_, 1);
v_v_1521_ = lean_ctor_get(v___x_1402_, 2);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; lean_object* v_unused_1547_; lean_object* v_unused_1548_; 
v_unused_1546_ = lean_ctor_get(v___x_1402_, 4);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v___x_1402_, 3);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v___x_1402_, 0);
lean_dec(v_unused_1548_);
v___x_1523_ = v___x_1402_;
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_v_1521_);
lean_inc(v_k_1520_);
lean_dec(v___x_1402_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_k_1525_; lean_object* v_v_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1541_; 
v_k_1525_ = lean_ctor_get(v_l_1499_, 1);
v_v_1526_ = lean_ctor_get(v_l_1499_, 2);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_l_1499_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; lean_object* v_unused_1543_; lean_object* v_unused_1544_; 
v_unused_1542_ = lean_ctor_get(v_l_1499_, 4);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_l_1499_, 3);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1499_, 0);
lean_dec(v_unused_1544_);
v___x_1528_ = v_l_1499_;
v_isShared_1529_ = v_isSharedCheck_1541_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_v_1526_);
lean_inc(v_k_1525_);
lean_dec(v_l_1499_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1541_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1530_ = lean_unsigned_to_nat(3u);
v___x_1531_ = lean_unsigned_to_nat(1u);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 4, v_r_1500_);
lean_ctor_set(v___x_1528_, 3, v_r_1500_);
lean_ctor_set(v___x_1528_, 2, v_v_1217_);
lean_ctor_set(v___x_1528_, 1, v_k_1216_);
lean_ctor_set(v___x_1528_, 0, v___x_1531_);
v___x_1533_ = v___x_1528_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_r_1500_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_r_1500_);
v___x_1533_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 3, v_r_1500_);
lean_ctor_set(v___x_1523_, 0, v___x_1531_);
v___x_1535_ = v___x_1523_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_r_1500_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1500_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1535_);
lean_ctor_set(v___x_1221_, 3, v___x_1533_);
lean_ctor_set(v___x_1221_, 2, v_v_1526_);
lean_ctor_set(v___x_1221_, 1, v_k_1525_);
lean_ctor_set(v___x_1221_, 0, v___x_1530_);
v___x_1537_ = v___x_1221_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1525_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1526_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1549_; 
v_r_1549_ = lean_ctor_get(v___x_1402_, 4);
lean_inc(v_r_1549_);
if (lean_obj_tag(v_r_1549_) == 0)
{
lean_object* v_k_1550_; lean_object* v_v_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1563_; 
v_k_1550_ = lean_ctor_get(v___x_1402_, 1);
v_v_1551_ = lean_ctor_get(v___x_1402_, 2);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1564_ = lean_ctor_get(v___x_1402_, 4);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v___x_1402_, 3);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v___x_1402_, 0);
lean_dec(v_unused_1566_);
v___x_1553_ = v___x_1402_;
v_isShared_1554_ = v_isSharedCheck_1563_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
lean_dec(v___x_1402_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1563_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1555_ = lean_unsigned_to_nat(3u);
v___x_1556_ = lean_unsigned_to_nat(1u);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_l_1499_);
lean_ctor_set(v___x_1553_, 2, v_v_1217_);
lean_ctor_set(v___x_1553_, 1, v_k_1216_);
lean_ctor_set(v___x_1553_, 0, v___x_1556_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_l_1499_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_l_1499_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v_r_1549_);
lean_ctor_set(v___x_1221_, 3, v___x_1558_);
lean_ctor_set(v___x_1221_, 2, v_v_1551_);
lean_ctor_set(v___x_1221_, 1, v_k_1550_);
lean_ctor_set(v___x_1221_, 0, v___x_1555_);
v___x_1560_ = v___x_1221_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_r_1549_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_unsigned_to_nat(2u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1402_);
lean_ctor_set(v___x_1221_, 3, v_r_1549_);
lean_ctor_set(v___x_1221_, 0, v___x_1567_);
v___x_1569_ = v___x_1221_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_r_1549_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v___x_1402_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_unsigned_to_nat(1u);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 4, v___x_1402_);
lean_ctor_set(v___x_1221_, 3, v___x_1402_);
lean_ctor_set(v___x_1221_, 0, v___x_1571_);
v___x_1573_ = v___x_1221_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v___x_1402_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v_k_1212_);
lean_ctor_set(v___x_1577_, 2, v_v_1213_);
lean_ctor_set(v___x_1577_, 3, v_t_1214_);
lean_ctor_set(v___x_1577_, 4, v_t_1214_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1578_, lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 0)
{
lean_object* v_k_1580_; lean_object* v_v_1581_; lean_object* v_l_1582_; lean_object* v_r_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_k_1580_ = lean_ctor_get(v_x_1579_, 1);
lean_inc(v_k_1580_);
v_v_1581_ = lean_ctor_get(v_x_1579_, 2);
lean_inc(v_v_1581_);
v_l_1582_ = lean_ctor_get(v_x_1579_, 3);
lean_inc(v_l_1582_);
v_r_1583_ = lean_ctor_get(v_x_1579_, 4);
lean_inc(v_r_1583_);
lean_dec_ref_known(v_x_1579_, 5);
v___x_1584_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1578_, v_l_1582_);
v___x_1585_ = 1;
v___x_1586_ = l_Lean_Name_toString(v_k_1580_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_v_1581_);
v___x_1588_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1586_, v___x_1587_, v___x_1584_);
v_init_1578_ = v___x_1588_;
v_x_1579_ = v_r_1583_;
goto _start;
}
else
{
return v_init_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_box(1);
v___x_1592_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1591_, v_m_1590_);
v___x_1593_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
if (lean_obj_tag(v_a_1594_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_array_to_list(v_a_1595_);
return v___x_1596_;
}
else
{
lean_object* v_head_1597_; lean_object* v_tail_1598_; lean_object* v___x_1599_; 
v_head_1597_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_head_1597_);
v_tail_1598_ = lean_ctor_get(v_a_1594_, 1);
lean_inc(v_tail_1598_);
lean_dec_ref_known(v_a_1594_, 2);
v___x_1599_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1595_, v_head_1597_);
v_a_1594_ = v_tail_1598_;
v_a_1595_ = v___x_1599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1609_){
_start:
{
lean_object* v_idx_1610_; lean_object* v_name_1611_; lean_object* v_platform_1612_; lean_object* v_leanHash_1613_; uint64_t v_configHash_1614_; lean_object* v_options_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_idx_1610_ = lean_ctor_get(v_x_1609_, 0);
lean_inc(v_idx_1610_);
v_name_1611_ = lean_ctor_get(v_x_1609_, 1);
lean_inc(v_name_1611_);
v_platform_1612_ = lean_ctor_get(v_x_1609_, 2);
lean_inc_ref(v_platform_1612_);
v_leanHash_1613_ = lean_ctor_get(v_x_1609_, 3);
lean_inc_ref(v_leanHash_1613_);
v_configHash_1614_ = lean_ctor_get_uint64(v_x_1609_, sizeof(void*)*5);
v_options_1615_ = lean_ctor_get(v_x_1609_, 4);
lean_inc(v_options_1615_);
lean_dec_ref(v_x_1609_);
v___x_1616_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1617_ = l_Lean_JsonNumber_fromNat(v_idx_1610_);
v___x_1618_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1623_ = 1;
v___x_1624_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1611_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1622_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1620_);
v___x_1628_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_platform_1612_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___x_1620_);
v___x_1632_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1633_, 0, v_leanHash_1613_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v___x_1620_);
v___x_1636_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1637_ = l_Lake_lowerHexUInt64(v_configHash_1614_);
v___x_1638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1636_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v___x_1620_);
v___x_1641_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1642_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1615_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1620_);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1620_);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1640_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1635_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1631_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1627_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1621_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1652_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1650_, v___x_1651_);
v___x_1653_ = l_Lean_Json_mkObj(v___x_1652_);
lean_dec(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1654_, lean_object* v_msg_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1657_, lean_object* v_k_1658_, lean_object* v_v_1659_, lean_object* v_t_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1658_, v_v_1659_, v_t_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1662_, lean_object* v_t_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1662_, v_t_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1667_, lean_object* v_k_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = l_Lean_Json_getObjValD(v_j_1667_, v_k_1668_);
v___x_1670_ = l_Lean_Json_getNat_x3f(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1671_, v_k_1672_);
lean_dec_ref(v_k_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1674_, lean_object* v_k_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = l_Lean_Json_getObjValD(v_j_1674_, v_k_1675_);
v___x_1677_ = l_Lean_Name_fromJson_x3f(v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1678_, lean_object* v_k_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1678_, v_k_1679_);
lean_dec_ref(v_k_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1681_, lean_object* v_k_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = l_Lean_Json_getObjValD(v_j_1681_, v_k_1682_);
v___x_1684_ = l_Lean_Json_getStr_x3f(v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1685_, lean_object* v_k_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1685_, v_k_1686_);
lean_dec_ref(v_k_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1688_, lean_object* v_k_1689_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = l_Lean_Json_getObjValD(v_j_1688_, v_k_1689_);
v___x_1691_ = l_Lake_Hash_fromJson_x3f(v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1692_, lean_object* v_k_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1692_, v_k_1693_);
lean_dec_ref(v_k_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1698_, lean_object* v_x_1699_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v_k_1700_; lean_object* v_v_1701_; lean_object* v_l_1702_; lean_object* v_r_1703_; lean_object* v___x_1704_; 
v_k_1700_ = lean_ctor_get(v_x_1699_, 1);
lean_inc(v_k_1700_);
v_v_1701_ = lean_ctor_get(v_x_1699_, 2);
lean_inc(v_v_1701_);
v_l_1702_ = lean_ctor_get(v_x_1699_, 3);
lean_inc(v_l_1702_);
v_r_1703_ = lean_ctor_get(v_x_1699_, 4);
lean_inc(v_r_1703_);
lean_dec_ref_known(v_x_1699_, 5);
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1698_, v_l_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_dec(v_r_1703_);
lean_dec(v_v_1701_);
lean_dec(v_k_1700_);
return v___x_1704_;
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1745_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1745_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1745_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1710_ = lean_string_dec_eq(v_k_1700_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v_n_1711_; uint8_t v___x_1712_; 
lean_inc(v_k_1700_);
v_n_1711_ = l_String_toName(v_k_1700_);
v___x_1712_ = l_Lean_Name_isAnonymous(v_n_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_del_object(v___x_1707_);
lean_dec(v_k_1700_);
v___x_1713_ = l_Lean_Json_getStr_x3f(v_v_1701_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_n_1711_);
lean_dec(v_a_1705_);
lean_dec(v_r_1703_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1723_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1711_, v_a_1722_, v_a_1705_);
v_init_1698_ = v___x_1723_;
v_x_1699_ = v_r_1703_;
goto _start;
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec(v_n_1711_);
lean_dec(v_a_1705_);
lean_dec(v_r_1703_);
lean_dec(v_v_1701_);
v___x_1725_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1726_ = lean_string_append(v___x_1725_, v_k_1700_);
lean_dec(v_k_1700_);
v___x_1727_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1728_);
v___x_1730_ = v___x_1707_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_del_object(v___x_1707_);
lean_dec(v_k_1700_);
v___x_1732_ = l_Lean_Json_getStr_x3f(v_v_1701_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1705_);
lean_dec(v_r_1703_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_a_1741_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1742_ = lean_box(0);
v___x_1743_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1742_, v_a_1741_, v_a_1705_);
v_init_1698_ = v___x_1743_;
v_x_1699_ = v_r_1703_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_init_1698_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 5)
{
lean_object* v_kvPairs_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_kvPairs_1749_ = lean_ctor_get(v_x_1748_, 0);
lean_inc(v_kvPairs_1749_);
lean_dec_ref_known(v_x_1748_, 1);
v___x_1750_ = lean_box(1);
v___x_1751_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1750_, v_kvPairs_1749_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1752_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1753_ = lean_unsigned_to_nat(80u);
v___x_1754_ = l_Lean_Json_pretty(v_x_1748_, v___x_1753_);
v___x_1755_ = lean_string_append(v___x_1752_, v___x_1754_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1757_ = lean_string_append(v___x_1755_, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1759_, lean_object* v_k_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = l_Lean_Json_getObjValD(v_j_1759_, v_k_1760_);
v___x_1762_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1763_, lean_object* v_k_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1763_, v_k_1764_);
lean_dec_ref(v_k_1764_);
return v_res_1765_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = 1;
v___x_1795_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1799_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1800_ = lean_string_append(v___x_1799_, v___x_1798_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = 1;
v___x_1804_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1807_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1808_ = lean_string_append(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1811_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1812_ = lean_string_append(v___x_1811_, v___x_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = 1;
v___x_1816_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1817_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1816_, v___x_1815_);
return v___x_1817_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1819_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1820_ = lean_string_append(v___x_1819_, v___x_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1822_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1823_ = lean_string_append(v___x_1822_, v___x_1821_);
return v___x_1823_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = 1;
v___x_1827_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1830_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1833_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1834_ = lean_string_append(v___x_1833_, v___x_1832_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = 1;
v___x_1838_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1841_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1842_ = lean_string_append(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1844_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1845_ = lean_string_append(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = 1;
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1852_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1853_ = lean_string_append(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1855_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1856_ = lean_string_append(v___x_1855_, v___x_1854_);
return v___x_1856_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = 1;
v___x_1860_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1860_, v___x_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1863_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1864_ = lean_string_append(v___x_1863_, v___x_1862_);
return v___x_1864_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1866_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1867_ = lean_string_append(v___x_1866_, v___x_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1868_);
v___x_1870_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1868_, v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_json_1868_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_1876_ = lean_string_append(v___x_1875_, v_a_1871_);
lean_dec(v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_json_1868_);
v_a_1881_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1870_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1870_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 0);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_a_1889_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1890_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1868_);
v___x_1891_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1868_, v___x_1890_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1896_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_1897_ = lean_string_append(v___x_1896_, v_a_1892_);
lean_dec(v_a_1892_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1897_);
v___x_1899_ = v___x_1894_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1902_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1891_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1891_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_a_1910_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1911_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1868_);
v___x_1912_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1868_, v___x_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1922_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1922_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1918_ = lean_string_append(v___x_1917_, v_a_1913_);
lean_dec(v_a_1913_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1918_);
v___x_1920_ = v___x_1915_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1923_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1912_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1912_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 0);
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1932_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1868_);
v___x_1933_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1868_, v___x_1932_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1931_);
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1938_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
v___x_1939_ = lean_string_append(v___x_1938_, v_a_1934_);
lean_dec(v_a_1934_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1939_);
v___x_1941_ = v___x_1936_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_a_1931_);
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1944_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1933_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1933_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 0);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1953_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1868_);
v___x_1954_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1868_, v___x_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1952_);
lean_dec(v_a_1931_);
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1964_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1964_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1959_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
v___x_1960_ = lean_string_append(v___x_1959_, v_a_1955_);
lean_dec(v_a_1955_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
else
{
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_a_1952_);
lean_dec(v_a_1931_);
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_json_1868_);
v_a_1965_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1954_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1954_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 0);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_a_1973_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1974_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1975_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1868_, v___x_1974_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_a_1973_);
lean_dec(v_a_1952_);
lean_dec(v_a_1931_);
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1985_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1985_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_1981_ = lean_string_append(v___x_1980_, v_a_1976_);
lean_dec(v_a_1976_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1981_);
v___x_1983_ = v___x_1978_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_a_1973_);
lean_dec(v_a_1952_);
lean_dec(v_a_1931_);
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
v_a_1986_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1975_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1975_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 0);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
v_a_1994_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1996_ = v___x_1975_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1975_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; uint64_t v___x_1999_; lean_object* v___x_2001_; 
v___x_1998_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1998_, 0, v_a_1889_);
lean_ctor_set(v___x_1998_, 1, v_a_1910_);
lean_ctor_set(v___x_1998_, 2, v_a_1931_);
lean_ctor_set(v___x_1998_, 3, v_a_1952_);
lean_ctor_set(v___x_1998_, 4, v_a_1994_);
v___x_1999_ = lean_unbox_uint64(v_a_1973_);
lean_dec(v_a_1973_);
lean_ctor_set_uint64(v___x_1998_, sizeof(void*)*5, v___x_1999_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_1998_);
v___x_2001_ = v___x_1996_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
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
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_2008_ = lean_mk_io_user_error(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_2009_, lean_object* v___x_2010_, lean_object* v_h_2011_){
_start:
{
uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = 1;
v___x_2014_ = lean_io_prim_handle_mk(v___x_2009_, v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = 1;
v___x_2017_ = lean_io_prim_handle_try_lock(v_a_2015_, v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; uint8_t v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = lean_unbox(v_a_2018_);
lean_dec(v_a_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v_a_2015_);
v___x_2020_ = lean_io_prim_handle_unlock(v_h_2011_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v___x_2020_, 0);
lean_dec(v_unused_2029_);
v___x_2022_ = v___x_2020_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v___x_2020_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2020_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2020_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_io_prim_handle_unlock(v_h_2011_);
if (lean_obj_tag(v___x_2038_) == 0)
{
uint8_t v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref_known(v___x_2038_, 1);
v___x_2039_ = 3;
v___x_2040_ = lean_io_prim_handle_mk(v___x_2010_, v___x_2039_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = lean_io_prim_handle_lock(v_a_2041_, v___x_2016_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; 
lean_dec_ref_known(v___x_2042_, 1);
v___x_2043_ = lean_io_prim_handle_unlock(v_a_2015_);
lean_dec(v_a_2015_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2043_, 0);
lean_dec(v_unused_2051_);
v___x_2045_ = v___x_2043_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v___x_2043_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_a_2041_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2041_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_a_2041_);
v_a_2052_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2043_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2043_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2041_);
lean_dec(v_a_2015_);
v_a_2060_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2042_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2042_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_dec(v_a_2015_);
return v___x_2040_;
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2015_);
v_a_2068_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2038_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2038_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_a_2015_);
v_a_2076_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2017_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2017_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2084_, lean_object* v___x_2085_, lean_object* v_h_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lake_importConfigFile___lam__0(v___x_2084_, v___x_2085_, v_h_2086_);
lean_dec(v_h_2086_);
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2113_; lean_object* v_a_2114_; lean_object* v_lakeEnv_2116_; lean_object* v_wsDir_2117_; lean_object* v_pkgIdx_2118_; lean_object* v_pkgName_2119_; lean_object* v_pkgDir_2120_; lean_object* v_configFile_2121_; lean_object* v_lakeOpts_2122_; lean_object* v_leanOpts_2123_; uint8_t v_reconfigure_2124_; lean_object* v___x_2125_; 
v_lakeEnv_2116_ = lean_ctor_get(v_cfg_2101_, 0);
lean_inc_ref(v_lakeEnv_2116_);
v_wsDir_2117_ = lean_ctor_get(v_cfg_2101_, 2);
lean_inc_ref(v_wsDir_2117_);
v_pkgIdx_2118_ = lean_ctor_get(v_cfg_2101_, 3);
lean_inc(v_pkgIdx_2118_);
v_pkgName_2119_ = lean_ctor_get(v_cfg_2101_, 4);
lean_inc(v_pkgName_2119_);
v_pkgDir_2120_ = lean_ctor_get(v_cfg_2101_, 6);
lean_inc_ref(v_pkgDir_2120_);
v_configFile_2121_ = lean_ctor_get(v_cfg_2101_, 8);
lean_inc_ref_n(v_configFile_2121_, 2);
v_lakeOpts_2122_ = lean_ctor_get(v_cfg_2101_, 12);
lean_inc(v_lakeOpts_2122_);
v_leanOpts_2123_ = lean_ctor_get(v_cfg_2101_, 13);
lean_inc_ref(v_leanOpts_2123_);
v_reconfigure_2124_ = lean_ctor_get_uint8(v_cfg_2101_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2101_);
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
lean_dec_ref(v_wsDir_2117_);
lean_dec_ref(v_lakeEnv_2116_);
v___x_2126_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2127_ = lean_array_get_size(v_a_2102_);
v___x_2128_ = lean_array_push(v_a_2102_, v___x_2126_);
v___x_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v_val_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_configDir_2136_; lean_object* v___x_2137_; 
v_val_2130_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2130_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2131_ = l_Lake_defaultLakeDir;
v___x_2132_ = l_Lake_joinRelative(v_wsDir_2117_, v___x_2131_);
v___x_2133_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2134_ = l_Lake_joinRelative(v___x_2132_, v___x_2133_);
lean_inc(v_pkgIdx_2118_);
v___x_2135_ = l_Nat_reprFast(v_pkgIdx_2118_);
v_configDir_2136_ = l_Lake_joinRelative(v___x_2134_, v___x_2135_);
lean_inc_ref(v_configDir_2136_);
v___x_2137_ = l_IO_FS_createDirAll(v_configDir_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2137_, 1);
v___x_2138_ = l_Lake_computeTextFileHash(v_configFile_2121_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_h_2147_; lean_object* v_lakeOpts_2148_; lean_object* v___y_2149_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v_h_2304_; lean_object* v___y_2305_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2130_, 2);
v___x_2141_ = l_System_FilePath_withExtension(v_val_2130_, v___x_2140_);
lean_inc_ref_n(v_configDir_2136_, 2);
v___x_2142_ = l_Lake_joinRelative(v_configDir_2136_, v___x_2141_);
v___x_2143_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2144_ = l_System_FilePath_withExtension(v_val_2130_, v___x_2143_);
v___x_2145_ = l_Lake_joinRelative(v_configDir_2136_, v___x_2144_);
v___x_2285_ = l_System_FilePath_pathExists(v___x_2145_);
v___x_2286_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2287_ = l_System_FilePath_withExtension(v_val_2130_, v___x_2286_);
v___x_2288_ = l_Lake_joinRelative(v_configDir_2136_, v___x_2287_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_inc_ref(v_pkgDir_2120_);
v___x_2389_ = l_Lake_joinRelative(v_pkgDir_2120_, v___x_2131_);
v___x_2390_ = l_IO_FS_createDirAll(v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 0)
{
uint8_t v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v___x_2390_, 1);
v___x_2391_ = 2;
v___x_2392_ = lean_io_prim_handle_mk(v___x_2145_, v___x_2391_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref(v___x_2288_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = 1;
v___x_2395_ = lean_io_prim_handle_lock(v_a_2393_, v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_dec_ref_known(v___x_2395_, 1);
v_h_2147_ = v_a_2393_;
v_lakeOpts_2148_ = v_lakeOpts_2122_;
v___y_2149_ = v_a_2102_;
goto v___jp_2146_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec(v_a_2393_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = lean_io_error_to_string(v_a_2396_);
v___x_2398_ = 3;
v___x_2399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1, v___x_2398_);
v___x_2400_ = lean_array_get_size(v_a_2102_);
v___x_2401_ = lean_array_push(v_a_2102_, v___x_2399_);
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
lean_dec_ref_known(v___x_2392_, 1);
if (lean_obj_tag(v_a_2403_) == 0)
{
uint8_t v___x_2404_; lean_object* v___x_2405_; 
lean_dec_ref_known(v_a_2403_, 2);
v___x_2404_ = 0;
v___x_2405_ = lean_io_prim_handle_mk(v___x_2145_, v___x_2404_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v_h_2304_ = v_a_2406_;
v___y_2305_ = v_a_2102_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2407_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2408_ = lean_io_error_to_string(v_a_2407_);
v___x_2409_ = 3;
v___x_2410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*1, v___x_2409_);
v___x_2411_ = lean_array_get_size(v_a_2102_);
v___x_2412_ = lean_array_push(v_a_2102_, v___x_2410_);
v___x_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___x_2414_ = lean_io_error_to_string(v_a_2403_);
v___x_2415_ = 3;
v___x_2416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*1, v___x_2415_);
v___x_2417_ = lean_array_get_size(v_a_2102_);
v___x_2418_ = lean_array_push(v_a_2102_, v___x_2416_);
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
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2420_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2421_ = lean_io_error_to_string(v_a_2420_);
v___x_2422_ = 3;
v___x_2423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1, v___x_2422_);
v___x_2424_ = lean_array_get_size(v_a_2102_);
v___x_2425_ = lean_array_push(v_a_2102_, v___x_2423_);
v___x_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
return v___x_2426_;
}
}
else
{
uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = 0;
v___x_2428_ = lean_io_prim_handle_mk(v___x_2145_, v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v_h_2304_ = v_a_2429_;
v___y_2305_ = v_a_2102_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2430_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2431_ = lean_io_error_to_string(v_a_2430_);
v___x_2432_ = 3;
v___x_2433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set_uint8(v___x_2433_, sizeof(void*)*1, v___x_2432_);
v___x_2434_ = lean_array_get_size(v_a_2102_);
v___x_2435_ = lean_array_push(v_a_2102_, v___x_2433_);
v___x_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
return v___x_2436_;
}
}
v___jp_2146_:
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_io_remove_file(v___x_2142_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint64_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref_known(v___x_2150_, 1);
lean_dec_ref(v___x_2145_);
v___x_2151_ = l_System_Platform_target;
v___x_2152_ = l_Lake_Env_leanGithash(v_lakeEnv_2116_);
lean_dec_ref(v_lakeEnv_2116_);
lean_inc(v_lakeOpts_2148_);
lean_inc(v_pkgName_2119_);
lean_inc(v_pkgIdx_2118_);
v___x_2153_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2153_, 0, v_pkgIdx_2118_);
lean_ctor_set(v___x_2153_, 1, v_pkgName_2119_);
lean_ctor_set(v___x_2153_, 2, v___x_2151_);
lean_ctor_set(v___x_2153_, 3, v___x_2152_);
lean_ctor_set(v___x_2153_, 4, v_lakeOpts_2148_);
v___x_2154_ = lean_unbox_uint64(v_a_2139_);
lean_dec(v_a_2139_);
lean_ctor_set_uint64(v___x_2153_, sizeof(void*)*5, v___x_2154_);
v___x_2155_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2153_);
v___x_2156_ = lean_unsigned_to_nat(80u);
v___x_2157_ = l_Lean_Json_pretty(v___x_2155_, v___x_2156_);
v___x_2158_ = l_IO_FS_Handle_putStrLn(v_h_2147_, v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v___x_2159_; 
lean_dec_ref_known(v___x_2158_, 1);
v___x_2159_ = lean_io_prim_handle_truncate(v_h_2147_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref_known(v___x_2159_, 1);
v___x_2160_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2118_, v_pkgName_2119_, v_pkgDir_2120_, v_lakeOpts_2148_, v_leanOpts_2123_, v_configFile_2121_, v___y_2149_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v_a_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
v_a_2162_ = lean_ctor_get(v___x_2160_, 1);
lean_inc(v_a_2162_);
v___x_2163_ = 1;
v___x_2164_ = l_Lean_writeModule(v_a_2161_, v___x_2142_, v___x_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v___x_2165_; 
lean_dec_ref_known(v___x_2164_, 1);
v___x_2165_ = lean_io_prim_handle_unlock(v_h_2147_);
lean_dec(v_h_2147_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_dec_ref_known(v___x_2165_, 1);
lean_dec(v_a_2162_);
return v___x_2160_;
}
else
{
lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2178_; 
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2179_ = lean_ctor_get(v___x_2160_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v___x_2160_, 0);
lean_dec(v_unused_2180_);
v___x_2167_ = v___x_2160_;
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
else
{
lean_dec(v___x_2160_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2178_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_a_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2170_ = lean_io_error_to_string(v_a_2169_);
v___x_2171_ = 3;
v___x_2172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*1, v___x_2171_);
v___x_2173_ = lean_array_get_size(v_a_2162_);
v___x_2174_ = lean_array_push(v_a_2162_, v___x_2172_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 1);
lean_ctor_set(v___x_2167_, 1, v___x_2174_);
lean_ctor_set(v___x_2167_, 0, v___x_2173_);
v___x_2176_ = v___x_2167_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_h_2147_);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2194_ = lean_ctor_get(v___x_2160_, 1);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v___x_2160_, 0);
lean_dec(v_unused_2195_);
v___x_2182_ = v___x_2160_;
v_isShared_2183_ = v_isSharedCheck_2193_;
goto v_resetjp_2181_;
}
else
{
lean_dec(v___x_2160_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2193_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_a_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v_a_2184_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2185_ = lean_io_error_to_string(v_a_2184_);
v___x_2186_ = 3;
v___x_2187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*1, v___x_2186_);
v___x_2188_ = lean_array_get_size(v_a_2162_);
v___x_2189_ = lean_array_push(v_a_2162_, v___x_2187_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
lean_ctor_set(v___x_2182_, 1, v___x_2189_);
lean_ctor_set(v___x_2182_, 0, v___x_2188_);
v___x_2191_ = v___x_2182_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_dec(v_h_2147_);
lean_dec_ref(v___x_2142_);
return v___x_2160_;
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_lakeOpts_2148_);
lean_dec(v_h_2147_);
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2196_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2197_ = lean_io_error_to_string(v_a_2196_);
v___x_2198_ = 3;
v___x_2199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set_uint8(v___x_2199_, sizeof(void*)*1, v___x_2198_);
v___x_2200_ = lean_array_get_size(v___y_2149_);
v___x_2201_ = lean_array_push(v___y_2149_, v___x_2199_);
v___x_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
return v___x_2202_;
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_lakeOpts_2148_);
lean_dec(v_h_2147_);
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2203_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2204_ = lean_io_error_to_string(v_a_2203_);
v___x_2205_ = 3;
v___x_2206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*1, v___x_2205_);
v___x_2207_ = lean_array_get_size(v___y_2149_);
v___x_2208_ = lean_array_push(v___y_2149_, v___x_2206_);
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
return v___x_2209_;
}
}
else
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2150_, 1);
if (lean_obj_tag(v_a_2210_) == 11)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint64_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref_known(v_a_2210_, 2);
lean_dec_ref(v___x_2145_);
v___x_2211_ = l_System_Platform_target;
v___x_2212_ = l_Lake_Env_leanGithash(v_lakeEnv_2116_);
lean_dec_ref(v_lakeEnv_2116_);
lean_inc(v_lakeOpts_2148_);
lean_inc(v_pkgName_2119_);
lean_inc(v_pkgIdx_2118_);
v___x_2213_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2213_, 0, v_pkgIdx_2118_);
lean_ctor_set(v___x_2213_, 1, v_pkgName_2119_);
lean_ctor_set(v___x_2213_, 2, v___x_2211_);
lean_ctor_set(v___x_2213_, 3, v___x_2212_);
lean_ctor_set(v___x_2213_, 4, v_lakeOpts_2148_);
v___x_2214_ = lean_unbox_uint64(v_a_2139_);
lean_dec(v_a_2139_);
lean_ctor_set_uint64(v___x_2213_, sizeof(void*)*5, v___x_2214_);
v___x_2215_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2213_);
v___x_2216_ = lean_unsigned_to_nat(80u);
v___x_2217_ = l_Lean_Json_pretty(v___x_2215_, v___x_2216_);
v___x_2218_ = l_IO_FS_Handle_putStrLn(v_h_2147_, v___x_2217_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2219_; 
lean_dec_ref_known(v___x_2218_, 1);
v___x_2219_ = lean_io_prim_handle_truncate(v_h_2147_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref_known(v___x_2219_, 1);
v___x_2220_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2118_, v_pkgName_2119_, v_pkgDir_2120_, v_lakeOpts_2148_, v_leanOpts_2123_, v_configFile_2121_, v___y_2149_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v_a_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
v_a_2222_ = lean_ctor_get(v___x_2220_, 1);
lean_inc(v_a_2222_);
v___x_2223_ = 1;
v___x_2224_ = l_Lean_writeModule(v_a_2221_, v___x_2142_, v___x_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2225_; 
lean_dec_ref_known(v___x_2224_, 1);
v___x_2225_ = lean_io_prim_handle_unlock(v_h_2147_);
lean_dec(v_h_2147_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_dec_ref_known(v___x_2225_, 1);
lean_dec(v_a_2222_);
return v___x_2220_;
}
else
{
lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2238_; 
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; lean_object* v_unused_2240_; 
v_unused_2239_ = lean_ctor_get(v___x_2220_, 1);
lean_dec(v_unused_2239_);
v_unused_2240_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2240_);
v___x_2227_ = v___x_2220_;
v_isShared_2228_ = v_isSharedCheck_2238_;
goto v_resetjp_2226_;
}
else
{
lean_dec(v___x_2220_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2238_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_a_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v_a_2229_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2230_ = lean_io_error_to_string(v_a_2229_);
v___x_2231_ = 3;
v___x_2232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*1, v___x_2231_);
v___x_2233_ = lean_array_get_size(v_a_2222_);
v___x_2234_ = lean_array_push(v_a_2222_, v___x_2232_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set_tag(v___x_2227_, 1);
lean_ctor_set(v___x_2227_, 1, v___x_2234_);
lean_ctor_set(v___x_2227_, 0, v___x_2233_);
v___x_2236_ = v___x_2227_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_h_2147_);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; lean_object* v_unused_2255_; 
v_unused_2254_ = lean_ctor_get(v___x_2220_, 1);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2255_);
v___x_2242_ = v___x_2220_;
v_isShared_2243_ = v_isSharedCheck_2253_;
goto v_resetjp_2241_;
}
else
{
lean_dec(v___x_2220_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2253_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_a_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v_a_2244_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2245_ = lean_io_error_to_string(v_a_2244_);
v___x_2246_ = 3;
v___x_2247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*1, v___x_2246_);
v___x_2248_ = lean_array_get_size(v_a_2222_);
v___x_2249_ = lean_array_push(v_a_2222_, v___x_2247_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
lean_ctor_set(v___x_2242_, 1, v___x_2249_);
lean_ctor_set(v___x_2242_, 0, v___x_2248_);
v___x_2251_ = v___x_2242_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_dec(v_h_2147_);
lean_dec_ref(v___x_2142_);
return v___x_2220_;
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v_lakeOpts_2148_);
lean_dec(v_h_2147_);
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2256_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2257_ = lean_io_error_to_string(v_a_2256_);
v___x_2258_ = 3;
v___x_2259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*1, v___x_2258_);
v___x_2260_ = lean_array_get_size(v___y_2149_);
v___x_2261_ = lean_array_push(v___y_2149_, v___x_2259_);
v___x_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
return v___x_2262_;
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec(v_lakeOpts_2148_);
lean_dec(v_h_2147_);
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
v_a_2263_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2264_ = lean_io_error_to_string(v_a_2263_);
v___x_2265_ = 3;
v___x_2266_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*1, v___x_2265_);
v___x_2267_ = lean_array_get_size(v___y_2149_);
v___x_2268_ = lean_array_push(v___y_2149_, v___x_2266_);
v___x_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
return v___x_2269_;
}
}
else
{
lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v_lakeOpts_2148_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___x_2270_ = lean_io_error_to_string(v_a_2210_);
v___x_2271_ = 3;
v___x_2272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*1, v___x_2271_);
v___x_2273_ = lean_array_get_size(v___y_2149_);
v___x_2274_ = lean_array_push(v___y_2149_, v___x_2272_);
v___x_2275_ = lean_io_prim_handle_unlock(v_h_2147_);
lean_dec(v_h_2147_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; 
lean_dec_ref_known(v___x_2275_, 1);
v___x_2276_ = lean_io_remove_file(v___x_2145_);
lean_dec_ref(v___x_2145_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec_ref_known(v___x_2276_, 1);
v___y_2113_ = v___x_2273_;
v_a_2114_ = v___x_2274_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = lean_io_error_to_string(v_a_2277_);
v___x_2279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*1, v___x_2271_);
v___x_2280_ = lean_array_push(v___x_2274_, v___x_2279_);
v___y_2113_ = v___x_2273_;
v_a_2114_ = v___x_2280_;
goto v___jp_2112_;
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref(v___x_2145_);
v_a_2281_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2275_, 1);
v___x_2282_ = lean_io_error_to_string(v_a_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*1, v___x_2271_);
v___x_2284_ = lean_array_push(v___x_2274_, v___x_2283_);
v___y_2113_ = v___x_2273_;
v_a_2114_ = v___x_2284_;
goto v___jp_2112_;
}
}
}
}
v___jp_2289_:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lake_importConfigFile___lam__0(v___x_2288_, v___x_2145_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___x_2288_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v_options_2295_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v_options_2295_ = lean_ctor_get(v___y_2292_, 4);
lean_inc(v_options_2295_);
lean_dec_ref(v___y_2292_);
v_h_2147_ = v_a_2294_;
v_lakeOpts_2148_ = v_options_2295_;
v___y_2149_ = v___y_2290_;
goto v___jp_2146_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2296_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2297_ = lean_io_error_to_string(v_a_2296_);
v___x_2298_ = 3;
v___x_2299_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*1, v___x_2298_);
v___x_2300_ = lean_array_get_size(v___y_2290_);
v___x_2301_ = lean_array_push(v___y_2290_, v___x_2299_);
v___x_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
return v___x_2302_;
}
}
v___jp_2303_:
{
if (v_reconfigure_2124_ == 0)
{
lean_object* v___x_2306_; 
lean_dec(v_lakeOpts_2122_);
v___x_2306_ = lean_io_prim_handle_lock(v_h_2304_, v_reconfigure_2124_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2306_, 1);
v___x_2307_ = l_IO_FS_Handle_readToEnd(v_h_2304_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2309_ = ((lean_object*)(l_Lake_importConfigFile___closed__6));
v___x_2310_ = l_Lean_Json_parse(v_a_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref_known(v___x_2310_, 1);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___x_2311_ = ((lean_object*)(l_Lake_importConfigFile___closed__7));
v___x_2312_ = lean_array_get_size(v___y_2305_);
v___x_2313_ = lean_array_push(v___y_2305_, v___x_2311_);
v___x_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
return v___x_2314_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_n(v_a_2315_, 2);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2316_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; 
lean_dec_ref_known(v___x_2316_, 1);
v___x_2317_ = l_Lean_Json_getObj_x3f(v_a_2315_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_dec_ref_known(v___x_2317_, 1);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___y_2105_ = v___y_2305_;
v___y_2106_ = v___x_2309_;
goto v___jp_2104_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2320_ = l_Lake_JsonObject_getJson_x3f(v_a_2318_, v___x_2319_);
lean_dec(v_a_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___y_2105_ = v___y_2305_;
v___y_2106_ = v___x_2309_;
goto v___jp_2104_;
}
else
{
lean_object* v_val_2321_; lean_object* v___x_2322_; 
v_val_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_val_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_dec_ref_known(v___x_2322_, 1);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___y_2105_ = v___y_2305_;
v___y_2106_ = v___x_2309_;
goto v___jp_2104_;
}
else
{
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_dec_ref_known(v___x_2322_, 1);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___y_2105_ = v___y_2305_;
v___y_2106_ = v___x_2309_;
goto v___jp_2104_;
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = l_Lake_importConfigFile___lam__0(v___x_2288_, v___x_2145_, v_h_2304_);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v_h_2147_ = v_a_2325_;
v_lakeOpts_2148_ = v_a_2323_;
v___y_2149_ = v___y_2305_;
goto v___jp_2146_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v_a_2323_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2326_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2327_ = lean_io_error_to_string(v_a_2326_);
v___x_2328_ = 3;
v___x_2329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*1, v___x_2328_);
v___x_2330_ = lean_array_get_size(v___y_2305_);
v___x_2331_ = lean_array_push(v___y_2305_, v___x_2329_);
v___x_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
return v___x_2332_;
}
}
}
}
}
}
else
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
lean_dec(v_a_2315_);
v_a_2333_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2334_ = l_System_FilePath_pathExists(v___x_2142_);
if (v___x_2334_ == 0)
{
v___y_2290_ = v___y_2305_;
v___y_2291_ = v_h_2304_;
v___y_2292_ = v_a_2333_;
goto v___jp_2289_;
}
else
{
lean_object* v_idx_2335_; lean_object* v_name_2336_; lean_object* v_platform_2337_; lean_object* v_leanHash_2338_; uint64_t v_configHash_2339_; uint8_t v___x_2340_; 
v_idx_2335_ = lean_ctor_get(v_a_2333_, 0);
v_name_2336_ = lean_ctor_get(v_a_2333_, 1);
v_platform_2337_ = lean_ctor_get(v_a_2333_, 2);
v_leanHash_2338_ = lean_ctor_get(v_a_2333_, 3);
v_configHash_2339_ = lean_ctor_get_uint64(v_a_2333_, sizeof(void*)*5);
v___x_2340_ = lean_nat_dec_eq(v_idx_2335_, v_pkgIdx_2118_);
if (v___x_2340_ == 0)
{
v___y_2290_ = v___y_2305_;
v___y_2291_ = v_h_2304_;
v___y_2292_ = v_a_2333_;
goto v___jp_2289_;
}
else
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_name_eq(v_name_2336_, v_pkgName_2119_);
if (v___x_2341_ == 0)
{
v___y_2290_ = v___y_2305_;
v___y_2291_ = v_h_2304_;
v___y_2292_ = v_a_2333_;
goto v___jp_2289_;
}
else
{
uint64_t v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_unbox_uint64(v_a_2139_);
v___x_2343_ = lean_uint64_dec_eq(v_configHash_2339_, v___x_2342_);
if (v___x_2343_ == 0)
{
v___y_2290_ = v___y_2305_;
v___y_2291_ = v_h_2304_;
v___y_2292_ = v_a_2333_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = l_System_Platform_target;
v___x_2345_ = lean_string_dec_eq(v_platform_2337_, v___x_2344_);
if (v___x_2345_ == 0)
{
v___y_2290_ = v___y_2305_;
v___y_2291_ = v_h_2304_;
v___y_2292_ = v_a_2333_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = l_Lake_Env_leanGithash(v_lakeEnv_2116_);
v___x_2347_ = lean_string_dec_eq(v_leanHash_2338_, v___x_2346_);
lean_dec_ref(v___x_2346_);
if (v___x_2347_ == 0)
{
v___y_2290_ = v___y_2305_;
v___y_2291_ = v_h_2304_;
v___y_2292_ = v_a_2333_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2348_; 
lean_dec(v_a_2333_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec(v_a_2139_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v___x_2348_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2142_, v_leanOpts_2123_);
lean_dec_ref(v___x_2142_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = lean_io_prim_handle_unlock(v_h_2304_);
lean_dec(v_h_2304_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref_known(v___x_2350_, 1);
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_a_2349_);
lean_ctor_set(v___x_2351_, 1, v___y_2305_);
return v___x_2351_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_a_2349_);
v_a_2352_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2353_ = lean_io_error_to_string(v_a_2352_);
v___x_2354_ = 3;
v___x_2355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*1, v___x_2354_);
v___x_2356_ = lean_array_get_size(v___y_2305_);
v___x_2357_ = lean_array_push(v___y_2305_, v___x_2355_);
v___x_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
return v___x_2358_;
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec(v_h_2304_);
v_a_2359_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2360_ = lean_io_error_to_string(v_a_2359_);
v___x_2361_ = 3;
v___x_2362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2361_);
v___x_2363_ = lean_array_get_size(v___y_2305_);
v___x_2364_ = lean_array_push(v___y_2305_, v___x_2362_);
v___x_2365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
return v___x_2365_;
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
lean_object* v_a_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2366_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2367_ = lean_io_error_to_string(v_a_2366_);
v___x_2368_ = 3;
v___x_2369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*1, v___x_2368_);
v___x_2370_ = lean_array_get_size(v___y_2305_);
v___x_2371_ = lean_array_push(v___y_2305_, v___x_2369_);
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
return v___x_2372_;
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2373_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2374_ = lean_io_error_to_string(v_a_2373_);
v___x_2375_ = 3;
v___x_2376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*1, v___x_2375_);
v___x_2377_ = lean_array_get_size(v___y_2305_);
v___x_2378_ = lean_array_push(v___y_2305_, v___x_2376_);
v___x_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
return v___x_2379_;
}
}
else
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lake_importConfigFile___lam__0(v___x_2288_, v___x_2145_, v_h_2304_);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2288_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v_h_2147_ = v_a_2381_;
v_lakeOpts_2148_ = v_lakeOpts_2122_;
v___y_2149_ = v___y_2305_;
goto v___jp_2146_;
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_dec_ref(v___x_2145_);
lean_dec_ref(v___x_2142_);
lean_dec(v_a_2139_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2382_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2383_ = lean_io_error_to_string(v_a_2382_);
v___x_2384_ = 3;
v___x_2385_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*1, v___x_2384_);
v___x_2386_ = lean_array_get_size(v___y_2305_);
v___x_2387_ = lean_array_push(v___y_2305_, v___x_2385_);
v___x_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec_ref(v_configDir_2136_);
lean_dec(v_val_2130_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2437_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2438_ = lean_io_error_to_string(v_a_2437_);
v___x_2439_ = 3;
v___x_2440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*1, v___x_2439_);
v___x_2441_ = lean_array_get_size(v_a_2102_);
v___x_2442_ = lean_array_push(v_a_2102_, v___x_2440_);
v___x_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
return v___x_2443_;
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_configDir_2136_);
lean_dec(v_val_2130_);
lean_dec_ref(v_leanOpts_2123_);
lean_dec(v_lakeOpts_2122_);
lean_dec_ref(v_configFile_2121_);
lean_dec_ref(v_pkgDir_2120_);
lean_dec(v_pkgName_2119_);
lean_dec(v_pkgIdx_2118_);
lean_dec_ref(v_lakeEnv_2116_);
v_a_2444_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2445_ = lean_io_error_to_string(v_a_2444_);
v___x_2446_ = 3;
v___x_2447_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set_uint8(v___x_2447_, sizeof(void*)*1, v___x_2446_);
v___x_2448_ = lean_array_get_size(v_a_2102_);
v___x_2449_ = lean_array_push(v_a_2102_, v___x_2447_);
v___x_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
return v___x_2450_;
}
}
v___jp_2104_:
{
uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2107_ = 3;
lean_inc_ref(v___y_2106_);
v___x_2108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2108_, 0, v___y_2106_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*1, v___x_2107_);
v___x_2109_ = lean_array_get_size(v___y_2105_);
v___x_2110_ = lean_array_push(v___y_2105_, v___x_2108_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
return v___x_2111_;
}
v___jp_2112_:
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___y_2113_);
lean_ctor_set(v___x_2115_, 1, v_a_2114_);
return v___x_2115_;
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
