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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqImport_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_instHashableImport_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_compare(lean_object*, lean_object*);
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
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
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
lean_object* lean_io_prim_handle_flush(lean_object*);
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
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__2_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__2_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg___boxed(lean_object*);
static const lean_array_object l_Lake_importModulesUsingCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_importModulesUsingCache___closed__0 = (const lean_object*)&l_Lake_importModulesUsingCache___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__2_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
v___x_6_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__2_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__2_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__2_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_);
v___x_11_ = lean_st_mk_ref(v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_enable_initializer_execution();
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4___boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg(lean_object* v_xs_19_, lean_object* v_ys_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_zero_22_; uint8_t v_isZero_23_; 
v_zero_22_ = lean_unsigned_to_nat(0u);
v_isZero_23_ = lean_nat_dec_eq(v_x_21_, v_zero_22_);
if (v_isZero_23_ == 1)
{
lean_dec(v_x_21_);
return v_isZero_23_;
}
else
{
lean_object* v_one_24_; lean_object* v_n_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_one_24_ = lean_unsigned_to_nat(1u);
v_n_25_ = lean_nat_sub(v_x_21_, v_one_24_);
lean_dec(v_x_21_);
v___x_26_ = lean_array_fget_borrowed(v_xs_19_, v_n_25_);
v___x_27_ = lean_array_fget_borrowed(v_ys_20_, v_n_25_);
v___x_28_ = l_Lean_instBEqImport_beq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_dec(v_n_25_);
return v___x_28_;
}
else
{
v_x_21_ = v_n_25_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_xs_30_, lean_object* v_ys_31_, lean_object* v_x_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg(v_xs_30_, v_ys_31_, v_x_32_);
lean_dec_ref(v_ys_31_);
lean_dec_ref(v_xs_30_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg(lean_object* v_m_35_, lean_object* v_query_36_, lean_object* v_x_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_zero_40_; uint8_t v_isZero_41_; 
v_zero_40_ = lean_unsigned_to_nat(0u);
v_isZero_41_ = lean_nat_dec_eq(v_x_38_, v_zero_40_);
if (v_isZero_41_ == 1)
{
lean_dec(v_x_39_);
lean_dec(v_x_38_);
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(2);
return v___x_42_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
v_val_43_ = lean_ctor_get(v_x_37_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v_x_37_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_val_43_);
lean_dec(v_x_37_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_val_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
else
{
lean_object* v_keyArray_51_; lean_object* v_valueArray_52_; lean_object* v___x_53_; uint8_t v_isSome_54_; 
v_keyArray_51_ = lean_ctor_get(v_m_35_, 1);
v_valueArray_52_ = lean_ctor_get(v_m_35_, 2);
v___x_53_ = lean_array_fget_borrowed(v_keyArray_51_, v_x_39_);
v_isSome_54_ = lean_noption_is_some(v___x_53_);
if (v_isSome_54_ == 0)
{
lean_dec(v_x_38_);
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_x_39_);
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec(v_x_39_);
v_val_56_ = lean_ctor_get(v_x_37_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v_x_37_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_x_37_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_val_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
else
{
lean_object* v_one_64_; lean_object* v_n_65_; lean_object* v___y_73_; 
v_one_64_ = lean_unsigned_to_nat(1u);
v_n_65_ = lean_nat_sub(v_x_38_, v_one_64_);
lean_dec(v_x_38_);
if (v_isSome_54_ == 0)
{
goto v___jp_79_;
}
else
{
lean_object* v___x_81_; uint8_t v_isSome_82_; 
v___x_81_ = lean_array_fget_borrowed(v_valueArray_52_, v_x_39_);
v_isSome_82_ = lean_noption_is_some(v___x_81_);
if (v_isSome_82_ == 0)
{
goto v___jp_79_;
}
else
{
lean_object* v_val_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
lean_inc(v___x_53_);
v_val_83_ = lean_noption_get(v___x_53_);
v___x_84_ = lean_array_get_size(v_val_83_);
v___x_85_ = lean_array_get_size(v_query_36_);
v___x_86_ = lean_nat_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_dec(v_val_83_);
goto v___jp_66_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg(v_val_83_, v_query_36_, v___x_84_);
if (v___x_87_ == 0)
{
lean_dec(v_val_83_);
goto v___jp_66_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_89_; 
lean_dec(v_n_65_);
lean_dec(v_x_37_);
lean_inc(v___x_81_);
v_val_88_ = lean_noption_get(v___x_81_);
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v_x_39_);
lean_ctor_set(v___x_89_, 1, v_val_83_);
lean_ctor_set(v___x_89_, 2, v_val_88_);
return v___x_89_;
}
}
}
}
v___jp_66_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_array_get_size(v_keyArray_51_);
v___x_68_ = lean_nat_add(v_x_39_, v_one_64_);
lean_dec(v_x_39_);
v___x_69_ = lean_nat_dec_lt(v___x_68_, v___x_67_);
if (v___x_69_ == 0)
{
lean_dec(v___x_68_);
v_x_38_ = v_n_65_;
v_x_39_ = v_zero_40_;
goto _start;
}
else
{
v_x_38_ = v_n_65_;
v_x_39_ = v___x_68_;
goto _start;
}
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_array_get_size(v_keyArray_51_);
v___x_75_ = lean_nat_add(v_x_39_, v_one_64_);
lean_dec(v_x_39_);
v___x_76_ = lean_nat_dec_lt(v___x_75_, v___x_74_);
if (v___x_76_ == 0)
{
lean_dec(v___x_75_);
v_x_37_ = v___y_73_;
v_x_38_ = v_n_65_;
v_x_39_ = v_zero_40_;
goto _start;
}
else
{
v_x_37_ = v___y_73_;
v_x_38_ = v_n_65_;
v_x_39_ = v___x_75_;
goto _start;
}
}
v___jp_79_:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_80_; 
lean_inc(v_x_39_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v_x_39_);
v___y_73_ = v___x_80_;
goto v___jp_72_;
}
else
{
v___y_73_ = v_x_37_;
goto v___jp_72_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg___boxed(lean_object* v_m_90_, lean_object* v_query_91_, lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg(v_m_90_, v_query_91_, v_x_92_, v_x_93_, v_x_94_);
lean_dec_ref(v_query_91_);
lean_dec_ref(v_m_90_);
return v_res_95_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object* v_as_96_, size_t v_i_97_, size_t v_stop_98_, uint64_t v_b_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_usize_dec_eq(v_i_97_, v_stop_98_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; uint64_t v___x_102_; uint64_t v___x_103_; size_t v___x_104_; size_t v___x_105_; 
v___x_101_ = lean_array_uget_borrowed(v_as_96_, v_i_97_);
v___x_102_ = l_Lean_instHashableImport_hash(v___x_101_);
v___x_103_ = lean_uint64_mix_hash(v_b_99_, v___x_102_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_97_, v___x_104_);
v_i_97_ = v___x_105_;
v_b_99_ = v___x_103_;
goto _start;
}
else
{
return v_b_99_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object* v_as_107_, lean_object* v_i_108_, lean_object* v_stop_109_, lean_object* v_b_110_){
_start:
{
size_t v_i_boxed_111_; size_t v_stop_boxed_112_; uint64_t v_b_boxed_113_; uint64_t v_res_114_; lean_object* v_r_115_; 
v_i_boxed_111_ = lean_unbox_usize(v_i_108_);
lean_dec(v_i_108_);
v_stop_boxed_112_ = lean_unbox_usize(v_stop_109_);
lean_dec(v_stop_109_);
v_b_boxed_113_ = lean_unbox_uint64(v_b_110_);
lean_dec_ref(v_b_110_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_as_107_, v_i_boxed_111_, v_stop_boxed_112_, v_b_boxed_113_);
lean_dec_ref(v_as_107_);
v_r_115_ = lean_box_uint64(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object* v_m_116_, lean_object* v_query_117_){
_start:
{
lean_object* v_keyArray_118_; lean_object* v___x_119_; uint64_t v___y_121_; uint64_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_keyArray_118_ = lean_ctor_get(v_m_116_, 1);
v___x_119_ = lean_array_get_size(v_keyArray_118_);
v___x_136_ = 7ULL;
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_query_117_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
v___y_121_ = v___x_136_;
goto v___jp_120_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_le(v___x_138_, v___x_138_);
if (v___x_140_ == 0)
{
if (v___x_139_ == 0)
{
v___y_121_ = v___x_136_;
goto v___jp_120_;
}
else
{
size_t v___x_141_; size_t v___x_142_; uint64_t v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_138_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_query_117_, v___x_141_, v___x_142_, v___x_136_);
v___y_121_ = v___x_143_;
goto v___jp_120_;
}
}
else
{
size_t v___x_144_; size_t v___x_145_; uint64_t v___x_146_; 
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_138_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_query_117_, v___x_144_, v___x_145_, v___x_136_);
v___y_121_ = v___x_146_;
goto v___jp_120_;
}
}
v___jp_120_:
{
uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v_fold_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_122_ = 32ULL;
v___x_123_ = lean_uint64_shift_right(v___y_121_, v___x_122_);
v_fold_124_ = lean_uint64_xor(v___y_121_, v___x_123_);
v___x_125_ = 16ULL;
v___x_126_ = lean_uint64_shift_right(v_fold_124_, v___x_125_);
v___x_127_ = lean_uint64_xor(v_fold_124_, v___x_126_);
v___x_128_ = lean_uint64_to_usize(v___x_127_);
v___x_129_ = lean_usize_of_nat(v___x_119_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v___x_129_, v___x_130_);
v___x_132_ = lean_usize_land(v___x_128_, v___x_131_);
v___x_133_ = lean_usize_to_nat(v___x_132_);
v___x_134_ = lean_box(0);
v___x_135_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg(v_m_116_, v_query_117_, v___x_134_, v___x_119_, v___x_133_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg___boxed(lean_object* v_m_147_, lean_object* v_query_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_147_, v_query_148_);
lean_dec_ref(v_query_148_);
lean_dec_ref(v_m_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object* v_m_150_, lean_object* v_query_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_150_, v_query_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_index_153_; lean_object* v_key_154_; lean_object* v_value_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_index_153_ = lean_ctor_get(v___x_152_, 0);
v_key_154_ = lean_ctor_get(v___x_152_, 1);
v_value_155_ = lean_ctor_get(v___x_152_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_152_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_value_155_);
lean_inc(v_key_154_);
lean_inc(v_index_153_);
lean_dec(v___x_152_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_index_153_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_key_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_value_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v___x_163_; 
lean_dec(v___x_152_);
v___x_163_ = lean_box(1);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object* v_m_164_, lean_object* v_query_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_m_164_, v_query_165_);
lean_dec_ref(v_query_165_);
lean_dec_ref(v_m_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object* v_m_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_m_167_, v_a_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_value_170_; lean_object* v___x_171_; 
v_value_170_ = lean_ctor_get(v___x_169_, 2);
lean_inc(v_value_170_);
lean_dec_ref_known(v___x_169_, 3);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v_value_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object* v_m_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_173_, v_a_174_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_m_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg(lean_object* v_b_176_, lean_object* v_acc_177_, lean_object* v_i_178_){
_start:
{
lean_object* v___y_180_; lean_object* v_keyArray_188_; lean_object* v_valueArray_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_keyArray_188_ = lean_ctor_get(v_b_176_, 1);
v_valueArray_189_ = lean_ctor_get(v_b_176_, 2);
v___x_190_ = lean_array_get_size(v_keyArray_188_);
v___x_191_ = lean_nat_dec_lt(v_i_178_, v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v_i_178_);
return v_acc_177_;
}
else
{
lean_object* v___x_192_; uint8_t v_isSome_193_; 
v___x_192_ = lean_array_fget_borrowed(v_keyArray_188_, v_i_178_);
v_isSome_193_ = lean_noption_is_some(v___x_192_);
if (v_isSome_193_ == 0)
{
goto v___jp_184_;
}
else
{
lean_object* v___x_194_; uint8_t v_isSome_195_; 
v___x_194_ = lean_array_fget_borrowed(v_valueArray_189_, v_i_178_);
v_isSome_195_ = lean_noption_is_some(v___x_194_);
if (v_isSome_195_ == 0)
{
goto v___jp_184_;
}
else
{
lean_object* v_val_196_; lean_object* v_val_197_; lean_object* v_i_199_; lean_object* v___x_204_; 
lean_inc(v___x_192_);
v_val_196_ = lean_noption_get(v___x_192_);
lean_inc(v___x_194_);
v_val_197_ = lean_noption_get(v___x_194_);
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v_acc_177_, v_val_196_);
switch(lean_obj_tag(v___x_204_))
{
case 0:
{
lean_object* v_index_205_; lean_object* v_size_206_; lean_object* v___x_207_; 
v_index_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_205_);
lean_dec_ref_known(v___x_204_, 3);
v_size_206_ = lean_ctor_get(v_acc_177_, 0);
lean_inc(v_size_206_);
v___x_207_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_177_, v_size_206_, v_index_205_, v_val_196_, v_val_197_);
lean_dec(v_index_205_);
v___y_180_ = v___x_207_;
goto v___jp_179_;
}
case 1:
{
lean_object* v_index_208_; 
v_index_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_204_, 1);
v_i_199_ = v_index_208_;
goto v___jp_198_;
}
default: 
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_177_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_index_211_; 
v_index_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_210_, 1);
v_i_199_ = v_index_211_;
goto v___jp_198_;
}
else
{
lean_dec(v_val_197_);
lean_dec(v_val_196_);
v___y_180_ = v_acc_177_;
goto v___jp_179_;
}
}
}
v___jp_198_:
{
lean_object* v_size_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_size_200_ = lean_ctor_get(v_acc_177_, 0);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_size_200_, v___x_201_);
v___x_203_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_177_, v___x_202_, v_i_199_, v_val_196_, v_val_197_);
lean_dec(v_i_199_);
v___y_180_ = v___x_203_;
goto v___jp_179_;
}
}
}
}
v___jp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_178_, v___x_181_);
lean_dec(v_i_178_);
v_acc_177_ = v___y_180_;
v_i_178_ = v___x_182_;
goto _start;
}
v___jp_184_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_i_178_, v___x_185_);
lean_dec(v_i_178_);
v_i_178_ = v___x_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_b_212_, lean_object* v_acc_213_, lean_object* v_i_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg(v_b_212_, v_acc_213_, v_i_214_);
lean_dec_ref(v_b_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg(lean_object* v_init_216_, lean_object* v_b_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg(v_b_217_, v_init_216_, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg___boxed(lean_object* v_init_220_, lean_object* v_b_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg(v_init_220_, v_b_221_);
lean_dec_ref(v_b_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(lean_object* v_m_223_){
_start:
{
lean_object* v_keyArray_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_cellCount_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_target_231_; lean_object* v___x_232_; 
v_keyArray_224_ = lean_ctor_get(v_m_223_, 1);
v___x_225_ = lean_array_get_size(v_keyArray_224_);
v___x_226_ = lean_unsigned_to_nat(2u);
v_cellCount_227_ = lean_nat_mul(v___x_225_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_227_);
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_227_);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_227_);
v_target_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_231_, 0, v___x_228_);
lean_ctor_set(v_target_231_, 1, v___x_229_);
lean_ctor_set(v_target_231_, 2, v___x_230_);
v___x_232_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg(v_target_231_, v_m_223_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg___boxed(lean_object* v_m_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(v_m_233_);
lean_dec_ref(v_m_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* v_imports_237_, lean_object* v_opts_238_, uint32_t v_trustLevel_239_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
v___x_242_ = lean_st_ref_get(v___x_241_);
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v___x_242_, v_imports_237_);
lean_dec(v___x_242_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v_opts_238_);
lean_dec_ref(v_imports_237_);
v_val_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_val_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v___x_243_);
v___x_252_ = lean_enable_initializer_execution();
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = ((lean_object*)(l_Lake_importModulesUsingCache___closed__0));
v___x_255_ = 0;
v___x_256_ = 1;
v___x_257_ = 2;
v___x_258_ = lean_box(1);
lean_inc_ref(v_imports_237_);
v___x_259_ = l_Lean_importModules(v_imports_237_, v_opts_238_, v_trustLevel_239_, v___x_254_, v___x_255_, v___x_256_, v___x_257_, v___x_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_333_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_333_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_333_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_333_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___y_266_; lean_object* v___y_272_; lean_object* v_i_273_; lean_object* v___y_279_; lean_object* v___y_288_; lean_object* v_i_289_; lean_object* v___x_303_; 
v___x_264_ = lean_st_ref_take(v___x_241_);
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_264_, v_imports_237_);
switch(lean_obj_tag(v___x_303_))
{
case 0:
{
lean_object* v_index_304_; lean_object* v_size_305_; lean_object* v___x_306_; 
v_index_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_index_304_);
lean_dec_ref_known(v___x_303_, 3);
v_size_305_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_size_305_);
lean_inc(v_a_260_);
v___x_306_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_264_, v_size_305_, v_index_304_, v_imports_237_, v_a_260_);
lean_dec(v_index_304_);
v___y_266_ = v___x_306_;
goto v___jp_265_;
}
case 1:
{
lean_object* v_index_307_; lean_object* v_size_308_; lean_object* v_keyArray_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_index_307_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_index_307_);
lean_dec_ref_known(v___x_303_, 1);
v_size_308_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_size_308_);
v_keyArray_309_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_keyArray_309_);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_size_308_, v___x_310_);
lean_dec(v_size_308_);
v___x_312_ = lean_array_get_size(v_keyArray_309_);
lean_dec_ref(v_keyArray_309_);
v___x_313_ = lean_nat_dec_lt(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec(v___x_311_);
lean_dec(v_index_307_);
goto v___jp_294_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_314_ = lean_unsigned_to_nat(4u);
v___x_315_ = lean_nat_mul(v___x_311_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(3u);
v___x_317_ = lean_nat_mul(v___x_312_, v___x_316_);
v___x_318_ = lean_nat_dec_le(v___x_315_, v___x_317_);
lean_dec(v___x_317_);
lean_dec(v___x_315_);
if (v___x_318_ == 0)
{
lean_dec(v___x_311_);
lean_dec(v_index_307_);
goto v___jp_294_;
}
else
{
lean_object* v___x_319_; 
lean_inc(v_a_260_);
v___x_319_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_264_, v___x_311_, v_index_307_, v_imports_237_, v_a_260_);
lean_dec(v_index_307_);
v___y_266_ = v___x_319_;
goto v___jp_265_;
}
}
}
default: 
{
lean_object* v_size_320_; lean_object* v_keyArray_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_size_320_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_size_320_);
v_keyArray_321_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_keyArray_321_);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_size_320_, v___x_322_);
lean_dec(v_size_320_);
v___x_324_ = lean_array_get_size(v_keyArray_321_);
lean_dec_ref(v_keyArray_321_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v___x_323_);
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(v___x_264_);
lean_dec(v___x_264_);
v___y_279_ = v___x_326_;
goto v___jp_278_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_327_ = lean_unsigned_to_nat(4u);
v___x_328_ = lean_nat_mul(v___x_323_, v___x_327_);
lean_dec(v___x_323_);
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = lean_nat_mul(v___x_324_, v___x_329_);
v___x_331_ = lean_nat_dec_le(v___x_328_, v___x_330_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(v___x_264_);
lean_dec(v___x_264_);
v___y_279_ = v___x_332_;
goto v___jp_278_;
}
else
{
v___y_279_ = v___x_264_;
goto v___jp_278_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_st_ref_put(v___x_241_, v___y_266_);
if (v_isShared_263_ == 0)
{
v___x_269_ = v___x_262_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_260_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
v___jp_271_:
{
lean_object* v_size_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_size_274_ = lean_ctor_get(v___y_272_, 0);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_size_274_, v___x_275_);
lean_inc(v_a_260_);
v___x_277_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_272_, v___x_276_, v_i_273_, v_imports_237_, v_a_260_);
lean_dec(v_i_273_);
v___y_266_ = v___x_277_;
goto v___jp_265_;
}
v___jp_278_:
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v___y_279_, v_imports_237_);
switch(lean_obj_tag(v___x_280_))
{
case 0:
{
lean_object* v_index_281_; lean_object* v_size_282_; lean_object* v___x_283_; 
v_index_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_281_);
lean_dec_ref_known(v___x_280_, 3);
v_size_282_ = lean_ctor_get(v___y_279_, 0);
lean_inc(v_size_282_);
lean_inc(v_a_260_);
v___x_283_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_279_, v_size_282_, v_index_281_, v_imports_237_, v_a_260_);
lean_dec(v_index_281_);
v___y_266_ = v___x_283_;
goto v___jp_265_;
}
case 1:
{
lean_object* v_index_284_; 
v_index_284_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_284_);
lean_dec_ref_known(v___x_280_, 1);
v___y_272_ = v___y_279_;
v_i_273_ = v_index_284_;
goto v___jp_271_;
}
default: 
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_279_, v___x_253_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_index_286_; 
v_index_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_index_286_);
lean_dec_ref_known(v___x_285_, 1);
v___y_272_ = v___y_279_;
v_i_273_ = v_index_286_;
goto v___jp_271_;
}
else
{
lean_dec_ref(v_imports_237_);
v___y_266_ = v___y_279_;
goto v___jp_265_;
}
}
}
}
v___jp_287_:
{
lean_object* v_size_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_size_290_ = lean_ctor_get(v___y_288_, 0);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_size_290_, v___x_291_);
lean_inc(v_a_260_);
v___x_293_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_288_, v___x_292_, v_i_289_, v_imports_237_, v_a_260_);
lean_dec(v_i_289_);
v___y_266_ = v___x_293_;
goto v___jp_265_;
}
v___jp_294_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(v___x_264_);
lean_dec(v___x_264_);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_295_, v_imports_237_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_index_297_; lean_object* v_size_298_; lean_object* v___x_299_; 
v_index_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_index_297_);
lean_dec_ref_known(v___x_296_, 3);
v_size_298_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_size_298_);
lean_inc(v_a_260_);
v___x_299_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_295_, v_size_298_, v_index_297_, v_imports_237_, v_a_260_);
lean_dec(v_index_297_);
v___y_266_ = v___x_299_;
goto v___jp_265_;
}
case 1:
{
lean_object* v_index_300_; 
v_index_300_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_296_, 1);
v___y_288_ = v___x_295_;
v_i_289_ = v_index_300_;
goto v___jp_287_;
}
default: 
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_295_, v___x_253_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_index_302_; 
v_index_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_index_302_);
lean_dec_ref_known(v___x_301_, 1);
v___y_288_ = v___x_295_;
v_i_289_ = v_index_302_;
goto v___jp_287_;
}
else
{
lean_dec_ref(v_imports_237_);
v___y_266_ = v___x_295_;
goto v___jp_265_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_imports_237_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* v_imports_334_, lean_object* v_opts_335_, lean_object* v_trustLevel_336_, lean_object* v_a_337_){
_start:
{
uint32_t v_trustLevel_boxed_338_; lean_object* v_res_339_; 
v_trustLevel_boxed_338_ = lean_unbox_uint32(v_trustLevel_336_);
lean_dec(v_trustLevel_336_);
v_res_339_ = l_Lake_importModulesUsingCache(v_imports_334_, v_opts_335_, v_trustLevel_boxed_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object* v_00_u03b2_340_, lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_341_, v_a_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object* v_00_u03b2_344_, lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_344_, v_m_345_, v_a_346_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_m_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1(lean_object* v_00_u03b2_348_, lean_object* v_m_349_, lean_object* v_query_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_349_, v_query_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1___boxed(lean_object* v_00_u03b2_352_, lean_object* v_m_353_, lean_object* v_query_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1(v_00_u03b2_352_, v_m_353_, v_query_354_);
lean_dec_ref(v_query_354_);
lean_dec_ref(v_m_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2(lean_object* v_00_u03b2_356_, lean_object* v_m_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___redArg(v_m_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2___boxed(lean_object* v_00_u03b2_359_, lean_object* v_m_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2(v_00_u03b2_359_, v_m_360_);
lean_dec_ref(v_m_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object* v_00_u03b2_362_, lean_object* v_m_363_, lean_object* v_query_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_m_363_, v_query_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_366_, lean_object* v_m_367_, lean_object* v_query_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_366_, v_m_367_, v_query_368_);
lean_dec_ref(v_query_368_);
lean_dec_ref(v_m_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2(lean_object* v_00_u03b2_370_, lean_object* v_m_371_, lean_object* v_query_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___redArg(v_m_371_, v_query_372_, v_x_373_, v_x_374_, v_x_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2___boxed(lean_object* v_00_u03b2_378_, lean_object* v_m_379_, lean_object* v_query_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2(v_00_u03b2_378_, v_m_379_, v_query_380_, v_x_381_, v_x_382_, v_x_383_, v_x_384_);
lean_dec_ref(v_query_380_);
lean_dec_ref(v_m_379_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5(lean_object* v_00_u03b2_386_, lean_object* v_init_387_, lean_object* v_b_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___redArg(v_init_387_, v_b_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5___boxed(lean_object* v_00_u03b2_390_, lean_object* v_init_391_, lean_object* v_b_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5(v_00_u03b2_390_, v_init_391_, v_b_392_);
lean_dec_ref(v_b_392_);
return v_res_393_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3(lean_object* v_xs_394_, lean_object* v_ys_395_, lean_object* v_hsz_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___redArg(v_xs_394_, v_ys_395_, v_x_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3___boxed(lean_object* v_xs_400_, lean_object* v_ys_401_, lean_object* v_hsz_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_importModulesUsingCache_spec__1_spec__2_spec__3(v_xs_400_, v_ys_401_, v_hsz_402_, v_x_403_, v_x_404_);
lean_dec_ref(v_ys_401_);
lean_dec_ref(v_xs_400_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_407_, lean_object* v_b_408_, lean_object* v_acc_409_, lean_object* v_i_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___redArg(v_b_408_, v_acc_409_, v_i_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_412_, lean_object* v_b_413_, lean_object* v_acc_414_, lean_object* v_i_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_importModulesUsingCache_spec__2_spec__5_spec__7(v_00_u03b2_412_, v_b_413_, v_acc_414_, v_i_415_);
lean_dec_ref(v_b_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object* v_header_418_, lean_object* v_opts_419_, lean_object* v_inputCtx_420_, lean_object* v_a_421_){
_start:
{
uint8_t v___x_423_; lean_object* v_imports_424_; uint32_t v___x_425_; lean_object* v___x_426_; 
v___x_423_ = 1;
lean_inc(v_header_418_);
v_imports_424_ = l_Lean_Elab_HeaderSyntax_imports(v_header_418_, v___x_423_);
v___x_425_ = 1024;
v___x_426_ = l_Lake_importModulesUsingCache(v_imports_424_, v_opts_419_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_inputCtx_420_);
lean_dec(v_header_418_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_435_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v_a_427_);
lean_ctor_set(v___x_431_, 1, v_a_421_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v_fileName_437_; lean_object* v_fileMap_438_; uint8_t v___x_439_; lean_object* v___y_441_; lean_object* v___x_470_; 
v_a_436_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_426_, 1);
v_fileName_437_ = lean_ctor_get(v_inputCtx_420_, 1);
lean_inc_ref(v_fileName_437_);
v_fileMap_438_ = lean_ctor_get(v_inputCtx_420_, 2);
lean_inc_ref(v_fileMap_438_);
lean_dec_ref(v_inputCtx_420_);
v___x_439_ = 0;
v___x_470_ = l_Lean_Syntax_getPos_x3f(v_header_418_, v___x_439_);
lean_dec(v_header_418_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___y_441_ = v___x_471_;
goto v___jp_440_;
}
else
{
lean_object* v_val_472_; 
v_val_472_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_470_, 1);
v___y_441_ = v_val_472_;
goto v___jp_440_;
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint32_t v___x_450_; lean_object* v___x_451_; 
v___x_442_ = l_Lean_FileMap_toPosition(v_fileMap_438_, v___y_441_);
lean_dec(v___y_441_);
v___x_443_ = lean_box(0);
v___x_444_ = 2;
v___x_445_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0));
v___x_446_ = lean_io_error_to_string(v_a_436_);
v___x_447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
v___x_448_ = l_Lean_MessageData_ofFormat(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_449_, 0, v_fileName_437_);
lean_ctor_set(v___x_449_, 1, v___x_442_);
lean_ctor_set(v___x_449_, 2, v___x_443_);
lean_ctor_set(v___x_449_, 3, v___x_445_);
lean_ctor_set(v___x_449_, 4, v___x_448_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*5, v___x_439_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*5 + 1, v___x_444_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*5 + 2, v___x_439_);
v___x_450_ = 0;
v___x_451_ = l_Lean_mkEmptyEnvironment(v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_461_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_461_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_456_ = l_Lean_MessageLog_add(v___x_449_, v_a_421_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_a_452_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref_known(v___x_449_, 5);
lean_dec_ref(v_a_421_);
v_a_462_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_451_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_451_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object* v_header_473_, lean_object* v_opts_474_, lean_object* v_inputCtx_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_473_, v_opts_474_, v_inputCtx_475_, v_a_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object* v_x_483_, lean_object* v___y_484_){
_start:
{
uint8_t v_isSilent_486_; 
v_isSilent_486_ = lean_ctor_get_uint8(v_x_483_, sizeof(void*)*5 + 2);
if (v_isSilent_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = l_Lake_LogEntry_ofMessage(v_x_483_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_array_push(v___y_484_, v___x_487_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v_x_483_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___y_484_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_493_, v___y_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_497_, lean_object* v_as_498_, size_t v_i_499_, size_t v_stop_500_, lean_object* v_b_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_499_, v_stop_500_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_498_, v_i_499_);
lean_inc_ref(v_f_497_);
lean_inc(v___x_505_);
v___x_506_ = lean_apply_3(v_f_497_, v___x_505_, v___y_502_, lean_box(0));
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v_a_508_; size_t v___x_509_; size_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
v_a_508_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_506_, 2);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_499_, v___x_509_);
v_i_499_ = v___x_510_;
v_b_501_ = v_a_507_;
v___y_502_ = v_a_508_;
goto _start;
}
else
{
lean_dec_ref(v_f_497_);
return v___x_506_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_f_497_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_b_501_);
lean_ctor_set(v___x_512_, 1, v___y_502_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_513_, lean_object* v_as_514_, lean_object* v_i_515_, lean_object* v_stop_516_, lean_object* v_b_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
size_t v_i_boxed_520_; size_t v_stop_boxed_521_; lean_object* v_res_522_; 
v_i_boxed_520_ = lean_unbox_usize(v_i_515_);
lean_dec(v_i_515_);
v_stop_boxed_521_ = lean_unbox_usize(v_stop_516_);
lean_dec(v_stop_516_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_513_, v_as_514_, v_i_boxed_520_, v_stop_boxed_521_, v_b_517_, v___y_518_);
lean_dec_ref(v_as_514_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_523_, lean_object* v_x_524_, lean_object* v___y_525_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v_cs_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_cs_527_ = lean_ctor_get(v_x_524_, 0);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_array_get_size(v_cs_527_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_nat_dec_lt(v___x_528_, v___x_529_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_dec_ref(v_f_523_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___y_525_);
return v___x_532_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_le(v___x_529_, v___x_529_);
if (v___x_533_ == 0)
{
if (v___x_531_ == 0)
{
lean_object* v___x_534_; 
lean_dec_ref(v_f_523_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_530_);
lean_ctor_set(v___x_534_, 1, v___y_525_);
return v___x_534_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((size_t)0ULL);
v___x_536_ = lean_usize_of_nat(v___x_529_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_523_, v_cs_527_, v___x_535_, v___x_536_, v___x_530_, v___y_525_);
return v___x_537_;
}
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_529_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_523_, v_cs_527_, v___x_538_, v___x_539_, v___x_530_, v___y_525_);
return v___x_540_;
}
}
}
else
{
lean_object* v_vs_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_vs_541_ = lean_ctor_get(v_x_524_, 0);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_array_get_size(v_vs_541_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_nat_dec_lt(v___x_542_, v___x_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec_ref(v_f_523_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___y_525_);
return v___x_546_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = lean_nat_dec_le(v___x_543_, v___x_543_);
if (v___x_547_ == 0)
{
if (v___x_545_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v_f_523_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_544_);
lean_ctor_set(v___x_548_, 1, v___y_525_);
return v___x_548_;
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_543_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_523_, v_vs_541_, v___x_549_, v___x_550_, v___x_544_, v___y_525_);
return v___x_551_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_543_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_523_, v_vs_541_, v___x_552_, v___x_553_, v___x_544_, v___y_525_);
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_555_, lean_object* v_as_556_, size_t v_i_557_, size_t v_stop_558_, lean_object* v_b_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_562_; 
v___x_562_ = lean_usize_dec_eq(v_i_557_, v_stop_558_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_array_uget_borrowed(v_as_556_, v_i_557_);
lean_inc_ref(v_f_555_);
v___x_564_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_555_, v___x_563_, v___y_560_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v_a_566_; size_t v___x_567_; size_t v___x_568_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
v_a_566_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_564_, 2);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_557_, v___x_567_);
v_i_557_ = v___x_568_;
v_b_559_ = v_a_565_;
v___y_560_ = v_a_566_;
goto _start;
}
else
{
lean_dec_ref(v_f_555_);
return v___x_564_;
}
}
else
{
lean_object* v___x_570_; 
lean_dec_ref(v_f_555_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_b_559_);
lean_ctor_set(v___x_570_, 1, v___y_560_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_571_, lean_object* v_as_572_, lean_object* v_i_573_, lean_object* v_stop_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
size_t v_i_boxed_578_; size_t v_stop_boxed_579_; lean_object* v_res_580_; 
v_i_boxed_578_ = lean_unbox_usize(v_i_573_);
lean_dec(v_i_573_);
v_stop_boxed_579_ = lean_unbox_usize(v_stop_574_);
lean_dec(v_stop_574_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_571_, v_as_572_, v_i_boxed_578_, v_stop_boxed_579_, v_b_575_, v___y_576_);
lean_dec_ref(v_as_572_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_581_, v_x_582_, v___y_583_);
lean_dec_ref(v_x_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_586_, lean_object* v_t_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_root_590_; lean_object* v_tail_591_; lean_object* v___x_592_; 
v_root_590_ = lean_ctor_get(v_t_587_, 0);
v_tail_591_ = lean_ctor_get(v_t_587_, 1);
lean_inc_ref(v_f_586_);
v___x_592_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_586_, v_root_590_, v___y_588_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_614_; 
v_a_593_ = lean_ctor_get(v___x_592_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_615_);
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_614_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_614_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v_tail_591_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_600_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_f_586_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_599_);
v___x_602_ = v___x_595_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_a_593_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_le(v___x_598_, v___x_598_);
if (v___x_604_ == 0)
{
if (v___x_600_ == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v_f_586_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_599_);
v___x_606_ = v___x_595_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_a_593_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_595_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_598_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_586_, v_tail_591_, v___x_608_, v___x_609_, v___x_599_, v_a_593_);
return v___x_610_;
}
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_595_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_598_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_586_, v_tail_591_, v___x_611_, v___x_612_, v___x_599_, v_a_593_);
return v___x_613_;
}
}
}
}
else
{
lean_dec_ref(v_f_586_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_616_, lean_object* v_t_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_616_, v_t_617_, v___y_618_);
lean_dec_ref(v_t_617_);
return v_res_620_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_622_, lean_object* v_x_623_, size_t v_x_624_, size_t v_x_625_, lean_object* v___y_626_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v_cs_628_; lean_object* v___x_629_; size_t v___x_630_; lean_object* v_j_631_; lean_object* v___x_632_; size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v_cs_628_ = lean_ctor_get(v_x_623_, 0);
v___x_629_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_630_ = lean_usize_shift_right(v_x_624_, v_x_625_);
v_j_631_ = lean_usize_to_nat(v___x_630_);
v___x_632_ = lean_array_get_borrowed(v___x_629_, v_cs_628_, v_j_631_);
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_shift_left(v___x_633_, v_x_625_);
v___x_635_ = lean_usize_sub(v___x_634_, v___x_633_);
v___x_636_ = lean_usize_land(v_x_624_, v___x_635_);
v___x_637_ = ((size_t)5ULL);
v___x_638_ = lean_usize_sub(v_x_625_, v___x_637_);
lean_inc_ref(v_f_622_);
v___x_639_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_622_, v___x_632_, v___x_636_, v___x_638_, v___y_626_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_662_; 
v_a_640_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_663_);
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_662_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_662_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_j_631_, v___x_644_);
lean_dec(v_j_631_);
v___x_646_ = lean_array_get_size(v_cs_628_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; 
lean_dec(v___x_645_);
lean_dec_ref(v_f_622_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_647_);
v___x_650_ = v___x_642_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_640_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_le(v___x_646_, v___x_646_);
if (v___x_652_ == 0)
{
if (v___x_648_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v___x_645_);
lean_dec_ref(v_f_622_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_647_);
v___x_654_ = v___x_642_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_a_640_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
lean_del_object(v___x_642_);
v___x_656_ = lean_usize_of_nat(v___x_645_);
lean_dec(v___x_645_);
v___x_657_ = lean_usize_of_nat(v___x_646_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_622_, v_cs_628_, v___x_656_, v___x_657_, v___x_647_, v_a_640_);
return v___x_658_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
lean_del_object(v___x_642_);
v___x_659_ = lean_usize_of_nat(v___x_645_);
lean_dec(v___x_645_);
v___x_660_ = lean_usize_of_nat(v___x_646_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_622_, v_cs_628_, v___x_659_, v___x_660_, v___x_647_, v_a_640_);
return v___x_661_;
}
}
}
}
else
{
lean_dec(v_j_631_);
lean_dec_ref(v_f_622_);
return v___x_639_;
}
}
else
{
lean_object* v_vs_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_vs_664_ = lean_ctor_get(v_x_623_, 0);
v___x_665_ = lean_usize_to_nat(v_x_624_);
v___x_666_ = lean_array_get_size(v_vs_664_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec(v___x_665_);
lean_dec_ref(v_f_622_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___y_626_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v___x_666_, v___x_666_);
if (v___x_670_ == 0)
{
if (v___x_668_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v___x_665_);
lean_dec_ref(v_f_622_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_667_);
lean_ctor_set(v___x_671_, 1, v___y_626_);
return v___x_671_;
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_usize_of_nat(v___x_665_);
lean_dec(v___x_665_);
v___x_673_ = lean_usize_of_nat(v___x_666_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_622_, v_vs_664_, v___x_672_, v___x_673_, v___x_667_, v___y_626_);
return v___x_674_;
}
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_usize_of_nat(v___x_665_);
lean_dec(v___x_665_);
v___x_676_ = lean_usize_of_nat(v___x_666_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_622_, v_vs_664_, v___x_675_, v___x_676_, v___x_667_, v___y_626_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
size_t v_x_13978__boxed_684_; size_t v_x_13979__boxed_685_; lean_object* v_res_686_; 
v_x_13978__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_x_13979__boxed_685_ = lean_unbox_usize(v_x_681_);
lean_dec(v_x_681_);
v_res_686_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_678_, v_x_679_, v_x_13978__boxed_684_, v_x_13979__boxed_685_, v___y_682_);
lean_dec_ref(v_x_679_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_687_, lean_object* v_t_688_, lean_object* v_start_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_nat_dec_eq(v_start_689_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v_root_694_; lean_object* v_tail_695_; size_t v_shift_696_; lean_object* v_tailOff_697_; uint8_t v___x_698_; 
v_root_694_ = lean_ctor_get(v_t_688_, 0);
v_tail_695_ = lean_ctor_get(v_t_688_, 1);
v_shift_696_ = lean_ctor_get_usize(v_t_688_, 4);
v_tailOff_697_ = lean_ctor_get(v_t_688_, 3);
v___x_698_ = lean_nat_dec_le(v_tailOff_697_, v_start_689_);
if (v___x_698_ == 0)
{
size_t v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_usize_of_nat(v_start_689_);
lean_inc_ref(v_f_687_);
v___x_700_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_687_, v_root_694_, v___x_699_, v_shift_696_, v___y_690_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_721_; 
v_a_701_ = lean_ctor_get(v___x_700_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_700_, 0);
lean_dec(v_unused_722_);
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_721_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_721_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_array_get_size(v_tail_695_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_nat_dec_lt(v___x_692_, v___x_705_);
if (v___x_707_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_f_687_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_701_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
uint8_t v___x_711_; 
v___x_711_ = lean_nat_dec_le(v___x_705_, v___x_705_);
if (v___x_711_ == 0)
{
if (v___x_707_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_f_687_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_713_ = v___x_703_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_a_701_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
lean_del_object(v___x_703_);
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_705_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_687_, v_tail_695_, v___x_715_, v___x_716_, v___x_706_, v_a_701_);
return v___x_717_;
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
lean_del_object(v___x_703_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_705_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_687_, v_tail_695_, v___x_718_, v___x_719_, v___x_706_, v_a_701_);
return v___x_720_;
}
}
}
}
else
{
lean_dec_ref(v_f_687_);
return v___x_700_;
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_723_ = lean_nat_sub(v_start_689_, v_tailOff_697_);
v___x_724_ = lean_array_get_size(v_tail_695_);
v___x_725_ = lean_box(0);
v___x_726_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v___x_723_);
lean_dec_ref(v_f_687_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___y_690_);
return v___x_727_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_le(v___x_724_, v___x_724_);
if (v___x_728_ == 0)
{
if (v___x_726_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v___x_723_);
lean_dec_ref(v_f_687_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_725_);
lean_ctor_set(v___x_729_, 1, v___y_690_);
return v___x_729_;
}
else
{
size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_usize_of_nat(v___x_723_);
lean_dec(v___x_723_);
v___x_731_ = lean_usize_of_nat(v___x_724_);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_687_, v_tail_695_, v___x_730_, v___x_731_, v___x_725_, v___y_690_);
return v___x_732_;
}
}
else
{
size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_usize_of_nat(v___x_723_);
lean_dec(v___x_723_);
v___x_734_ = lean_usize_of_nat(v___x_724_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_687_, v_tail_695_, v___x_733_, v___x_734_, v___x_725_, v___y_690_);
return v___x_735_;
}
}
}
}
else
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_687_, v_t_688_, v___y_690_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_737_, lean_object* v_t_738_, lean_object* v_start_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_737_, v_t_738_, v_start_739_, v___y_740_);
lean_dec(v_start_739_);
lean_dec_ref(v_t_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_743_, lean_object* v_f_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_unreported_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_unreported_747_ = lean_ctor_get(v_log_743_, 1);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_744_, v_unreported_747_, v___x_748_, v___y_745_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_750_, lean_object* v_f_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_750_, v_f_751_, v___y_752_);
lean_dec_ref(v_log_750_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_757_, lean_object* v_pkgName_758_, lean_object* v_pkgDir_759_, lean_object* v_lakeOpts_760_, lean_object* v_leanOpts_761_, lean_object* v_configFile_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_IO_FS_readFile(v_configFile_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = 1;
v___x_768_ = lean_string_utf8_byte_size(v_a_766_);
lean_inc_ref(v_configFile_762_);
v___x_769_ = l_Lean_Parser_mkInputContext___redArg(v_a_766_, v_configFile_762_, v___x_767_, v___x_768_);
lean_inc_ref(v___x_769_);
v___x_770_ = l_Lean_Parser_parseHeader(v___x_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_869_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_869_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_869_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_869_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_snd_775_; lean_object* v_fst_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_868_; 
v_snd_775_ = lean_ctor_get(v_a_771_, 1);
lean_inc(v_snd_775_);
v_fst_776_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_fst_776_);
lean_dec(v_a_771_);
v_fst_777_ = lean_ctor_get(v_snd_775_, 0);
v_snd_778_ = lean_ctor_get(v_snd_775_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_snd_775_);
if (v_isSharedCheck_868_ == 0)
{
v___x_780_ = v_snd_775_;
v_isShared_781_ = v_isSharedCheck_868_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
lean_dec(v_snd_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_868_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; 
lean_inc_ref(v___x_769_);
lean_inc_ref(v_leanOpts_761_);
v___x_782_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_776_, v_leanOpts_761_, v___x_769_, v_snd_778_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_858_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_858_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_858_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_858_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_fst_787_; lean_object* v_snd_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_857_; 
v_fst_787_ = lean_ctor_get(v_a_783_, 0);
v_snd_788_ = lean_ctor_get(v_a_783_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_a_783_);
if (v_isSharedCheck_857_ == 0)
{
v___x_790_ = v_a_783_;
v_isShared_791_ = v_isSharedCheck_857_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snd_788_);
lean_inc(v_fst_787_);
lean_dec(v_a_783_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_857_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v_asyncMode_793_; lean_object* v___x_794_; lean_object* v_asyncMode_795_; lean_object* v___x_796_; lean_object* v_asyncMode_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_792_ = l_Lake_nameExt;
v_asyncMode_793_ = lean_ctor_get(v___x_792_, 2);
v___x_794_ = l_Lake_dirExt;
v_asyncMode_795_ = lean_ctor_get(v___x_794_, 2);
v___x_796_ = l_Lake_optsExt;
v_asyncMode_797_ = lean_ctor_get(v___x_796_, 2);
v___x_798_ = ((lean_object*)(l_Lake_configModuleName));
v___x_799_ = l_Lean_Environment_setMainModule(v_fst_787_, v___x_798_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v_pkgName_758_);
lean_ctor_set(v___x_790_, 0, v_pkgIdx_757_);
v___x_801_ = v___x_790_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_pkgIdx_757_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_pkgName_758_);
v___x_801_ = v_reuseFailAlloc_856_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l_Lean_EnvExtension_setState___redArg(v___x_792_, v___x_799_, v___x_801_, v_asyncMode_793_);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 1);
lean_ctor_set(v___x_785_, 0, v_pkgDir_759_);
v___x_804_ = v___x_785_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_pkgDir_759_);
v___x_804_ = v_reuseFailAlloc_855_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_EnvExtension_setState___redArg(v___x_794_, v___x_802_, v___x_804_, v_asyncMode_795_);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 1);
lean_ctor_set(v___x_773_, 0, v_lakeOpts_760_);
v___x_807_ = v___x_773_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_lakeOpts_760_);
v___x_807_ = v_reuseFailAlloc_854_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = l_Lean_EnvExtension_setState___redArg(v___x_796_, v___x_805_, v___x_807_, v_asyncMode_797_);
v___x_809_ = l_Lean_Elab_Command_mkState(v___x_808_, v_snd_788_, v_leanOpts_761_);
v___x_810_ = l_Lean_Elab_IO_processCommands(v___x_769_, v_fst_777_, v___x_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v_commandState_812_; lean_object* v_env_813_; lean_object* v_messages_814_; lean_object* v___f_815_; lean_object* v___x_816_; 
lean_del_object(v___x_780_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v_commandState_812_ = lean_ctor_get(v_a_811_, 0);
lean_inc_ref(v_commandState_812_);
lean_dec(v_a_811_);
v_env_813_ = lean_ctor_get(v_commandState_812_, 0);
lean_inc_ref(v_env_813_);
v_messages_814_ = lean_ctor_get(v_commandState_812_, 1);
lean_inc_ref(v_messages_814_);
lean_dec_ref(v_commandState_812_);
v___f_815_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_816_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_814_, v___f_815_, v_a_763_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_834_; 
v_a_817_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_816_, 0);
lean_dec(v_unused_835_);
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_834_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_834_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
uint8_t v___x_821_; 
v___x_821_ = l_Lean_MessageLog_hasErrors(v_messages_814_);
lean_dec_ref(v_messages_814_);
if (v___x_821_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_configFile_762_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v_env_813_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_env_813_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_a_817_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
lean_dec_ref(v_env_813_);
v___x_825_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1));
v___x_826_ = lean_string_append(v_configFile_762_, v___x_825_);
v___x_827_ = 3;
v___x_828_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*1, v___x_827_);
v___x_829_ = lean_array_get_size(v_a_817_);
v___x_830_ = lean_array_push(v_a_817_, v___x_828_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 1);
lean_ctor_set(v___x_819_, 1, v___x_830_);
lean_ctor_set(v___x_819_, 0, v___x_829_);
v___x_832_ = v___x_819_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_messages_814_);
lean_dec_ref(v_env_813_);
lean_dec_ref(v_configFile_762_);
v_a_836_ = lean_ctor_get(v___x_816_, 0);
v_a_837_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_816_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_inc(v_a_836_);
lean_dec(v___x_816_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_836_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
lean_dec_ref(v_configFile_762_);
v_a_845_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_810_, 1);
v___x_846_ = lean_io_error_to_string(v_a_845_);
v___x_847_ = 3;
v___x_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*1, v___x_847_);
v___x_849_ = lean_array_get_size(v_a_763_);
v___x_850_ = lean_array_push(v_a_763_, v___x_848_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 1, v___x_850_);
lean_ctor_set(v___x_780_, 0, v___x_849_);
v___x_852_ = v___x_780_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
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
lean_object* v_a_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
lean_dec(v_fst_777_);
lean_del_object(v___x_773_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v_configFile_762_);
lean_dec_ref(v_leanOpts_761_);
lean_dec(v_lakeOpts_760_);
lean_dec_ref(v_pkgDir_759_);
lean_dec(v_pkgName_758_);
lean_dec(v_pkgIdx_757_);
v_a_859_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_782_, 1);
v___x_860_ = lean_io_error_to_string(v_a_859_);
v___x_861_ = 3;
v___x_862_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v___x_861_);
v___x_863_ = lean_array_get_size(v_a_763_);
v___x_864_ = lean_array_push(v_a_763_, v___x_862_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 1, v___x_864_);
lean_ctor_set(v___x_780_, 0, v___x_863_);
v___x_866_ = v___x_780_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v___x_769_);
lean_dec_ref(v_configFile_762_);
lean_dec_ref(v_leanOpts_761_);
lean_dec(v_lakeOpts_760_);
lean_dec_ref(v_pkgDir_759_);
lean_dec(v_pkgName_758_);
lean_dec(v_pkgIdx_757_);
v_a_870_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_770_, 1);
v___x_871_ = lean_io_error_to_string(v_a_870_);
v___x_872_ = 3;
v___x_873_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*1, v___x_872_);
v___x_874_ = lean_array_get_size(v_a_763_);
v___x_875_ = lean_array_push(v_a_763_, v___x_873_);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
return v___x_876_;
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref(v_configFile_762_);
lean_dec_ref(v_leanOpts_761_);
lean_dec(v_lakeOpts_760_);
lean_dec_ref(v_pkgDir_759_);
lean_dec(v_pkgName_758_);
lean_dec(v_pkgIdx_757_);
v_a_877_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_765_, 1);
v___x_878_ = lean_io_error_to_string(v_a_877_);
v___x_879_ = 3;
v___x_880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1, v___x_879_);
v___x_881_ = lean_array_get_size(v_a_763_);
v___x_882_ = lean_array_push(v_a_763_, v___x_880_);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_884_, lean_object* v_pkgName_885_, lean_object* v_pkgDir_886_, lean_object* v_lakeOpts_887_, lean_object* v_leanOpts_888_, lean_object* v_configFile_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_884_, v_pkgName_885_, v_pkgDir_886_, v_lakeOpts_887_, v_leanOpts_888_, v_configFile_889_, v_a_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_895_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = lake_environment_add(v_env_895_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_896_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_904_ = l_Lean_NameSet_empty;
v___x_905_ = l_Lean_NameSet_insert(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_911_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_912_ = l_Lean_NameSet_insert(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_918_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_919_ = l_Lean_NameSet_insert(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_925_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_926_ = l_Lean_NameSet_insert(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_932_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_933_ = l_Lean_NameSet_insert(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_939_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_940_ = l_Lean_NameSet_insert(v___x_939_, v___x_938_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_946_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_947_ = l_Lean_NameSet_insert(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_953_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_954_ = l_Lean_NameSet_insert(v___x_953_, v___x_952_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_960_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_961_ = l_Lean_NameSet_insert(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_967_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_968_ = l_Lean_NameSet_insert(v___x_967_, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_974_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_975_ = l_Lean_NameSet_insert(v___x_974_, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_981_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_982_ = l_Lean_NameSet_insert(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_988_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_989_ = l_Lean_NameSet_insert(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_995_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_996_ = l_Lean_NameSet_insert(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_1002_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_1003_ = l_Lean_NameSet_insert(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_1010_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_1011_ = l_Lean_NameSet_insert(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52));
v___x_1019_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_1020_ = l_Lean_NameSet_insert(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53);
return v___x_1021_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = l_Lean_instInhabitedEnvExtensionState;
v___x_1023_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_1024_, lean_object* v_val_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; 
v___x_1031_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
v___x_1032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_1033_ = lean_array_get_borrowed(v___x_1032_, v_val_1024_, v_val_1025_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_box(0);
lean_inc(v___x_1031_);
lean_inc(v___x_1033_);
v___x_1036_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1033_, v_b_1029_, v___x_1031_, v___x_1034_, v___x_1035_);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1027_, v___x_1037_);
v_i_1027_ = v___x_1038_;
v_b_1029_ = v___x_1036_;
goto _start;
}
else
{
return v_b_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_1040_, lean_object* v_val_1041_, lean_object* v_as_1042_, lean_object* v_i_1043_, lean_object* v_stop_1044_, lean_object* v_b_1045_){
_start:
{
size_t v_i_boxed_1046_; size_t v_stop_boxed_1047_; lean_object* v_res_1048_; 
v_i_boxed_1046_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_stop_boxed_1047_ = lean_unbox_usize(v_stop_1044_);
lean_dec(v_stop_1044_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1040_, v_val_1041_, v_as_1042_, v_i_boxed_1046_, v_stop_boxed_1047_, v_b_1045_);
lean_dec_ref(v_as_1042_);
lean_dec(v_val_1041_);
lean_dec_ref(v_val_1040_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_m_1049_, lean_object* v_query_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v_zero_1054_; uint8_t v_isZero_1055_; 
v_zero_1054_ = lean_unsigned_to_nat(0u);
v_isZero_1055_ = lean_nat_dec_eq(v_x_1052_, v_zero_1054_);
if (v_isZero_1055_ == 1)
{
lean_dec(v_x_1053_);
lean_dec(v_x_1052_);
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_box(2);
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_val_1057_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v_x_1051_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_val_1057_);
lean_dec(v_x_1051_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_val_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_keyArray_1065_; lean_object* v_valueArray_1066_; lean_object* v___x_1067_; uint8_t v_isSome_1068_; 
v_keyArray_1065_ = lean_ctor_get(v_m_1049_, 1);
v_valueArray_1066_ = lean_ctor_get(v_m_1049_, 2);
v___x_1067_ = lean_array_fget_borrowed(v_keyArray_1065_, v_x_1053_);
v_isSome_1068_ = lean_noption_is_some(v___x_1067_);
if (v_isSome_1068_ == 0)
{
lean_dec(v_x_1052_);
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_x_1053_);
return v___x_1069_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_x_1053_);
v_val_1070_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v_x_1051_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_val_1070_);
lean_dec(v_x_1051_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_val_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_one_1078_; lean_object* v_n_1079_; lean_object* v___y_1081_; 
v_one_1078_ = lean_unsigned_to_nat(1u);
v_n_1079_ = lean_nat_sub(v_x_1052_, v_one_1078_);
lean_dec(v_x_1052_);
if (v_isSome_1068_ == 0)
{
goto v___jp_1087_;
}
else
{
lean_object* v___x_1089_; uint8_t v_isSome_1090_; 
v___x_1089_ = lean_array_fget_borrowed(v_valueArray_1066_, v_x_1053_);
v_isSome_1090_ = lean_noption_is_some(v___x_1089_);
if (v_isSome_1090_ == 0)
{
goto v___jp_1087_;
}
else
{
lean_object* v_val_1091_; uint8_t v___x_1092_; 
lean_inc(v___x_1067_);
v_val_1091_ = lean_noption_get(v___x_1067_);
v___x_1092_ = lean_name_eq(v_val_1091_, v_query_1050_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
lean_dec(v_val_1091_);
v___x_1093_ = lean_array_get_size(v_keyArray_1065_);
v___x_1094_ = lean_nat_add(v_x_1053_, v_one_1078_);
lean_dec(v_x_1053_);
v___x_1095_ = lean_nat_dec_lt(v___x_1094_, v___x_1093_);
if (v___x_1095_ == 0)
{
lean_dec(v___x_1094_);
v_x_1052_ = v_n_1079_;
v_x_1053_ = v_zero_1054_;
goto _start;
}
else
{
v_x_1052_ = v_n_1079_;
v_x_1053_ = v___x_1094_;
goto _start;
}
}
else
{
lean_object* v_val_1098_; lean_object* v___x_1099_; 
lean_dec(v_n_1079_);
lean_dec(v_x_1051_);
lean_inc(v___x_1089_);
v_val_1098_ = lean_noption_get(v___x_1089_);
v___x_1099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1099_, 0, v_x_1053_);
lean_ctor_set(v___x_1099_, 1, v_val_1091_);
lean_ctor_set(v___x_1099_, 2, v_val_1098_);
return v___x_1099_;
}
}
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_array_get_size(v_keyArray_1065_);
v___x_1083_ = lean_nat_add(v_x_1053_, v_one_1078_);
lean_dec(v_x_1053_);
v___x_1084_ = lean_nat_dec_lt(v___x_1083_, v___x_1082_);
if (v___x_1084_ == 0)
{
lean_dec(v___x_1083_);
v_x_1051_ = v___y_1081_;
v_x_1052_ = v_n_1079_;
v_x_1053_ = v_zero_1054_;
goto _start;
}
else
{
v_x_1051_ = v___y_1081_;
v_x_1052_ = v_n_1079_;
v_x_1053_ = v___x_1083_;
goto _start;
}
}
v___jp_1087_:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1088_; 
lean_inc(v_x_1053_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_x_1053_);
v___y_1081_ = v___x_1088_;
goto v___jp_1080_;
}
else
{
v___y_1081_ = v_x_1051_;
goto v___jp_1080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_1100_, lean_object* v_query_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg(v_m_1100_, v_query_1101_, v_x_1102_, v_x_1103_, v_x_1104_);
lean_dec(v_query_1101_);
lean_dec_ref(v_m_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg(lean_object* v_m_1106_, lean_object* v_query_1107_){
_start:
{
lean_object* v_keyArray_1108_; lean_object* v___x_1109_; uint64_t v___y_1111_; 
v_keyArray_1108_ = lean_ctor_get(v_m_1106_, 1);
v___x_1109_ = lean_array_get_size(v_keyArray_1108_);
if (lean_obj_tag(v_query_1107_) == 0)
{
uint64_t v___x_1126_; 
v___x_1126_ = 1723ULL;
v___y_1111_ = v___x_1126_;
goto v___jp_1110_;
}
else
{
uint64_t v_hash_1127_; 
v_hash_1127_ = lean_ctor_get_uint64(v_query_1107_, sizeof(void*)*2);
v___y_1111_ = v_hash_1127_;
goto v___jp_1110_;
}
v___jp_1110_:
{
uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v_fold_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; uint64_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1112_ = 32ULL;
v___x_1113_ = lean_uint64_shift_right(v___y_1111_, v___x_1112_);
v_fold_1114_ = lean_uint64_xor(v___y_1111_, v___x_1113_);
v___x_1115_ = 16ULL;
v___x_1116_ = lean_uint64_shift_right(v_fold_1114_, v___x_1115_);
v___x_1117_ = lean_uint64_xor(v_fold_1114_, v___x_1116_);
v___x_1118_ = lean_uint64_to_usize(v___x_1117_);
v___x_1119_ = lean_usize_of_nat(v___x_1109_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_sub(v___x_1119_, v___x_1120_);
v___x_1122_ = lean_usize_land(v___x_1118_, v___x_1121_);
v___x_1123_ = lean_usize_to_nat(v___x_1122_);
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg(v_m_1106_, v_query_1107_, v___x_1124_, v___x_1109_, v___x_1123_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_1128_, lean_object* v_query_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg(v_m_1128_, v_query_1129_);
lean_dec(v_query_1129_);
lean_dec_ref(v_m_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_m_1131_, lean_object* v_query_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg(v_m_1131_, v_query_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_index_1134_; lean_object* v_key_1135_; lean_object* v_value_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_index_1134_ = lean_ctor_get(v___x_1133_, 0);
v_key_1135_ = lean_ctor_get(v___x_1133_, 1);
v_value_1136_ = lean_ctor_get(v___x_1133_, 2);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1133_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_value_1136_);
lean_inc(v_key_1135_);
lean_inc(v_index_1134_);
lean_dec(v___x_1133_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_index_1134_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_key_1135_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_value_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v___x_1133_);
v___x_1144_ = lean_box(1);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_m_1145_, lean_object* v_query_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_m_1145_, v_query_1146_);
lean_dec(v_query_1146_);
lean_dec_ref(v_m_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_m_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_value_1151_; lean_object* v___x_1152_; 
v_value_1151_ = lean_ctor_get(v___x_1150_, 2);
lean_inc(v_value_1151_);
lean_dec_ref_known(v___x_1150_, 3);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_value_1151_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_m_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_1157_, lean_object* v_val_1158_, lean_object* v_as_1159_, size_t v_i_1160_, size_t v_stop_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v___y_1164_; uint8_t v___x_1168_; 
v___x_1168_ = lean_usize_dec_eq(v_i_1160_, v_stop_1161_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1169_ = lean_array_uget_borrowed(v_as_1159_, v_i_1160_);
v_fst_1170_ = lean_ctor_get(v___x_1169_, 0);
v_snd_1171_ = lean_ctor_get(v___x_1169_, 1);
v___x_1172_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_1173_ = l_Lean_NameSet_contains(v___x_1172_, v_fst_1170_);
if (v___x_1173_ == 0)
{
v___y_1164_ = v_b_1162_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_1157_, v_fst_1170_);
if (lean_obj_tag(v___x_1174_) == 0)
{
v___y_1164_ = v_b_1162_;
goto v___jp_1163_;
}
else
{
lean_object* v_val_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_array_get_size(v_snd_1171_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_val_1175_);
v___y_1164_ = v_b_1162_;
goto v___jp_1163_;
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_nat_dec_le(v___x_1177_, v___x_1177_);
if (v___x_1179_ == 0)
{
if (v___x_1178_ == 0)
{
lean_dec(v_val_1175_);
v___y_1164_ = v_b_1162_;
goto v___jp_1163_;
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1177_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1158_, v_val_1175_, v_snd_1171_, v___x_1180_, v___x_1181_, v_b_1162_);
lean_dec(v_val_1175_);
v___y_1164_ = v___x_1182_;
goto v___jp_1163_;
}
}
else
{
size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = ((size_t)0ULL);
v___x_1184_ = lean_usize_of_nat(v___x_1177_);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1158_, v_val_1175_, v_snd_1171_, v___x_1183_, v___x_1184_, v_b_1162_);
lean_dec(v_val_1175_);
v___y_1164_ = v___x_1185_;
goto v___jp_1163_;
}
}
}
}
}
else
{
return v_b_1162_;
}
v___jp_1163_:
{
size_t v___x_1165_; size_t v___x_1166_; 
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_add(v_i_1160_, v___x_1165_);
v_i_1160_ = v___x_1166_;
v_b_1162_ = v___y_1164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1186_, lean_object* v_val_1187_, lean_object* v_as_1188_, lean_object* v_i_1189_, lean_object* v_stop_1190_, lean_object* v_b_1191_){
_start:
{
size_t v_i_boxed_1192_; size_t v_stop_boxed_1193_; lean_object* v_res_1194_; 
v_i_boxed_1192_ = lean_unbox_usize(v_i_1189_);
lean_dec(v_i_1189_);
v_stop_boxed_1193_ = lean_unbox_usize(v_stop_1190_);
lean_dec(v_stop_1190_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1186_, v_val_1187_, v_as_1188_, v_i_boxed_1192_, v_stop_boxed_1193_, v_b_1191_);
lean_dec_ref(v_as_1188_);
lean_dec_ref(v_val_1187_);
lean_dec_ref(v_a_1186_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1195_, size_t v_i_1196_, size_t v_stop_1197_, lean_object* v_b_1198_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_usize_dec_eq(v_i_1196_, v_stop_1197_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; 
v___x_1200_ = lean_array_uget_borrowed(v_as_1195_, v_i_1196_);
lean_inc(v___x_1200_);
v___x_1201_ = lake_environment_add(v_b_1198_, v___x_1200_);
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_add(v_i_1196_, v___x_1202_);
v_i_1196_ = v___x_1203_;
v_b_1198_ = v___x_1201_;
goto _start;
}
else
{
return v_b_1198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1205_, lean_object* v_i_1206_, lean_object* v_stop_1207_, lean_object* v_b_1208_){
_start:
{
size_t v_i_boxed_1209_; size_t v_stop_boxed_1210_; lean_object* v_res_1211_; 
v_i_boxed_1209_ = lean_unbox_usize(v_i_1206_);
lean_dec(v_i_1206_);
v_stop_boxed_1210_ = lean_unbox_usize(v_stop_1207_);
lean_dec(v_stop_1207_);
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1205_, v_i_boxed_1209_, v_stop_boxed_1210_, v_b_1208_);
lean_dec_ref(v_as_1205_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1212_, lean_object* v_leanOpts_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_readModuleData(v_olean_1212_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_fst_1217_; lean_object* v_imports_1218_; lean_object* v_constants_1219_; lean_object* v_entries_1220_; uint32_t v___x_1221_; lean_object* v___x_1222_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v_fst_1217_ = lean_ctor_get(v_a_1216_, 0);
lean_inc(v_fst_1217_);
lean_dec(v_a_1216_);
v_imports_1218_ = lean_ctor_get(v_fst_1217_, 0);
lean_inc_ref(v_imports_1218_);
v_constants_1219_ = lean_ctor_get(v_fst_1217_, 2);
lean_inc_ref(v_constants_1219_);
v_entries_1220_ = lean_ctor_get(v_fst_1217_, 4);
lean_inc_ref(v_entries_1220_);
lean_dec(v_fst_1217_);
v___x_1221_ = 1024;
v___x_1222_ = l_Lake_importModulesUsingCache(v_imports_1218_, v_leanOpts_1213_, v___x_1221_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; lean_object* v___y_1226_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_array_get_size(v_constants_1219_);
v___x_1265_ = lean_nat_dec_lt(v___x_1224_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v_constants_1219_);
v___y_1226_ = v_a_1223_;
goto v___jp_1225_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_le(v___x_1264_, v___x_1264_);
if (v___x_1266_ == 0)
{
if (v___x_1265_ == 0)
{
lean_dec_ref(v_constants_1219_);
v___y_1226_ = v_a_1223_;
goto v___jp_1225_;
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((size_t)0ULL);
v___x_1268_ = lean_usize_of_nat(v___x_1264_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1219_, v___x_1267_, v___x_1268_, v_a_1223_);
lean_dec_ref(v_constants_1219_);
v___y_1226_ = v___x_1269_;
goto v___jp_1225_;
}
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = lean_usize_of_nat(v___x_1264_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1219_, v___x_1270_, v___x_1271_, v_a_1223_);
lean_dec_ref(v_constants_1219_);
v___y_1226_ = v___x_1272_;
goto v___jp_1225_;
}
}
v___jp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = l_Lean_persistentEnvExtensionsRef;
v___x_1228_ = lean_st_ref_get(v___x_1227_);
v___x_1229_ = l_Lean_mkExtNameMap(v___x_1224_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1255_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = lean_array_get_size(v_entries_1220_);
v___x_1235_ = lean_nat_dec_lt(v___x_1224_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1237_; 
lean_dec(v_a_1230_);
lean_dec(v___x_1228_);
lean_dec_ref(v_entries_1220_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___y_1226_);
v___x_1237_ = v___x_1232_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___y_1226_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_le(v___x_1234_, v___x_1234_);
if (v___x_1239_ == 0)
{
if (v___x_1235_ == 0)
{
lean_object* v___x_1241_; 
lean_dec(v_a_1230_);
lean_dec(v___x_1228_);
lean_dec_ref(v_entries_1220_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___y_1226_);
v___x_1241_ = v___x_1232_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___y_1226_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
else
{
size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1243_ = ((size_t)0ULL);
v___x_1244_ = lean_usize_of_nat(v___x_1234_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1230_, v___x_1228_, v_entries_1220_, v___x_1243_, v___x_1244_, v___y_1226_);
lean_dec_ref(v_entries_1220_);
lean_dec(v___x_1228_);
lean_dec(v_a_1230_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1245_);
v___x_1247_ = v___x_1232_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
size_t v___x_1249_; size_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = lean_usize_of_nat(v___x_1234_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1230_, v___x_1228_, v_entries_1220_, v___x_1249_, v___x_1250_, v___y_1226_);
lean_dec_ref(v_entries_1220_);
lean_dec(v___x_1228_);
lean_dec(v_a_1230_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1251_);
v___x_1253_ = v___x_1232_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v___x_1228_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_entries_1220_);
v_a_1256_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1229_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1229_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
else
{
lean_dec_ref(v_entries_1220_);
lean_dec_ref(v_constants_1219_);
return v___x_1222_;
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_leanOpts_1213_);
v_a_1273_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1215_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1215_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1281_, lean_object* v_leanOpts_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1281_, v_leanOpts_1282_);
lean_dec_ref(v_olean_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1286_, v_a_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_m_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1289_, v_m_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_m_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1293_, lean_object* v_m_1294_, lean_object* v_query_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_m_1294_, v_query_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_m_1298_, lean_object* v_query_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1297_, v_m_1298_, v_query_1299_);
lean_dec(v_query_1299_);
lean_dec_ref(v_m_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1301_, lean_object* v_m_1302_, lean_object* v_query_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___redArg(v_m_1302_, v_query_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_m_1306_, lean_object* v_query_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1(v_00_u03b2_1305_, v_m_1306_, v_query_1307_);
lean_dec(v_query_1307_);
lean_dec_ref(v_m_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1309_, lean_object* v_m_1310_, lean_object* v_query_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___redArg(v_m_1310_, v_query_1311_, v_x_1312_, v_x_1313_, v_x_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1317_, lean_object* v_m_1318_, lean_object* v_query_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_1317_, v_m_1318_, v_query_1319_, v_x_1320_, v_x_1321_, v_x_1322_, v_x_1323_);
lean_dec(v_query_1319_);
lean_dec_ref(v_m_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_box(1);
v___x_1327_ = lean_panic_fn_borrowed(v___x_1326_, v_msg_1325_);
return v___x_1327_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1331_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1332_ = lean_unsigned_to_nat(35u);
v___x_1333_ = lean_unsigned_to_nat(182u);
v___x_1334_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1335_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1336_ = l_mkPanicMessageWithDecl(v___x_1335_, v___x_1334_, v___x_1333_, v___x_1332_, v___x_1331_);
return v___x_1336_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1338_ = lean_unsigned_to_nat(21u);
v___x_1339_ = lean_unsigned_to_nat(183u);
v___x_1340_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1341_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1342_ = l_mkPanicMessageWithDecl(v___x_1341_, v___x_1340_, v___x_1339_, v___x_1338_, v___x_1337_);
return v___x_1342_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1345_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1346_ = lean_unsigned_to_nat(35u);
v___x_1347_ = lean_unsigned_to_nat(276u);
v___x_1348_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1349_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1350_ = l_mkPanicMessageWithDecl(v___x_1349_, v___x_1348_, v___x_1347_, v___x_1346_, v___x_1345_);
return v___x_1350_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1351_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1352_ = lean_unsigned_to_nat(21u);
v___x_1353_ = lean_unsigned_to_nat(277u);
v___x_1354_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1355_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1356_ = l_mkPanicMessageWithDecl(v___x_1355_, v___x_1354_, v___x_1353_, v___x_1352_, v___x_1351_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1357_, lean_object* v_v_1358_, lean_object* v_t_1359_){
_start:
{
if (lean_obj_tag(v_t_1359_) == 0)
{
lean_object* v_size_1360_; lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v_l_1363_; lean_object* v_r_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1720_; 
v_size_1360_ = lean_ctor_get(v_t_1359_, 0);
v_k_1361_ = lean_ctor_get(v_t_1359_, 1);
v_v_1362_ = lean_ctor_get(v_t_1359_, 2);
v_l_1363_ = lean_ctor_get(v_t_1359_, 3);
v_r_1364_ = lean_ctor_get(v_t_1359_, 4);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_t_1359_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1366_ = v_t_1359_;
v_isShared_1367_ = v_isSharedCheck_1720_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_r_1364_);
lean_inc(v_l_1363_);
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
lean_inc(v_size_1360_);
lean_dec(v_t_1359_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1720_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_string_compare(v_k_1357_, v_k_1361_);
switch(v___x_1368_)
{
case 0:
{
lean_object* v___x_1369_; 
lean_dec(v_size_1360_);
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1357_, v_v_1358_, v_l_1363_);
if (lean_obj_tag(v_r_1364_) == 0)
{
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_size_1370_; lean_object* v_size_1371_; lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v_l_1374_; lean_object* v_r_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_size_1370_ = lean_ctor_get(v_r_1364_, 0);
v_size_1371_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_size_1371_);
v_k_1372_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_k_1372_);
v_v_1373_ = lean_ctor_get(v___x_1369_, 2);
lean_inc(v_v_1373_);
v_l_1374_ = lean_ctor_get(v___x_1369_, 3);
lean_inc(v_l_1374_);
v_r_1375_ = lean_ctor_get(v___x_1369_, 4);
lean_inc(v_r_1375_);
v___x_1376_ = lean_unsigned_to_nat(3u);
v___x_1377_ = lean_nat_mul(v___x_1376_, v_size_1370_);
v___x_1378_ = lean_nat_dec_lt(v___x_1377_, v_size_1371_);
lean_dec(v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec(v_r_1375_);
lean_dec(v_l_1374_);
lean_dec(v_v_1373_);
lean_dec(v_k_1372_);
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_nat_add(v___x_1379_, v_size_1371_);
lean_dec(v_size_1371_);
v___x_1381_ = lean_nat_add(v___x_1380_, v_size_1370_);
lean_dec(v___x_1380_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 3, v___x_1369_);
lean_ctor_set(v___x_1366_, 0, v___x_1381_);
v___x_1383_ = v___x_1366_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_r_1364_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1456_; 
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1457_ = lean_ctor_get(v___x_1369_, 4);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v___x_1369_, 3);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v___x_1369_, 2);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v___x_1369_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1461_);
v___x_1386_ = v___x_1369_;
v_isShared_1387_ = v_isSharedCheck_1456_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v___x_1369_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1456_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
if (lean_obj_tag(v_l_1374_) == 0)
{
if (lean_obj_tag(v_r_1375_) == 0)
{
lean_object* v_size_1388_; lean_object* v_size_1389_; lean_object* v_k_1390_; lean_object* v_v_1391_; lean_object* v_l_1392_; lean_object* v_r_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_size_1388_ = lean_ctor_get(v_l_1374_, 0);
v_size_1389_ = lean_ctor_get(v_r_1375_, 0);
v_k_1390_ = lean_ctor_get(v_r_1375_, 1);
v_v_1391_ = lean_ctor_get(v_r_1375_, 2);
v_l_1392_ = lean_ctor_get(v_r_1375_, 3);
v_r_1393_ = lean_ctor_get(v_r_1375_, 4);
v___x_1394_ = lean_unsigned_to_nat(2u);
v___x_1395_ = lean_nat_mul(v___x_1394_, v_size_1388_);
v___x_1396_ = lean_nat_dec_lt(v_size_1389_, v___x_1395_);
lean_dec(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1426_; 
lean_inc(v_r_1393_);
lean_inc(v_l_1392_);
lean_inc(v_v_1391_);
lean_inc(v_k_1390_);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_r_1375_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1427_ = lean_ctor_get(v_r_1375_, 4);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_r_1375_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_r_1375_, 2);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_r_1375_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_r_1375_, 0);
lean_dec(v_unused_1431_);
v___x_1398_ = v_r_1375_;
v_isShared_1399_ = v_isSharedCheck_1426_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v_r_1375_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1426_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___x_1414_; lean_object* v___y_1416_; 
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_nat_add(v___x_1400_, v_size_1371_);
lean_dec(v_size_1371_);
v___x_1402_ = lean_nat_add(v___x_1401_, v_size_1370_);
lean_dec(v___x_1401_);
v___x_1414_ = lean_nat_add(v___x_1400_, v_size_1388_);
if (lean_obj_tag(v_l_1392_) == 0)
{
lean_object* v_size_1424_; 
v_size_1424_ = lean_ctor_get(v_l_1392_, 0);
lean_inc(v_size_1424_);
v___y_1416_ = v_size_1424_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v___y_1416_ = v___x_1425_;
goto v___jp_1415_;
}
v___jp_1403_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_nat_add(v___y_1404_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec(v___y_1404_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v_r_1364_);
lean_ctor_set(v___x_1398_, 3, v_r_1393_);
lean_ctor_set(v___x_1398_, 2, v_v_1362_);
lean_ctor_set(v___x_1398_, 1, v_k_1361_);
lean_ctor_set(v___x_1398_, 0, v___x_1407_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_r_1393_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_r_1364_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1409_);
lean_ctor_set(v___x_1386_, 3, v___y_1405_);
lean_ctor_set(v___x_1386_, 2, v_v_1391_);
lean_ctor_set(v___x_1386_, 1, v_k_1390_);
lean_ctor_set(v___x_1386_, 0, v___x_1402_);
v___x_1411_ = v___x_1386_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_k_1390_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_v_1391_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v___y_1405_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
v___jp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_nat_add(v___x_1414_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec(v___x_1414_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_l_1392_);
lean_ctor_set(v___x_1366_, 3, v_l_1374_);
lean_ctor_set(v___x_1366_, 2, v_v_1373_);
lean_ctor_set(v___x_1366_, 1, v_k_1372_);
lean_ctor_set(v___x_1366_, 0, v___x_1417_);
v___x_1419_ = v___x_1366_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_l_1392_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_nat_add(v___x_1400_, v_size_1370_);
if (lean_obj_tag(v_r_1393_) == 0)
{
lean_object* v_size_1421_; 
v_size_1421_ = lean_ctor_get(v_r_1393_, 0);
lean_inc(v_size_1421_);
v___y_1404_ = v___x_1420_;
v___y_1405_ = v___x_1419_;
v___y_1406_ = v_size_1421_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_unsigned_to_nat(0u);
v___y_1404_ = v___x_1420_;
v___y_1405_ = v___x_1419_;
v___y_1406_ = v___x_1422_;
goto v___jp_1403_;
}
}
}
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_del_object(v___x_1366_);
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_add(v___x_1432_, v_size_1371_);
lean_dec(v_size_1371_);
v___x_1434_ = lean_nat_add(v___x_1433_, v_size_1370_);
lean_dec(v___x_1433_);
v___x_1435_ = lean_nat_add(v___x_1432_, v_size_1370_);
v___x_1436_ = lean_nat_add(v___x_1435_, v_size_1389_);
lean_dec(v___x_1435_);
lean_inc_ref(v_r_1364_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_r_1364_);
lean_ctor_set(v___x_1386_, 3, v_r_1375_);
lean_ctor_set(v___x_1386_, 2, v_v_1362_);
lean_ctor_set(v___x_1386_, 1, v_k_1361_);
lean_ctor_set(v___x_1386_, 0, v___x_1436_);
v___x_1438_ = v___x_1386_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_r_1375_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_r_1364_);
v___x_1438_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v_r_1364_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1446_ = lean_ctor_get(v_r_1364_, 4);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_r_1364_, 3);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_r_1364_, 2);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_r_1364_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_r_1364_, 0);
lean_dec(v_unused_1450_);
v___x_1440_ = v_r_1364_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v_r_1364_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1438_);
lean_ctor_set(v___x_1440_, 3, v_l_1374_);
lean_ctor_set(v___x_1440_, 2, v_v_1373_);
lean_ctor_set(v___x_1440_, 1, v_k_1372_);
lean_ctor_set(v___x_1440_, 0, v___x_1434_);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_l_1374_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v___x_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref_known(v_l_1374_, 5);
lean_del_object(v___x_1386_);
lean_dec(v_v_1373_);
lean_dec(v_k_1372_);
lean_dec(v_size_1371_);
lean_dec_ref_known(v_r_1364_, 5);
lean_del_object(v___x_1366_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
v___x_1452_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1453_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1452_);
return v___x_1453_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_del_object(v___x_1386_);
lean_dec(v_r_1375_);
lean_dec(v_v_1373_);
lean_dec(v_k_1372_);
lean_dec(v_size_1371_);
lean_dec_ref_known(v_r_1364_, 5);
lean_del_object(v___x_1366_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
v___x_1454_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1455_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1454_);
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_size_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v_size_1462_ = lean_ctor_get(v_r_1364_, 0);
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_nat_add(v___x_1463_, v_size_1462_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 3, v___x_1369_);
lean_ctor_set(v___x_1366_, 0, v___x_1464_);
v___x_1466_ = v___x_1366_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_r_1364_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_l_1468_; 
v_l_1468_ = lean_ctor_get(v___x_1369_, 3);
lean_inc(v_l_1468_);
if (lean_obj_tag(v_l_1468_) == 0)
{
lean_object* v_r_1469_; 
v_r_1469_ = lean_ctor_get(v___x_1369_, 4);
lean_inc(v_r_1469_);
if (lean_obj_tag(v_r_1469_) == 0)
{
lean_object* v_size_1470_; lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1486_; 
v_size_1470_ = lean_ctor_get(v___x_1369_, 0);
v_k_1471_ = lean_ctor_get(v___x_1369_, 1);
v_v_1472_ = lean_ctor_get(v___x_1369_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1487_ = lean_ctor_get(v___x_1369_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v___x_1369_, 3);
lean_dec(v_unused_1488_);
v___x_1474_ = v___x_1369_;
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_inc(v_size_1470_);
lean_dec(v___x_1369_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1486_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_size_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v_size_1476_ = lean_ctor_get(v_r_1469_, 0);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v___x_1477_, v_size_1470_);
lean_dec(v_size_1470_);
v___x_1479_ = lean_nat_add(v___x_1477_, v_size_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v_r_1364_);
lean_ctor_set(v___x_1474_, 3, v_r_1469_);
lean_ctor_set(v___x_1474_, 2, v_v_1362_);
lean_ctor_set(v___x_1474_, 1, v_k_1361_);
lean_ctor_set(v___x_1474_, 0, v___x_1479_);
v___x_1481_ = v___x_1474_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_r_1469_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_r_1364_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1481_);
lean_ctor_set(v___x_1366_, 3, v_l_1468_);
lean_ctor_set(v___x_1366_, 2, v_v_1472_);
lean_ctor_set(v___x_1366_, 1, v_k_1471_);
lean_ctor_set(v___x_1366_, 0, v___x_1478_);
v___x_1483_ = v___x_1366_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_l_1468_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1502_; 
v_k_1489_ = lean_ctor_get(v___x_1369_, 1);
v_v_1490_ = lean_ctor_get(v___x_1369_, 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1503_ = lean_ctor_get(v___x_1369_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v___x_1369_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1505_);
v___x_1492_ = v___x_1369_;
v_isShared_1493_ = v_isSharedCheck_1502_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_dec(v___x_1369_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1502_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1494_ = lean_unsigned_to_nat(3u);
v___x_1495_ = lean_unsigned_to_nat(1u);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 3, v_r_1469_);
lean_ctor_set(v___x_1492_, 2, v_v_1362_);
lean_ctor_set(v___x_1492_, 1, v_k_1361_);
lean_ctor_set(v___x_1492_, 0, v___x_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_r_1469_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1469_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1497_);
lean_ctor_set(v___x_1366_, 3, v_l_1468_);
lean_ctor_set(v___x_1366_, 2, v_v_1490_);
lean_ctor_set(v___x_1366_, 1, v_k_1489_);
lean_ctor_set(v___x_1366_, 0, v___x_1494_);
v___x_1499_ = v___x_1366_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1468_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
else
{
lean_object* v_r_1506_; 
v_r_1506_ = lean_ctor_get(v___x_1369_, 4);
lean_inc(v_r_1506_);
if (lean_obj_tag(v_r_1506_) == 0)
{
lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1532_; 
v_k_1507_ = lean_ctor_get(v___x_1369_, 1);
v_v_1508_ = lean_ctor_get(v___x_1369_, 2);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; 
v_unused_1533_ = lean_ctor_get(v___x_1369_, 4);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v___x_1369_, 3);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1535_);
v___x_1510_ = v___x_1369_;
v_isShared_1511_ = v_isSharedCheck_1532_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_v_1508_);
lean_inc(v_k_1507_);
lean_dec(v___x_1369_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1532_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1528_; 
v_k_1512_ = lean_ctor_get(v_r_1506_, 1);
v_v_1513_ = lean_ctor_get(v_r_1506_, 2);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_r_1506_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; 
v_unused_1529_ = lean_ctor_get(v_r_1506_, 4);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_r_1506_, 3);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_r_1506_, 0);
lean_dec(v_unused_1531_);
v___x_1515_ = v_r_1506_;
v_isShared_1516_ = v_isSharedCheck_1528_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
lean_dec(v_r_1506_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1528_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1517_ = lean_unsigned_to_nat(3u);
v___x_1518_ = lean_unsigned_to_nat(1u);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 4, v_l_1468_);
lean_ctor_set(v___x_1515_, 3, v_l_1468_);
lean_ctor_set(v___x_1515_, 2, v_v_1508_);
lean_ctor_set(v___x_1515_, 1, v_k_1507_);
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1508_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_l_1468_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v_l_1468_);
v___x_1520_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_l_1468_);
lean_ctor_set(v___x_1510_, 2, v_v_1362_);
lean_ctor_set(v___x_1510_, 1, v_k_1361_);
lean_ctor_set(v___x_1510_, 0, v___x_1518_);
v___x_1522_ = v___x_1510_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_l_1468_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_l_1468_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1522_);
lean_ctor_set(v___x_1366_, 3, v___x_1520_);
lean_ctor_set(v___x_1366_, 2, v_v_1513_);
lean_ctor_set(v___x_1366_, 1, v_k_1512_);
lean_ctor_set(v___x_1366_, 0, v___x_1517_);
v___x_1524_ = v___x_1366_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = lean_unsigned_to_nat(2u);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_r_1506_);
lean_ctor_set(v___x_1366_, 3, v___x_1369_);
lean_ctor_set(v___x_1366_, 0, v___x_1536_);
v___x_1538_ = v___x_1366_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1506_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_unsigned_to_nat(1u);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1369_);
lean_ctor_set(v___x_1366_, 3, v___x_1369_);
lean_ctor_set(v___x_1366_, 0, v___x_1540_);
v___x_1542_ = v___x_1366_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v___x_1369_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
case 1:
{
lean_object* v___x_1545_; 
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 2, v_v_1358_);
lean_ctor_set(v___x_1366_, 1, v_k_1357_);
v___x_1545_ = v___x_1366_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_size_1360_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_r_1364_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
default: 
{
lean_object* v___x_1547_; 
lean_dec(v_size_1360_);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1357_, v_v_1358_, v_r_1364_);
if (lean_obj_tag(v_l_1363_) == 0)
{
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_size_1548_; lean_object* v_size_1549_; lean_object* v_k_1550_; lean_object* v_v_1551_; lean_object* v_l_1552_; lean_object* v_r_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_size_1548_ = lean_ctor_get(v_l_1363_, 0);
v_size_1549_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_size_1549_);
v_k_1550_ = lean_ctor_get(v___x_1547_, 1);
lean_inc(v_k_1550_);
v_v_1551_ = lean_ctor_get(v___x_1547_, 2);
lean_inc(v_v_1551_);
v_l_1552_ = lean_ctor_get(v___x_1547_, 3);
lean_inc(v_l_1552_);
v_r_1553_ = lean_ctor_get(v___x_1547_, 4);
lean_inc(v_r_1553_);
v___x_1554_ = lean_unsigned_to_nat(3u);
v___x_1555_ = lean_nat_mul(v___x_1554_, v_size_1548_);
v___x_1556_ = lean_nat_dec_lt(v___x_1555_, v_size_1549_);
lean_dec(v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_dec(v_r_1553_);
lean_dec(v_l_1552_);
lean_dec(v_v_1551_);
lean_dec(v_k_1550_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v___x_1557_, v_size_1548_);
v___x_1559_ = lean_nat_add(v___x_1558_, v_size_1549_);
lean_dec(v_size_1549_);
lean_dec(v___x_1558_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1547_);
lean_ctor_set(v___x_1366_, 0, v___x_1559_);
v___x_1561_ = v___x_1366_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v___x_1547_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
else
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1632_; 
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; 
v_unused_1633_ = lean_ctor_get(v___x_1547_, 4);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v___x_1547_, 3);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v___x_1547_, 2);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v___x_1547_, 1);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1637_);
v___x_1564_ = v___x_1547_;
v_isShared_1565_ = v_isSharedCheck_1632_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v___x_1547_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1632_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
if (lean_obj_tag(v_l_1552_) == 0)
{
if (lean_obj_tag(v_r_1553_) == 0)
{
lean_object* v_size_1566_; lean_object* v_k_1567_; lean_object* v_v_1568_; lean_object* v_l_1569_; lean_object* v_r_1570_; lean_object* v_size_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_size_1566_ = lean_ctor_get(v_l_1552_, 0);
v_k_1567_ = lean_ctor_get(v_l_1552_, 1);
v_v_1568_ = lean_ctor_get(v_l_1552_, 2);
v_l_1569_ = lean_ctor_get(v_l_1552_, 3);
v_r_1570_ = lean_ctor_get(v_l_1552_, 4);
v_size_1571_ = lean_ctor_get(v_r_1553_, 0);
v___x_1572_ = lean_unsigned_to_nat(2u);
v___x_1573_ = lean_nat_mul(v___x_1572_, v_size_1571_);
v___x_1574_ = lean_nat_dec_lt(v_size_1566_, v___x_1573_);
lean_dec(v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1603_; 
lean_inc(v_r_1570_);
lean_inc(v_l_1569_);
lean_inc(v_v_1568_);
lean_inc(v_k_1567_);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_l_1552_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1604_ = lean_ctor_get(v_l_1552_, 4);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_l_1552_, 3);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1552_, 2);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1552_, 1);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_l_1552_, 0);
lean_dec(v_unused_1608_);
v___x_1576_ = v_l_1552_;
v_isShared_1577_ = v_isSharedCheck_1603_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_l_1552_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1603_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1593_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1548_);
v___x_1580_ = lean_nat_add(v___x_1579_, v_size_1549_);
lean_dec(v_size_1549_);
if (lean_obj_tag(v_l_1569_) == 0)
{
lean_object* v_size_1601_; 
v_size_1601_ = lean_ctor_get(v_l_1569_, 0);
lean_inc(v_size_1601_);
v___y_1593_ = v_size_1601_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_unsigned_to_nat(0u);
v___y_1593_ = v___x_1602_;
goto v___jp_1592_;
}
v___jp_1581_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_nat_add(v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec(v___y_1583_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 4, v_r_1553_);
lean_ctor_set(v___x_1576_, 3, v_r_1570_);
lean_ctor_set(v___x_1576_, 2, v_v_1551_);
lean_ctor_set(v___x_1576_, 1, v_k_1550_);
lean_ctor_set(v___x_1576_, 0, v___x_1585_);
v___x_1587_ = v___x_1576_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_r_1570_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_r_1553_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v___x_1587_);
lean_ctor_set(v___x_1564_, 3, v___y_1582_);
lean_ctor_set(v___x_1564_, 2, v_v_1568_);
lean_ctor_set(v___x_1564_, 1, v_k_1567_);
lean_ctor_set(v___x_1564_, 0, v___x_1580_);
v___x_1589_ = v___x_1564_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___y_1582_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_nat_add(v___x_1579_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec(v___x_1579_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_l_1569_);
lean_ctor_set(v___x_1366_, 0, v___x_1594_);
v___x_1596_ = v___x_1366_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_l_1569_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_nat_add(v___x_1578_, v_size_1571_);
if (lean_obj_tag(v_r_1570_) == 0)
{
lean_object* v_size_1598_; 
v_size_1598_ = lean_ctor_get(v_r_1570_, 0);
lean_inc(v_size_1598_);
v___y_1582_ = v___x_1596_;
v___y_1583_ = v___x_1597_;
v___y_1584_ = v_size_1598_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___y_1582_ = v___x_1596_;
v___y_1583_ = v___x_1597_;
v___y_1584_ = v___x_1599_;
goto v___jp_1581_;
}
}
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
lean_del_object(v___x_1366_);
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_add(v___x_1609_, v_size_1548_);
v___x_1611_ = lean_nat_add(v___x_1610_, v_size_1549_);
lean_dec(v_size_1549_);
v___x_1612_ = lean_nat_add(v___x_1610_, v_size_1566_);
lean_dec(v___x_1610_);
lean_inc_ref(v_l_1363_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 4, v_l_1552_);
lean_ctor_set(v___x_1564_, 3, v_l_1363_);
lean_ctor_set(v___x_1564_, 2, v_v_1362_);
lean_ctor_set(v___x_1564_, 1, v_k_1361_);
lean_ctor_set(v___x_1564_, 0, v___x_1612_);
v___x_1614_ = v___x_1564_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_l_1552_);
v___x_1614_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_isSharedCheck_1621_ = !lean_is_exclusive(v_l_1363_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; 
v_unused_1622_ = lean_ctor_get(v_l_1363_, 4);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_l_1363_, 3);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1363_, 2);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1363_, 1);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_l_1363_, 0);
lean_dec(v_unused_1626_);
v___x_1616_ = v_l_1363_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_dec(v_l_1363_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_r_1553_);
lean_ctor_set(v___x_1616_, 3, v___x_1614_);
lean_ctor_set(v___x_1616_, 2, v_v_1551_);
lean_ctor_set(v___x_1616_, 1, v_k_1550_);
lean_ctor_set(v___x_1616_, 0, v___x_1611_);
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_r_1553_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec_ref_known(v_l_1552_, 5);
lean_del_object(v___x_1564_);
lean_dec(v_v_1551_);
lean_dec(v_k_1550_);
lean_dec(v_size_1549_);
lean_dec_ref_known(v_l_1363_, 5);
lean_del_object(v___x_1366_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
v___x_1628_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1629_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1628_);
return v___x_1629_;
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1564_);
lean_dec(v_r_1553_);
lean_dec(v_v_1551_);
lean_dec(v_k_1550_);
lean_dec(v_size_1549_);
lean_dec_ref_known(v_l_1363_, 5);
lean_del_object(v___x_1366_);
lean_dec(v_v_1362_);
lean_dec(v_k_1361_);
v___x_1630_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1631_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1630_);
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_size_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v_size_1638_ = lean_ctor_get(v_l_1363_, 0);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_add(v___x_1639_, v_size_1638_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1547_);
lean_ctor_set(v___x_1366_, 0, v___x_1640_);
v___x_1642_ = v___x_1366_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___x_1547_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_l_1644_; 
v_l_1644_ = lean_ctor_get(v___x_1547_, 3);
lean_inc(v_l_1644_);
if (lean_obj_tag(v_l_1644_) == 0)
{
lean_object* v_r_1645_; 
v_r_1645_ = lean_ctor_get(v___x_1547_, 4);
lean_inc(v_r_1645_);
if (lean_obj_tag(v_r_1645_) == 0)
{
lean_object* v_size_1646_; lean_object* v_k_1647_; lean_object* v_v_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1662_; 
v_size_1646_ = lean_ctor_get(v___x_1547_, 0);
v_k_1647_ = lean_ctor_get(v___x_1547_, 1);
v_v_1648_ = lean_ctor_get(v___x_1547_, 2);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; lean_object* v_unused_1664_; 
v_unused_1663_ = lean_ctor_get(v___x_1547_, 4);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v___x_1547_, 3);
lean_dec(v_unused_1664_);
v___x_1650_ = v___x_1547_;
v_isShared_1651_ = v_isSharedCheck_1662_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_v_1648_);
lean_inc(v_k_1647_);
lean_inc(v_size_1646_);
lean_dec(v___x_1547_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1662_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_size_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_size_1652_ = lean_ctor_get(v_l_1644_, 0);
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_add(v___x_1653_, v_size_1646_);
lean_dec(v_size_1646_);
v___x_1655_ = lean_nat_add(v___x_1653_, v_size_1652_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v_l_1644_);
lean_ctor_set(v___x_1650_, 3, v_l_1363_);
lean_ctor_set(v___x_1650_, 2, v_v_1362_);
lean_ctor_set(v___x_1650_, 1, v_k_1361_);
lean_ctor_set(v___x_1650_, 0, v___x_1655_);
v___x_1657_ = v___x_1650_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1363_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1644_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_r_1645_);
lean_ctor_set(v___x_1366_, 3, v___x_1657_);
lean_ctor_set(v___x_1366_, 2, v_v_1648_);
lean_ctor_set(v___x_1366_, 1, v_k_1647_);
lean_ctor_set(v___x_1366_, 0, v___x_1654_);
v___x_1659_ = v___x_1366_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1647_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1648_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1645_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_k_1665_; lean_object* v_v_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1690_; 
v_k_1665_ = lean_ctor_get(v___x_1547_, 1);
v_v_1666_ = lean_ctor_get(v___x_1547_, 2);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1691_ = lean_ctor_get(v___x_1547_, 4);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v___x_1547_, 3);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1693_);
v___x_1668_ = v___x_1547_;
v_isShared_1669_ = v_isSharedCheck_1690_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_v_1666_);
lean_inc(v_k_1665_);
lean_dec(v___x_1547_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1690_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_k_1670_; lean_object* v_v_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1686_; 
v_k_1670_ = lean_ctor_get(v_l_1644_, 1);
v_v_1671_ = lean_ctor_get(v_l_1644_, 2);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_l_1644_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; lean_object* v_unused_1688_; lean_object* v_unused_1689_; 
v_unused_1687_ = lean_ctor_get(v_l_1644_, 4);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_l_1644_, 3);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_l_1644_, 0);
lean_dec(v_unused_1689_);
v___x_1673_ = v_l_1644_;
v_isShared_1674_ = v_isSharedCheck_1686_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_v_1671_);
lean_inc(v_k_1670_);
lean_dec(v_l_1644_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1686_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = lean_unsigned_to_nat(3u);
v___x_1676_ = lean_unsigned_to_nat(1u);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 4, v_r_1645_);
lean_ctor_set(v___x_1673_, 3, v_r_1645_);
lean_ctor_set(v___x_1673_, 2, v_v_1362_);
lean_ctor_set(v___x_1673_, 1, v_k_1361_);
lean_ctor_set(v___x_1673_, 0, v___x_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_r_1645_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_r_1645_);
v___x_1678_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 3, v_r_1645_);
lean_ctor_set(v___x_1668_, 0, v___x_1676_);
v___x_1680_ = v___x_1668_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_r_1645_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_r_1645_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1680_);
lean_ctor_set(v___x_1366_, 3, v___x_1678_);
lean_ctor_set(v___x_1366_, 2, v_v_1671_);
lean_ctor_set(v___x_1366_, 1, v_k_1670_);
lean_ctor_set(v___x_1366_, 0, v___x_1675_);
v___x_1682_ = v___x_1366_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1670_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1671_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1694_; 
v_r_1694_ = lean_ctor_get(v___x_1547_, 4);
lean_inc(v_r_1694_);
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1708_; 
v_k_1695_ = lean_ctor_get(v___x_1547_, 1);
v_v_1696_ = lean_ctor_get(v___x_1547_, 2);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; 
v_unused_1709_ = lean_ctor_get(v___x_1547_, 4);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v___x_1547_, 3);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1711_);
v___x_1698_ = v___x_1547_;
v_isShared_1699_ = v_isSharedCheck_1708_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_v_1696_);
lean_inc(v_k_1695_);
lean_dec(v___x_1547_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1708_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1700_ = lean_unsigned_to_nat(3u);
v___x_1701_ = lean_unsigned_to_nat(1u);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 4, v_l_1644_);
lean_ctor_set(v___x_1698_, 2, v_v_1362_);
lean_ctor_set(v___x_1698_, 1, v_k_1361_);
lean_ctor_set(v___x_1698_, 0, v___x_1701_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_l_1644_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_l_1644_);
v___x_1703_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v_r_1694_);
lean_ctor_set(v___x_1366_, 3, v___x_1703_);
lean_ctor_set(v___x_1366_, 2, v_v_1696_);
lean_ctor_set(v___x_1366_, 1, v_k_1695_);
lean_ctor_set(v___x_1366_, 0, v___x_1700_);
v___x_1705_ = v___x_1366_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1695_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1696_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_r_1694_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_unsigned_to_nat(2u);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1547_);
lean_ctor_set(v___x_1366_, 3, v_r_1694_);
lean_ctor_set(v___x_1366_, 0, v___x_1712_);
v___x_1714_ = v___x_1366_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v___x_1547_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_unsigned_to_nat(1u);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1547_);
lean_ctor_set(v___x_1366_, 3, v___x_1547_);
lean_ctor_set(v___x_1366_, 0, v___x_1716_);
v___x_1718_ = v___x_1366_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v___x_1547_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_k_1357_);
lean_ctor_set(v___x_1722_, 2, v_v_1358_);
lean_ctor_set(v___x_1722_, 3, v_t_1359_);
lean_ctor_set(v___x_1722_, 4, v_t_1359_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1723_, lean_object* v_x_1724_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
lean_object* v_k_1725_; lean_object* v_v_1726_; lean_object* v_l_1727_; lean_object* v_r_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_k_1725_ = lean_ctor_get(v_x_1724_, 1);
lean_inc(v_k_1725_);
v_v_1726_ = lean_ctor_get(v_x_1724_, 2);
lean_inc(v_v_1726_);
v_l_1727_ = lean_ctor_get(v_x_1724_, 3);
lean_inc(v_l_1727_);
v_r_1728_ = lean_ctor_get(v_x_1724_, 4);
lean_inc(v_r_1728_);
lean_dec_ref_known(v_x_1724_, 5);
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1723_, v_l_1727_);
v___x_1730_ = 1;
v___x_1731_ = l_Lean_Name_toString(v_k_1725_, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_v_1726_);
v___x_1733_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1731_, v___x_1732_, v___x_1729_);
v_init_1723_ = v___x_1733_;
v_x_1724_ = v_r_1728_;
goto _start;
}
else
{
return v_init_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_box(1);
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1736_, v_m_1735_);
v___x_1738_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
if (lean_obj_tag(v_a_1739_) == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_array_to_list(v_a_1740_);
return v___x_1741_;
}
else
{
lean_object* v_head_1742_; lean_object* v_tail_1743_; lean_object* v___x_1744_; 
v_head_1742_ = lean_ctor_get(v_a_1739_, 0);
lean_inc(v_head_1742_);
v_tail_1743_ = lean_ctor_get(v_a_1739_, 1);
lean_inc(v_tail_1743_);
lean_dec_ref_known(v_a_1739_, 2);
v___x_1744_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1740_, v_head_1742_);
v_a_1739_ = v_tail_1743_;
v_a_1740_ = v___x_1744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1754_){
_start:
{
lean_object* v_idx_1755_; lean_object* v_name_1756_; lean_object* v_platform_1757_; lean_object* v_leanHash_1758_; uint64_t v_configHash_1759_; lean_object* v_options_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_idx_1755_ = lean_ctor_get(v_x_1754_, 0);
lean_inc(v_idx_1755_);
v_name_1756_ = lean_ctor_get(v_x_1754_, 1);
lean_inc(v_name_1756_);
v_platform_1757_ = lean_ctor_get(v_x_1754_, 2);
lean_inc_ref(v_platform_1757_);
v_leanHash_1758_ = lean_ctor_get(v_x_1754_, 3);
lean_inc_ref(v_leanHash_1758_);
v_configHash_1759_ = lean_ctor_get_uint64(v_x_1754_, sizeof(void*)*5);
v_options_1760_ = lean_ctor_get(v_x_1754_, 4);
lean_inc(v_options_1760_);
lean_dec_ref(v_x_1754_);
v___x_1761_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1762_ = l_Lean_JsonNumber_fromNat(v_idx_1755_);
v___x_1763_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1761_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1764_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1768_ = 1;
v___x_1769_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1756_, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1767_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1765_);
v___x_1773_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_platform_1757_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1765_);
v___x_1777_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_leanHash_1758_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v___x_1765_);
v___x_1781_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1782_ = l_Lake_lowerHexUInt64(v_configHash_1759_);
v___x_1783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1781_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1765_);
v___x_1786_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1787_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1760_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1765_);
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1765_);
v___x_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1785_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1780_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1776_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1772_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1766_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1797_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1795_, v___x_1796_);
v___x_1798_ = l_Lean_Json_mkObj(v___x_1797_);
lean_dec(v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1799_, lean_object* v_msg_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1802_, lean_object* v_k_1803_, lean_object* v_v_1804_, lean_object* v_t_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1803_, v_v_1804_, v_t_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1807_, lean_object* v_t_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1807_, v_t_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1812_, lean_object* v_k_1813_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = l_Lean_Json_getObjValD(v_j_1812_, v_k_1813_);
v___x_1815_ = l_Lean_Json_getNat_x3f(v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1816_, lean_object* v_k_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1816_, v_k_1817_);
lean_dec_ref(v_k_1817_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1819_, lean_object* v_k_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = l_Lean_Json_getObjValD(v_j_1819_, v_k_1820_);
v___x_1822_ = l_Lean_Name_fromJson_x3f(v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1823_, lean_object* v_k_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1823_, v_k_1824_);
lean_dec_ref(v_k_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1826_, lean_object* v_k_1827_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = l_Lean_Json_getObjValD(v_j_1826_, v_k_1827_);
v___x_1829_ = l_Lean_Json_getStr_x3f(v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1830_, lean_object* v_k_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1830_, v_k_1831_);
lean_dec_ref(v_k_1831_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1833_, lean_object* v_k_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = l_Lean_Json_getObjValD(v_j_1833_, v_k_1834_);
v___x_1836_ = l_Lake_Hash_fromJson_x3f(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1837_, lean_object* v_k_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1837_, v_k_1838_);
lean_dec_ref(v_k_1838_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_object* v_k_1845_; lean_object* v_v_1846_; lean_object* v_l_1847_; lean_object* v_r_1848_; lean_object* v___x_1849_; 
v_k_1845_ = lean_ctor_get(v_x_1844_, 1);
lean_inc(v_k_1845_);
v_v_1846_ = lean_ctor_get(v_x_1844_, 2);
lean_inc(v_v_1846_);
v_l_1847_ = lean_ctor_get(v_x_1844_, 3);
lean_inc(v_l_1847_);
v_r_1848_ = lean_ctor_get(v_x_1844_, 4);
lean_inc(v_r_1848_);
lean_dec_ref_known(v_x_1844_, 5);
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1843_, v_l_1847_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_dec(v_r_1848_);
lean_dec(v_v_1846_);
lean_dec(v_k_1845_);
return v___x_1849_;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1890_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1890_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1890_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1855_ = lean_string_dec_eq(v_k_1845_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v_n_1856_; uint8_t v___x_1857_; 
lean_inc(v_k_1845_);
v_n_1856_ = l_String_toName(v_k_1845_);
v___x_1857_ = l_Lean_Name_isAnonymous(v_n_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_del_object(v___x_1852_);
lean_dec(v_k_1845_);
v___x_1858_ = l_Lean_Json_getStr_x3f(v_v_1846_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_n_1856_);
lean_dec(v_a_1850_);
lean_dec(v_r_1848_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1858_, 1);
v___x_1868_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1856_, v_a_1867_, v_a_1850_);
v_init_1843_ = v___x_1868_;
v_x_1844_ = v_r_1848_;
goto _start;
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_dec(v_n_1856_);
lean_dec(v_a_1850_);
lean_dec(v_r_1848_);
lean_dec(v_v_1846_);
v___x_1870_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1871_ = lean_string_append(v___x_1870_, v_k_1845_);
lean_dec(v_k_1845_);
v___x_1872_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1873_ = lean_string_append(v___x_1871_, v___x_1872_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1873_);
v___x_1875_ = v___x_1852_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v___x_1877_; 
lean_del_object(v___x_1852_);
lean_dec(v_k_1845_);
v___x_1877_ = l_Lean_Json_getStr_x3f(v_v_1846_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1850_);
lean_dec(v_r_1848_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_a_1886_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1887_ = lean_box(0);
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1887_, v_a_1886_, v_a_1850_);
v_init_1843_ = v___x_1888_;
v_x_1844_ = v_r_1848_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_init_1843_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1893_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 5)
{
lean_object* v_kvPairs_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_kvPairs_1894_ = lean_ctor_get(v_x_1893_, 0);
lean_inc(v_kvPairs_1894_);
lean_dec_ref_known(v_x_1893_, 1);
v___x_1895_ = lean_box(1);
v___x_1896_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1895_, v_kvPairs_1894_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1897_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1898_ = lean_unsigned_to_nat(80u);
v___x_1899_ = l_Lean_Json_pretty(v_x_1893_, v___x_1898_);
v___x_1900_ = lean_string_append(v___x_1897_, v___x_1899_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1902_ = lean_string_append(v___x_1900_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1904_, lean_object* v_k_1905_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = l_Lean_Json_getObjValD(v_j_1904_, v_k_1905_);
v___x_1907_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1908_, lean_object* v_k_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1908_, v_k_1909_);
lean_dec_ref(v_k_1909_);
return v_res_1910_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = 1;
v___x_1940_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1940_, v___x_1939_);
return v___x_1941_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1944_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1945_ = lean_string_append(v___x_1944_, v___x_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = 1;
v___x_1949_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1950_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1949_, v___x_1948_);
return v___x_1950_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1952_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1953_ = lean_string_append(v___x_1952_, v___x_1951_);
return v___x_1953_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1956_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1957_ = lean_string_append(v___x_1956_, v___x_1955_);
return v___x_1957_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = 1;
v___x_1961_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1962_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1961_, v___x_1960_);
return v___x_1962_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1964_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1965_ = lean_string_append(v___x_1964_, v___x_1963_);
return v___x_1965_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1967_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1968_ = lean_string_append(v___x_1967_, v___x_1966_);
return v___x_1968_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = 1;
v___x_1972_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1973_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1972_, v___x_1971_);
return v___x_1973_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1975_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1976_ = lean_string_append(v___x_1975_, v___x_1974_);
return v___x_1976_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1978_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1979_ = lean_string_append(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = 1;
v___x_1983_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1984_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1983_, v___x_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1986_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1987_ = lean_string_append(v___x_1986_, v___x_1985_);
return v___x_1987_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1989_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1990_ = lean_string_append(v___x_1989_, v___x_1988_);
return v___x_1990_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = 1;
v___x_1994_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1994_, v___x_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1997_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1998_ = lean_string_append(v___x_1997_, v___x_1996_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_2000_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_2001_ = lean_string_append(v___x_2000_, v___x_1999_);
return v___x_2001_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = 1;
v___x_2005_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_2006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2005_, v___x_2004_);
return v___x_2006_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_2008_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_2009_ = lean_string_append(v___x_2008_, v___x_2007_);
return v___x_2009_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_2011_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_2012_ = lean_string_append(v___x_2011_, v___x_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_2013_);
v___x_2015_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_2013_, v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_json_2013_);
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2025_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2025_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2020_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_2021_ = lean_string_append(v___x_2020_, v_a_2016_);
lean_dec(v_a_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2021_);
v___x_2023_ = v___x_2018_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_json_2013_);
v_a_2026_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2015_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2015_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2035_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_2013_);
v___x_2036_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_2013_, v___x_2035_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_2042_ = lean_string_append(v___x_2041_, v_a_2037_);
lean_dec(v_a_2037_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2047_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2036_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2036_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 0);
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_a_2055_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2056_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_2013_);
v___x_2057_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_2013_, v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2067_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2067_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2062_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_2063_ = lean_string_append(v___x_2062_, v_a_2058_);
lean_dec(v_a_2058_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2063_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2068_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2057_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2057_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 0);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2077_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_2013_);
v___x_2078_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_2013_, v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_2076_);
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2088_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2088_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2083_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
v___x_2084_ = lean_string_append(v___x_2083_, v_a_2079_);
lean_dec(v_a_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2084_);
v___x_2086_ = v___x_2081_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_a_2076_);
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2089_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2078_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2078_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 0);
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2097_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2098_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_2013_);
v___x_2099_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_2013_, v___x_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2097_);
lean_dec(v_a_2076_);
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2109_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2109_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2104_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
v___x_2105_ = lean_string_append(v___x_2104_, v_a_2100_);
lean_dec(v_a_2100_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
else
{
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_a_2097_);
lean_dec(v_a_2076_);
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
lean_dec(v_json_2013_);
v_a_2110_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2099_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2099_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 0);
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_a_2118_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2119_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2120_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_2013_, v___x_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_a_2118_);
lean_dec(v_a_2097_);
lean_dec(v_a_2076_);
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2130_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2130_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2125_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_2126_ = lean_string_append(v___x_2125_, v_a_2121_);
lean_dec(v_a_2121_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2126_);
v___x_2128_ = v___x_2123_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_a_2118_);
lean_dec(v_a_2097_);
lean_dec(v_a_2076_);
lean_dec(v_a_2055_);
lean_dec(v_a_2034_);
v_a_2131_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2120_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2120_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 0);
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2148_; 
v_a_2139_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2141_ = v___x_2120_;
v_isShared_2142_ = v_isSharedCheck_2148_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2120_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2148_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; uint64_t v___x_2144_; lean_object* v___x_2146_; 
v___x_2143_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2143_, 0, v_a_2034_);
lean_ctor_set(v___x_2143_, 1, v_a_2055_);
lean_ctor_set(v___x_2143_, 2, v_a_2076_);
lean_ctor_set(v___x_2143_, 3, v_a_2097_);
lean_ctor_set(v___x_2143_, 4, v_a_2139_);
v___x_2144_ = lean_unbox_uint64(v_a_2118_);
lean_dec(v_a_2118_);
lean_ctor_set_uint64(v___x_2143_, sizeof(void*)*5, v___x_2144_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2143_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2143_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
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
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_2153_ = lean_mk_io_user_error(v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_2154_, lean_object* v___x_2155_, lean_object* v_h_2156_){
_start:
{
uint8_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = 1;
v___x_2159_ = lean_io_prim_handle_mk(v___x_2154_, v___x_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = 1;
v___x_2162_ = lean_io_prim_handle_try_lock(v_a_2160_, v___x_2161_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; uint8_t v___x_2164_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = lean_unbox(v_a_2163_);
lean_dec(v_a_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_dec(v_a_2160_);
v___x_2165_ = lean_io_prim_handle_unlock(v_h_2156_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v___x_2165_, 0);
lean_dec(v_unused_2174_);
v___x_2167_ = v___x_2165_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_dec(v___x_2165_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 1);
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
v_a_2175_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2165_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2165_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_io_prim_handle_unlock(v_h_2156_);
if (lean_obj_tag(v___x_2183_) == 0)
{
uint8_t v___x_2184_; lean_object* v___x_2185_; 
lean_dec_ref_known(v___x_2183_, 1);
v___x_2184_ = 3;
v___x_2185_ = lean_io_prim_handle_mk(v___x_2155_, v___x_2184_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = lean_io_prim_handle_lock(v_a_2186_, v___x_2161_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2188_; 
lean_dec_ref_known(v___x_2187_, 1);
v___x_2188_ = lean_io_prim_handle_unlock(v_a_2160_);
lean_dec(v_a_2160_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v___x_2188_, 0);
lean_dec(v_unused_2196_);
v___x_2190_ = v___x_2188_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_dec(v___x_2188_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v_a_2186_);
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2186_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2186_);
v_a_2197_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2188_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2188_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2186_);
lean_dec(v_a_2160_);
v_a_2205_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2187_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2187_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_dec(v_a_2160_);
return v___x_2185_;
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2160_);
v_a_2213_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2183_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2183_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_a_2160_);
v_a_2221_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2162_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2162_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v_h_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lake_importConfigFile___lam__0(v___x_2229_, v___x_2230_, v_h_2231_);
lean_dec(v_h_2231_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2229_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v___y_2246_; lean_object* v_a_2247_; lean_object* v_lakeEnv_2249_; lean_object* v_wsDir_2250_; lean_object* v_pkgIdx_2251_; lean_object* v_pkgName_2252_; lean_object* v_pkgDir_2253_; lean_object* v_configFile_2254_; lean_object* v_lakeOpts_2255_; lean_object* v_leanOpts_2256_; uint8_t v_reconfigure_2257_; lean_object* v___x_2258_; 
v_lakeEnv_2249_ = lean_ctor_get(v_cfg_2242_, 0);
lean_inc_ref(v_lakeEnv_2249_);
v_wsDir_2250_ = lean_ctor_get(v_cfg_2242_, 2);
lean_inc_ref(v_wsDir_2250_);
v_pkgIdx_2251_ = lean_ctor_get(v_cfg_2242_, 3);
lean_inc(v_pkgIdx_2251_);
v_pkgName_2252_ = lean_ctor_get(v_cfg_2242_, 4);
lean_inc(v_pkgName_2252_);
v_pkgDir_2253_ = lean_ctor_get(v_cfg_2242_, 6);
lean_inc_ref(v_pkgDir_2253_);
v_configFile_2254_ = lean_ctor_get(v_cfg_2242_, 8);
lean_inc_ref_n(v_configFile_2254_, 2);
v_lakeOpts_2255_ = lean_ctor_get(v_cfg_2242_, 12);
lean_inc(v_lakeOpts_2255_);
v_leanOpts_2256_ = lean_ctor_get(v_cfg_2242_, 13);
lean_inc_ref(v_leanOpts_2256_);
v_reconfigure_2257_ = lean_ctor_get_uint8(v_cfg_2242_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2242_);
v___x_2258_ = l_System_FilePath_fileName(v_configFile_2254_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_wsDir_2250_);
lean_dec_ref(v_lakeEnv_2249_);
v___x_2259_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2260_ = lean_array_get_size(v_a_2243_);
v___x_2261_ = lean_array_push(v_a_2243_, v___x_2259_);
v___x_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
return v___x_2262_;
}
else
{
lean_object* v_val_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_configDir_2269_; lean_object* v___x_2270_; 
v_val_2263_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2264_ = l_Lake_defaultLakeDir;
v___x_2265_ = l_Lake_joinRelative(v_wsDir_2250_, v___x_2264_);
v___x_2266_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2267_ = l_Lake_joinRelative(v___x_2265_, v___x_2266_);
lean_inc(v_pkgIdx_2251_);
v___x_2268_ = l_Nat_reprFast(v_pkgIdx_2251_);
v_configDir_2269_ = l_Lake_joinRelative(v___x_2267_, v___x_2268_);
lean_inc_ref(v_configDir_2269_);
v___x_2270_ = l_IO_FS_createDirAll(v_configDir_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
lean_dec_ref_known(v___x_2270_, 1);
v___x_2271_ = l_Lake_computeTextFileHash(v_configFile_2254_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_h_2280_; lean_object* v_lakeOpts_2281_; lean_object* v___y_2282_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v_h_2465_; lean_object* v___y_2466_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2263_, 2);
v___x_2274_ = l_System_FilePath_withExtension(v_val_2263_, v___x_2273_);
lean_inc_ref_n(v_configDir_2269_, 2);
v___x_2275_ = l_Lake_joinRelative(v_configDir_2269_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2277_ = l_System_FilePath_withExtension(v_val_2263_, v___x_2276_);
v___x_2278_ = l_Lake_joinRelative(v_configDir_2269_, v___x_2277_);
v___x_2434_ = l_System_FilePath_pathExists(v___x_2278_);
v___x_2435_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2436_ = l_System_FilePath_withExtension(v_val_2263_, v___x_2435_);
v___x_2437_ = l_Lake_joinRelative(v_configDir_2269_, v___x_2436_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc_ref(v_pkgDir_2253_);
v___x_2554_ = l_Lake_joinRelative(v_pkgDir_2253_, v___x_2264_);
v___x_2555_ = l_IO_FS_createDirAll(v___x_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
uint8_t v___x_2556_; lean_object* v___x_2557_; 
lean_dec_ref_known(v___x_2555_, 1);
v___x_2556_ = 2;
v___x_2557_ = lean_io_prim_handle_mk(v___x_2278_, v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; 
lean_dec_ref(v___x_2437_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = 1;
v___x_2560_ = lean_io_prim_handle_lock(v_a_2558_, v___x_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_dec_ref_known(v___x_2560_, 1);
v_h_2280_ = v_a_2558_;
v_lakeOpts_2281_ = v_lakeOpts_2255_;
v___y_2282_ = v_a_2243_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_a_2558_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v___x_2562_ = lean_io_error_to_string(v_a_2561_);
v___x_2563_ = 3;
v___x_2564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*1, v___x_2563_);
v___x_2565_ = lean_array_get_size(v_a_2243_);
v___x_2566_ = lean_array_push(v_a_2243_, v___x_2564_);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
return v___x_2567_;
}
}
else
{
lean_object* v_a_2568_; 
v_a_2568_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2557_, 1);
if (lean_obj_tag(v_a_2568_) == 0)
{
uint8_t v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref_known(v_a_2568_, 2);
v___x_2569_ = 0;
v___x_2570_ = lean_io_prim_handle_mk(v___x_2278_, v___x_2569_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v_h_2465_ = v_a_2571_;
v___y_2466_ = v_a_2243_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2572_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2573_ = lean_io_error_to_string(v_a_2572_);
v___x_2574_ = 3;
v___x_2575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*1, v___x_2574_);
v___x_2576_ = lean_array_get_size(v_a_2243_);
v___x_2577_ = lean_array_push(v_a_2243_, v___x_2575_);
v___x_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
return v___x_2578_;
}
}
else
{
lean_object* v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v___x_2579_ = lean_io_error_to_string(v_a_2568_);
v___x_2580_ = 3;
v___x_2581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*1, v___x_2580_);
v___x_2582_ = lean_array_get_size(v_a_2243_);
v___x_2583_ = lean_array_push(v_a_2243_, v___x_2581_);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2585_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2586_ = lean_io_error_to_string(v_a_2585_);
v___x_2587_ = 3;
v___x_2588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*1, v___x_2587_);
v___x_2589_ = lean_array_get_size(v_a_2243_);
v___x_2590_ = lean_array_push(v_a_2243_, v___x_2588_);
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
return v___x_2591_;
}
}
else
{
uint8_t v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = 0;
v___x_2593_ = lean_io_prim_handle_mk(v___x_2278_, v___x_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v_h_2465_ = v_a_2594_;
v___y_2466_ = v_a_2243_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2595_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2596_ = lean_io_error_to_string(v_a_2595_);
v___x_2597_ = 3;
v___x_2598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*1, v___x_2597_);
v___x_2599_ = lean_array_get_size(v_a_2243_);
v___x_2600_ = lean_array_push(v_a_2243_, v___x_2598_);
v___x_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
return v___x_2601_;
}
}
v___jp_2279_:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_io_remove_file(v___x_2275_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint64_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec_ref_known(v___x_2283_, 1);
lean_dec_ref(v___x_2278_);
v___x_2284_ = l_System_Platform_target;
v___x_2285_ = l_Lake_Env_leanGithash(v_lakeEnv_2249_);
lean_dec_ref(v_lakeEnv_2249_);
lean_inc(v_lakeOpts_2281_);
lean_inc(v_pkgName_2252_);
lean_inc(v_pkgIdx_2251_);
v___x_2286_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2286_, 0, v_pkgIdx_2251_);
lean_ctor_set(v___x_2286_, 1, v_pkgName_2252_);
lean_ctor_set(v___x_2286_, 2, v___x_2284_);
lean_ctor_set(v___x_2286_, 3, v___x_2285_);
lean_ctor_set(v___x_2286_, 4, v_lakeOpts_2281_);
v___x_2287_ = lean_unbox_uint64(v_a_2272_);
lean_dec(v_a_2272_);
lean_ctor_set_uint64(v___x_2286_, sizeof(void*)*5, v___x_2287_);
v___x_2288_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2286_);
v___x_2289_ = lean_unsigned_to_nat(80u);
v___x_2290_ = l_Lean_Json_pretty(v___x_2288_, v___x_2289_);
v___x_2291_ = l_IO_FS_Handle_putStrLn(v_h_2280_, v___x_2290_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2292_; 
lean_dec_ref_known(v___x_2291_, 1);
v___x_2292_ = lean_io_prim_handle_flush(v_h_2280_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2292_, 1);
v___x_2293_ = lean_io_prim_handle_truncate(v_h_2280_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; 
lean_dec_ref_known(v___x_2293_, 1);
v___x_2294_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2251_, v_pkgName_2252_, v_pkgDir_2253_, v_lakeOpts_2281_, v_leanOpts_2256_, v_configFile_2254_, v___y_2282_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_a_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
v_a_2296_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_a_2296_);
v___x_2297_ = 1;
v___x_2298_ = l_Lean_writeModule(v_a_2295_, v___x_2275_, v___x_2297_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v___x_2299_; 
lean_dec_ref_known(v___x_2298_, 1);
v___x_2299_ = lean_io_prim_handle_unlock(v_h_2280_);
lean_dec(v_h_2280_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_dec_ref_known(v___x_2299_, 1);
lean_dec(v_a_2296_);
return v___x_2294_;
}
else
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2312_; 
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2313_ = lean_ctor_get(v___x_2294_, 1);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v___x_2294_, 0);
lean_dec(v_unused_2314_);
v___x_2301_ = v___x_2294_;
v_isShared_2302_ = v_isSharedCheck_2312_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v___x_2294_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2312_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_a_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v_a_2303_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2304_ = lean_io_error_to_string(v_a_2303_);
v___x_2305_ = 3;
v___x_2306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*1, v___x_2305_);
v___x_2307_ = lean_array_get_size(v_a_2296_);
v___x_2308_ = lean_array_push(v_a_2296_, v___x_2306_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 1);
lean_ctor_set(v___x_2301_, 1, v___x_2308_);
lean_ctor_set(v___x_2301_, 0, v___x_2307_);
v___x_2310_ = v___x_2301_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_h_2280_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; lean_object* v_unused_2329_; 
v_unused_2328_ = lean_ctor_get(v___x_2294_, 1);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v___x_2294_, 0);
lean_dec(v_unused_2329_);
v___x_2316_ = v___x_2294_;
v_isShared_2317_ = v_isSharedCheck_2327_;
goto v_resetjp_2315_;
}
else
{
lean_dec(v___x_2294_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2327_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_a_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v_a_2318_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2319_ = lean_io_error_to_string(v_a_2318_);
v___x_2320_ = 3;
v___x_2321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*1, v___x_2320_);
v___x_2322_ = lean_array_get_size(v_a_2296_);
v___x_2323_ = lean_array_push(v_a_2296_, v___x_2321_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set_tag(v___x_2316_, 1);
lean_ctor_set(v___x_2316_, 1, v___x_2323_);
lean_ctor_set(v___x_2316_, 0, v___x_2322_);
v___x_2325_ = v___x_2316_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
return v___x_2294_;
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_lakeOpts_2281_);
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
v_a_2330_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2331_ = lean_io_error_to_string(v_a_2330_);
v___x_2332_ = 3;
v___x_2333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*1, v___x_2332_);
v___x_2334_ = lean_array_get_size(v___y_2282_);
v___x_2335_ = lean_array_push(v___y_2282_, v___x_2333_);
v___x_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
return v___x_2336_;
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v_lakeOpts_2281_);
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
v_a_2337_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2338_ = lean_io_error_to_string(v_a_2337_);
v___x_2339_ = 3;
v___x_2340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*1, v___x_2339_);
v___x_2341_ = lean_array_get_size(v___y_2282_);
v___x_2342_ = lean_array_push(v___y_2282_, v___x_2340_);
v___x_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
return v___x_2343_;
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v_lakeOpts_2281_);
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
v_a_2344_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2345_ = lean_io_error_to_string(v_a_2344_);
v___x_2346_ = 3;
v___x_2347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*1, v___x_2346_);
v___x_2348_ = lean_array_get_size(v___y_2282_);
v___x_2349_ = lean_array_push(v___y_2282_, v___x_2347_);
v___x_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
return v___x_2350_;
}
}
else
{
lean_object* v_a_2351_; 
v_a_2351_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2283_, 1);
if (lean_obj_tag(v_a_2351_) == 11)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint64_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec_ref_known(v_a_2351_, 2);
lean_dec_ref(v___x_2278_);
v___x_2352_ = l_System_Platform_target;
v___x_2353_ = l_Lake_Env_leanGithash(v_lakeEnv_2249_);
lean_dec_ref(v_lakeEnv_2249_);
lean_inc(v_lakeOpts_2281_);
lean_inc(v_pkgName_2252_);
lean_inc(v_pkgIdx_2251_);
v___x_2354_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2354_, 0, v_pkgIdx_2251_);
lean_ctor_set(v___x_2354_, 1, v_pkgName_2252_);
lean_ctor_set(v___x_2354_, 2, v___x_2352_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
lean_ctor_set(v___x_2354_, 4, v_lakeOpts_2281_);
v___x_2355_ = lean_unbox_uint64(v_a_2272_);
lean_dec(v_a_2272_);
lean_ctor_set_uint64(v___x_2354_, sizeof(void*)*5, v___x_2355_);
v___x_2356_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2354_);
v___x_2357_ = lean_unsigned_to_nat(80u);
v___x_2358_ = l_Lean_Json_pretty(v___x_2356_, v___x_2357_);
v___x_2359_ = l_IO_FS_Handle_putStrLn(v_h_2280_, v___x_2358_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v___x_2360_; 
lean_dec_ref_known(v___x_2359_, 1);
v___x_2360_ = lean_io_prim_handle_flush(v_h_2280_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; 
lean_dec_ref_known(v___x_2360_, 1);
v___x_2361_ = lean_io_prim_handle_truncate(v_h_2280_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2361_, 1);
v___x_2362_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2251_, v_pkgName_2252_, v_pkgDir_2253_, v_lakeOpts_2281_, v_leanOpts_2256_, v_configFile_2254_, v___y_2282_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_a_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
v_a_2364_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_a_2364_);
v___x_2365_ = 1;
v___x_2366_ = l_Lean_writeModule(v_a_2363_, v___x_2275_, v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2367_; 
lean_dec_ref_known(v___x_2366_, 1);
v___x_2367_ = lean_io_prim_handle_unlock(v_h_2280_);
lean_dec(v_h_2280_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec_ref_known(v___x_2367_, 1);
lean_dec(v_a_2364_);
return v___x_2362_;
}
else
{
lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2380_; 
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; lean_object* v_unused_2382_; 
v_unused_2381_ = lean_ctor_get(v___x_2362_, 1);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v___x_2362_, 0);
lean_dec(v_unused_2382_);
v___x_2369_ = v___x_2362_;
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
else
{
lean_dec(v___x_2362_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_a_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2372_ = lean_io_error_to_string(v_a_2371_);
v___x_2373_ = 3;
v___x_2374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1, v___x_2373_);
v___x_2375_ = lean_array_get_size(v_a_2364_);
v___x_2376_ = lean_array_push(v_a_2364_, v___x_2374_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set_tag(v___x_2369_, 1);
lean_ctor_set(v___x_2369_, 1, v___x_2376_);
lean_ctor_set(v___x_2369_, 0, v___x_2375_);
v___x_2378_ = v___x_2369_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_h_2280_);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; lean_object* v_unused_2397_; 
v_unused_2396_ = lean_ctor_get(v___x_2362_, 1);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v___x_2362_, 0);
lean_dec(v_unused_2397_);
v___x_2384_ = v___x_2362_;
v_isShared_2385_ = v_isSharedCheck_2395_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v___x_2362_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2395_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_a_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v_a_2386_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2387_ = lean_io_error_to_string(v_a_2386_);
v___x_2388_ = 3;
v___x_2389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set_uint8(v___x_2389_, sizeof(void*)*1, v___x_2388_);
v___x_2390_ = lean_array_get_size(v_a_2364_);
v___x_2391_ = lean_array_push(v_a_2364_, v___x_2389_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set_tag(v___x_2384_, 1);
lean_ctor_set(v___x_2384_, 1, v___x_2391_);
lean_ctor_set(v___x_2384_, 0, v___x_2390_);
v___x_2393_ = v___x_2384_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
return v___x_2362_;
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_dec(v_lakeOpts_2281_);
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
v_a_2398_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2399_ = lean_io_error_to_string(v_a_2398_);
v___x_2400_ = 3;
v___x_2401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*1, v___x_2400_);
v___x_2402_ = lean_array_get_size(v___y_2282_);
v___x_2403_ = lean_array_push(v___y_2282_, v___x_2401_);
v___x_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
return v___x_2404_;
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v_lakeOpts_2281_);
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
v_a_2405_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2406_ = lean_io_error_to_string(v_a_2405_);
v___x_2407_ = 3;
v___x_2408_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*1, v___x_2407_);
v___x_2409_ = lean_array_get_size(v___y_2282_);
v___x_2410_ = lean_array_push(v___y_2282_, v___x_2408_);
v___x_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
return v___x_2411_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec(v_lakeOpts_2281_);
lean_dec(v_h_2280_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
v_a_2412_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2413_ = lean_io_error_to_string(v_a_2412_);
v___x_2414_ = 3;
v___x_2415_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*1, v___x_2414_);
v___x_2416_ = lean_array_get_size(v___y_2282_);
v___x_2417_ = lean_array_push(v___y_2282_, v___x_2415_);
v___x_2418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
return v___x_2418_;
}
}
else
{
lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v_lakeOpts_2281_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v___x_2419_ = lean_io_error_to_string(v_a_2351_);
v___x_2420_ = 3;
v___x_2421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*1, v___x_2420_);
v___x_2422_ = lean_array_get_size(v___y_2282_);
v___x_2423_ = lean_array_push(v___y_2282_, v___x_2421_);
v___x_2424_ = lean_io_prim_handle_unlock(v_h_2280_);
lean_dec(v_h_2280_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2425_; 
lean_dec_ref_known(v___x_2424_, 1);
v___x_2425_ = lean_io_remove_file(v___x_2278_);
lean_dec_ref(v___x_2278_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_dec_ref_known(v___x_2425_, 1);
v___y_2246_ = v___x_2422_;
v_a_2247_ = v___x_2423_;
goto v___jp_2245_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = lean_io_error_to_string(v_a_2426_);
v___x_2428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*1, v___x_2420_);
v___x_2429_ = lean_array_push(v___x_2423_, v___x_2428_);
v___y_2246_ = v___x_2422_;
v_a_2247_ = v___x_2429_;
goto v___jp_2245_;
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref(v___x_2278_);
v_a_2430_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2431_ = lean_io_error_to_string(v_a_2430_);
v___x_2432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*1, v___x_2420_);
v___x_2433_ = lean_array_push(v___x_2423_, v___x_2432_);
v___y_2246_ = v___x_2422_;
v_a_2247_ = v___x_2433_;
goto v___jp_2245_;
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lake_importConfigFile___lam__0(v___x_2437_, v___x_2278_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___x_2437_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v_options_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v_options_2444_ = lean_ctor_get(v___y_2440_, 4);
lean_inc(v_options_2444_);
lean_dec_ref(v___y_2440_);
v_h_2280_ = v_a_2443_;
v_lakeOpts_2281_ = v_options_2444_;
v___y_2282_ = v___y_2439_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2445_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2446_ = lean_io_error_to_string(v_a_2445_);
v___x_2447_ = 3;
v___x_2448_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*1, v___x_2447_);
v___x_2449_ = lean_array_get_size(v___y_2439_);
v___x_2450_ = lean_array_push(v___y_2439_, v___x_2448_);
v___x_2451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
return v___x_2451_;
}
}
v___jp_2452_:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lake_importConfigFile___lam__0(v___x_2437_, v___x_2278_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___x_2437_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v_h_2280_ = v_a_2456_;
v_lakeOpts_2281_ = v_lakeOpts_2255_;
v___y_2282_ = v___y_2453_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2457_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2458_ = lean_io_error_to_string(v_a_2457_);
v___x_2459_ = 3;
v___x_2460_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*1, v___x_2459_);
v___x_2461_ = lean_array_get_size(v___y_2453_);
v___x_2462_ = lean_array_push(v___y_2453_, v___x_2460_);
v___x_2463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
return v___x_2463_;
}
}
v___jp_2464_:
{
if (v_reconfigure_2257_ == 0)
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_io_prim_handle_lock(v_h_2465_, v_reconfigure_2257_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v___x_2468_; 
lean_dec_ref_known(v___x_2467_, 1);
v___x_2468_ = l_IO_FS_Handle_readToEnd(v_h_2465_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = l_Lean_Json_parse(v_a_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2471_; 
lean_dec_ref_known(v___x_2470_, 1);
v___x_2471_ = l_Lake_importConfigFile___lam__0(v___x_2437_, v___x_2278_, v_h_2465_);
lean_dec(v_h_2465_);
lean_dec_ref(v___x_2437_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v_h_2280_ = v_a_2472_;
v_lakeOpts_2281_ = v_lakeOpts_2255_;
v___y_2282_ = v___y_2466_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2473_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2474_ = lean_io_error_to_string(v_a_2473_);
v___x_2475_ = 3;
v___x_2476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*1, v___x_2475_);
v___x_2477_ = lean_array_get_size(v___y_2466_);
v___x_2478_ = lean_array_push(v___y_2466_, v___x_2476_);
v___x_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
return v___x_2479_;
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_n(v_a_2480_, 2);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2481_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2481_, 1);
v___x_2482_ = l_Lean_Json_getObj_x3f(v_a_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_dec_ref_known(v___x_2482_, 1);
v___y_2453_ = v___y_2466_;
v___y_2454_ = v_h_2465_;
goto v___jp_2452_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2485_ = l_Lake_JsonObject_getJson_x3f(v_a_2483_, v___x_2484_);
lean_dec(v_a_2483_);
if (lean_obj_tag(v___x_2485_) == 0)
{
v___y_2453_ = v___y_2466_;
v___y_2454_ = v_h_2465_;
goto v___jp_2452_;
}
else
{
lean_object* v_val_2486_; lean_object* v___x_2487_; 
v_val_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2487_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_dec_ref_known(v___x_2487_, 1);
v___y_2453_ = v___y_2466_;
v___y_2454_ = v_h_2465_;
goto v___jp_2452_;
}
else
{
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_dec_ref_known(v___x_2487_, 1);
v___y_2453_ = v___y_2466_;
v___y_2454_ = v_h_2465_;
goto v___jp_2452_;
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2489_; 
lean_dec(v_lakeOpts_2255_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = l_Lake_importConfigFile___lam__0(v___x_2437_, v___x_2278_, v_h_2465_);
lean_dec(v_h_2465_);
lean_dec_ref(v___x_2437_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v_h_2280_ = v_a_2490_;
v_lakeOpts_2281_ = v_a_2488_;
v___y_2282_ = v___y_2466_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_dec(v_a_2488_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2492_ = lean_io_error_to_string(v_a_2491_);
v___x_2493_ = 3;
v___x_2494_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*1, v___x_2493_);
v___x_2495_ = lean_array_get_size(v___y_2466_);
v___x_2496_ = lean_array_push(v___y_2466_, v___x_2494_);
v___x_2497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
return v___x_2497_;
}
}
}
}
}
}
else
{
lean_object* v_a_2498_; uint8_t v___x_2499_; 
lean_dec(v_a_2480_);
lean_dec(v_lakeOpts_2255_);
v_a_2498_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2499_ = l_System_FilePath_pathExists(v___x_2275_);
if (v___x_2499_ == 0)
{
v___y_2439_ = v___y_2466_;
v___y_2440_ = v_a_2498_;
v___y_2441_ = v_h_2465_;
goto v___jp_2438_;
}
else
{
lean_object* v_idx_2500_; lean_object* v_name_2501_; lean_object* v_platform_2502_; lean_object* v_leanHash_2503_; uint64_t v_configHash_2504_; uint8_t v___x_2505_; 
v_idx_2500_ = lean_ctor_get(v_a_2498_, 0);
v_name_2501_ = lean_ctor_get(v_a_2498_, 1);
v_platform_2502_ = lean_ctor_get(v_a_2498_, 2);
v_leanHash_2503_ = lean_ctor_get(v_a_2498_, 3);
v_configHash_2504_ = lean_ctor_get_uint64(v_a_2498_, sizeof(void*)*5);
v___x_2505_ = lean_nat_dec_eq(v_idx_2500_, v_pkgIdx_2251_);
if (v___x_2505_ == 0)
{
v___y_2439_ = v___y_2466_;
v___y_2440_ = v_a_2498_;
v___y_2441_ = v_h_2465_;
goto v___jp_2438_;
}
else
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_name_eq(v_name_2501_, v_pkgName_2252_);
if (v___x_2506_ == 0)
{
v___y_2439_ = v___y_2466_;
v___y_2440_ = v_a_2498_;
v___y_2441_ = v_h_2465_;
goto v___jp_2438_;
}
else
{
uint64_t v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = lean_unbox_uint64(v_a_2272_);
v___x_2508_ = lean_uint64_dec_eq(v_configHash_2504_, v___x_2507_);
if (v___x_2508_ == 0)
{
v___y_2439_ = v___y_2466_;
v___y_2440_ = v_a_2498_;
v___y_2441_ = v_h_2465_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2509_ = l_System_Platform_target;
v___x_2510_ = lean_string_dec_eq(v_platform_2502_, v___x_2509_);
if (v___x_2510_ == 0)
{
v___y_2439_ = v___y_2466_;
v___y_2440_ = v_a_2498_;
v___y_2441_ = v_h_2465_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2511_ = l_Lake_Env_leanGithash(v_lakeEnv_2249_);
v___x_2512_ = lean_string_dec_eq(v_leanHash_2503_, v___x_2511_);
lean_dec_ref(v___x_2511_);
if (v___x_2512_ == 0)
{
v___y_2439_ = v___y_2466_;
v___y_2440_ = v_a_2498_;
v___y_2441_ = v_h_2465_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2513_; 
lean_dec(v_a_2498_);
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec(v_a_2272_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v___x_2513_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2275_, v_leanOpts_2256_);
lean_dec_ref(v___x_2275_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = lean_io_prim_handle_unlock(v_h_2465_);
lean_dec(v_h_2465_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref_known(v___x_2515_, 1);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2514_);
lean_ctor_set(v___x_2516_, 1, v___y_2466_);
return v___x_2516_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v_a_2514_);
v_a_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2518_ = lean_io_error_to_string(v_a_2517_);
v___x_2519_ = 3;
v___x_2520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set_uint8(v___x_2520_, sizeof(void*)*1, v___x_2519_);
v___x_2521_ = lean_array_get_size(v___y_2466_);
v___x_2522_ = lean_array_push(v___y_2466_, v___x_2520_);
v___x_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
return v___x_2523_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_h_2465_);
v_a_2524_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2525_ = lean_io_error_to_string(v_a_2524_);
v___x_2526_ = 3;
v___x_2527_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*1, v___x_2526_);
v___x_2528_ = lean_array_get_size(v___y_2466_);
v___x_2529_ = lean_array_push(v___y_2466_, v___x_2527_);
v___x_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
return v___x_2530_;
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
lean_object* v_a_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v_h_2465_);
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2531_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2532_ = lean_io_error_to_string(v_a_2531_);
v___x_2533_ = 3;
v___x_2534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*1, v___x_2533_);
v___x_2535_ = lean_array_get_size(v___y_2466_);
v___x_2536_ = lean_array_push(v___y_2466_, v___x_2534_);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
return v___x_2537_;
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_h_2465_);
lean_dec_ref(v___x_2437_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2538_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2539_ = lean_io_error_to_string(v_a_2538_);
v___x_2540_ = 3;
v___x_2541_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*1, v___x_2540_);
v___x_2542_ = lean_array_get_size(v___y_2466_);
v___x_2543_ = lean_array_push(v___y_2466_, v___x_2541_);
v___x_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
return v___x_2544_;
}
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lake_importConfigFile___lam__0(v___x_2437_, v___x_2278_, v_h_2465_);
lean_dec(v_h_2465_);
lean_dec_ref(v___x_2437_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v_h_2280_ = v_a_2546_;
v_lakeOpts_2281_ = v_lakeOpts_2255_;
v___y_2282_ = v___y_2466_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2275_);
lean_dec(v_a_2272_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2547_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2548_ = lean_io_error_to_string(v_a_2547_);
v___x_2549_ = 3;
v___x_2550_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*1, v___x_2549_);
v___x_2551_ = lean_array_get_size(v___y_2466_);
v___x_2552_ = lean_array_push(v___y_2466_, v___x_2550_);
v___x_2553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
return v___x_2553_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec_ref(v_configDir_2269_);
lean_dec(v_val_2263_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2602_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2603_ = lean_io_error_to_string(v_a_2602_);
v___x_2604_ = 3;
v___x_2605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*1, v___x_2604_);
v___x_2606_ = lean_array_get_size(v_a_2243_);
v___x_2607_ = lean_array_push(v_a_2243_, v___x_2605_);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
return v___x_2608_;
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref(v_configDir_2269_);
lean_dec(v_val_2263_);
lean_dec_ref(v_leanOpts_2256_);
lean_dec(v_lakeOpts_2255_);
lean_dec_ref(v_configFile_2254_);
lean_dec_ref(v_pkgDir_2253_);
lean_dec(v_pkgName_2252_);
lean_dec(v_pkgIdx_2251_);
lean_dec_ref(v_lakeEnv_2249_);
v_a_2609_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2610_ = lean_io_error_to_string(v_a_2609_);
v___x_2611_ = 3;
v___x_2612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1, v___x_2611_);
v___x_2613_ = lean_array_get_size(v_a_2243_);
v___x_2614_ = lean_array_push(v_a_2243_, v___x_2612_);
v___x_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
return v___x_2615_;
}
}
v___jp_2245_:
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___y_2246_);
lean_ctor_set(v___x_2248_, 1, v_a_2247_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lake_importConfigFile(v_cfg_2616_, v_a_2617_);
return v_res_2619_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_AttributesCore(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Lean_Elab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
