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
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* v_key_90_; lean_object* v_value_91_; lean_object* v_tail_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_123_; 
v_key_90_ = lean_ctor_get(v_x_89_, 0);
v_value_91_ = lean_ctor_get(v_x_89_, 1);
v_tail_92_ = lean_ctor_get(v_x_89_, 2);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_123_ == 0)
{
v___x_94_ = v_x_89_;
v_isShared_95_ = v_isSharedCheck_123_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_tail_92_);
lean_inc(v_value_91_);
lean_inc(v_key_90_);
lean_dec(v_x_89_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_123_;
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
size_t v___x_120_; size_t v___x_121_; uint64_t v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_118_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_key_90_, v___x_120_, v___x_121_, v___x_116_);
v___y_98_ = v___x_122_;
goto v___jp_97_;
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(lean_object* v_i_124_, lean_object* v_source_125_, lean_object* v_target_126_){
_start:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_array_get_size(v_source_125_);
v___x_128_ = lean_nat_dec_lt(v_i_124_, v___x_127_);
if (v___x_128_ == 0)
{
lean_dec_ref(v_source_125_);
lean_dec(v_i_124_);
return v_target_126_;
}
else
{
lean_object* v_es_129_; lean_object* v___x_130_; lean_object* v_source_131_; lean_object* v_target_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_es_129_ = lean_array_fget(v_source_125_, v_i_124_);
v___x_130_ = lean_box(0);
v_source_131_ = lean_array_fset(v_source_125_, v_i_124_, v___x_130_);
v_target_132_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_target_126_, v_es_129_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_i_124_, v___x_133_);
lean_dec(v_i_124_);
v_i_124_ = v___x_134_;
v_source_125_ = v_source_131_;
v_target_126_ = v_target_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(lean_object* v_data_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_nbuckets_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_137_ = lean_array_get_size(v_data_136_);
v___x_138_ = lean_unsigned_to_nat(2u);
v_nbuckets_139_ = lean_nat_mul(v___x_137_, v___x_138_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_box(0);
v___x_142_ = lean_mk_array(v_nbuckets_139_, v___x_141_);
v___x_143_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v___x_140_, v_data_136_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object* v_m_144_, lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
lean_object* v_size_147_; lean_object* v_buckets_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_199_; 
v_size_147_ = lean_ctor_get(v_m_144_, 0);
v_buckets_148_ = lean_ctor_get(v_m_144_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_m_144_);
if (v_isSharedCheck_199_ == 0)
{
v___x_150_ = v_m_144_;
v_isShared_151_ = v_isSharedCheck_199_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_buckets_148_);
lean_inc(v_size_147_);
lean_dec(v_m_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_199_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; uint64_t v___y_154_; uint64_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_152_ = lean_array_get_size(v_buckets_148_);
v___x_192_ = 7ULL;
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_array_get_size(v_a_145_);
v___x_195_ = lean_nat_dec_lt(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
v___y_154_ = v___x_192_;
goto v___jp_153_;
}
else
{
size_t v___x_196_; size_t v___x_197_; uint64_t v___x_198_; 
v___x_196_ = ((size_t)0ULL);
v___x_197_ = lean_usize_of_nat(v___x_194_);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_145_, v___x_196_, v___x_197_, v___x_192_);
v___y_154_ = v___x_198_;
goto v___jp_153_;
}
v___jp_153_:
{
uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v_fold_157_; uint64_t v___x_158_; uint64_t v___x_159_; uint64_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v_bkt_166_; uint8_t v___x_167_; 
v___x_155_ = 32ULL;
v___x_156_ = lean_uint64_shift_right(v___y_154_, v___x_155_);
v_fold_157_ = lean_uint64_xor(v___y_154_, v___x_156_);
v___x_158_ = 16ULL;
v___x_159_ = lean_uint64_shift_right(v_fold_157_, v___x_158_);
v___x_160_ = lean_uint64_xor(v_fold_157_, v___x_159_);
v___x_161_ = lean_uint64_to_usize(v___x_160_);
v___x_162_ = lean_usize_of_nat(v___x_152_);
v___x_163_ = ((size_t)1ULL);
v___x_164_ = lean_usize_sub(v___x_162_, v___x_163_);
v___x_165_ = lean_usize_land(v___x_161_, v___x_164_);
v_bkt_166_ = lean_array_uget_borrowed(v_buckets_148_, v___x_165_);
v___x_167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_145_, v_bkt_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v_size_x27_169_; lean_object* v___x_170_; lean_object* v_buckets_x27_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_168_ = lean_unsigned_to_nat(1u);
v_size_x27_169_ = lean_nat_add(v_size_147_, v___x_168_);
lean_dec(v_size_147_);
lean_inc(v_bkt_166_);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v_a_145_);
lean_ctor_set(v___x_170_, 1, v_b_146_);
lean_ctor_set(v___x_170_, 2, v_bkt_166_);
v_buckets_x27_171_ = lean_array_uset(v_buckets_148_, v___x_165_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(4u);
v___x_173_ = lean_nat_mul(v_size_x27_169_, v___x_172_);
v___x_174_ = lean_unsigned_to_nat(3u);
v___x_175_ = lean_nat_div(v___x_173_, v___x_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_array_get_size(v_buckets_x27_171_);
v___x_177_ = lean_nat_dec_le(v___x_175_, v___x_176_);
lean_dec(v___x_175_);
if (v___x_177_ == 0)
{
lean_object* v_val_178_; lean_object* v___x_180_; 
v_val_178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_buckets_x27_171_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_val_178_);
lean_ctor_set(v___x_150_, 0, v_size_x27_169_);
v___x_180_ = v___x_150_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_size_x27_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_val_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v___x_183_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_buckets_x27_171_);
lean_ctor_set(v___x_150_, 0, v_size_x27_169_);
v___x_183_ = v___x_150_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_size_x27_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_buckets_x27_171_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_object* v___x_185_; lean_object* v_buckets_x27_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_bkt_166_);
v___x_185_ = lean_box(0);
v_buckets_x27_186_ = lean_array_uset(v_buckets_148_, v___x_165_, v___x_185_);
v___x_187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_145_, v_b_146_, v_bkt_166_);
v___x_188_ = lean_array_uset(v_buckets_x27_186_, v___x_165_, v___x_187_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_188_);
v___x_190_ = v___x_150_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_size_147_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object* v_a_200_, lean_object* v_x_201_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v_key_203_; lean_object* v_value_204_; lean_object* v_tail_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_key_203_ = lean_ctor_get(v_x_201_, 0);
v_value_204_ = lean_ctor_get(v_x_201_, 1);
v_tail_205_ = lean_ctor_get(v_x_201_, 2);
v___x_206_ = lean_array_get_size(v_key_203_);
v___x_207_ = lean_array_get_size(v_a_200_);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
v_x_201_ = v_tail_205_;
goto _start;
}
else
{
uint8_t v___x_210_; 
v___x_210_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_203_, v_a_200_, v___x_206_);
if (v___x_210_ == 0)
{
v_x_201_ = v_tail_205_;
goto _start;
}
else
{
lean_object* v___x_212_; 
lean_inc(v_value_204_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_value_204_);
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_213_, v_x_214_);
lean_dec(v_x_214_);
lean_dec_ref(v_a_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object* v_m_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_buckets_218_; lean_object* v___x_219_; uint64_t v___y_221_; uint64_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_buckets_218_ = lean_ctor_get(v_m_216_, 1);
v___x_219_ = lean_array_get_size(v_buckets_218_);
v___x_235_ = 7ULL;
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_array_get_size(v_a_217_);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
v___y_221_ = v___x_235_;
goto v___jp_220_;
}
else
{
size_t v___x_239_; size_t v___x_240_; uint64_t v___x_241_; 
v___x_239_ = ((size_t)0ULL);
v___x_240_ = lean_usize_of_nat(v___x_237_);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_217_, v___x_239_, v___x_240_, v___x_235_);
v___y_221_ = v___x_241_;
goto v___jp_220_;
}
v___jp_220_:
{
uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v_fold_224_; uint64_t v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_222_ = 32ULL;
v___x_223_ = lean_uint64_shift_right(v___y_221_, v___x_222_);
v_fold_224_ = lean_uint64_xor(v___y_221_, v___x_223_);
v___x_225_ = 16ULL;
v___x_226_ = lean_uint64_shift_right(v_fold_224_, v___x_225_);
v___x_227_ = lean_uint64_xor(v_fold_224_, v___x_226_);
v___x_228_ = lean_uint64_to_usize(v___x_227_);
v___x_229_ = lean_usize_of_nat(v___x_219_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_sub(v___x_229_, v___x_230_);
v___x_232_ = lean_usize_land(v___x_228_, v___x_231_);
v___x_233_ = lean_array_uget_borrowed(v_buckets_218_, v___x_232_);
v___x_234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_217_, v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_242_, v_a_243_);
lean_dec_ref(v_a_243_);
lean_dec_ref(v_m_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* v_imports_247_, lean_object* v_opts_248_, uint32_t v_trustLevel_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
v___x_252_ = lean_st_ref_get(v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v___x_252_, v_imports_247_);
lean_dec(v___x_252_);
if (lean_obj_tag(v___x_253_) == 1)
{
lean_object* v_val_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_opts_248_);
lean_dec_ref(v_imports_247_);
v_val_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_val_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 0);
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_val_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; uint8_t v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_253_);
v___x_262_ = lean_enable_initializer_execution();
v___x_263_ = ((lean_object*)(l_Lake_importModulesUsingCache___closed__0));
v___x_264_ = 0;
v___x_265_ = 1;
v___x_266_ = 2;
v___x_267_ = lean_box(1);
lean_inc_ref(v_imports_247_);
v___x_268_ = l_Lean_importModules(v_imports_247_, v_opts_248_, v_trustLevel_249_, v___x_263_, v___x_264_, v___x_265_, v___x_266_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_279_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_273_ = lean_st_ref_take(v___x_251_);
lean_inc(v_a_269_);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_273_, v_imports_247_, v_a_269_);
v___x_275_ = lean_st_ref_put(v___x_251_, v___x_274_);
if (v_isShared_272_ == 0)
{
v___x_277_ = v___x_271_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_269_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_dec_ref(v_imports_247_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* v_imports_280_, lean_object* v_opts_281_, lean_object* v_trustLevel_282_, lean_object* v_a_283_){
_start:
{
uint32_t v_trustLevel_boxed_284_; lean_object* v_res_285_; 
v_trustLevel_boxed_284_ = lean_unbox_uint32(v_trustLevel_282_);
lean_dec(v_trustLevel_282_);
v_res_285_ = l_Lake_importModulesUsingCache(v_imports_280_, v_opts_281_, v_trustLevel_boxed_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object* v_00_u03b2_286_, lean_object* v_m_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_287_, v_a_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object* v_00_u03b2_290_, lean_object* v_m_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_290_, v_m_291_, v_a_292_);
lean_dec_ref(v_a_292_);
lean_dec_ref(v_m_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(lean_object* v_00_u03b2_294_, lean_object* v_m_295_, lean_object* v_a_296_, lean_object* v_b_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_295_, v_a_296_, v_b_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object* v_00_u03b2_299_, lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_300_, v_x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_303_, lean_object* v_a_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_303_, v_a_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec_ref(v_a_304_);
return v_res_306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object* v_00_u03b2_307_, lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_308_, v_x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_00_u03b2_311_, v_a_312_, v_x_313_);
lean_dec(v_x_313_);
lean_dec_ref(v_a_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(lean_object* v_00_u03b2_316_, lean_object* v_data_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_data_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_b_321_, lean_object* v_x_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_320_, v_b_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(lean_object* v_xs_324_, lean_object* v_ys_325_, lean_object* v_hsz_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_324_, v_ys_325_, v_x_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_330_, lean_object* v_ys_331_, lean_object* v_hsz_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_330_, v_ys_331_, v_hsz_332_, v_x_333_, v_x_334_);
lean_dec_ref(v_ys_331_);
lean_dec_ref(v_xs_330_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_337_, lean_object* v_i_338_, lean_object* v_source_339_, lean_object* v_target_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v_i_338_, v_source_339_, v_target_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_x_343_, v_x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object* v_header_347_, lean_object* v_opts_348_, lean_object* v_inputCtx_349_, lean_object* v_a_350_){
_start:
{
uint8_t v___x_352_; lean_object* v_imports_353_; uint32_t v___x_354_; lean_object* v___x_355_; 
v___x_352_ = 1;
lean_inc(v_header_347_);
v_imports_353_ = l_Lean_Elab_HeaderSyntax_imports(v_header_347_, v___x_352_);
v___x_354_ = 1024;
v___x_355_ = l_Lake_importModulesUsingCache(v_imports_353_, v_opts_348_, v___x_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v_inputCtx_349_);
lean_dec(v_header_347_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_364_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_a_356_);
lean_ctor_set(v___x_360_, 1, v_a_350_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v_fileName_366_; lean_object* v_fileMap_367_; uint8_t v___x_368_; lean_object* v___y_370_; lean_object* v___x_399_; 
v_a_365_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_355_, 1);
v_fileName_366_ = lean_ctor_get(v_inputCtx_349_, 1);
lean_inc_ref(v_fileName_366_);
v_fileMap_367_ = lean_ctor_get(v_inputCtx_349_, 2);
lean_inc_ref(v_fileMap_367_);
lean_dec_ref(v_inputCtx_349_);
v___x_368_ = 0;
v___x_399_ = l_Lean_Syntax_getPos_x3f(v_header_347_, v___x_368_);
lean_dec(v_header_347_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___y_370_ = v___x_400_;
goto v___jp_369_;
}
else
{
lean_object* v_val_401_; 
v_val_401_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v___x_399_, 1);
v___y_370_ = v_val_401_;
goto v___jp_369_;
}
v___jp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint32_t v___x_379_; lean_object* v___x_380_; 
v___x_371_ = l_Lean_FileMap_toPosition(v_fileMap_367_, v___y_370_);
lean_dec(v___y_370_);
v___x_372_ = lean_box(0);
v___x_373_ = 2;
v___x_374_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0));
v___x_375_ = lean_io_error_to_string(v_a_365_);
v___x_376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___x_377_ = l_Lean_MessageData_ofFormat(v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_378_, 0, v_fileName_366_);
lean_ctor_set(v___x_378_, 1, v___x_371_);
lean_ctor_set(v___x_378_, 2, v___x_372_);
lean_ctor_set(v___x_378_, 3, v___x_374_);
lean_ctor_set(v___x_378_, 4, v___x_377_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*5, v___x_368_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*5 + 1, v___x_373_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*5 + 2, v___x_368_);
v___x_379_ = 0;
v___x_380_ = l_Lean_mkEmptyEnvironment(v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_390_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = l_Lean_MessageLog_add(v___x_378_, v_a_350_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_a_381_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref_known(v___x_378_, 5);
lean_dec_ref(v_a_350_);
v_a_391_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_380_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_380_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object* v_header_402_, lean_object* v_opts_403_, lean_object* v_inputCtx_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_402_, v_opts_403_, v_inputCtx_404_, v_a_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
uint8_t v_isSilent_415_; 
v_isSilent_415_ = lean_ctor_get_uint8(v_x_412_, sizeof(void*)*5 + 2);
if (v_isSilent_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_416_ = l_Lake_LogEntry_ofMessage(v_x_412_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_array_push(v___y_413_, v___x_416_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_x_412_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___y_413_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_422_, v___y_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_426_, lean_object* v_as_427_, size_t v_i_428_, size_t v_stop_429_, lean_object* v_b_430_, lean_object* v___y_431_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_eq(v_i_428_, v_stop_429_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_array_uget_borrowed(v_as_427_, v_i_428_);
lean_inc_ref(v_f_426_);
lean_inc(v___x_434_);
v___x_435_ = lean_apply_3(v_f_426_, v___x_434_, v___y_431_, lean_box(0));
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_a_437_; size_t v___x_438_; size_t v___x_439_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
v_a_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_435_, 2);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_428_, v___x_438_);
v_i_428_ = v___x_439_;
v_b_430_ = v_a_436_;
v___y_431_ = v_a_437_;
goto _start;
}
else
{
lean_dec_ref(v_f_426_);
return v___x_435_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec_ref(v_f_426_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_b_430_);
lean_ctor_set(v___x_441_, 1, v___y_431_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_442_, lean_object* v_as_443_, lean_object* v_i_444_, lean_object* v_stop_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
size_t v_i_boxed_449_; size_t v_stop_boxed_450_; lean_object* v_res_451_; 
v_i_boxed_449_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_stop_boxed_450_ = lean_unbox_usize(v_stop_445_);
lean_dec(v_stop_445_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_442_, v_as_443_, v_i_boxed_449_, v_stop_boxed_450_, v_b_446_, v___y_447_);
lean_dec_ref(v_as_443_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_452_, lean_object* v_x_453_, lean_object* v___y_454_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v_cs_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_cs_456_ = lean_ctor_get(v_x_453_, 0);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_array_get_size(v_cs_456_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_nat_dec_lt(v___x_457_, v___x_458_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec_ref(v_f_452_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___y_454_);
return v___x_461_;
}
else
{
size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v___x_462_ = ((size_t)0ULL);
v___x_463_ = lean_usize_of_nat(v___x_458_);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_452_, v_cs_456_, v___x_462_, v___x_463_, v___x_459_, v___y_454_);
return v___x_464_;
}
}
else
{
lean_object* v_vs_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_vs_465_ = lean_ctor_get(v_x_453_, 0);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_array_get_size(v_vs_465_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec_ref(v_f_452_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___y_454_);
return v___x_470_;
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((size_t)0ULL);
v___x_472_ = lean_usize_of_nat(v___x_467_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_452_, v_vs_465_, v___x_471_, v___x_472_, v___x_468_, v___y_454_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_474_, lean_object* v_as_475_, size_t v_i_476_, size_t v_stop_477_, lean_object* v_b_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_eq(v_i_476_, v_stop_477_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_array_uget_borrowed(v_as_475_, v_i_476_);
lean_inc_ref(v_f_474_);
v___x_483_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_474_, v___x_482_, v___y_479_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v_a_485_; size_t v___x_486_; size_t v___x_487_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
v_a_485_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_483_, 2);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_476_, v___x_486_);
v_i_476_ = v___x_487_;
v_b_478_ = v_a_484_;
v___y_479_ = v_a_485_;
goto _start;
}
else
{
lean_dec_ref(v_f_474_);
return v___x_483_;
}
}
else
{
lean_object* v___x_489_; 
lean_dec_ref(v_f_474_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_b_478_);
lean_ctor_set(v___x_489_, 1, v___y_479_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_490_, lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
size_t v_i_boxed_497_; size_t v_stop_boxed_498_; lean_object* v_res_499_; 
v_i_boxed_497_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_498_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_490_, v_as_491_, v_i_boxed_497_, v_stop_boxed_498_, v_b_494_, v___y_495_);
lean_dec_ref(v_as_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_500_, v_x_501_, v___y_502_);
lean_dec_ref(v_x_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_505_, lean_object* v_t_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_root_509_; lean_object* v_tail_510_; lean_object* v___x_511_; 
v_root_509_ = lean_ctor_get(v_t_506_, 0);
v_tail_510_ = lean_ctor_get(v_t_506_, 1);
lean_inc_ref(v_f_505_);
v___x_511_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_505_, v_root_509_, v___y_507_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_526_; 
v_a_512_ = lean_ctor_get(v___x_511_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___x_511_, 0);
lean_dec(v_unused_527_);
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_526_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_array_get_size(v_tail_510_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_nat_dec_lt(v___x_516_, v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; 
lean_dec_ref(v_f_505_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_518_);
v___x_521_ = v___x_514_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_a_512_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
lean_del_object(v___x_514_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_517_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_505_, v_tail_510_, v___x_523_, v___x_524_, v___x_518_, v_a_512_);
return v___x_525_;
}
}
}
else
{
lean_dec_ref(v_f_505_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_528_, lean_object* v_t_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_528_, v_t_529_, v___y_530_);
lean_dec_ref(v_t_529_);
return v_res_532_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_534_, lean_object* v_x_535_, size_t v_x_536_, size_t v_x_537_, lean_object* v___y_538_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
lean_object* v_cs_540_; lean_object* v___x_541_; size_t v___x_542_; lean_object* v_j_543_; lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v_cs_540_ = lean_ctor_get(v_x_535_, 0);
v___x_541_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_542_ = lean_usize_shift_right(v_x_536_, v_x_537_);
v_j_543_ = lean_usize_to_nat(v___x_542_);
v___x_544_ = lean_array_get_borrowed(v___x_541_, v_cs_540_, v_j_543_);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_shift_left(v___x_545_, v_x_537_);
v___x_547_ = lean_usize_sub(v___x_546_, v___x_545_);
v___x_548_ = lean_usize_land(v_x_536_, v___x_547_);
v___x_549_ = ((size_t)5ULL);
v___x_550_ = lean_usize_sub(v_x_537_, v___x_549_);
lean_inc_ref(v_f_534_);
v___x_551_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_534_, v___x_544_, v___x_548_, v___x_550_, v___y_538_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_567_; 
v_a_552_ = lean_ctor_get(v___x_551_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_568_);
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_567_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_567_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_add(v_j_543_, v___x_556_);
lean_dec(v_j_543_);
v___x_558_ = lean_array_get_size(v_cs_540_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_nat_dec_lt(v___x_557_, v___x_558_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; 
lean_dec(v___x_557_);
lean_dec_ref(v_f_534_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_559_);
v___x_562_ = v___x_554_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_552_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
lean_del_object(v___x_554_);
v___x_564_ = lean_usize_of_nat(v___x_557_);
lean_dec(v___x_557_);
v___x_565_ = lean_usize_of_nat(v___x_558_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_534_, v_cs_540_, v___x_564_, v___x_565_, v___x_559_, v_a_552_);
return v___x_566_;
}
}
}
else
{
lean_dec(v_j_543_);
lean_dec_ref(v_f_534_);
return v___x_551_;
}
}
else
{
lean_object* v_vs_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_vs_569_ = lean_ctor_get(v_x_535_, 0);
v___x_570_ = lean_usize_to_nat(v_x_536_);
v___x_571_ = lean_array_get_size(v_vs_569_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v___x_570_);
lean_dec_ref(v_f_534_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___y_538_);
return v___x_574_;
}
else
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_usize_of_nat(v___x_570_);
lean_dec(v___x_570_);
v___x_576_ = lean_usize_of_nat(v___x_571_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_534_, v_vs_569_, v___x_575_, v___x_576_, v___x_572_, v___y_538_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
size_t v_x_12359__boxed_584_; size_t v_x_12360__boxed_585_; lean_object* v_res_586_; 
v_x_12359__boxed_584_ = lean_unbox_usize(v_x_580_);
lean_dec(v_x_580_);
v_x_12360__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_res_586_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_578_, v_x_579_, v_x_12359__boxed_584_, v_x_12360__boxed_585_, v___y_582_);
lean_dec_ref(v_x_579_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_587_, lean_object* v_t_588_, lean_object* v_start_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_nat_dec_eq(v_start_589_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v_root_594_; lean_object* v_tail_595_; size_t v_shift_596_; lean_object* v_tailOff_597_; uint8_t v___x_598_; 
v_root_594_ = lean_ctor_get(v_t_588_, 0);
v_tail_595_ = lean_ctor_get(v_t_588_, 1);
v_shift_596_ = lean_ctor_get_usize(v_t_588_, 4);
v_tailOff_597_ = lean_ctor_get(v_t_588_, 3);
v___x_598_ = lean_nat_dec_le(v_tailOff_597_, v_start_589_);
if (v___x_598_ == 0)
{
size_t v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_usize_of_nat(v_start_589_);
lean_inc_ref(v_f_587_);
v___x_600_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_587_, v_root_594_, v___x_599_, v_shift_596_, v___y_590_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_614_; 
v_a_601_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_615_);
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_614_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_array_get_size(v_tail_595_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_nat_dec_lt(v___x_592_, v___x_605_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_f_587_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_606_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_601_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_603_);
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_605_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_587_, v_tail_595_, v___x_611_, v___x_612_, v___x_606_, v_a_601_);
return v___x_613_;
}
}
}
else
{
lean_dec_ref(v_f_587_);
return v___x_600_;
}
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_616_ = lean_nat_sub(v_start_589_, v_tailOff_597_);
v___x_617_ = lean_array_get_size(v_tail_595_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_nat_dec_lt(v___x_616_, v___x_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v___x_616_);
lean_dec_ref(v_f_587_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___y_590_);
return v___x_620_;
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_usize_of_nat(v___x_616_);
lean_dec(v___x_616_);
v___x_622_ = lean_usize_of_nat(v___x_617_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_587_, v_tail_595_, v___x_621_, v___x_622_, v___x_618_, v___y_590_);
return v___x_623_;
}
}
}
else
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_587_, v_t_588_, v___y_590_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_625_, lean_object* v_t_626_, lean_object* v_start_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_625_, v_t_626_, v_start_627_, v___y_628_);
lean_dec(v_start_627_);
lean_dec_ref(v_t_626_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_631_, lean_object* v_f_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_unreported_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_unreported_635_ = lean_ctor_get(v_log_631_, 1);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_632_, v_unreported_635_, v___x_636_, v___y_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_638_, lean_object* v_f_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_638_, v_f_639_, v___y_640_);
lean_dec_ref(v_log_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_645_, lean_object* v_pkgName_646_, lean_object* v_pkgDir_647_, lean_object* v_lakeOpts_648_, lean_object* v_leanOpts_649_, lean_object* v_configFile_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_IO_FS_readFile(v_configFile_650_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = 1;
v___x_656_ = lean_string_utf8_byte_size(v_a_654_);
lean_inc_ref(v_configFile_650_);
v___x_657_ = l_Lean_Parser_mkInputContext___redArg(v_a_654_, v_configFile_650_, v___x_655_, v___x_656_);
lean_inc_ref(v___x_657_);
v___x_658_ = l_Lean_Parser_parseHeader(v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_757_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_757_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_757_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_757_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_snd_663_; lean_object* v_fst_664_; lean_object* v_fst_665_; lean_object* v_snd_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_756_; 
v_snd_663_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_snd_663_);
v_fst_664_ = lean_ctor_get(v_a_659_, 0);
lean_inc(v_fst_664_);
lean_dec(v_a_659_);
v_fst_665_ = lean_ctor_get(v_snd_663_, 0);
v_snd_666_ = lean_ctor_get(v_snd_663_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_snd_663_);
if (v_isSharedCheck_756_ == 0)
{
v___x_668_ = v_snd_663_;
v_isShared_669_ = v_isSharedCheck_756_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_snd_666_);
lean_inc(v_fst_665_);
lean_dec(v_snd_663_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_756_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; 
lean_inc_ref(v___x_657_);
lean_inc_ref(v_leanOpts_649_);
v___x_670_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_664_, v_leanOpts_649_, v___x_657_, v_snd_666_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_746_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_746_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_746_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_746_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_745_; 
v_fst_675_ = lean_ctor_get(v_a_671_, 0);
v_snd_676_ = lean_ctor_get(v_a_671_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_a_671_);
if (v_isSharedCheck_745_ == 0)
{
v___x_678_ = v_a_671_;
v_isShared_679_ = v_isSharedCheck_745_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_inc(v_fst_675_);
lean_dec(v_a_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_745_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v_asyncMode_681_; lean_object* v___x_682_; lean_object* v_asyncMode_683_; lean_object* v___x_684_; lean_object* v_asyncMode_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_680_ = l_Lake_nameExt;
v_asyncMode_681_ = lean_ctor_get(v___x_680_, 2);
v___x_682_ = l_Lake_dirExt;
v_asyncMode_683_ = lean_ctor_get(v___x_682_, 2);
v___x_684_ = l_Lake_optsExt;
v_asyncMode_685_ = lean_ctor_get(v___x_684_, 2);
v___x_686_ = ((lean_object*)(l_Lake_configModuleName));
v___x_687_ = l_Lean_Environment_setMainModule(v_fst_675_, v___x_686_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v_pkgName_646_);
lean_ctor_set(v___x_678_, 0, v_pkgIdx_645_);
v___x_689_ = v___x_678_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_pkgIdx_645_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_pkgName_646_);
v___x_689_ = v_reuseFailAlloc_744_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_EnvExtension_setState___redArg(v___x_680_, v___x_687_, v___x_689_, v_asyncMode_681_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
lean_ctor_set(v___x_673_, 0, v_pkgDir_647_);
v___x_692_ = v___x_673_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_pkgDir_647_);
v___x_692_ = v_reuseFailAlloc_743_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_EnvExtension_setState___redArg(v___x_682_, v___x_690_, v___x_692_, v_asyncMode_683_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 0, v_lakeOpts_648_);
v___x_695_ = v___x_661_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_lakeOpts_648_);
v___x_695_ = v_reuseFailAlloc_742_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_EnvExtension_setState___redArg(v___x_684_, v___x_693_, v___x_695_, v_asyncMode_685_);
v___x_697_ = l_Lean_Elab_Command_mkState(v___x_696_, v_snd_676_, v_leanOpts_649_);
v___x_698_ = l_Lean_Elab_IO_processCommands(v___x_657_, v_fst_665_, v___x_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v_commandState_700_; lean_object* v_env_701_; lean_object* v_messages_702_; lean_object* v___f_703_; lean_object* v___x_704_; 
lean_del_object(v___x_668_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v_commandState_700_ = lean_ctor_get(v_a_699_, 0);
lean_inc_ref(v_commandState_700_);
lean_dec(v_a_699_);
v_env_701_ = lean_ctor_get(v_commandState_700_, 0);
lean_inc_ref(v_env_701_);
v_messages_702_ = lean_ctor_get(v_commandState_700_, 1);
lean_inc_ref(v_messages_702_);
lean_dec_ref(v_commandState_700_);
v___f_703_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_704_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_702_, v___f_703_, v_a_651_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_722_; 
v_a_705_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_704_, 0);
lean_dec(v_unused_723_);
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_722_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_722_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_MessageLog_hasErrors(v_messages_702_);
lean_dec_ref(v_messages_702_);
if (v___x_709_ == 0)
{
lean_object* v___x_711_; 
lean_dec_ref(v_configFile_650_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_env_701_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_env_701_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_a_705_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec_ref(v_env_701_);
v___x_713_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1));
v___x_714_ = lean_string_append(v_configFile_650_, v___x_713_);
v___x_715_ = 3;
v___x_716_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_715_);
v___x_717_ = lean_array_get_size(v_a_705_);
v___x_718_ = lean_array_push(v_a_705_, v___x_716_);
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 1);
lean_ctor_set(v___x_707_, 1, v___x_718_);
lean_ctor_set(v___x_707_, 0, v___x_717_);
v___x_720_ = v___x_707_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_messages_702_);
lean_dec_ref(v_env_701_);
lean_dec_ref(v_configFile_650_);
v_a_724_ = lean_ctor_get(v___x_704_, 0);
v_a_725_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_704_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_inc(v_a_724_);
lean_dec(v___x_704_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_724_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec_ref(v_configFile_650_);
v_a_733_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_698_, 1);
v___x_734_ = lean_io_error_to_string(v_a_733_);
v___x_735_ = 3;
v___x_736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*1, v___x_735_);
v___x_737_ = lean_array_get_size(v_a_651_);
v___x_738_ = lean_array_push(v_a_651_, v___x_736_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 1);
lean_ctor_set(v___x_668_, 1, v___x_738_);
lean_ctor_set(v___x_668_, 0, v___x_737_);
v___x_740_ = v___x_668_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
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
lean_object* v_a_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_fst_665_);
lean_del_object(v___x_661_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v_configFile_650_);
lean_dec_ref(v_leanOpts_649_);
lean_dec(v_lakeOpts_648_);
lean_dec_ref(v_pkgDir_647_);
lean_dec(v_pkgName_646_);
lean_dec(v_pkgIdx_645_);
v_a_747_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_670_, 1);
v___x_748_ = lean_io_error_to_string(v_a_747_);
v___x_749_ = 3;
v___x_750_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*1, v___x_749_);
v___x_751_ = lean_array_get_size(v_a_651_);
v___x_752_ = lean_array_push(v_a_651_, v___x_750_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 1);
lean_ctor_set(v___x_668_, 1, v___x_752_);
lean_ctor_set(v___x_668_, 0, v___x_751_);
v___x_754_ = v___x_668_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_657_);
lean_dec_ref(v_configFile_650_);
lean_dec_ref(v_leanOpts_649_);
lean_dec(v_lakeOpts_648_);
lean_dec_ref(v_pkgDir_647_);
lean_dec(v_pkgName_646_);
lean_dec(v_pkgIdx_645_);
v_a_758_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_658_, 1);
v___x_759_ = lean_io_error_to_string(v_a_758_);
v___x_760_ = 3;
v___x_761_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*1, v___x_760_);
v___x_762_ = lean_array_get_size(v_a_651_);
v___x_763_ = lean_array_push(v_a_651_, v___x_761_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
return v___x_764_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_configFile_650_);
lean_dec_ref(v_leanOpts_649_);
lean_dec(v_lakeOpts_648_);
lean_dec_ref(v_pkgDir_647_);
lean_dec(v_pkgName_646_);
lean_dec(v_pkgIdx_645_);
v_a_765_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_653_, 1);
v___x_766_ = lean_io_error_to_string(v_a_765_);
v___x_767_ = 3;
v___x_768_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*1, v___x_767_);
v___x_769_ = lean_array_get_size(v_a_651_);
v___x_770_ = lean_array_push(v_a_651_, v___x_768_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_772_, lean_object* v_pkgName_773_, lean_object* v_pkgDir_774_, lean_object* v_lakeOpts_775_, lean_object* v_leanOpts_776_, lean_object* v_configFile_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_772_, v_pkgName_773_, v_pkgDir_774_, v_lakeOpts_775_, v_leanOpts_776_, v_configFile_777_, v_a_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_783_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = lake_environment_add(v_env_783_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_784_);
return v_res_785_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_792_ = l_Lean_NameSet_empty;
v___x_793_ = l_Lean_NameSet_insert(v___x_792_, v___x_791_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_799_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_800_ = l_Lean_NameSet_insert(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_806_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_807_ = l_Lean_NameSet_insert(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_813_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_814_ = l_Lean_NameSet_insert(v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_820_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_821_ = l_Lean_NameSet_insert(v___x_820_, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_827_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_828_ = l_Lean_NameSet_insert(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_834_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_835_ = l_Lean_NameSet_insert(v___x_834_, v___x_833_);
return v___x_835_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_841_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_842_ = l_Lean_NameSet_insert(v___x_841_, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_848_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_849_ = l_Lean_NameSet_insert(v___x_848_, v___x_847_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_855_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_856_ = l_Lean_NameSet_insert(v___x_855_, v___x_854_);
return v___x_856_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_862_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_863_ = l_Lean_NameSet_insert(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_869_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_870_ = l_Lean_NameSet_insert(v___x_869_, v___x_868_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_876_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_877_ = l_Lean_NameSet_insert(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_883_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_884_ = l_Lean_NameSet_insert(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_890_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_891_ = l_Lean_NameSet_insert(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_898_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_899_ = l_Lean_NameSet_insert(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52));
v___x_907_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_908_ = l_Lean_NameSet_insert(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53);
return v___x_909_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = l_Lean_instInhabitedEnvExtensionState;
v___x_911_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_912_, lean_object* v_val_913_, lean_object* v_as_914_, size_t v_i_915_, size_t v_stop_916_, lean_object* v_b_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_usize_dec_eq(v_i_915_, v_stop_916_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; size_t v___x_925_; size_t v___x_926_; 
v___x_919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_920_ = lean_array_uget_borrowed(v_as_914_, v_i_915_);
v___x_921_ = lean_array_get_borrowed(v___x_919_, v_val_912_, v_val_913_);
v___x_922_ = lean_box(0);
v___x_923_ = lean_box(0);
lean_inc(v___x_920_);
lean_inc(v___x_921_);
v___x_924_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_921_, v_b_917_, v___x_920_, v___x_922_, v___x_923_);
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_915_, v___x_925_);
v_i_915_ = v___x_926_;
v_b_917_ = v___x_924_;
goto _start;
}
else
{
return v_b_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_928_, lean_object* v_val_929_, lean_object* v_as_930_, lean_object* v_i_931_, lean_object* v_stop_932_, lean_object* v_b_933_){
_start:
{
size_t v_i_boxed_934_; size_t v_stop_boxed_935_; lean_object* v_res_936_; 
v_i_boxed_934_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_stop_boxed_935_ = lean_unbox_usize(v_stop_932_);
lean_dec(v_stop_932_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_928_, v_val_929_, v_as_930_, v_i_boxed_934_, v_stop_boxed_935_, v_b_933_);
lean_dec_ref(v_as_930_);
lean_dec(v_val_929_);
lean_dec_ref(v_val_928_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_937_, lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_box(0);
return v___x_939_;
}
else
{
lean_object* v_key_940_; lean_object* v_value_941_; lean_object* v_tail_942_; uint8_t v___x_943_; 
v_key_940_ = lean_ctor_get(v_x_938_, 0);
v_value_941_ = lean_ctor_get(v_x_938_, 1);
v_tail_942_ = lean_ctor_get(v_x_938_, 2);
v___x_943_ = lean_name_eq(v_key_940_, v_a_937_);
if (v___x_943_ == 0)
{
v_x_938_ = v_tail_942_;
goto _start;
}
else
{
lean_object* v___x_945_; 
lean_inc(v_value_941_);
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_value_941_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_946_, lean_object* v_x_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_946_, v_x_947_);
lean_dec(v_x_947_);
lean_dec(v_a_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_buckets_951_; lean_object* v___x_952_; uint64_t v___y_954_; 
v_buckets_951_ = lean_ctor_get(v_m_949_, 1);
v___x_952_ = lean_array_get_size(v_buckets_951_);
if (lean_obj_tag(v_a_950_) == 0)
{
uint64_t v___x_968_; 
v___x_968_ = 1723ULL;
v___y_954_ = v___x_968_;
goto v___jp_953_;
}
else
{
uint64_t v_hash_969_; 
v_hash_969_ = lean_ctor_get_uint64(v_a_950_, sizeof(void*)*2);
v___y_954_ = v_hash_969_;
goto v___jp_953_;
}
v___jp_953_:
{
uint64_t v___x_955_; uint64_t v___x_956_; uint64_t v_fold_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_955_ = 32ULL;
v___x_956_ = lean_uint64_shift_right(v___y_954_, v___x_955_);
v_fold_957_ = lean_uint64_xor(v___y_954_, v___x_956_);
v___x_958_ = 16ULL;
v___x_959_ = lean_uint64_shift_right(v_fold_957_, v___x_958_);
v___x_960_ = lean_uint64_xor(v_fold_957_, v___x_959_);
v___x_961_ = lean_uint64_to_usize(v___x_960_);
v___x_962_ = lean_usize_of_nat(v___x_952_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_sub(v___x_962_, v___x_963_);
v___x_965_ = lean_usize_land(v___x_961_, v___x_964_);
v___x_966_ = lean_array_uget_borrowed(v_buckets_951_, v___x_965_);
v___x_967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_950_, v___x_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_m_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_973_, lean_object* v_val_974_, lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_, lean_object* v_b_978_){
_start:
{
lean_object* v___y_980_; uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_985_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
v_fst_986_ = lean_ctor_get(v___x_985_, 0);
v_snd_987_ = lean_ctor_get(v___x_985_, 1);
v___x_988_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_989_ = l_Lean_NameSet_contains(v___x_988_, v_fst_986_);
if (v___x_989_ == 0)
{
v___y_980_ = v_b_978_;
goto v___jp_979_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_973_, v_fst_986_);
if (lean_obj_tag(v___x_990_) == 0)
{
v___y_980_ = v_b_978_;
goto v___jp_979_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_array_get_size(v_snd_987_);
v___x_994_ = lean_nat_dec_lt(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_val_991_);
v___y_980_ = v_b_978_;
goto v___jp_979_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_le(v___x_993_, v___x_993_);
if (v___x_995_ == 0)
{
if (v___x_994_ == 0)
{
lean_dec(v_val_991_);
v___y_980_ = v_b_978_;
goto v___jp_979_;
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_993_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_974_, v_val_991_, v_snd_987_, v___x_996_, v___x_997_, v_b_978_);
lean_dec(v_val_991_);
v___y_980_ = v___x_998_;
goto v___jp_979_;
}
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = lean_usize_of_nat(v___x_993_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_974_, v_val_991_, v_snd_987_, v___x_999_, v___x_1000_, v_b_978_);
lean_dec(v_val_991_);
v___y_980_ = v___x_1001_;
goto v___jp_979_;
}
}
}
}
}
else
{
return v_b_978_;
}
v___jp_979_:
{
size_t v___x_981_; size_t v___x_982_; 
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_976_, v___x_981_);
v_i_976_ = v___x_982_;
v_b_978_ = v___y_980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1002_, lean_object* v_val_1003_, lean_object* v_as_1004_, lean_object* v_i_1005_, lean_object* v_stop_1006_, lean_object* v_b_1007_){
_start:
{
size_t v_i_boxed_1008_; size_t v_stop_boxed_1009_; lean_object* v_res_1010_; 
v_i_boxed_1008_ = lean_unbox_usize(v_i_1005_);
lean_dec(v_i_1005_);
v_stop_boxed_1009_ = lean_unbox_usize(v_stop_1006_);
lean_dec(v_stop_1006_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1002_, v_val_1003_, v_as_1004_, v_i_boxed_1008_, v_stop_boxed_1009_, v_b_1007_);
lean_dec_ref(v_as_1004_);
lean_dec_ref(v_val_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1011_, size_t v_i_1012_, size_t v_stop_1013_, lean_object* v_b_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_usize_dec_eq(v_i_1012_, v_stop_1013_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; 
v___x_1016_ = lean_array_uget_borrowed(v_as_1011_, v_i_1012_);
lean_inc(v___x_1016_);
v___x_1017_ = lake_environment_add(v_b_1014_, v___x_1016_);
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1012_, v___x_1018_);
v_i_1012_ = v___x_1019_;
v_b_1014_ = v___x_1017_;
goto _start;
}
else
{
return v_b_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1021_, lean_object* v_i_1022_, lean_object* v_stop_1023_, lean_object* v_b_1024_){
_start:
{
size_t v_i_boxed_1025_; size_t v_stop_boxed_1026_; lean_object* v_res_1027_; 
v_i_boxed_1025_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_stop_boxed_1026_ = lean_unbox_usize(v_stop_1023_);
lean_dec(v_stop_1023_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1021_, v_i_boxed_1025_, v_stop_boxed_1026_, v_b_1024_);
lean_dec_ref(v_as_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1028_, lean_object* v_leanOpts_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_readModuleData(v_olean_1028_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v_fst_1033_; lean_object* v_imports_1034_; lean_object* v_constants_1035_; lean_object* v_entries_1036_; uint32_t v___x_1037_; lean_object* v___x_1038_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_fst_1033_ = lean_ctor_get(v_a_1032_, 0);
lean_inc(v_fst_1033_);
lean_dec(v_a_1032_);
v_imports_1034_ = lean_ctor_get(v_fst_1033_, 0);
lean_inc_ref(v_imports_1034_);
v_constants_1035_ = lean_ctor_get(v_fst_1033_, 2);
lean_inc_ref(v_constants_1035_);
v_entries_1036_ = lean_ctor_get(v_fst_1033_, 4);
lean_inc_ref(v_entries_1036_);
lean_dec(v_fst_1033_);
v___x_1037_ = 1024;
v___x_1038_ = l_Lake_importModulesUsingCache(v_imports_1034_, v_leanOpts_1029_, v___x_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___y_1042_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_array_get_size(v_constants_1035_);
v___x_1081_ = lean_nat_dec_lt(v___x_1040_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_dec_ref(v_constants_1035_);
v___y_1042_ = v_a_1039_;
goto v___jp_1041_;
}
else
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_nat_dec_le(v___x_1080_, v___x_1080_);
if (v___x_1082_ == 0)
{
if (v___x_1081_ == 0)
{
lean_dec_ref(v_constants_1035_);
v___y_1042_ = v_a_1039_;
goto v___jp_1041_;
}
else
{
size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = lean_usize_of_nat(v___x_1080_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1035_, v___x_1083_, v___x_1084_, v_a_1039_);
lean_dec_ref(v_constants_1035_);
v___y_1042_ = v___x_1085_;
goto v___jp_1041_;
}
}
else
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = lean_usize_of_nat(v___x_1080_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1035_, v___x_1086_, v___x_1087_, v_a_1039_);
lean_dec_ref(v_constants_1035_);
v___y_1042_ = v___x_1088_;
goto v___jp_1041_;
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = l_Lean_persistentEnvExtensionsRef;
v___x_1044_ = lean_st_ref_get(v___x_1043_);
v___x_1045_ = l_Lean_mkExtNameMap(v___x_1040_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1071_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1071_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1071_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_entries_1036_);
v___x_1051_ = lean_nat_dec_lt(v___x_1040_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1053_; 
lean_dec(v_a_1046_);
lean_dec(v___x_1044_);
lean_dec_ref(v_entries_1036_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___y_1042_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___y_1042_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_nat_dec_le(v___x_1050_, v___x_1050_);
if (v___x_1055_ == 0)
{
if (v___x_1051_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v_a_1046_);
lean_dec(v___x_1044_);
lean_dec_ref(v_entries_1036_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___y_1042_);
v___x_1057_ = v___x_1048_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___y_1042_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
else
{
size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = lean_usize_of_nat(v___x_1050_);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1046_, v___x_1044_, v_entries_1036_, v___x_1059_, v___x_1060_, v___y_1042_);
lean_dec_ref(v_entries_1036_);
lean_dec(v___x_1044_);
lean_dec(v_a_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1061_);
v___x_1063_ = v___x_1048_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1050_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1046_, v___x_1044_, v_entries_1036_, v___x_1065_, v___x_1066_, v___y_1042_);
lean_dec_ref(v_entries_1036_);
lean_dec(v___x_1044_);
lean_dec(v_a_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1067_);
v___x_1069_ = v___x_1048_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v___x_1044_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_entries_1036_);
v_a_1072_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1045_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1045_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
else
{
lean_dec_ref(v_entries_1036_);
lean_dec_ref(v_constants_1035_);
return v___x_1038_;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_leanOpts_1029_);
v_a_1089_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1031_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1031_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1097_, lean_object* v_leanOpts_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1097_, v_leanOpts_1098_);
lean_dec_ref(v_olean_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1101_, lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1102_, v_a_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1105_, lean_object* v_m_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1105_, v_m_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_m_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1109_, lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_a_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1113_, v_a_1114_, v_x_1115_);
lean_dec(v_x_1115_);
lean_dec(v_a_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_box(1);
v___x_1119_ = lean_panic_fn_borrowed(v___x_1118_, v_msg_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1123_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1124_ = lean_unsigned_to_nat(35u);
v___x_1125_ = lean_unsigned_to_nat(182u);
v___x_1126_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1127_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1128_ = l_mkPanicMessageWithDecl(v___x_1127_, v___x_1126_, v___x_1125_, v___x_1124_, v___x_1123_);
return v___x_1128_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1129_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1130_ = lean_unsigned_to_nat(21u);
v___x_1131_ = lean_unsigned_to_nat(183u);
v___x_1132_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1134_ = l_mkPanicMessageWithDecl(v___x_1133_, v___x_1132_, v___x_1131_, v___x_1130_, v___x_1129_);
return v___x_1134_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1137_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1138_ = lean_unsigned_to_nat(35u);
v___x_1139_ = lean_unsigned_to_nat(276u);
v___x_1140_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1141_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1142_ = l_mkPanicMessageWithDecl(v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_);
return v___x_1142_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1143_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1144_ = lean_unsigned_to_nat(21u);
v___x_1145_ = lean_unsigned_to_nat(277u);
v___x_1146_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1148_ = l_mkPanicMessageWithDecl(v___x_1147_, v___x_1146_, v___x_1145_, v___x_1144_, v___x_1143_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1149_, lean_object* v_v_1150_, lean_object* v_t_1151_){
_start:
{
if (lean_obj_tag(v_t_1151_) == 0)
{
lean_object* v_size_1152_; lean_object* v_k_1153_; lean_object* v_v_1154_; lean_object* v_l_1155_; lean_object* v_r_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1512_; 
v_size_1152_ = lean_ctor_get(v_t_1151_, 0);
v_k_1153_ = lean_ctor_get(v_t_1151_, 1);
v_v_1154_ = lean_ctor_get(v_t_1151_, 2);
v_l_1155_ = lean_ctor_get(v_t_1151_, 3);
v_r_1156_ = lean_ctor_get(v_t_1151_, 4);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_t_1151_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1158_ = v_t_1151_;
v_isShared_1159_ = v_isSharedCheck_1512_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_r_1156_);
lean_inc(v_l_1155_);
lean_inc(v_v_1154_);
lean_inc(v_k_1153_);
lean_inc(v_size_1152_);
lean_dec(v_t_1151_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1512_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_string_compare(v_k_1149_, v_k_1153_);
switch(v___x_1160_)
{
case 0:
{
lean_object* v___x_1161_; 
lean_dec(v_size_1152_);
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1149_, v_v_1150_, v_l_1155_);
if (lean_obj_tag(v_r_1156_) == 0)
{
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_size_1162_; lean_object* v_size_1163_; lean_object* v_k_1164_; lean_object* v_v_1165_; lean_object* v_l_1166_; lean_object* v_r_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_size_1162_ = lean_ctor_get(v_r_1156_, 0);
v_size_1163_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_size_1163_);
v_k_1164_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_k_1164_);
v_v_1165_ = lean_ctor_get(v___x_1161_, 2);
lean_inc(v_v_1165_);
v_l_1166_ = lean_ctor_get(v___x_1161_, 3);
lean_inc(v_l_1166_);
v_r_1167_ = lean_ctor_get(v___x_1161_, 4);
lean_inc(v_r_1167_);
v___x_1168_ = lean_unsigned_to_nat(3u);
v___x_1169_ = lean_nat_mul(v___x_1168_, v_size_1162_);
v___x_1170_ = lean_nat_dec_lt(v___x_1169_, v_size_1163_);
lean_dec(v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_dec(v_r_1167_);
lean_dec(v_l_1166_);
lean_dec(v_v_1165_);
lean_dec(v_k_1164_);
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_nat_add(v___x_1171_, v_size_1163_);
lean_dec(v_size_1163_);
v___x_1173_ = lean_nat_add(v___x_1172_, v_size_1162_);
lean_dec(v___x_1172_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 3, v___x_1161_);
lean_ctor_set(v___x_1158_, 0, v___x_1173_);
v___x_1175_ = v___x_1158_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_r_1156_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1248_; 
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; lean_object* v_unused_1250_; lean_object* v_unused_1251_; lean_object* v_unused_1252_; lean_object* v_unused_1253_; 
v_unused_1249_ = lean_ctor_get(v___x_1161_, 4);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v___x_1161_, 3);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v___x_1161_, 2);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v___x_1161_, 1);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v___x_1161_, 0);
lean_dec(v_unused_1253_);
v___x_1178_ = v___x_1161_;
v_isShared_1179_ = v_isSharedCheck_1248_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v___x_1161_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1248_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
if (lean_obj_tag(v_l_1166_) == 0)
{
if (lean_obj_tag(v_r_1167_) == 0)
{
lean_object* v_size_1180_; lean_object* v_size_1181_; lean_object* v_k_1182_; lean_object* v_v_1183_; lean_object* v_l_1184_; lean_object* v_r_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_size_1180_ = lean_ctor_get(v_l_1166_, 0);
v_size_1181_ = lean_ctor_get(v_r_1167_, 0);
v_k_1182_ = lean_ctor_get(v_r_1167_, 1);
v_v_1183_ = lean_ctor_get(v_r_1167_, 2);
v_l_1184_ = lean_ctor_get(v_r_1167_, 3);
v_r_1185_ = lean_ctor_get(v_r_1167_, 4);
v___x_1186_ = lean_unsigned_to_nat(2u);
v___x_1187_ = lean_nat_mul(v___x_1186_, v_size_1180_);
v___x_1188_ = lean_nat_dec_lt(v_size_1181_, v___x_1187_);
lean_dec(v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1218_; 
lean_inc(v_r_1185_);
lean_inc(v_l_1184_);
lean_inc(v_v_1183_);
lean_inc(v_k_1182_);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_r_1167_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1219_ = lean_ctor_get(v_r_1167_, 4);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_r_1167_, 3);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_r_1167_, 2);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_r_1167_, 1);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_r_1167_, 0);
lean_dec(v_unused_1223_);
v___x_1190_ = v_r_1167_;
v_isShared_1191_ = v_isSharedCheck_1218_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_r_1167_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1218_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___x_1206_; lean_object* v___y_1208_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_add(v___x_1192_, v_size_1163_);
lean_dec(v_size_1163_);
v___x_1194_ = lean_nat_add(v___x_1193_, v_size_1162_);
lean_dec(v___x_1193_);
v___x_1206_ = lean_nat_add(v___x_1192_, v_size_1180_);
if (lean_obj_tag(v_l_1184_) == 0)
{
lean_object* v_size_1216_; 
v_size_1216_ = lean_ctor_get(v_l_1184_, 0);
lean_inc(v_size_1216_);
v___y_1208_ = v_size_1216_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___y_1208_ = v___x_1217_;
goto v___jp_1207_;
}
v___jp_1195_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_nat_add(v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec(v___y_1197_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 4, v_r_1156_);
lean_ctor_set(v___x_1190_, 3, v_r_1185_);
lean_ctor_set(v___x_1190_, 2, v_v_1154_);
lean_ctor_set(v___x_1190_, 1, v_k_1153_);
lean_ctor_set(v___x_1190_, 0, v___x_1199_);
v___x_1201_ = v___x_1190_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_r_1185_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_r_1156_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v___x_1201_);
lean_ctor_set(v___x_1178_, 3, v___y_1196_);
lean_ctor_set(v___x_1178_, 2, v_v_1183_);
lean_ctor_set(v___x_1178_, 1, v_k_1182_);
lean_ctor_set(v___x_1178_, 0, v___x_1194_);
v___x_1203_ = v___x_1178_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1182_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1183_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___y_1196_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_nat_add(v___x_1206_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec(v___x_1206_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_l_1184_);
lean_ctor_set(v___x_1158_, 3, v_l_1166_);
lean_ctor_set(v___x_1158_, 2, v_v_1165_);
lean_ctor_set(v___x_1158_, 1, v_k_1164_);
lean_ctor_set(v___x_1158_, 0, v___x_1209_);
v___x_1211_ = v___x_1158_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_1164_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_1165_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_l_1166_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_l_1184_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_nat_add(v___x_1192_, v_size_1162_);
if (lean_obj_tag(v_r_1185_) == 0)
{
lean_object* v_size_1213_; 
v_size_1213_ = lean_ctor_get(v_r_1185_, 0);
lean_inc(v_size_1213_);
v___y_1196_ = v___x_1211_;
v___y_1197_ = v___x_1212_;
v___y_1198_ = v_size_1213_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___y_1196_ = v___x_1211_;
v___y_1197_ = v___x_1212_;
v___y_1198_ = v___x_1214_;
goto v___jp_1195_;
}
}
}
}
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_del_object(v___x_1158_);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_add(v___x_1224_, v_size_1163_);
lean_dec(v_size_1163_);
v___x_1226_ = lean_nat_add(v___x_1225_, v_size_1162_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_nat_add(v___x_1224_, v_size_1162_);
v___x_1228_ = lean_nat_add(v___x_1227_, v_size_1181_);
lean_dec(v___x_1227_);
lean_inc_ref(v_r_1156_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v_r_1156_);
lean_ctor_set(v___x_1178_, 3, v_r_1167_);
lean_ctor_set(v___x_1178_, 2, v_v_1154_);
lean_ctor_set(v___x_1178_, 1, v_k_1153_);
lean_ctor_set(v___x_1178_, 0, v___x_1228_);
v___x_1230_ = v___x_1178_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_r_1167_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_r_1156_);
v___x_1230_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_isSharedCheck_1237_ = !lean_is_exclusive(v_r_1156_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; lean_object* v_unused_1241_; lean_object* v_unused_1242_; 
v_unused_1238_ = lean_ctor_get(v_r_1156_, 4);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_r_1156_, 3);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_r_1156_, 2);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v_r_1156_, 1);
lean_dec(v_unused_1241_);
v_unused_1242_ = lean_ctor_get(v_r_1156_, 0);
lean_dec(v_unused_1242_);
v___x_1232_ = v_r_1156_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v_r_1156_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 4, v___x_1230_);
lean_ctor_set(v___x_1232_, 3, v_l_1166_);
lean_ctor_set(v___x_1232_, 2, v_v_1165_);
lean_ctor_set(v___x_1232_, 1, v_k_1164_);
lean_ctor_set(v___x_1232_, 0, v___x_1226_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_k_1164_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_v_1165_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_l_1166_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v___x_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref_known(v_l_1166_, 5);
lean_del_object(v___x_1178_);
lean_dec(v_v_1165_);
lean_dec(v_k_1164_);
lean_dec(v_size_1163_);
lean_dec_ref_known(v_r_1156_, 5);
lean_del_object(v___x_1158_);
lean_dec(v_v_1154_);
lean_dec(v_k_1153_);
v___x_1244_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1245_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1244_);
return v___x_1245_;
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_del_object(v___x_1178_);
lean_dec(v_r_1167_);
lean_dec(v_v_1165_);
lean_dec(v_k_1164_);
lean_dec(v_size_1163_);
lean_dec_ref_known(v_r_1156_, 5);
lean_del_object(v___x_1158_);
lean_dec(v_v_1154_);
lean_dec(v_k_1153_);
v___x_1246_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1247_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1246_);
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_size_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v_size_1254_ = lean_ctor_get(v_r_1156_, 0);
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_nat_add(v___x_1255_, v_size_1254_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 3, v___x_1161_);
lean_ctor_set(v___x_1158_, 0, v___x_1256_);
v___x_1258_ = v___x_1158_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_r_1156_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_l_1260_; 
v_l_1260_ = lean_ctor_get(v___x_1161_, 3);
lean_inc(v_l_1260_);
if (lean_obj_tag(v_l_1260_) == 0)
{
lean_object* v_r_1261_; 
v_r_1261_ = lean_ctor_get(v___x_1161_, 4);
lean_inc(v_r_1261_);
if (lean_obj_tag(v_r_1261_) == 0)
{
lean_object* v_size_1262_; lean_object* v_k_1263_; lean_object* v_v_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1278_; 
v_size_1262_ = lean_ctor_get(v___x_1161_, 0);
v_k_1263_ = lean_ctor_get(v___x_1161_, 1);
v_v_1264_ = lean_ctor_get(v___x_1161_, 2);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; lean_object* v_unused_1280_; 
v_unused_1279_ = lean_ctor_get(v___x_1161_, 4);
lean_dec(v_unused_1279_);
v_unused_1280_ = lean_ctor_get(v___x_1161_, 3);
lean_dec(v_unused_1280_);
v___x_1266_ = v___x_1161_;
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_v_1264_);
lean_inc(v_k_1263_);
lean_inc(v_size_1262_);
lean_dec(v___x_1161_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_size_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v_size_1268_ = lean_ctor_get(v_r_1261_, 0);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v___x_1269_, v_size_1262_);
lean_dec(v_size_1262_);
v___x_1271_ = lean_nat_add(v___x_1269_, v_size_1268_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 4, v_r_1156_);
lean_ctor_set(v___x_1266_, 3, v_r_1261_);
lean_ctor_set(v___x_1266_, 2, v_v_1154_);
lean_ctor_set(v___x_1266_, 1, v_k_1153_);
lean_ctor_set(v___x_1266_, 0, v___x_1271_);
v___x_1273_ = v___x_1266_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_r_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_r_1156_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1273_);
lean_ctor_set(v___x_1158_, 3, v_l_1260_);
lean_ctor_set(v___x_1158_, 2, v_v_1264_);
lean_ctor_set(v___x_1158_, 1, v_k_1263_);
lean_ctor_set(v___x_1158_, 0, v___x_1270_);
v___x_1275_ = v___x_1158_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1263_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1264_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_l_1260_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_k_1281_; lean_object* v_v_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1294_; 
v_k_1281_ = lean_ctor_get(v___x_1161_, 1);
v_v_1282_ = lean_ctor_get(v___x_1161_, 2);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1295_ = lean_ctor_get(v___x_1161_, 4);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v___x_1161_, 3);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v___x_1161_, 0);
lean_dec(v_unused_1297_);
v___x_1284_ = v___x_1161_;
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_v_1282_);
lean_inc(v_k_1281_);
lean_dec(v___x_1161_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1286_ = lean_unsigned_to_nat(3u);
v___x_1287_ = lean_unsigned_to_nat(1u);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 3, v_r_1261_);
lean_ctor_set(v___x_1284_, 2, v_v_1154_);
lean_ctor_set(v___x_1284_, 1, v_k_1153_);
lean_ctor_set(v___x_1284_, 0, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_r_1261_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_r_1261_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1289_);
lean_ctor_set(v___x_1158_, 3, v_l_1260_);
lean_ctor_set(v___x_1158_, 2, v_v_1282_);
lean_ctor_set(v___x_1158_, 1, v_k_1281_);
lean_ctor_set(v___x_1158_, 0, v___x_1286_);
v___x_1291_ = v___x_1158_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_k_1281_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_v_1282_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_l_1260_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v_r_1298_; 
v_r_1298_ = lean_ctor_get(v___x_1161_, 4);
lean_inc(v_r_1298_);
if (lean_obj_tag(v_r_1298_) == 0)
{
lean_object* v_k_1299_; lean_object* v_v_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1324_; 
v_k_1299_ = lean_ctor_get(v___x_1161_, 1);
v_v_1300_ = lean_ctor_get(v___x_1161_, 2);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; lean_object* v_unused_1326_; lean_object* v_unused_1327_; 
v_unused_1325_ = lean_ctor_get(v___x_1161_, 4);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v___x_1161_, 3);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v___x_1161_, 0);
lean_dec(v_unused_1327_);
v___x_1302_ = v___x_1161_;
v_isShared_1303_ = v_isSharedCheck_1324_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_v_1300_);
lean_inc(v_k_1299_);
lean_dec(v___x_1161_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1324_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_k_1304_; lean_object* v_v_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1320_; 
v_k_1304_ = lean_ctor_get(v_r_1298_, 1);
v_v_1305_ = lean_ctor_get(v_r_1298_, 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_r_1298_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; 
v_unused_1321_ = lean_ctor_get(v_r_1298_, 4);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_r_1298_, 3);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_r_1298_, 0);
lean_dec(v_unused_1323_);
v___x_1307_ = v_r_1298_;
v_isShared_1308_ = v_isSharedCheck_1320_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_v_1305_);
lean_inc(v_k_1304_);
lean_dec(v_r_1298_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1320_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1309_ = lean_unsigned_to_nat(3u);
v___x_1310_ = lean_unsigned_to_nat(1u);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 4, v_l_1260_);
lean_ctor_set(v___x_1307_, 3, v_l_1260_);
lean_ctor_set(v___x_1307_, 2, v_v_1300_);
lean_ctor_set(v___x_1307_, 1, v_k_1299_);
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1299_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1300_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_l_1260_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_l_1260_);
v___x_1312_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v_l_1260_);
lean_ctor_set(v___x_1302_, 2, v_v_1154_);
lean_ctor_set(v___x_1302_, 1, v_k_1153_);
lean_ctor_set(v___x_1302_, 0, v___x_1310_);
v___x_1314_ = v___x_1302_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_l_1260_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_l_1260_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1314_);
lean_ctor_set(v___x_1158_, 3, v___x_1312_);
lean_ctor_set(v___x_1158_, 2, v_v_1305_);
lean_ctor_set(v___x_1158_, 1, v_k_1304_);
lean_ctor_set(v___x_1158_, 0, v___x_1309_);
v___x_1316_ = v___x_1158_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(2u);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_r_1298_);
lean_ctor_set(v___x_1158_, 3, v___x_1161_);
lean_ctor_set(v___x_1158_, 0, v___x_1328_);
v___x_1330_ = v___x_1158_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_r_1298_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1161_);
lean_ctor_set(v___x_1158_, 3, v___x_1161_);
lean_ctor_set(v___x_1158_, 0, v___x_1332_);
v___x_1334_ = v___x_1158_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___x_1161_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
case 1:
{
lean_object* v___x_1337_; 
lean_dec(v_v_1154_);
lean_dec(v_k_1153_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 2, v_v_1150_);
lean_ctor_set(v___x_1158_, 1, v_k_1149_);
v___x_1337_ = v___x_1158_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_size_1152_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_r_1156_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
default: 
{
lean_object* v___x_1339_; 
lean_dec(v_size_1152_);
v___x_1339_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1149_, v_v_1150_, v_r_1156_);
if (lean_obj_tag(v_l_1155_) == 0)
{
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_size_1340_; lean_object* v_size_1341_; lean_object* v_k_1342_; lean_object* v_v_1343_; lean_object* v_l_1344_; lean_object* v_r_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_size_1340_ = lean_ctor_get(v_l_1155_, 0);
v_size_1341_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_size_1341_);
v_k_1342_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_k_1342_);
v_v_1343_ = lean_ctor_get(v___x_1339_, 2);
lean_inc(v_v_1343_);
v_l_1344_ = lean_ctor_get(v___x_1339_, 3);
lean_inc(v_l_1344_);
v_r_1345_ = lean_ctor_get(v___x_1339_, 4);
lean_inc(v_r_1345_);
v___x_1346_ = lean_unsigned_to_nat(3u);
v___x_1347_ = lean_nat_mul(v___x_1346_, v_size_1340_);
v___x_1348_ = lean_nat_dec_lt(v___x_1347_, v_size_1341_);
lean_dec(v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec(v_r_1345_);
lean_dec(v_l_1344_);
lean_dec(v_v_1343_);
lean_dec(v_k_1342_);
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = lean_nat_add(v___x_1349_, v_size_1340_);
v___x_1351_ = lean_nat_add(v___x_1350_, v_size_1341_);
lean_dec(v_size_1341_);
lean_dec(v___x_1350_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1339_);
lean_ctor_set(v___x_1158_, 0, v___x_1351_);
v___x_1353_ = v___x_1158_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v___x_1339_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1424_; 
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; 
v_unused_1425_ = lean_ctor_get(v___x_1339_, 4);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v___x_1339_, 3);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v___x_1339_, 2);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v___x_1339_, 1);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v___x_1339_, 0);
lean_dec(v_unused_1429_);
v___x_1356_ = v___x_1339_;
v_isShared_1357_ = v_isSharedCheck_1424_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v___x_1339_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1424_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
if (lean_obj_tag(v_l_1344_) == 0)
{
if (lean_obj_tag(v_r_1345_) == 0)
{
lean_object* v_size_1358_; lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v_l_1361_; lean_object* v_r_1362_; lean_object* v_size_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_size_1358_ = lean_ctor_get(v_l_1344_, 0);
v_k_1359_ = lean_ctor_get(v_l_1344_, 1);
v_v_1360_ = lean_ctor_get(v_l_1344_, 2);
v_l_1361_ = lean_ctor_get(v_l_1344_, 3);
v_r_1362_ = lean_ctor_get(v_l_1344_, 4);
v_size_1363_ = lean_ctor_get(v_r_1345_, 0);
v___x_1364_ = lean_unsigned_to_nat(2u);
v___x_1365_ = lean_nat_mul(v___x_1364_, v_size_1363_);
v___x_1366_ = lean_nat_dec_lt(v_size_1358_, v___x_1365_);
lean_dec(v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1395_; 
lean_inc(v_r_1362_);
lean_inc(v_l_1361_);
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_l_1344_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1396_ = lean_ctor_get(v_l_1344_, 4);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_l_1344_, 3);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_l_1344_, 2);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_l_1344_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_l_1344_, 0);
lean_dec(v_unused_1400_);
v___x_1368_ = v_l_1344_;
v_isShared_1369_ = v_isSharedCheck_1395_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v_l_1344_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1395_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1385_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v___x_1370_, v_size_1340_);
v___x_1372_ = lean_nat_add(v___x_1371_, v_size_1341_);
lean_dec(v_size_1341_);
if (lean_obj_tag(v_l_1361_) == 0)
{
lean_object* v_size_1393_; 
v_size_1393_ = lean_ctor_get(v_l_1361_, 0);
lean_inc(v_size_1393_);
v___y_1385_ = v_size_1393_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___y_1385_ = v___x_1394_;
goto v___jp_1384_;
}
v___jp_1373_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_nat_add(v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec(v___y_1375_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_r_1345_);
lean_ctor_set(v___x_1368_, 3, v_r_1362_);
lean_ctor_set(v___x_1368_, 2, v_v_1343_);
lean_ctor_set(v___x_1368_, 1, v_k_1342_);
lean_ctor_set(v___x_1368_, 0, v___x_1377_);
v___x_1379_ = v___x_1368_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1342_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1343_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_r_1362_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_r_1345_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 4, v___x_1379_);
lean_ctor_set(v___x_1356_, 3, v___y_1374_);
lean_ctor_set(v___x_1356_, 2, v_v_1360_);
lean_ctor_set(v___x_1356_, 1, v_k_1359_);
lean_ctor_set(v___x_1356_, 0, v___x_1372_);
v___x_1381_ = v___x_1356_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v___y_1374_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
v___jp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = lean_nat_add(v___x_1371_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec(v___x_1371_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_l_1361_);
lean_ctor_set(v___x_1158_, 0, v___x_1386_);
v___x_1388_ = v___x_1158_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_l_1361_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_nat_add(v___x_1370_, v_size_1363_);
if (lean_obj_tag(v_r_1362_) == 0)
{
lean_object* v_size_1390_; 
v_size_1390_ = lean_ctor_get(v_r_1362_, 0);
lean_inc(v_size_1390_);
v___y_1374_ = v___x_1388_;
v___y_1375_ = v___x_1389_;
v___y_1376_ = v_size_1390_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v___y_1374_ = v___x_1388_;
v___y_1375_ = v___x_1389_;
v___y_1376_ = v___x_1391_;
goto v___jp_1373_;
}
}
}
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_del_object(v___x_1158_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v___x_1401_, v_size_1340_);
v___x_1403_ = lean_nat_add(v___x_1402_, v_size_1341_);
lean_dec(v_size_1341_);
v___x_1404_ = lean_nat_add(v___x_1402_, v_size_1358_);
lean_dec(v___x_1402_);
lean_inc_ref(v_l_1155_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 4, v_l_1344_);
lean_ctor_set(v___x_1356_, 3, v_l_1155_);
lean_ctor_set(v___x_1356_, 2, v_v_1154_);
lean_ctor_set(v___x_1356_, 1, v_k_1153_);
lean_ctor_set(v___x_1356_, 0, v___x_1404_);
v___x_1406_ = v___x_1356_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_l_1344_);
v___x_1406_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_isSharedCheck_1413_ = !lean_is_exclusive(v_l_1155_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; lean_object* v_unused_1415_; lean_object* v_unused_1416_; lean_object* v_unused_1417_; lean_object* v_unused_1418_; 
v_unused_1414_ = lean_ctor_get(v_l_1155_, 4);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_l_1155_, 3);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_l_1155_, 2);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_l_1155_, 1);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_l_1155_, 0);
lean_dec(v_unused_1418_);
v___x_1408_ = v_l_1155_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v_l_1155_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 4, v_r_1345_);
lean_ctor_set(v___x_1408_, 3, v___x_1406_);
lean_ctor_set(v___x_1408_, 2, v_v_1343_);
lean_ctor_set(v___x_1408_, 1, v_k_1342_);
lean_ctor_set(v___x_1408_, 0, v___x_1403_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_k_1342_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_v_1343_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_r_1345_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec_ref_known(v_l_1344_, 5);
lean_del_object(v___x_1356_);
lean_dec(v_v_1343_);
lean_dec(v_k_1342_);
lean_dec(v_size_1341_);
lean_dec_ref_known(v_l_1155_, 5);
lean_del_object(v___x_1158_);
lean_dec(v_v_1154_);
lean_dec(v_k_1153_);
v___x_1420_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1421_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1420_);
return v___x_1421_;
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1356_);
lean_dec(v_r_1345_);
lean_dec(v_v_1343_);
lean_dec(v_k_1342_);
lean_dec(v_size_1341_);
lean_dec_ref_known(v_l_1155_, 5);
lean_del_object(v___x_1158_);
lean_dec(v_v_1154_);
lean_dec(v_k_1153_);
v___x_1422_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1423_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1422_);
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_size_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v_size_1430_ = lean_ctor_get(v_l_1155_, 0);
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_add(v___x_1431_, v_size_1430_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1339_);
lean_ctor_set(v___x_1158_, 0, v___x_1432_);
v___x_1434_ = v___x_1158_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v___x_1339_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_l_1436_; 
v_l_1436_ = lean_ctor_get(v___x_1339_, 3);
lean_inc(v_l_1436_);
if (lean_obj_tag(v_l_1436_) == 0)
{
lean_object* v_r_1437_; 
v_r_1437_ = lean_ctor_get(v___x_1339_, 4);
lean_inc(v_r_1437_);
if (lean_obj_tag(v_r_1437_) == 0)
{
lean_object* v_size_1438_; lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1454_; 
v_size_1438_ = lean_ctor_get(v___x_1339_, 0);
v_k_1439_ = lean_ctor_get(v___x_1339_, 1);
v_v_1440_ = lean_ctor_get(v___x_1339_, 2);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1455_ = lean_ctor_get(v___x_1339_, 4);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v___x_1339_, 3);
lean_dec(v_unused_1456_);
v___x_1442_ = v___x_1339_;
v_isShared_1443_ = v_isSharedCheck_1454_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
lean_inc(v_size_1438_);
lean_dec(v___x_1339_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1454_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_size_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v_size_1444_ = lean_ctor_get(v_l_1436_, 0);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v___x_1445_, v_size_1438_);
lean_dec(v_size_1438_);
v___x_1447_ = lean_nat_add(v___x_1445_, v_size_1444_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v_l_1436_);
lean_ctor_set(v___x_1442_, 3, v_l_1155_);
lean_ctor_set(v___x_1442_, 2, v_v_1154_);
lean_ctor_set(v___x_1442_, 1, v_k_1153_);
lean_ctor_set(v___x_1442_, 0, v___x_1447_);
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_l_1155_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_l_1436_);
v___x_1449_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1451_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_r_1437_);
lean_ctor_set(v___x_1158_, 3, v___x_1449_);
lean_ctor_set(v___x_1158_, 2, v_v_1440_);
lean_ctor_set(v___x_1158_, 1, v_k_1439_);
lean_ctor_set(v___x_1158_, 0, v___x_1446_);
v___x_1451_ = v___x_1158_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_r_1437_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_k_1457_; lean_object* v_v_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1482_; 
v_k_1457_ = lean_ctor_get(v___x_1339_, 1);
v_v_1458_ = lean_ctor_get(v___x_1339_, 2);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1483_ = lean_ctor_get(v___x_1339_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v___x_1339_, 3);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v___x_1339_, 0);
lean_dec(v_unused_1485_);
v___x_1460_ = v___x_1339_;
v_isShared_1461_ = v_isSharedCheck_1482_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_v_1458_);
lean_inc(v_k_1457_);
lean_dec(v___x_1339_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1482_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1478_; 
v_k_1462_ = lean_ctor_get(v_l_1436_, 1);
v_v_1463_ = lean_ctor_get(v_l_1436_, 2);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_l_1436_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1479_ = lean_ctor_get(v_l_1436_, 4);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_l_1436_, 3);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1436_, 0);
lean_dec(v_unused_1481_);
v___x_1465_ = v_l_1436_;
v_isShared_1466_ = v_isSharedCheck_1478_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
lean_dec(v_l_1436_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1478_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = lean_unsigned_to_nat(3u);
v___x_1468_ = lean_unsigned_to_nat(1u);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v_r_1437_);
lean_ctor_set(v___x_1465_, 3, v_r_1437_);
lean_ctor_set(v___x_1465_, 2, v_v_1154_);
lean_ctor_set(v___x_1465_, 1, v_k_1153_);
lean_ctor_set(v___x_1465_, 0, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_r_1437_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1437_);
v___x_1470_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 3, v_r_1437_);
lean_ctor_set(v___x_1460_, 0, v___x_1468_);
v___x_1472_ = v___x_1460_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1457_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1458_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_r_1437_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_r_1437_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1472_);
lean_ctor_set(v___x_1158_, 3, v___x_1470_);
lean_ctor_set(v___x_1158_, 2, v_v_1463_);
lean_ctor_set(v___x_1158_, 1, v_k_1462_);
lean_ctor_set(v___x_1158_, 0, v___x_1467_);
v___x_1474_ = v___x_1158_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1472_);
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
}
}
else
{
lean_object* v_r_1486_; 
v_r_1486_ = lean_ctor_get(v___x_1339_, 4);
lean_inc(v_r_1486_);
if (lean_obj_tag(v_r_1486_) == 0)
{
lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1500_; 
v_k_1487_ = lean_ctor_get(v___x_1339_, 1);
v_v_1488_ = lean_ctor_get(v___x_1339_, 2);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1501_ = lean_ctor_get(v___x_1339_, 4);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v___x_1339_, 3);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v___x_1339_, 0);
lean_dec(v_unused_1503_);
v___x_1490_ = v___x_1339_;
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_v_1488_);
lean_inc(v_k_1487_);
lean_dec(v___x_1339_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = lean_unsigned_to_nat(3u);
v___x_1493_ = lean_unsigned_to_nat(1u);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 4, v_l_1436_);
lean_ctor_set(v___x_1490_, 2, v_v_1154_);
lean_ctor_set(v___x_1490_, 1, v_k_1153_);
lean_ctor_set(v___x_1490_, 0, v___x_1493_);
v___x_1495_ = v___x_1490_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_l_1436_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_r_1486_);
lean_ctor_set(v___x_1158_, 3, v___x_1495_);
lean_ctor_set(v___x_1158_, 2, v_v_1488_);
lean_ctor_set(v___x_1158_, 1, v_k_1487_);
lean_ctor_set(v___x_1158_, 0, v___x_1492_);
v___x_1497_ = v___x_1158_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_r_1486_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_unsigned_to_nat(2u);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1339_);
lean_ctor_set(v___x_1158_, 3, v_r_1486_);
lean_ctor_set(v___x_1158_, 0, v___x_1504_);
v___x_1506_ = v___x_1158_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_r_1486_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v___x_1339_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_unsigned_to_nat(1u);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v___x_1339_);
lean_ctor_set(v___x_1158_, 3, v___x_1339_);
lean_ctor_set(v___x_1158_, 0, v___x_1508_);
v___x_1510_ = v___x_1158_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v___x_1339_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_k_1149_);
lean_ctor_set(v___x_1514_, 2, v_v_1150_);
lean_ctor_set(v___x_1514_, 3, v_t_1151_);
lean_ctor_set(v___x_1514_, 4, v_t_1151_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1515_, lean_object* v_x_1516_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 0)
{
lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v_l_1519_; lean_object* v_r_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_k_1517_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_k_1517_);
v_v_1518_ = lean_ctor_get(v_x_1516_, 2);
lean_inc(v_v_1518_);
v_l_1519_ = lean_ctor_get(v_x_1516_, 3);
lean_inc(v_l_1519_);
v_r_1520_ = lean_ctor_get(v_x_1516_, 4);
lean_inc(v_r_1520_);
lean_dec_ref_known(v_x_1516_, 5);
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1515_, v_l_1519_);
v___x_1522_ = 1;
v___x_1523_ = l_Lean_Name_toString(v_k_1517_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_v_1518_);
v___x_1525_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1523_, v___x_1524_, v___x_1521_);
v_init_1515_ = v___x_1525_;
v_x_1516_ = v_r_1520_;
goto _start;
}
else
{
return v_init_1515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_box(1);
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1528_, v_m_1527_);
v___x_1530_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
if (lean_obj_tag(v_a_1531_) == 0)
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_array_to_list(v_a_1532_);
return v___x_1533_;
}
else
{
lean_object* v_head_1534_; lean_object* v_tail_1535_; lean_object* v___x_1536_; 
v_head_1534_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_head_1534_);
v_tail_1535_ = lean_ctor_get(v_a_1531_, 1);
lean_inc(v_tail_1535_);
lean_dec_ref_known(v_a_1531_, 2);
v___x_1536_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1532_, v_head_1534_);
v_a_1531_ = v_tail_1535_;
v_a_1532_ = v___x_1536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1546_){
_start:
{
lean_object* v_idx_1547_; lean_object* v_name_1548_; lean_object* v_platform_1549_; lean_object* v_leanHash_1550_; uint64_t v_configHash_1551_; lean_object* v_options_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_idx_1547_ = lean_ctor_get(v_x_1546_, 0);
lean_inc(v_idx_1547_);
v_name_1548_ = lean_ctor_get(v_x_1546_, 1);
lean_inc(v_name_1548_);
v_platform_1549_ = lean_ctor_get(v_x_1546_, 2);
lean_inc_ref(v_platform_1549_);
v_leanHash_1550_ = lean_ctor_get(v_x_1546_, 3);
lean_inc_ref(v_leanHash_1550_);
v_configHash_1551_ = lean_ctor_get_uint64(v_x_1546_, sizeof(void*)*5);
v_options_1552_ = lean_ctor_get(v_x_1546_, 4);
lean_inc(v_options_1552_);
lean_dec_ref(v_x_1546_);
v___x_1553_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1554_ = l_Lean_JsonNumber_fromNat(v_idx_1547_);
v___x_1555_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1553_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1560_ = 1;
v___x_1561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1548_, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1559_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1557_);
v___x_1565_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_platform_1549_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1557_);
v___x_1569_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_leanHash_1550_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1557_);
v___x_1573_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1574_ = l_Lake_lowerHexUInt64(v_configHash_1551_);
v___x_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1573_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v___x_1557_);
v___x_1578_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1579_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1552_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___x_1557_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___x_1557_);
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1577_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1572_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1568_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1564_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1558_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1589_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1587_, v___x_1588_);
v___x_1590_ = l_Lean_Json_mkObj(v___x_1589_);
lean_dec(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1591_, lean_object* v_msg_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1594_, lean_object* v_k_1595_, lean_object* v_v_1596_, lean_object* v_t_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1595_, v_v_1596_, v_t_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1599_, lean_object* v_t_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1599_, v_t_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1604_, lean_object* v_k_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l_Lean_Json_getObjValD(v_j_1604_, v_k_1605_);
v___x_1607_ = l_Lean_Json_getNat_x3f(v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1608_, lean_object* v_k_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1608_, v_k_1609_);
lean_dec_ref(v_k_1609_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1611_, lean_object* v_k_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l_Lean_Json_getObjValD(v_j_1611_, v_k_1612_);
v___x_1614_ = l_Lean_Name_fromJson_x3f(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1615_, lean_object* v_k_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1615_, v_k_1616_);
lean_dec_ref(v_k_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1618_, lean_object* v_k_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = l_Lean_Json_getObjValD(v_j_1618_, v_k_1619_);
v___x_1621_ = l_Lean_Json_getStr_x3f(v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1622_, v_k_1623_);
lean_dec_ref(v_k_1623_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1625_, lean_object* v_k_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = l_Lean_Json_getObjValD(v_j_1625_, v_k_1626_);
v___x_1628_ = l_Lake_Hash_fromJson_x3f(v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1629_, v_k_1630_);
lean_dec_ref(v_k_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 0)
{
lean_object* v_k_1637_; lean_object* v_v_1638_; lean_object* v_l_1639_; lean_object* v_r_1640_; lean_object* v___x_1641_; 
v_k_1637_ = lean_ctor_get(v_x_1636_, 1);
lean_inc(v_k_1637_);
v_v_1638_ = lean_ctor_get(v_x_1636_, 2);
lean_inc(v_v_1638_);
v_l_1639_ = lean_ctor_get(v_x_1636_, 3);
lean_inc(v_l_1639_);
v_r_1640_ = lean_ctor_get(v_x_1636_, 4);
lean_inc(v_r_1640_);
lean_dec_ref_known(v_x_1636_, 5);
v___x_1641_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1635_, v_l_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec(v_r_1640_);
lean_dec(v_v_1638_);
lean_dec(v_k_1637_);
return v___x_1641_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1682_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1682_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1682_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1647_ = lean_string_dec_eq(v_k_1637_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v_n_1648_; uint8_t v___x_1649_; 
lean_inc(v_k_1637_);
v_n_1648_ = l_String_toName(v_k_1637_);
v___x_1649_ = l_Lean_Name_isAnonymous(v_n_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_del_object(v___x_1644_);
lean_dec(v_k_1637_);
v___x_1650_ = l_Lean_Json_getStr_x3f(v_v_1638_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_n_1648_);
lean_dec(v_a_1642_);
lean_dec(v_r_1640_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1660_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1648_, v_a_1659_, v_a_1642_);
v_init_1635_ = v___x_1660_;
v_x_1636_ = v_r_1640_;
goto _start;
}
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
lean_dec(v_n_1648_);
lean_dec(v_a_1642_);
lean_dec(v_r_1640_);
lean_dec(v_v_1638_);
v___x_1662_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1663_ = lean_string_append(v___x_1662_, v_k_1637_);
lean_dec(v_k_1637_);
v___x_1664_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1665_ = lean_string_append(v___x_1663_, v___x_1664_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1665_);
v___x_1667_ = v___x_1644_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v___x_1669_; 
lean_del_object(v___x_1644_);
lean_dec(v_k_1637_);
v___x_1669_ = l_Lean_Json_getStr_x3f(v_v_1638_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_a_1642_);
lean_dec(v_r_1640_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_a_1678_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1679_ = lean_box(0);
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1679_, v_a_1678_, v_a_1642_);
v_init_1635_ = v___x_1680_;
v_x_1636_ = v_r_1640_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_init_1635_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 5)
{
lean_object* v_kvPairs_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_kvPairs_1686_ = lean_ctor_get(v_x_1685_, 0);
lean_inc(v_kvPairs_1686_);
lean_dec_ref_known(v_x_1685_, 1);
v___x_1687_ = lean_box(1);
v___x_1688_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1687_, v_kvPairs_1686_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1689_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1690_ = lean_unsigned_to_nat(80u);
v___x_1691_ = l_Lean_Json_pretty(v_x_1685_, v___x_1690_);
v___x_1692_ = lean_string_append(v___x_1689_, v___x_1691_);
lean_dec_ref(v___x_1691_);
v___x_1693_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1694_ = lean_string_append(v___x_1692_, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1696_, lean_object* v_k_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = l_Lean_Json_getObjValD(v_j_1696_, v_k_1697_);
v___x_1699_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1700_, lean_object* v_k_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1700_, v_k_1701_);
lean_dec_ref(v_k_1701_);
return v_res_1702_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = 1;
v___x_1732_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1733_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1732_, v___x_1731_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1736_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1737_ = lean_string_append(v___x_1736_, v___x_1735_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = 1;
v___x_1741_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1742_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1744_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1745_ = lean_string_append(v___x_1744_, v___x_1743_);
return v___x_1745_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1748_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1749_ = lean_string_append(v___x_1748_, v___x_1747_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = 1;
v___x_1753_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1754_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1753_, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1756_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1757_ = lean_string_append(v___x_1756_, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1759_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1760_ = lean_string_append(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = 1;
v___x_1764_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1765_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1764_, v___x_1763_);
return v___x_1765_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1767_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1768_ = lean_string_append(v___x_1767_, v___x_1766_);
return v___x_1768_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1770_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1771_ = lean_string_append(v___x_1770_, v___x_1769_);
return v___x_1771_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = 1;
v___x_1775_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1776_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1775_, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1778_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1779_ = lean_string_append(v___x_1778_, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1781_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1782_ = lean_string_append(v___x_1781_, v___x_1780_);
return v___x_1782_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = 1;
v___x_1786_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1789_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1790_ = lean_string_append(v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1792_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1793_ = lean_string_append(v___x_1792_, v___x_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = 1;
v___x_1797_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1797_, v___x_1796_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1800_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1801_ = lean_string_append(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1803_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1804_ = lean_string_append(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1805_);
v___x_1807_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1805_, v___x_1806_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_json_1805_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_1813_ = lean_string_append(v___x_1812_, v_a_1808_);
lean_dec(v_a_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1813_);
v___x_1815_ = v___x_1810_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_json_1805_);
v_a_1818_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1807_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1807_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set_tag(v___x_1820_, 0);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1826_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1827_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1805_);
v___x_1828_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1805_, v___x_1827_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1833_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_1834_ = lean_string_append(v___x_1833_, v_a_1829_);
lean_dec(v_a_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1834_);
v___x_1836_ = v___x_1831_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
else
{
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
v_a_1839_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1828_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1828_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 0);
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_a_1847_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1848_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1805_);
v___x_1849_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1805_, v___x_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1854_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1855_ = lean_string_append(v___x_1854_, v_a_1850_);
lean_dec(v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1855_);
v___x_1857_ = v___x_1852_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
v_a_1860_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1849_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1849_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_a_1868_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1869_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1805_);
v___x_1870_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1805_, v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1868_);
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
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
v___x_1875_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
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
lean_dec(v_a_1868_);
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
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
v___x_1890_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1805_);
v___x_1891_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1805_, v___x_1890_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1889_);
lean_dec(v_a_1868_);
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
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
v___x_1896_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
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
lean_dec(v_a_1868_);
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
lean_dec(v_json_1805_);
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
v___x_1911_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1912_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1805_, v___x_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1910_);
lean_dec(v_a_1889_);
lean_dec(v_a_1868_);
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
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
v___x_1917_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
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
lean_dec(v_a_1868_);
lean_dec(v_a_1847_);
lean_dec(v_a_1826_);
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
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1940_; 
v_a_1931_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1933_ = v___x_1912_;
v_isShared_1934_ = v_isSharedCheck_1940_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1912_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1940_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; uint64_t v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1935_, 0, v_a_1826_);
lean_ctor_set(v___x_1935_, 1, v_a_1847_);
lean_ctor_set(v___x_1935_, 2, v_a_1868_);
lean_ctor_set(v___x_1935_, 3, v_a_1889_);
lean_ctor_set(v___x_1935_, 4, v_a_1931_);
v___x_1936_ = lean_unbox_uint64(v_a_1910_);
lean_dec(v_a_1910_);
lean_ctor_set_uint64(v___x_1935_, sizeof(void*)*5, v___x_1936_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1935_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1935_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
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
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_1945_ = lean_mk_io_user_error(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v_h_1948_){
_start:
{
uint8_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = 1;
v___x_1951_ = lean_io_prim_handle_mk(v___x_1946_, v___x_1950_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = 1;
v___x_1954_ = lean_io_prim_handle_try_lock(v_a_1952_, v___x_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; uint8_t v___x_1956_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_dec(v_a_1952_);
v___x_1957_ = lean_io_prim_handle_unlock(v_h_1948_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1966_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1957_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1957_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_io_prim_handle_unlock(v_h_1948_);
if (lean_obj_tag(v___x_1975_) == 0)
{
uint8_t v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref_known(v___x_1975_, 1);
v___x_1976_ = 3;
v___x_1977_ = lean_io_prim_handle_mk(v___x_1947_, v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = lean_io_prim_handle_lock(v_a_1978_, v___x_1953_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1980_; 
lean_dec_ref_known(v___x_1979_, 1);
v___x_1980_ = lean_io_prim_handle_unlock(v_a_1952_);
lean_dec(v_a_1952_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1980_, 0);
lean_dec(v_unused_1988_);
v___x_1982_ = v___x_1980_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v___x_1980_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_a_1978_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1978_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1978_);
v_a_1989_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1980_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1980_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v_a_1978_);
lean_dec(v_a_1952_);
v_a_1997_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1979_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1979_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
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
else
{
lean_dec(v_a_1952_);
return v___x_1977_;
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1952_);
v_a_2005_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1975_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1975_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_a_1952_);
v_a_2013_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1954_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1954_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2021_, lean_object* v___x_2022_, lean_object* v_h_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lake_importConfigFile___lam__0(v___x_2021_, v___x_2022_, v_h_2023_);
lean_dec(v_h_2023_);
lean_dec_ref(v___x_2022_);
lean_dec_ref(v___x_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___y_2038_; lean_object* v_a_2039_; lean_object* v_lakeEnv_2041_; lean_object* v_wsDir_2042_; lean_object* v_pkgIdx_2043_; lean_object* v_pkgName_2044_; lean_object* v_pkgDir_2045_; lean_object* v_configFile_2046_; lean_object* v_lakeOpts_2047_; lean_object* v_leanOpts_2048_; uint8_t v_reconfigure_2049_; lean_object* v___x_2050_; 
v_lakeEnv_2041_ = lean_ctor_get(v_cfg_2034_, 0);
lean_inc_ref(v_lakeEnv_2041_);
v_wsDir_2042_ = lean_ctor_get(v_cfg_2034_, 2);
lean_inc_ref(v_wsDir_2042_);
v_pkgIdx_2043_ = lean_ctor_get(v_cfg_2034_, 3);
lean_inc(v_pkgIdx_2043_);
v_pkgName_2044_ = lean_ctor_get(v_cfg_2034_, 4);
lean_inc(v_pkgName_2044_);
v_pkgDir_2045_ = lean_ctor_get(v_cfg_2034_, 6);
lean_inc_ref(v_pkgDir_2045_);
v_configFile_2046_ = lean_ctor_get(v_cfg_2034_, 8);
lean_inc_ref_n(v_configFile_2046_, 2);
v_lakeOpts_2047_ = lean_ctor_get(v_cfg_2034_, 12);
lean_inc(v_lakeOpts_2047_);
v_leanOpts_2048_ = lean_ctor_get(v_cfg_2034_, 13);
lean_inc_ref(v_leanOpts_2048_);
v_reconfigure_2049_ = lean_ctor_get_uint8(v_cfg_2034_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2034_);
v___x_2050_ = l_System_FilePath_fileName(v_configFile_2046_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_wsDir_2042_);
lean_dec_ref(v_lakeEnv_2041_);
v___x_2051_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2052_ = lean_array_get_size(v_a_2035_);
v___x_2053_ = lean_array_push(v_a_2035_, v___x_2051_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
return v___x_2054_;
}
else
{
lean_object* v_val_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_configDir_2061_; lean_object* v___x_2062_; 
v_val_2055_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_val_2055_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2056_ = l_Lake_defaultLakeDir;
v___x_2057_ = l_Lake_joinRelative(v_wsDir_2042_, v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2059_ = l_Lake_joinRelative(v___x_2057_, v___x_2058_);
lean_inc(v_pkgIdx_2043_);
v___x_2060_ = l_Nat_reprFast(v_pkgIdx_2043_);
v_configDir_2061_ = l_Lake_joinRelative(v___x_2059_, v___x_2060_);
lean_inc_ref(v_configDir_2061_);
v___x_2062_ = l_IO_FS_createDirAll(v_configDir_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2063_ = l_Lake_computeTextFileHash(v_configFile_2046_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_h_2072_; lean_object* v_lakeOpts_2073_; lean_object* v___y_2074_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; uint8_t v___y_2248_; uint8_t v___y_2268_; lean_object* v___y_2269_; uint8_t v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2275_; uint8_t v___y_2276_; uint8_t v___y_2277_; uint8_t v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2281_; uint8_t v___y_2283_; uint8_t v___y_2284_; lean_object* v___y_2285_; uint8_t v___y_2286_; uint8_t v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v_h_2304_; lean_object* v___y_2305_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2055_, 2);
v___x_2066_ = l_System_FilePath_withExtension(v_val_2055_, v___x_2065_);
lean_inc_ref_n(v_configDir_2061_, 2);
v___x_2067_ = l_Lake_joinRelative(v_configDir_2061_, v___x_2066_);
v___x_2068_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2069_ = l_System_FilePath_withExtension(v_val_2055_, v___x_2068_);
v___x_2070_ = l_Lake_joinRelative(v_configDir_2061_, v___x_2069_);
v___x_2226_ = l_System_FilePath_pathExists(v___x_2070_);
v___x_2227_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2228_ = l_System_FilePath_withExtension(v_val_2055_, v___x_2227_);
v___x_2229_ = l_Lake_joinRelative(v_configDir_2061_, v___x_2228_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_inc_ref(v_pkgDir_2045_);
v___x_2376_ = l_Lake_joinRelative(v_pkgDir_2045_, v___x_2056_);
v___x_2377_ = l_IO_FS_createDirAll(v___x_2376_);
if (lean_obj_tag(v___x_2377_) == 0)
{
uint8_t v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref_known(v___x_2377_, 1);
v___x_2378_ = 2;
v___x_2379_ = lean_io_prim_handle_mk(v___x_2070_, v___x_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v___x_2229_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = 1;
v___x_2382_ = lean_io_prim_handle_lock(v_a_2380_, v___x_2381_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_dec_ref_known(v___x_2382_, 1);
v_h_2072_ = v_a_2380_;
v_lakeOpts_2073_ = v_lakeOpts_2047_;
v___y_2074_ = v_a_2035_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v_a_2380_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = lean_io_error_to_string(v_a_2383_);
v___x_2385_ = 3;
v___x_2386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*1, v___x_2385_);
v___x_2387_ = lean_array_get_size(v_a_2035_);
v___x_2388_ = lean_array_push(v_a_2035_, v___x_2386_);
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
return v___x_2389_;
}
}
else
{
lean_object* v_a_2390_; 
v_a_2390_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2379_, 1);
if (lean_obj_tag(v_a_2390_) == 0)
{
uint8_t v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v_a_2390_, 2);
v___x_2391_ = 0;
v___x_2392_ = lean_io_prim_handle_mk(v___x_2070_, v___x_2391_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v_h_2304_ = v_a_2393_;
v___y_2305_ = v_a_2035_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2394_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2395_ = lean_io_error_to_string(v_a_2394_);
v___x_2396_ = 3;
v___x_2397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2396_);
v___x_2398_ = lean_array_get_size(v_a_2035_);
v___x_2399_ = lean_array_push(v_a_2035_, v___x_2397_);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
return v___x_2400_;
}
}
else
{
lean_object* v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v___x_2401_ = lean_io_error_to_string(v_a_2390_);
v___x_2402_ = 3;
v___x_2403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*1, v___x_2402_);
v___x_2404_ = lean_array_get_size(v_a_2035_);
v___x_2405_ = lean_array_push(v_a_2035_, v___x_2403_);
v___x_2406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
return v___x_2406_;
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2407_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2408_ = lean_io_error_to_string(v_a_2407_);
v___x_2409_ = 3;
v___x_2410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*1, v___x_2409_);
v___x_2411_ = lean_array_get_size(v_a_2035_);
v___x_2412_ = lean_array_push(v_a_2035_, v___x_2410_);
v___x_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
}
else
{
uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = 0;
v___x_2415_ = lean_io_prim_handle_mk(v___x_2070_, v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_h_2304_ = v_a_2416_;
v___y_2305_ = v_a_2035_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2417_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2418_ = lean_io_error_to_string(v_a_2417_);
v___x_2419_ = 3;
v___x_2420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*1, v___x_2419_);
v___x_2421_ = lean_array_get_size(v_a_2035_);
v___x_2422_ = lean_array_push(v_a_2035_, v___x_2420_);
v___x_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
return v___x_2423_;
}
}
v___jp_2071_:
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_io_remove_file(v___x_2067_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint64_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref_known(v___x_2075_, 1);
lean_dec_ref(v___x_2070_);
v___x_2076_ = l_System_Platform_target;
v___x_2077_ = l_Lake_Env_leanGithash(v_lakeEnv_2041_);
lean_dec_ref(v_lakeEnv_2041_);
lean_inc(v_lakeOpts_2073_);
lean_inc(v_pkgName_2044_);
lean_inc(v_pkgIdx_2043_);
v___x_2078_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2078_, 0, v_pkgIdx_2043_);
lean_ctor_set(v___x_2078_, 1, v_pkgName_2044_);
lean_ctor_set(v___x_2078_, 2, v___x_2076_);
lean_ctor_set(v___x_2078_, 3, v___x_2077_);
lean_ctor_set(v___x_2078_, 4, v_lakeOpts_2073_);
v___x_2079_ = lean_unbox_uint64(v_a_2064_);
lean_dec(v_a_2064_);
lean_ctor_set_uint64(v___x_2078_, sizeof(void*)*5, v___x_2079_);
v___x_2080_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2078_);
v___x_2081_ = lean_unsigned_to_nat(80u);
v___x_2082_ = l_Lean_Json_pretty(v___x_2080_, v___x_2081_);
v___x_2083_ = l_IO_FS_Handle_putStrLn(v_h_2072_, v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2084_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2084_ = lean_io_prim_handle_flush(v_h_2072_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref_known(v___x_2084_, 1);
v___x_2085_ = lean_io_prim_handle_truncate(v_h_2072_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2086_; 
lean_dec_ref_known(v___x_2085_, 1);
v___x_2086_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2043_, v_pkgName_2044_, v_pkgDir_2045_, v_lakeOpts_2073_, v_leanOpts_2048_, v_configFile_2046_, v___y_2074_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v_a_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
v_a_2088_ = lean_ctor_get(v___x_2086_, 1);
lean_inc(v_a_2088_);
v___x_2089_ = 1;
v___x_2090_ = l_Lean_writeModule(v_a_2087_, v___x_2067_, v___x_2089_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref_known(v___x_2090_, 1);
v___x_2091_ = lean_io_prim_handle_unlock(v_h_2072_);
lean_dec(v_h_2072_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_dec_ref_known(v___x_2091_, 1);
lean_dec(v_a_2088_);
return v___x_2086_;
}
else
{
lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2104_; 
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2105_ = lean_ctor_get(v___x_2086_, 1);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v___x_2086_, 0);
lean_dec(v_unused_2106_);
v___x_2093_ = v___x_2086_;
v_isShared_2094_ = v_isSharedCheck_2104_;
goto v_resetjp_2092_;
}
else
{
lean_dec(v___x_2086_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2104_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_a_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v_a_2095_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2096_ = lean_io_error_to_string(v_a_2095_);
v___x_2097_ = 3;
v___x_2098_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*1, v___x_2097_);
v___x_2099_ = lean_array_get_size(v_a_2088_);
v___x_2100_ = lean_array_push(v_a_2088_, v___x_2098_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 1);
lean_ctor_set(v___x_2093_, 1, v___x_2100_);
lean_ctor_set(v___x_2093_, 0, v___x_2099_);
v___x_2102_ = v___x_2093_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_h_2072_);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; lean_object* v_unused_2121_; 
v_unused_2120_ = lean_ctor_get(v___x_2086_, 1);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v___x_2086_, 0);
lean_dec(v_unused_2121_);
v___x_2108_ = v___x_2086_;
v_isShared_2109_ = v_isSharedCheck_2119_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v___x_2086_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2119_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_a_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v_a_2110_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2111_ = lean_io_error_to_string(v_a_2110_);
v___x_2112_ = 3;
v___x_2113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*1, v___x_2112_);
v___x_2114_ = lean_array_get_size(v_a_2088_);
v___x_2115_ = lean_array_push(v_a_2088_, v___x_2113_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 1);
lean_ctor_set(v___x_2108_, 1, v___x_2115_);
lean_ctor_set(v___x_2108_, 0, v___x_2114_);
v___x_2117_ = v___x_2108_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
return v___x_2086_;
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v_lakeOpts_2073_);
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2122_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2123_ = lean_io_error_to_string(v_a_2122_);
v___x_2124_ = 3;
v___x_2125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*1, v___x_2124_);
v___x_2126_ = lean_array_get_size(v___y_2074_);
v___x_2127_ = lean_array_push(v___y_2074_, v___x_2125_);
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
return v___x_2128_;
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_dec(v_lakeOpts_2073_);
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2129_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2130_ = lean_io_error_to_string(v_a_2129_);
v___x_2131_ = 3;
v___x_2132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set_uint8(v___x_2132_, sizeof(void*)*1, v___x_2131_);
v___x_2133_ = lean_array_get_size(v___y_2074_);
v___x_2134_ = lean_array_push(v___y_2074_, v___x_2132_);
v___x_2135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
return v___x_2135_;
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_lakeOpts_2073_);
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2136_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2137_ = lean_io_error_to_string(v_a_2136_);
v___x_2138_ = 3;
v___x_2139_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*1, v___x_2138_);
v___x_2140_ = lean_array_get_size(v___y_2074_);
v___x_2141_ = lean_array_push(v___y_2074_, v___x_2139_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
return v___x_2142_;
}
}
else
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2075_, 1);
if (lean_obj_tag(v_a_2143_) == 11)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint64_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref_known(v_a_2143_, 2);
lean_dec_ref(v___x_2070_);
v___x_2144_ = l_System_Platform_target;
v___x_2145_ = l_Lake_Env_leanGithash(v_lakeEnv_2041_);
lean_dec_ref(v_lakeEnv_2041_);
lean_inc(v_lakeOpts_2073_);
lean_inc(v_pkgName_2044_);
lean_inc(v_pkgIdx_2043_);
v___x_2146_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2146_, 0, v_pkgIdx_2043_);
lean_ctor_set(v___x_2146_, 1, v_pkgName_2044_);
lean_ctor_set(v___x_2146_, 2, v___x_2144_);
lean_ctor_set(v___x_2146_, 3, v___x_2145_);
lean_ctor_set(v___x_2146_, 4, v_lakeOpts_2073_);
v___x_2147_ = lean_unbox_uint64(v_a_2064_);
lean_dec(v_a_2064_);
lean_ctor_set_uint64(v___x_2146_, sizeof(void*)*5, v___x_2147_);
v___x_2148_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2146_);
v___x_2149_ = lean_unsigned_to_nat(80u);
v___x_2150_ = l_Lean_Json_pretty(v___x_2148_, v___x_2149_);
v___x_2151_ = l_IO_FS_Handle_putStrLn(v_h_2072_, v___x_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2152_; 
lean_dec_ref_known(v___x_2151_, 1);
v___x_2152_ = lean_io_prim_handle_flush(v_h_2072_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2153_; 
lean_dec_ref_known(v___x_2152_, 1);
v___x_2153_ = lean_io_prim_handle_truncate(v_h_2072_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; 
lean_dec_ref_known(v___x_2153_, 1);
v___x_2154_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2043_, v_pkgName_2044_, v_pkgDir_2045_, v_lakeOpts_2073_, v_leanOpts_2048_, v_configFile_2046_, v___y_2074_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_a_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
v_a_2156_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_a_2156_);
v___x_2157_ = 1;
v___x_2158_ = l_Lean_writeModule(v_a_2155_, v___x_2067_, v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v___x_2159_; 
lean_dec_ref_known(v___x_2158_, 1);
v___x_2159_ = lean_io_prim_handle_unlock(v_h_2072_);
lean_dec(v_h_2072_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref_known(v___x_2159_, 1);
lean_dec(v_a_2156_);
return v___x_2154_;
}
else
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2172_; 
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2173_ = lean_ctor_get(v___x_2154_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v___x_2154_, 0);
lean_dec(v_unused_2174_);
v___x_2161_ = v___x_2154_;
v_isShared_2162_ = v_isSharedCheck_2172_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v___x_2154_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2172_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_a_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v_a_2163_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2164_ = lean_io_error_to_string(v_a_2163_);
v___x_2165_ = 3;
v___x_2166_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*1, v___x_2165_);
v___x_2167_ = lean_array_get_size(v_a_2156_);
v___x_2168_ = lean_array_push(v_a_2156_, v___x_2166_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 1);
lean_ctor_set(v___x_2161_, 1, v___x_2168_);
lean_ctor_set(v___x_2161_, 0, v___x_2167_);
v___x_2170_ = v___x_2161_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_h_2072_);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; 
v_unused_2188_ = lean_ctor_get(v___x_2154_, 1);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v___x_2154_, 0);
lean_dec(v_unused_2189_);
v___x_2176_ = v___x_2154_;
v_isShared_2177_ = v_isSharedCheck_2187_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v___x_2154_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2187_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_a_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v_a_2178_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2179_ = lean_io_error_to_string(v_a_2178_);
v___x_2180_ = 3;
v___x_2181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*1, v___x_2180_);
v___x_2182_ = lean_array_get_size(v_a_2156_);
v___x_2183_ = lean_array_push(v_a_2156_, v___x_2181_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 1);
lean_ctor_set(v___x_2176_, 1, v___x_2183_);
lean_ctor_set(v___x_2176_, 0, v___x_2182_);
v___x_2185_ = v___x_2176_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
return v___x_2154_;
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec(v_lakeOpts_2073_);
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2190_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2191_ = lean_io_error_to_string(v_a_2190_);
v___x_2192_ = 3;
v___x_2193_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set_uint8(v___x_2193_, sizeof(void*)*1, v___x_2192_);
v___x_2194_ = lean_array_get_size(v___y_2074_);
v___x_2195_ = lean_array_push(v___y_2074_, v___x_2193_);
v___x_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
return v___x_2196_;
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v_lakeOpts_2073_);
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2197_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2198_ = lean_io_error_to_string(v_a_2197_);
v___x_2199_ = 3;
v___x_2200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*1, v___x_2199_);
v___x_2201_ = lean_array_get_size(v___y_2074_);
v___x_2202_ = lean_array_push(v___y_2074_, v___x_2200_);
v___x_2203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
return v___x_2203_;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec(v_lakeOpts_2073_);
lean_dec(v_h_2072_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2204_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2205_ = lean_io_error_to_string(v_a_2204_);
v___x_2206_ = 3;
v___x_2207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2206_);
v___x_2208_ = lean_array_get_size(v___y_2074_);
v___x_2209_ = lean_array_push(v___y_2074_, v___x_2207_);
v___x_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
return v___x_2210_;
}
}
else
{
lean_object* v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v_lakeOpts_2073_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v___x_2211_ = lean_io_error_to_string(v_a_2143_);
v___x_2212_ = 3;
v___x_2213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*1, v___x_2212_);
v___x_2214_ = lean_array_get_size(v___y_2074_);
v___x_2215_ = lean_array_push(v___y_2074_, v___x_2213_);
v___x_2216_ = lean_io_prim_handle_unlock(v_h_2072_);
lean_dec(v_h_2072_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v___x_2217_; 
lean_dec_ref_known(v___x_2216_, 1);
v___x_2217_ = lean_io_remove_file(v___x_2070_);
lean_dec_ref(v___x_2070_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
v___y_2038_ = v___x_2214_;
v_a_2039_ = v___x_2215_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_io_error_to_string(v_a_2218_);
v___x_2220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*1, v___x_2212_);
v___x_2221_ = lean_array_push(v___x_2215_, v___x_2220_);
v___y_2038_ = v___x_2214_;
v_a_2039_ = v___x_2221_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec_ref(v___x_2070_);
v_a_2222_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2223_ = lean_io_error_to_string(v_a_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*1, v___x_2212_);
v___x_2225_ = lean_array_push(v___x_2215_, v___x_2224_);
v___y_2038_ = v___x_2214_;
v_a_2039_ = v___x_2225_;
goto v___jp_2037_;
}
}
}
}
v___jp_2230_:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lake_importConfigFile___lam__0(v___x_2229_, v___x_2070_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___x_2229_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v_h_2072_ = v_a_2235_;
v_lakeOpts_2073_ = v___y_2232_;
v___y_2074_ = v___y_2231_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec(v___y_2232_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2236_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2237_ = lean_io_error_to_string(v_a_2236_);
v___x_2238_ = 3;
v___x_2239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set_uint8(v___x_2239_, sizeof(void*)*1, v___x_2238_);
v___x_2240_ = lean_array_get_size(v___y_2231_);
v___x_2241_ = lean_array_push(v___y_2231_, v___x_2239_);
v___x_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
return v___x_2242_;
}
}
v___jp_2243_:
{
if (v___y_2245_ == 0)
{
v___y_2231_ = v___y_2244_;
v___y_2232_ = v___y_2247_;
v___y_2233_ = v___y_2246_;
goto v___jp_2230_;
}
else
{
if (v___y_2248_ == 0)
{
v___y_2231_ = v___y_2244_;
v___y_2232_ = v___y_2247_;
v___y_2233_ = v___y_2246_;
goto v___jp_2230_;
}
else
{
lean_object* v___x_2249_; 
lean_dec(v___y_2247_);
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec(v_a_2064_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v___x_2249_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2067_, v_leanOpts_2048_);
lean_dec_ref(v___x_2067_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = lean_io_prim_handle_unlock(v___y_2246_);
lean_dec(v___y_2246_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; 
lean_dec_ref_known(v___x_2251_, 1);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_a_2250_);
lean_ctor_set(v___x_2252_, 1, v___y_2244_);
return v___x_2252_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_dec(v_a_2250_);
v_a_2253_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2254_ = lean_io_error_to_string(v_a_2253_);
v___x_2255_ = 3;
v___x_2256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*1, v___x_2255_);
v___x_2257_ = lean_array_get_size(v___y_2244_);
v___x_2258_ = lean_array_push(v___y_2244_, v___x_2256_);
v___x_2259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
return v___x_2259_;
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v___y_2246_);
v_a_2260_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2261_ = lean_io_error_to_string(v_a_2260_);
v___x_2262_ = 3;
v___x_2263_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*1, v___x_2262_);
v___x_2264_ = lean_array_get_size(v___y_2244_);
v___x_2265_ = lean_array_push(v___y_2244_, v___x_2263_);
v___x_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
return v___x_2266_;
}
}
}
}
v___jp_2267_:
{
if (v___y_2268_ == 0)
{
v___y_2244_ = v___y_2269_;
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2272_;
v___y_2247_ = v___y_2271_;
v___y_2248_ = v___y_2268_;
goto v___jp_2243_;
}
else
{
v___y_2244_ = v___y_2269_;
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2272_;
v___y_2247_ = v___y_2271_;
v___y_2248_ = v___y_2273_;
goto v___jp_2243_;
}
}
v___jp_2274_:
{
if (v___y_2277_ == 0)
{
v___y_2268_ = v___y_2276_;
v___y_2269_ = v___y_2275_;
v___y_2270_ = v___y_2278_;
v___y_2271_ = v___y_2280_;
v___y_2272_ = v___y_2279_;
v___y_2273_ = v___y_2277_;
goto v___jp_2267_;
}
else
{
v___y_2268_ = v___y_2276_;
v___y_2269_ = v___y_2275_;
v___y_2270_ = v___y_2278_;
v___y_2271_ = v___y_2280_;
v___y_2272_ = v___y_2279_;
v___y_2273_ = v___y_2281_;
goto v___jp_2267_;
}
}
v___jp_2282_:
{
if (v___y_2283_ == 0)
{
v___y_2275_ = v___y_2285_;
v___y_2276_ = v___y_2284_;
v___y_2277_ = v___y_2286_;
v___y_2278_ = v___y_2287_;
v___y_2279_ = v___y_2289_;
v___y_2280_ = v___y_2288_;
v___y_2281_ = v___y_2283_;
goto v___jp_2274_;
}
else
{
v___y_2275_ = v___y_2285_;
v___y_2276_ = v___y_2284_;
v___y_2277_ = v___y_2286_;
v___y_2278_ = v___y_2287_;
v___y_2279_ = v___y_2289_;
v___y_2280_ = v___y_2288_;
v___y_2281_ = v___y_2290_;
goto v___jp_2274_;
}
}
v___jp_2291_:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lake_importConfigFile___lam__0(v___x_2229_, v___x_2070_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___x_2229_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v_h_2072_ = v_a_2295_;
v_lakeOpts_2073_ = v_lakeOpts_2047_;
v___y_2074_ = v___y_2292_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2296_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2297_ = lean_io_error_to_string(v_a_2296_);
v___x_2298_ = 3;
v___x_2299_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*1, v___x_2298_);
v___x_2300_ = lean_array_get_size(v___y_2292_);
v___x_2301_ = lean_array_push(v___y_2292_, v___x_2299_);
v___x_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
return v___x_2302_;
}
}
v___jp_2303_:
{
if (v_reconfigure_2049_ == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_io_prim_handle_lock(v_h_2304_, v_reconfigure_2049_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2306_, 1);
v___x_2307_ = l_IO_FS_Handle_readToEnd(v_h_2304_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2309_ = l_Lean_Json_parse(v_a_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v___x_2310_; 
lean_dec_ref_known(v___x_2309_, 1);
v___x_2310_ = l_Lake_importConfigFile___lam__0(v___x_2229_, v___x_2070_, v_h_2304_);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2229_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v_h_2072_ = v_a_2311_;
v_lakeOpts_2073_ = v_lakeOpts_2047_;
v___y_2074_ = v___y_2305_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2312_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2313_ = lean_io_error_to_string(v_a_2312_);
v___x_2314_ = 3;
v___x_2315_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*1, v___x_2314_);
v___x_2316_ = lean_array_get_size(v___y_2305_);
v___x_2317_ = lean_array_push(v___y_2305_, v___x_2315_);
v___x_2318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
return v___x_2318_;
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_n(v_a_2319_, 2);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2320_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v___x_2321_; 
lean_dec_ref_known(v___x_2320_, 1);
v___x_2321_ = l_Lean_Json_getObj_x3f(v_a_2319_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_dec_ref_known(v___x_2321_, 1);
v___y_2292_ = v___y_2305_;
v___y_2293_ = v_h_2304_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2324_ = l_Lake_JsonObject_getJson_x3f(v_a_2322_, v___x_2323_);
lean_dec(v_a_2322_);
if (lean_obj_tag(v___x_2324_) == 0)
{
v___y_2292_ = v___y_2305_;
v___y_2293_ = v_h_2304_;
goto v___jp_2291_;
}
else
{
lean_object* v_val_2325_; lean_object* v___x_2326_; 
v_val_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_dec_ref_known(v___x_2326_, 1);
v___y_2292_ = v___y_2305_;
v___y_2293_ = v_h_2304_;
goto v___jp_2291_;
}
else
{
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_dec_ref_known(v___x_2326_, 1);
v___y_2292_ = v___y_2305_;
v___y_2293_ = v_h_2304_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
lean_dec(v_lakeOpts_2047_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = l_Lake_importConfigFile___lam__0(v___x_2229_, v___x_2070_, v_h_2304_);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2229_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v_h_2072_ = v_a_2329_;
v_lakeOpts_2073_ = v_a_2327_;
v___y_2074_ = v___y_2305_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_a_2327_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2330_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2331_ = lean_io_error_to_string(v_a_2330_);
v___x_2332_ = 3;
v___x_2333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*1, v___x_2332_);
v___x_2334_ = lean_array_get_size(v___y_2305_);
v___x_2335_ = lean_array_push(v___y_2305_, v___x_2333_);
v___x_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
return v___x_2336_;
}
}
}
}
}
}
else
{
lean_object* v_a_2337_; uint8_t v___x_2338_; lean_object* v_idx_2339_; lean_object* v_name_2340_; lean_object* v_platform_2341_; lean_object* v_leanHash_2342_; uint64_t v_configHash_2343_; lean_object* v_options_2344_; uint8_t v___x_2345_; uint8_t v___x_2346_; uint64_t v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
lean_dec(v_a_2319_);
lean_dec(v_lakeOpts_2047_);
v_a_2337_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2338_ = l_System_FilePath_pathExists(v___x_2067_);
v_idx_2339_ = lean_ctor_get(v_a_2337_, 0);
lean_inc(v_idx_2339_);
v_name_2340_ = lean_ctor_get(v_a_2337_, 1);
lean_inc(v_name_2340_);
v_platform_2341_ = lean_ctor_get(v_a_2337_, 2);
lean_inc_ref(v_platform_2341_);
v_leanHash_2342_ = lean_ctor_get(v_a_2337_, 3);
lean_inc_ref(v_leanHash_2342_);
v_configHash_2343_ = lean_ctor_get_uint64(v_a_2337_, sizeof(void*)*5);
v_options_2344_ = lean_ctor_get(v_a_2337_, 4);
lean_inc(v_options_2344_);
lean_dec(v_a_2337_);
v___x_2345_ = lean_nat_dec_eq(v_idx_2339_, v_pkgIdx_2043_);
lean_dec(v_idx_2339_);
v___x_2346_ = lean_name_eq(v_name_2340_, v_pkgName_2044_);
lean_dec(v_name_2340_);
v___x_2347_ = lean_unbox_uint64(v_a_2064_);
v___x_2348_ = lean_uint64_dec_eq(v_configHash_2343_, v___x_2347_);
v___x_2349_ = l_System_Platform_target;
v___x_2350_ = lean_string_dec_eq(v_platform_2341_, v___x_2349_);
lean_dec_ref(v_platform_2341_);
if (v___x_2350_ == 0)
{
lean_dec_ref(v_leanHash_2342_);
v___y_2283_ = v___x_2348_;
v___y_2284_ = v___x_2345_;
v___y_2285_ = v___y_2305_;
v___y_2286_ = v___x_2346_;
v___y_2287_ = v___x_2338_;
v___y_2288_ = v_options_2344_;
v___y_2289_ = v_h_2304_;
v___y_2290_ = v___x_2350_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = l_Lake_Env_leanGithash(v_lakeEnv_2041_);
v___x_2352_ = lean_string_dec_eq(v_leanHash_2342_, v___x_2351_);
lean_dec_ref(v___x_2351_);
lean_dec_ref(v_leanHash_2342_);
v___y_2283_ = v___x_2348_;
v___y_2284_ = v___x_2345_;
v___y_2285_ = v___y_2305_;
v___y_2286_ = v___x_2346_;
v___y_2287_ = v___x_2338_;
v___y_2288_ = v_options_2344_;
v___y_2289_ = v_h_2304_;
v___y_2290_ = v___x_2352_;
goto v___jp_2282_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2353_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2354_ = lean_io_error_to_string(v_a_2353_);
v___x_2355_ = 3;
v___x_2356_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1, v___x_2355_);
v___x_2357_ = lean_array_get_size(v___y_2305_);
v___x_2358_ = lean_array_push(v___y_2305_, v___x_2356_);
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
return v___x_2359_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2229_);
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2360_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2361_ = lean_io_error_to_string(v_a_2360_);
v___x_2362_ = 3;
v___x_2363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*1, v___x_2362_);
v___x_2364_ = lean_array_get_size(v___y_2305_);
v___x_2365_ = lean_array_push(v___y_2305_, v___x_2363_);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
return v___x_2366_;
}
}
else
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lake_importConfigFile___lam__0(v___x_2229_, v___x_2070_, v_h_2304_);
lean_dec(v_h_2304_);
lean_dec_ref(v___x_2229_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v_h_2072_ = v_a_2368_;
v_lakeOpts_2073_ = v_lakeOpts_2047_;
v___y_2074_ = v___y_2305_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v___x_2070_);
lean_dec_ref(v___x_2067_);
lean_dec(v_a_2064_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2369_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2370_ = lean_io_error_to_string(v_a_2369_);
v___x_2371_ = 3;
v___x_2372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*1, v___x_2371_);
v___x_2373_ = lean_array_get_size(v___y_2305_);
v___x_2374_ = lean_array_push(v___y_2305_, v___x_2372_);
v___x_2375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec_ref(v_configDir_2061_);
lean_dec(v_val_2055_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2424_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2425_ = lean_io_error_to_string(v_a_2424_);
v___x_2426_ = 3;
v___x_2427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*1, v___x_2426_);
v___x_2428_ = lean_array_get_size(v_a_2035_);
v___x_2429_ = lean_array_push(v_a_2035_, v___x_2427_);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
return v___x_2430_;
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec_ref(v_configDir_2061_);
lean_dec(v_val_2055_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2431_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2432_ = lean_io_error_to_string(v_a_2431_);
v___x_2433_ = 3;
v___x_2434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*1, v___x_2433_);
v___x_2435_ = lean_array_get_size(v_a_2035_);
v___x_2436_ = lean_array_push(v_a_2035_, v___x_2434_);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
return v___x_2437_;
}
}
v___jp_2037_:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___y_2038_);
lean_ctor_set(v___x_2040_, 1, v_a_2039_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lake_importConfigFile(v_cfg_2438_, v_a_2439_);
return v_res_2441_;
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
