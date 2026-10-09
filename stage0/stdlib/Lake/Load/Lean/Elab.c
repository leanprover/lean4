// Lean compiler output
// Module: Lake.Load.Lean.Elab
// Imports: public import Lake.Load.Config import Lean.Compiler.Bytecode.Basic import Lean.Elab.Frontend import Lake.DSL.Extensions import Lake.Util.JsonObject import Init.System.Platform import Lake.DSL.AttributesCore
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_instInhabitedPersistentEnvExtension___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_mkExtNameMap(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lake_optsExt;
extern lean_object* l_Lake_dirExt;
extern lean_object* l_Lake_nameExt;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_unlock(lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* l_System_FilePath_fileName(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*);
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Bytecode"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value_aux_1),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value),LEAN_SCALAR_PTR_LITERAL(242, 230, 44, 113, 60, 53, 46, 71)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value_aux_2),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_value),LEAN_SCALAR_PTR_LITERAL(31, 66, 12, 20, 163, 101, 6, 94)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_11_;
v_res_11_ = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2____boxed(lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_4183325717____hygCtx___hyg_2_();
return v_res_13_;
}
}
lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_enable_initializer_execution();
return v___x_15_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4___boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lake_Load_Lean_Elab_0__Lake_importModulesUsingCache_unsafe__4();
return v_res_18_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(lean_object* v_xs_19_, lean_object* v_ys_20_, lean_object* v_x_21_){
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
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_19_ = stack[0].m_obj;
lean_object* v_ys_20_ = stack[1].m_obj;
lean_object* v_x_21_ = stack[2].m_obj;
uint8_t v_res_30_;
v_res_30_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_19_, v_ys_20_, v_x_21_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_xs_31_, lean_object* v_ys_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_31_, v_ys_32_, v_x_33_);
lean_dec_ref(v_ys_32_);
lean_dec_ref(v_xs_31_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(lean_object* v_a_36_, lean_object* v_b_37_, lean_object* v_x_38_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_dec(v_b_37_);
lean_dec_ref(v_a_36_);
return v_x_38_;
}
else
{
lean_object* v_key_39_; lean_object* v_value_40_; lean_object* v_tail_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_55_; 
v_key_39_ = lean_ctor_get(v_x_38_, 0);
v_value_40_ = lean_ctor_get(v_x_38_, 1);
v_tail_41_ = lean_ctor_get(v_x_38_, 2);
v_isSharedCheck_55_ = !lean_is_exclusive(v_x_38_);
if (v_isSharedCheck_55_ == 0)
{
v___x_43_ = v_x_38_;
v_isShared_44_ = v_isSharedCheck_55_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_tail_41_);
lean_inc(v_value_40_);
lean_inc(v_key_39_);
lean_dec(v_x_38_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_55_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_50_ = lean_array_get_size(v_key_39_);
v___x_51_ = lean_array_get_size(v_a_36_);
v___x_52_ = lean_nat_dec_eq(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
goto v___jp_45_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_39_, v_a_36_, v___x_50_);
if (v___x_53_ == 0)
{
goto v___jp_45_;
}
else
{
lean_object* v___x_54_; 
lean_del_object(v___x_43_);
lean_dec(v_value_40_);
lean_dec(v_key_39_);
v___x_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_54_, 0, v_a_36_);
lean_ctor_set(v___x_54_, 1, v_b_37_);
lean_ctor_set(v___x_54_, 2, v_tail_41_);
return v___x_54_;
}
}
v___jp_45_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_36_, v_b_37_, v_tail_41_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 2, v___x_46_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_key_39_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_value_40_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v___x_46_);
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
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(lean_object* v_a_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
uint8_t v___x_58_; 
v___x_58_ = 0;
return v___x_58_;
}
else
{
lean_object* v_key_59_; lean_object* v_tail_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_key_59_ = lean_ctor_get(v_x_57_, 0);
v_tail_60_ = lean_ctor_get(v_x_57_, 2);
v___x_61_ = lean_array_get_size(v_key_59_);
v___x_62_ = lean_array_get_size(v_a_56_);
v___x_63_ = lean_nat_dec_eq(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
v_x_57_ = v_tail_60_;
goto _start;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_59_, v_a_56_, v___x_61_);
if (v___x_65_ == 0)
{
v_x_57_ = v_tail_60_;
goto _start;
}
else
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_56_ = stack[0].m_obj;
lean_object* v_x_57_ = stack[1].m_obj;
uint8_t v_res_67_;
v_res_67_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_56_, v_x_57_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg___boxed(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec_ref(v_a_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(lean_object* v_as_72_, size_t v_i_73_, size_t v_stop_74_, uint64_t v_b_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_usize_dec_eq(v_i_73_, v_stop_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; size_t v___x_80_; size_t v___x_81_; 
v___x_77_ = lean_array_uget_borrowed(v_as_72_, v_i_73_);
v___x_78_ = l_Lean_instHashableImport_hash(v___x_77_);
v___x_79_ = lean_uint64_mix_hash(v_b_75_, v___x_78_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_add(v_i_73_, v___x_80_);
v_i_73_ = v___x_81_;
v_b_75_ = v___x_79_;
goto _start;
}
else
{
return v_b_75_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_72_ = stack[0].m_obj;
size_t v_i_73_ = stack[1].m_num;
size_t v_stop_74_ = stack[2].m_num;
uint64_t v_b_75_ = stack[3].m_num;
uint64_t v_res_83_;
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_as_72_, v_i_73_, v_stop_74_, v_b_75_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1___boxed(lean_object* v_as_84_, lean_object* v_i_85_, lean_object* v_stop_86_, lean_object* v_b_87_){
_start:
{
size_t v_i_boxed_88_; size_t v_stop_boxed_89_; uint64_t v_b_boxed_90_; uint64_t v_res_91_; lean_object* v_r_92_; 
v_i_boxed_88_ = lean_unbox_usize(v_i_85_);
lean_dec(v_i_85_);
v_stop_boxed_89_ = lean_unbox_usize(v_stop_86_);
lean_dec(v_stop_86_);
v_b_boxed_90_ = lean_unbox_uint64(v_b_87_);
lean_dec_ref(v_b_87_);
v_res_91_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_as_84_, v_i_boxed_88_, v_stop_boxed_89_, v_b_boxed_90_);
lean_dec_ref(v_as_84_);
v_r_92_ = lean_box_uint64(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
return v_x_93_;
}
else
{
lean_object* v_key_95_; lean_object* v_value_96_; lean_object* v_tail_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_128_; 
v_key_95_ = lean_ctor_get(v_x_94_, 0);
v_value_96_ = lean_ctor_get(v_x_94_, 1);
v_tail_97_ = lean_ctor_get(v_x_94_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_128_ == 0)
{
v___x_99_ = v_x_94_;
v_isShared_100_ = v_isSharedCheck_128_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_tail_97_);
lean_inc(v_value_96_);
lean_inc(v_key_95_);
lean_dec(v_x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_128_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; uint64_t v___y_103_; uint64_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_101_ = lean_array_get_size(v_x_93_);
v___x_121_ = 7ULL;
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_array_get_size(v_key_95_);
v___x_124_ = lean_nat_dec_lt(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
v___y_103_ = v___x_121_;
goto v___jp_102_;
}
else
{
size_t v___x_125_; size_t v___x_126_; uint64_t v___x_127_; 
v___x_125_ = ((size_t)0ULL);
v___x_126_ = lean_usize_of_nat(v___x_123_);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_key_95_, v___x_125_, v___x_126_, v___x_121_);
v___y_103_ = v___x_127_;
goto v___jp_102_;
}
v___jp_102_:
{
uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v_fold_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_104_ = 32ULL;
v___x_105_ = lean_uint64_shift_right(v___y_103_, v___x_104_);
v_fold_106_ = lean_uint64_xor(v___y_103_, v___x_105_);
v___x_107_ = 16ULL;
v___x_108_ = lean_uint64_shift_right(v_fold_106_, v___x_107_);
v___x_109_ = lean_uint64_xor(v_fold_106_, v___x_108_);
v___x_110_ = lean_uint64_to_usize(v___x_109_);
v___x_111_ = lean_usize_of_nat(v___x_101_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_sub(v___x_111_, v___x_112_);
v___x_114_ = lean_usize_land(v___x_110_, v___x_113_);
v___x_115_ = lean_array_uget_borrowed(v_x_93_, v___x_114_);
lean_inc(v___x_115_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 2, v___x_115_);
v___x_117_ = v___x_99_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_key_95_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_value_96_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v___x_115_);
v___x_117_ = v_reuseFailAlloc_120_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_array_uset(v_x_93_, v___x_114_, v___x_117_);
v_x_93_ = v___x_118_;
v_x_94_ = v_tail_97_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(lean_object* v_i_129_, lean_object* v_source_130_, lean_object* v_target_131_){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_array_get_size(v_source_130_);
v___x_133_ = lean_nat_dec_lt(v_i_129_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec_ref(v_source_130_);
lean_dec(v_i_129_);
return v_target_131_;
}
else
{
lean_object* v_es_134_; lean_object* v___x_135_; lean_object* v_source_136_; lean_object* v_target_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_es_134_ = lean_array_fget(v_source_130_, v_i_129_);
v___x_135_ = lean_box(0);
v_source_136_ = lean_array_fset(v_source_130_, v_i_129_, v___x_135_);
v_target_137_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_target_131_, v_es_134_);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_i_129_, v___x_138_);
lean_dec(v_i_129_);
v_i_129_ = v___x_139_;
v_source_130_ = v_source_136_;
v_target_131_ = v_target_137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(lean_object* v_data_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_nbuckets_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_142_ = lean_array_get_size(v_data_141_);
v___x_143_ = lean_unsigned_to_nat(2u);
v_nbuckets_144_ = lean_nat_mul(v___x_142_, v___x_143_);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_box(0);
v___x_147_ = lean_mk_array(v_nbuckets_144_, v___x_146_);
v___x_148_ = lean_array_propagate_mark(v_data_141_, v___x_147_);
v___x_149_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v___x_145_, v_data_141_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object* v_m_150_, lean_object* v_a_151_, lean_object* v_b_152_){
_start:
{
lean_object* v_size_153_; lean_object* v_buckets_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_205_; 
v_size_153_ = lean_ctor_get(v_m_150_, 0);
v_buckets_154_ = lean_ctor_get(v_m_150_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_m_150_);
if (v_isSharedCheck_205_ == 0)
{
v___x_156_ = v_m_150_;
v_isShared_157_ = v_isSharedCheck_205_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_buckets_154_);
lean_inc(v_size_153_);
lean_dec(v_m_150_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_205_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; uint64_t v___y_160_; uint64_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_158_ = lean_array_get_size(v_buckets_154_);
v___x_198_ = 7ULL;
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_array_get_size(v_a_151_);
v___x_201_ = lean_nat_dec_lt(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
v___y_160_ = v___x_198_;
goto v___jp_159_;
}
else
{
size_t v___x_202_; size_t v___x_203_; uint64_t v___x_204_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_200_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_151_, v___x_202_, v___x_203_, v___x_198_);
v___y_160_ = v___x_204_;
goto v___jp_159_;
}
v___jp_159_:
{
uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v_fold_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; lean_object* v_bkt_172_; uint8_t v___x_173_; 
v___x_161_ = 32ULL;
v___x_162_ = lean_uint64_shift_right(v___y_160_, v___x_161_);
v_fold_163_ = lean_uint64_xor(v___y_160_, v___x_162_);
v___x_164_ = 16ULL;
v___x_165_ = lean_uint64_shift_right(v_fold_163_, v___x_164_);
v___x_166_ = lean_uint64_xor(v_fold_163_, v___x_165_);
v___x_167_ = lean_uint64_to_usize(v___x_166_);
v___x_168_ = lean_usize_of_nat(v___x_158_);
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_sub(v___x_168_, v___x_169_);
v___x_171_ = lean_usize_land(v___x_167_, v___x_170_);
v_bkt_172_ = lean_array_uget_borrowed(v_buckets_154_, v___x_171_);
v___x_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_151_, v_bkt_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v_size_x27_175_; lean_object* v___x_176_; lean_object* v_buckets_x27_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v_size_x27_175_ = lean_nat_add(v_size_153_, v___x_174_);
lean_dec(v_size_153_);
lean_inc(v_bkt_172_);
v___x_176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_176_, 0, v_a_151_);
lean_ctor_set(v___x_176_, 1, v_b_152_);
lean_ctor_set(v___x_176_, 2, v_bkt_172_);
v_buckets_x27_177_ = lean_array_uset(v_buckets_154_, v___x_171_, v___x_176_);
v___x_178_ = lean_unsigned_to_nat(4u);
v___x_179_ = lean_nat_mul(v_size_x27_175_, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(3u);
v___x_181_ = lean_nat_div(v___x_179_, v___x_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_array_get_size(v_buckets_x27_177_);
v___x_183_ = lean_nat_dec_le(v___x_181_, v___x_182_);
lean_dec(v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v_val_184_; lean_object* v___x_186_; 
v_val_184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_buckets_x27_177_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_val_184_);
lean_ctor_set(v___x_156_, 0, v_size_x27_175_);
v___x_186_ = v___x_156_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_size_x27_175_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_val_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v___x_189_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_buckets_x27_177_);
lean_ctor_set(v___x_156_, 0, v_size_x27_175_);
v___x_189_ = v___x_156_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_size_x27_175_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_buckets_x27_177_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
lean_object* v___x_191_; lean_object* v_buckets_x27_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
lean_inc(v_bkt_172_);
v___x_191_ = lean_box(0);
v_buckets_x27_192_ = lean_array_uset(v_buckets_154_, v___x_171_, v___x_191_);
v___x_193_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_151_, v_b_152_, v_bkt_172_);
v___x_194_ = lean_array_uset(v_buckets_x27_192_, v___x_171_, v___x_193_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_194_);
v___x_196_ = v___x_156_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_size_153_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object* v_a_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v_key_209_; lean_object* v_value_210_; lean_object* v_tail_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_key_209_ = lean_ctor_get(v_x_207_, 0);
v_value_210_ = lean_ctor_get(v_x_207_, 1);
v_tail_211_ = lean_ctor_get(v_x_207_, 2);
v___x_212_ = lean_array_get_size(v_key_209_);
v___x_213_ = lean_array_get_size(v_a_206_);
v___x_214_ = lean_nat_dec_eq(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
v_x_207_ = v_tail_211_;
goto _start;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_209_, v_a_206_, v___x_212_);
if (v___x_216_ == 0)
{
v_x_207_ = v_tail_211_;
goto _start;
}
else
{
lean_object* v___x_218_; 
lean_inc(v_value_210_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_value_210_);
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec_ref(v_a_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object* v_m_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_buckets_224_; lean_object* v___x_225_; uint64_t v___y_227_; uint64_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_buckets_224_ = lean_ctor_get(v_m_222_, 1);
v___x_225_ = lean_array_get_size(v_buckets_224_);
v___x_241_ = 7ULL;
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_array_get_size(v_a_223_);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
v___y_227_ = v___x_241_;
goto v___jp_226_;
}
else
{
size_t v___x_245_; size_t v___x_246_; uint64_t v___x_247_; 
v___x_245_ = ((size_t)0ULL);
v___x_246_ = lean_usize_of_nat(v___x_243_);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_223_, v___x_245_, v___x_246_, v___x_241_);
v___y_227_ = v___x_247_;
goto v___jp_226_;
}
v___jp_226_:
{
uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_228_ = 32ULL;
v___x_229_ = lean_uint64_shift_right(v___y_227_, v___x_228_);
v_fold_230_ = lean_uint64_xor(v___y_227_, v___x_229_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_225_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v___x_239_ = lean_array_uget_borrowed(v_buckets_224_, v___x_238_);
v___x_240_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_223_, v___x_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object* v_m_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_248_, v_a_249_);
lean_dec_ref(v_a_249_);
lean_dec_ref(v_m_248_);
return v_res_250_;
}
}
lean_object* l_Lake_importModulesUsingCache(lean_object* v_imports_253_, lean_object* v_opts_254_, uint32_t v_trustLevel_255_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
v___x_258_ = lean_st_ref_get(v___x_257_);
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v___x_258_, v_imports_253_);
lean_dec(v___x_258_);
if (lean_obj_tag(v___x_259_) == 1)
{
lean_object* v_val_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_opts_254_);
lean_dec_ref(v_imports_253_);
v_val_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_val_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 0);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_val_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v___x_259_);
v___x_268_ = lean_enable_initializer_execution();
v___x_269_ = ((lean_object*)(l_Lake_importModulesUsingCache___closed__0));
v___x_270_ = 0;
v___x_271_ = 1;
v___x_272_ = 2;
v___x_273_ = lean_box(1);
lean_inc_ref(v_imports_253_);
v___x_274_ = l_Lean_importModules(v_imports_253_, v_opts_254_, v_trustLevel_255_, v___x_269_, v___x_270_, v___x_271_, v___x_272_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_285_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_285_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_279_ = lean_st_ref_take(v___x_257_);
lean_inc(v_a_275_);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_279_, v_imports_253_, v_a_275_);
v___x_281_ = lean_st_ref_put(v___x_257_, v___x_280_);
if (v_isShared_278_ == 0)
{
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_275_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_dec_ref(v_imports_253_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT void l_Lake_importModulesUsingCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_imports_253_ = stack[0].m_obj;
lean_object* v_opts_254_ = stack[1].m_obj;
uint32_t v_trustLevel_255_ = stack[2].m_num;
lean_object* v_res_286_;
v_res_286_ = l_Lake_importModulesUsingCache(v_imports_253_, v_opts_254_, v_trustLevel_255_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* v_imports_287_, lean_object* v_opts_288_, lean_object* v_trustLevel_289_, lean_object* v_a_290_){
_start:
{
uint32_t v_trustLevel_boxed_291_; lean_object* v_res_292_; 
v_trustLevel_boxed_291_ = lean_unbox_uint32(v_trustLevel_289_);
lean_dec(v_trustLevel_289_);
v_res_292_ = l_Lake_importModulesUsingCache(v_imports_287_, v_opts_288_, v_trustLevel_boxed_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object* v_00_u03b2_293_, lean_object* v_m_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_294_, v_a_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_297_, v_m_298_, v_a_299_);
lean_dec_ref(v_a_299_);
lean_dec_ref(v_m_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_302_, v_a_303_, v_b_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object* v_00_u03b2_306_, lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_307_, v_x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_310_, lean_object* v_a_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_310_, v_a_311_, v_x_312_);
lean_dec(v_x_312_);
lean_dec_ref(v_a_311_);
return v_res_313_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object* v_00_u03b2_314_, lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_315_, v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_315_ = stack[1].m_obj;
lean_object* v_x_316_ = stack[2].m_obj;
uint8_t v_res_318_;
v_res_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_box(0), v_a_315_, v_x_316_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_00_u03b2_319_, v_a_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec_ref(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(lean_object* v_00_u03b2_324_, lean_object* v_data_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_data_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(lean_object* v_00_u03b2_327_, lean_object* v_a_328_, lean_object* v_b_329_, lean_object* v_x_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_328_, v_b_329_, v_x_330_);
return v___x_331_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(lean_object* v_xs_332_, lean_object* v_ys_333_, lean_object* v_hsz_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_332_, v_ys_333_, v_x_335_);
return v___x_337_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_332_ = stack[0].m_obj;
lean_object* v_ys_333_ = stack[1].m_obj;
lean_object* v_x_335_ = stack[3].m_obj;
uint8_t v_res_338_;
v_res_338_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_332_, v_ys_333_, lean_box(0), v_x_335_, lean_box(0));
stack->m_num = v_res_338_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_339_, lean_object* v_ys_340_, lean_object* v_hsz_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_339_, v_ys_340_, v_hsz_341_, v_x_342_, v_x_343_);
lean_dec_ref(v_ys_340_);
lean_dec_ref(v_xs_339_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_346_, lean_object* v_i_347_, lean_object* v_source_348_, lean_object* v_target_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v_i_347_, v_source_348_, v_target_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_x_352_, v_x_353_);
return v___x_354_;
}
}
lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object* v_header_356_, lean_object* v_opts_357_, lean_object* v_inputCtx_358_, lean_object* v_a_359_){
_start:
{
uint8_t v___x_361_; lean_object* v_imports_362_; uint32_t v___x_363_; lean_object* v___x_364_; 
v___x_361_ = 1;
lean_inc(v_header_356_);
v_imports_362_ = l_Lean_Elab_HeaderSyntax_imports(v_header_356_, v___x_361_);
v___x_363_ = 1024;
v___x_364_ = l_Lake_importModulesUsingCache(v_imports_362_, v_opts_357_, v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_inputCtx_358_);
lean_dec(v_header_356_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_a_365_);
lean_ctor_set(v___x_369_, 1, v_a_359_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v_fileName_375_; lean_object* v_fileMap_376_; uint8_t v___x_377_; lean_object* v___y_379_; lean_object* v___x_408_; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_364_, 1);
v_fileName_375_ = lean_ctor_get(v_inputCtx_358_, 1);
lean_inc_ref(v_fileName_375_);
v_fileMap_376_ = lean_ctor_get(v_inputCtx_358_, 2);
lean_inc_ref(v_fileMap_376_);
lean_dec_ref(v_inputCtx_358_);
v___x_377_ = 0;
v___x_408_ = l_Lean_Syntax_getPos_x3f(v_header_356_, v___x_377_);
lean_dec(v_header_356_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___y_379_ = v___x_409_;
goto v___jp_378_;
}
else
{
lean_object* v_val_410_; 
v_val_410_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v___x_408_, 1);
v___y_379_ = v_val_410_;
goto v___jp_378_;
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint32_t v___x_389_; lean_object* v___x_390_; 
v___x_380_ = l_Lean_FileMap_toPosition(v_fileMap_376_, v___y_379_);
lean_dec(v___y_379_);
v___x_381_ = lean_box(0);
v___x_382_ = 2;
v___x_383_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0));
v___x_384_ = lean_io_error_to_string(v_a_374_);
v___x_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___x_386_ = l_Lean_MessageData_ofFormat(v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_387_, 0, v_fileName_375_);
lean_ctor_set(v___x_387_, 1, v___x_380_);
lean_ctor_set(v___x_387_, 2, v___x_381_);
lean_ctor_set(v___x_387_, 3, v___x_383_);
lean_ctor_set(v___x_387_, 4, v___x_386_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*5, v___x_377_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*5 + 1, v___x_382_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*5 + 2, v___x_377_);
v___x_388_ = l_Lean_MessageLog_add(v___x_387_, v_a_359_);
v___x_389_ = 0;
v___x_390_ = l_Lean_mkEmptyEnvironment(v___x_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_399_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_399_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_a_391_);
lean_ctor_set(v___x_395_, 1, v___x_388_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v___x_388_);
v_a_400_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_390_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_390_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_processHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_356_ = stack[0].m_obj;
lean_object* v_opts_357_ = stack[1].m_obj;
lean_object* v_inputCtx_358_ = stack[2].m_obj;
lean_object* v_a_359_ = stack[3].m_obj;
lean_object* v_res_411_;
v_res_411_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_356_, v_opts_357_, v_inputCtx_358_, v_a_359_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object* v_header_412_, lean_object* v_opts_413_, lean_object* v_inputCtx_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_412_, v_opts_413_, v_inputCtx_414_, v_a_415_);
return v_res_417_;
}
}
lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object* v_x_422_, lean_object* v___y_423_){
_start:
{
uint8_t v_isSilent_425_; 
v_isSilent_425_ = lean_ctor_get_uint8(v_x_422_, sizeof(void*)*5 + 2);
if (v_isSilent_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = l_Lake_LogEntry_ofMessage(v_x_422_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_array_push(v___y_423_, v___x_426_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_x_422_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___y_423_);
return v___x_431_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_422_ = stack[0].m_obj;
lean_object* v___y_423_ = stack[1].m_obj;
lean_object* v_res_432_;
v_res_432_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_422_, v___y_423_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object* v_x_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_433_, v___y_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1(lean_object* v___x_437_, lean_object* v_x_438_){
_start:
{
lean_inc(v___x_437_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1___boxed(lean_object* v___x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1(v___x_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec(v___x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2(lean_object* v___x_442_, lean_object* v_x_443_){
_start:
{
lean_inc(v___x_442_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2___boxed(lean_object* v___x_444_, lean_object* v_x_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2(v___x_444_, v_x_445_);
lean_dec(v_x_445_);
lean_dec(v___x_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3(lean_object* v___x_447_, lean_object* v_x_448_){
_start:
{
lean_inc_ref(v___x_447_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3___boxed(lean_object* v___x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3(v___x_449_, v_x_450_);
lean_dec_ref(v_x_450_);
lean_dec_ref(v___x_449_);
return v_res_451_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_452_, lean_object* v_as_453_, size_t v_i_454_, size_t v_stop_455_, lean_object* v_b_456_, lean_object* v___y_457_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_eq(v_i_454_, v_stop_455_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_array_uget_borrowed(v_as_453_, v_i_454_);
lean_inc_ref(v_f_452_);
lean_inc(v___x_460_);
v___x_461_ = lean_apply_3(v_f_452_, v___x_460_, v___y_457_, lean_box(0));
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v_a_463_; size_t v___x_464_; size_t v___x_465_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
v_a_463_ = lean_ctor_get(v___x_461_, 1);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_461_, 2);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_add(v_i_454_, v___x_464_);
v_i_454_ = v___x_465_;
v_b_456_ = v_a_462_;
v___y_457_ = v_a_463_;
goto _start;
}
else
{
lean_dec_ref(v_f_452_);
return v___x_461_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec_ref(v_f_452_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_b_456_);
lean_ctor_set(v___x_467_, 1, v___y_457_);
return v___x_467_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_452_ = stack[0].m_obj;
lean_object* v_as_453_ = stack[1].m_obj;
size_t v_i_454_ = stack[2].m_num;
size_t v_stop_455_ = stack[3].m_num;
lean_object* v_b_456_ = stack[4].m_obj;
lean_object* v___y_457_ = stack[5].m_obj;
lean_object* v_res_468_;
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_452_, v_as_453_, v_i_454_, v_stop_455_, v_b_456_, v___y_457_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_469_, lean_object* v_as_470_, lean_object* v_i_471_, lean_object* v_stop_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
size_t v_i_boxed_476_; size_t v_stop_boxed_477_; lean_object* v_res_478_; 
v_i_boxed_476_ = lean_unbox_usize(v_i_471_);
lean_dec(v_i_471_);
v_stop_boxed_477_ = lean_unbox_usize(v_stop_472_);
lean_dec(v_stop_472_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_469_, v_as_470_, v_i_boxed_476_, v_stop_boxed_477_, v_b_473_, v___y_474_);
lean_dec_ref(v_as_470_);
return v_res_478_;
}
}
lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_479_, lean_object* v_x_480_, lean_object* v___y_481_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_cs_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_cs_483_ = lean_ctor_get(v_x_480_, 0);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_array_get_size(v_cs_483_);
v___x_486_ = lean_box(0);
v___x_487_ = lean_nat_dec_lt(v___x_484_, v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v_f_479_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___y_481_);
return v___x_488_;
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_485_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_479_, v_cs_483_, v___x_489_, v___x_490_, v___x_486_, v___y_481_);
return v___x_491_;
}
}
else
{
lean_object* v_vs_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_vs_492_ = lean_ctor_get(v_x_480_, 0);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_array_get_size(v_vs_492_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_nat_dec_lt(v___x_493_, v___x_494_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v_f_479_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___y_481_);
return v___x_497_;
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((size_t)0ULL);
v___x_499_ = lean_usize_of_nat(v___x_494_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_479_, v_vs_492_, v___x_498_, v___x_499_, v___x_495_, v___y_481_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_479_ = stack[0].m_obj;
lean_object* v_x_480_ = stack[1].m_obj;
lean_object* v___y_481_ = stack[2].m_obj;
lean_object* v_res_501_;
v_res_501_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_479_, v_x_480_, v___y_481_);
stack->m_obj
 = v_res_501_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_502_, lean_object* v_as_503_, size_t v_i_504_, size_t v_stop_505_, lean_object* v_b_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_eq(v_i_504_, v_stop_505_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_array_uget_borrowed(v_as_503_, v_i_504_);
lean_inc_ref(v_f_502_);
v___x_511_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_502_, v___x_510_, v___y_507_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_a_513_; size_t v___x_514_; size_t v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
v_a_513_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_511_, 2);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_504_, v___x_514_);
v_i_504_ = v___x_515_;
v_b_506_ = v_a_512_;
v___y_507_ = v_a_513_;
goto _start;
}
else
{
lean_dec_ref(v_f_502_);
return v___x_511_;
}
}
else
{
lean_object* v___x_517_; 
lean_dec_ref(v_f_502_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_b_506_);
lean_ctor_set(v___x_517_, 1, v___y_507_);
return v___x_517_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_502_ = stack[0].m_obj;
lean_object* v_as_503_ = stack[1].m_obj;
size_t v_i_504_ = stack[2].m_num;
size_t v_stop_505_ = stack[3].m_num;
lean_object* v_b_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v_res_518_;
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_502_, v_as_503_, v_i_504_, v_stop_505_, v_b_506_, v___y_507_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_519_, lean_object* v_as_520_, lean_object* v_i_521_, lean_object* v_stop_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_i_boxed_526_; size_t v_stop_boxed_527_; lean_object* v_res_528_; 
v_i_boxed_526_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_519_, v_as_520_, v_i_boxed_526_, v_stop_boxed_527_, v_b_523_, v___y_524_);
lean_dec_ref(v_as_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_529_, lean_object* v_x_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_529_, v_x_530_, v___y_531_);
lean_dec_ref(v_x_530_);
return v_res_533_;
}
}
lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_534_, lean_object* v_t_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_root_538_; lean_object* v_tail_539_; lean_object* v___x_540_; 
v_root_538_ = lean_ctor_get(v_t_535_, 0);
v_tail_539_ = lean_ctor_get(v_t_535_, 1);
lean_inc_ref(v_f_534_);
v___x_540_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_534_, v_root_538_, v___y_536_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_555_; 
v_a_541_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_540_, 0);
lean_dec(v_unused_556_);
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_array_get_size(v_tail_539_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_nat_dec_lt(v___x_545_, v___x_546_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; 
lean_dec_ref(v_f_534_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_547_);
v___x_550_ = v___x_543_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_a_541_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
lean_del_object(v___x_543_);
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_546_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_534_, v_tail_539_, v___x_552_, v___x_553_, v___x_547_, v_a_541_);
return v___x_554_;
}
}
}
else
{
lean_dec_ref(v_f_534_);
return v___x_540_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_534_ = stack[0].m_obj;
lean_object* v_t_535_ = stack[1].m_obj;
lean_object* v___y_536_ = stack[2].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_534_, v_t_535_, v___y_536_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_558_, lean_object* v_t_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_558_, v_t_559_, v___y_560_);
lean_dec_ref(v_t_559_);
return v_res_562_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_563_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_564_, lean_object* v_x_565_, size_t v_x_566_, size_t v_x_567_, lean_object* v___y_568_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v_cs_570_; lean_object* v___x_571_; size_t v___x_572_; lean_object* v_j_573_; lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v_cs_570_ = lean_ctor_get(v_x_565_, 0);
v___x_571_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_572_ = lean_usize_shift_right(v_x_566_, v_x_567_);
v_j_573_ = lean_usize_to_nat(v___x_572_);
v___x_574_ = lean_array_get_borrowed(v___x_571_, v_cs_570_, v_j_573_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_shift_left(v___x_575_, v_x_567_);
v___x_577_ = lean_usize_sub(v___x_576_, v___x_575_);
v___x_578_ = lean_usize_land(v_x_566_, v___x_577_);
v___x_579_ = ((size_t)5ULL);
v___x_580_ = lean_usize_sub(v_x_567_, v___x_579_);
lean_inc_ref(v_f_564_);
v___x_581_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_564_, v___x_574_, v___x_578_, v___x_580_, v___y_568_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_597_; 
v_a_582_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_598_);
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_597_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_597_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_j_573_, v___x_586_);
lean_dec(v_j_573_);
v___x_588_ = lean_array_get_size(v_cs_570_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v___x_587_);
lean_dec_ref(v_f_564_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_589_);
v___x_592_ = v___x_584_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_a_582_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_584_);
v___x_594_ = lean_usize_of_nat(v___x_587_);
lean_dec(v___x_587_);
v___x_595_ = lean_usize_of_nat(v___x_588_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_564_, v_cs_570_, v___x_594_, v___x_595_, v___x_589_, v_a_582_);
return v___x_596_;
}
}
}
else
{
lean_dec(v_j_573_);
lean_dec_ref(v_f_564_);
return v___x_581_;
}
}
else
{
lean_object* v_vs_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_vs_599_ = lean_ctor_get(v_x_565_, 0);
v___x_600_ = lean_usize_to_nat(v_x_566_);
v___x_601_ = lean_array_get_size(v_vs_599_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_dec(v___x_600_);
lean_dec_ref(v_f_564_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___y_568_);
return v___x_604_;
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_usize_of_nat(v___x_600_);
lean_dec(v___x_600_);
v___x_606_ = lean_usize_of_nat(v___x_601_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_564_, v_vs_599_, v___x_605_, v___x_606_, v___x_602_, v___y_568_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_564_ = stack[0].m_obj;
lean_object* v_x_565_ = stack[1].m_obj;
size_t v_x_566_ = stack[2].m_num;
size_t v_x_567_ = stack[3].m_num;
lean_object* v___y_568_ = stack[4].m_obj;
lean_object* v_res_608_;
v_res_608_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_564_, v_x_565_, v_x_566_, v_x_567_, v___y_568_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_x_13233__boxed_615_; size_t v_x_13234__boxed_616_; lean_object* v_res_617_; 
v_x_13233__boxed_615_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_x_13234__boxed_616_ = lean_unbox_usize(v_x_612_);
lean_dec(v_x_612_);
v_res_617_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_609_, v_x_610_, v_x_13233__boxed_615_, v_x_13234__boxed_616_, v___y_613_);
lean_dec_ref(v_x_610_);
return v_res_617_;
}
}
lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_618_, lean_object* v_t_619_, lean_object* v_start_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_dec_eq(v_start_620_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v_root_625_; lean_object* v_tail_626_; size_t v_shift_627_; lean_object* v_tailOff_628_; uint8_t v___x_629_; 
v_root_625_ = lean_ctor_get(v_t_619_, 0);
v_tail_626_ = lean_ctor_get(v_t_619_, 1);
v_shift_627_ = lean_ctor_get_usize(v_t_619_, 4);
v_tailOff_628_ = lean_ctor_get(v_t_619_, 3);
v___x_629_ = lean_nat_dec_le(v_tailOff_628_, v_start_620_);
if (v___x_629_ == 0)
{
size_t v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_usize_of_nat(v_start_620_);
lean_inc_ref(v_f_618_);
v___x_631_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_618_, v_root_625_, v___x_630_, v_shift_627_, v___y_621_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_645_; 
v_a_632_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_631_, 0);
lean_dec(v_unused_646_);
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_645_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_645_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_array_get_size(v_tail_626_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_nat_dec_lt(v___x_623_, v___x_636_);
if (v___x_638_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_f_618_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_637_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_a_632_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
lean_del_object(v___x_634_);
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_636_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_618_, v_tail_626_, v___x_642_, v___x_643_, v___x_637_, v_a_632_);
return v___x_644_;
}
}
}
else
{
lean_dec_ref(v_f_618_);
return v___x_631_;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_647_ = lean_nat_sub(v_start_620_, v_tailOff_628_);
v___x_648_ = lean_array_get_size(v_tail_626_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec(v___x_647_);
lean_dec_ref(v_f_618_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___y_621_);
return v___x_651_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_usize_of_nat(v___x_647_);
lean_dec(v___x_647_);
v___x_653_ = lean_usize_of_nat(v___x_648_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_618_, v_tail_626_, v___x_652_, v___x_653_, v___x_649_, v___y_621_);
return v___x_654_;
}
}
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_618_, v_t_619_, v___y_621_);
return v___x_655_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_618_ = stack[0].m_obj;
lean_object* v_t_619_ = stack[1].m_obj;
lean_object* v_start_620_ = stack[2].m_obj;
lean_object* v___y_621_ = stack[3].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_618_, v_t_619_, v_start_620_, v___y_621_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_657_, lean_object* v_t_658_, lean_object* v_start_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_657_, v_t_658_, v_start_659_, v___y_660_);
lean_dec(v_start_659_);
lean_dec_ref(v_t_658_);
return v_res_662_;
}
}
lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_663_, lean_object* v_f_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_unreported_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_unreported_667_ = lean_ctor_get(v_log_663_, 1);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_664_, v_unreported_667_, v___x_668_, v___y_665_);
return v___x_669_;
}
}
LEAN_EXPORT void l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_663_ = stack[0].m_obj;
lean_object* v_f_664_ = stack[1].m_obj;
lean_object* v___y_665_ = stack[2].m_obj;
lean_object* v_res_670_;
v_res_670_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_663_, v_f_664_, v___y_665_);
stack->m_obj
 = v_res_670_;
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_671_, lean_object* v_f_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_671_, v_f_672_, v___y_673_);
lean_dec_ref(v_log_671_);
return v_res_675_;
}
}
lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_678_, lean_object* v_pkgName_679_, lean_object* v_pkgDir_680_, lean_object* v_lakeOpts_681_, lean_object* v_leanOpts_682_, lean_object* v_configFile_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___f_686_; lean_object* v___x_687_; 
v___f_686_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_687_ = l_IO_FS_readFile(v_configFile_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = 1;
v___x_690_ = lean_string_utf8_byte_size(v_a_688_);
lean_inc_ref(v_configFile_683_);
v___x_691_ = l_Lean_Parser_mkInputContext___redArg(v_a_688_, v_configFile_683_, v___x_689_, v___x_690_);
lean_inc_ref(v___x_691_);
v___x_692_ = l_Lean_Parser_parseHeader(v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_811_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_811_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_811_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_811_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_snd_697_; lean_object* v_fst_698_; lean_object* v_fst_699_; lean_object* v_snd_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_810_; 
v_snd_697_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_697_);
v_fst_698_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_fst_698_);
lean_dec(v_a_693_);
v_fst_699_ = lean_ctor_get(v_snd_697_, 0);
v_snd_700_ = lean_ctor_get(v_snd_697_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_snd_697_);
if (v_isSharedCheck_810_ == 0)
{
v___x_702_ = v_snd_697_;
v_isShared_703_ = v_isSharedCheck_810_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_snd_700_);
lean_inc(v_fst_699_);
lean_dec(v_snd_697_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_810_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; 
lean_inc_ref(v___x_691_);
lean_inc_ref(v_leanOpts_682_);
v___x_704_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_698_, v_leanOpts_682_, v___x_691_, v_snd_700_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_800_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_800_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_800_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_800_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_799_; 
v_fst_709_ = lean_ctor_get(v_a_705_, 0);
v_snd_710_ = lean_ctor_get(v_a_705_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_799_ == 0)
{
v___x_712_ = v_a_705_;
v_isShared_713_ = v_isSharedCheck_799_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_a_705_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_799_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___y_715_; lean_object* v___y_761_; lean_object* v___y_774_; lean_object* v___x_786_; lean_object* v_asyncMode_787_; uint8_t v_logWrites_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_786_ = l_Lake_nameExt;
v_asyncMode_787_ = lean_ctor_get(v___x_786_, 2);
v_logWrites_788_ = lean_ctor_get_uint8(v___x_786_, sizeof(void*)*6);
v___x_789_ = ((lean_object*)(l_Lake_configModuleName));
v___x_790_ = l_Lean_Environment_setMainModule(v_fst_709_, v___x_789_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_pkgName_679_);
lean_ctor_set(v___x_712_, 0, v_pkgIdx_678_);
v___x_792_ = v___x_712_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_pkgIdx_678_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_pkgName_679_);
v___x_792_ = v_reuseFailAlloc_798_;
goto v_reusejp_791_;
}
v___jp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = l_Lean_Elab_Command_mkState(v___y_715_, v_snd_710_, v_leanOpts_682_);
v___x_717_ = l_Lean_Elab_IO_processCommands(v___x_691_, v_fst_699_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_commandState_719_; lean_object* v_env_720_; lean_object* v_messages_721_; lean_object* v___x_722_; 
lean_del_object(v___x_702_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v_commandState_719_ = lean_ctor_get(v_a_718_, 0);
lean_inc_ref(v_commandState_719_);
lean_dec(v_a_718_);
v_env_720_ = lean_ctor_get(v_commandState_719_, 0);
lean_inc_ref(v_env_720_);
v_messages_721_ = lean_ctor_get(v_commandState_719_, 1);
lean_inc_ref(v_messages_721_);
lean_dec_ref(v_commandState_719_);
v___x_722_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_721_, v___f_686_, v_a_684_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_740_; 
v_a_723_ = lean_ctor_get(v___x_722_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_722_, 0);
lean_dec(v_unused_741_);
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_740_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_740_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
uint8_t v___x_727_; 
v___x_727_ = l_Lean_MessageLog_hasErrors(v_messages_721_);
lean_dec_ref(v_messages_721_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; 
lean_dec_ref(v_configFile_683_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_env_720_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_env_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_723_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec_ref(v_env_720_);
v___x_731_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1));
v___x_732_ = lean_string_append(v_configFile_683_, v___x_731_);
v___x_733_ = 3;
v___x_734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*1, v___x_733_);
v___x_735_ = lean_array_get_size(v_a_723_);
v___x_736_ = lean_array_push(v_a_723_, v___x_734_);
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 1);
lean_ctor_set(v___x_725_, 1, v___x_736_);
lean_ctor_set(v___x_725_, 0, v___x_735_);
v___x_738_ = v___x_725_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_messages_721_);
lean_dec_ref(v_env_720_);
lean_dec_ref(v_configFile_683_);
v_a_742_ = lean_ctor_get(v___x_722_, 0);
v_a_743_ = lean_ctor_get(v___x_722_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_722_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_inc(v_a_742_);
lean_dec(v___x_722_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_742_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec_ref(v_configFile_683_);
v_a_751_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_717_, 1);
v___x_752_ = lean_io_error_to_string(v_a_751_);
v___x_753_ = 3;
v___x_754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_753_);
v___x_755_ = lean_array_get_size(v_a_684_);
v___x_756_ = lean_array_push(v_a_684_, v___x_754_);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 1);
lean_ctor_set(v___x_702_, 1, v___x_756_);
lean_ctor_set(v___x_702_, 0, v___x_755_);
v___x_758_ = v___x_702_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v_asyncMode_763_; uint8_t v_logWrites_764_; lean_object* v___x_766_; 
v___x_762_ = l_Lake_optsExt;
v_asyncMode_763_ = lean_ctor_get(v___x_762_, 2);
v_logWrites_764_ = lean_ctor_get_uint8(v___x_762_, sizeof(void*)*6);
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 1);
lean_ctor_set(v___x_707_, 0, v_lakeOpts_681_);
v___x_766_ = v___x_707_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_lakeOpts_681_);
v___x_766_ = v_reuseFailAlloc_772_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___f_767_; lean_object* v___x_768_; 
v___f_767_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1___boxed), 2, 1);
lean_closure_set(v___f_767_, 0, v___x_766_);
v___x_768_ = lean_box(0);
if (v_logWrites_764_ == 0)
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_762_, v___y_761_, v___f_767_, v_asyncMode_763_, v___x_768_, v___x_689_);
v___y_715_ = v___x_769_;
goto v___jp_714_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_762_, v___y_761_);
lean_dec_ref(v___y_761_);
v___x_771_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_762_, v___x_770_, v___f_767_, v_asyncMode_763_, v___x_768_, v___x_689_);
v___y_715_ = v___x_771_;
goto v___jp_714_;
}
}
}
v___jp_773_:
{
lean_object* v___x_775_; lean_object* v_asyncMode_776_; uint8_t v_logWrites_777_; lean_object* v___x_779_; 
v___x_775_ = l_Lake_dirExt;
v_asyncMode_776_ = lean_ctor_get(v___x_775_, 2);
v_logWrites_777_ = lean_ctor_get_uint8(v___x_775_, sizeof(void*)*6);
if (v_isShared_696_ == 0)
{
lean_ctor_set_tag(v___x_695_, 1);
lean_ctor_set(v___x_695_, 0, v_pkgDir_680_);
v___x_779_ = v___x_695_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_pkgDir_680_);
v___x_779_ = v_reuseFailAlloc_785_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___f_780_; lean_object* v___x_781_; 
v___f_780_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2___boxed), 2, 1);
lean_closure_set(v___f_780_, 0, v___x_779_);
v___x_781_ = lean_box(0);
if (v_logWrites_777_ == 0)
{
lean_object* v___x_782_; 
v___x_782_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_775_, v___y_774_, v___f_780_, v_asyncMode_776_, v___x_781_, v___x_689_);
v___y_761_ = v___x_782_;
goto v___jp_760_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_775_, v___y_774_);
lean_dec_ref(v___y_774_);
v___x_784_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_775_, v___x_783_, v___f_780_, v_asyncMode_776_, v___x_781_, v___x_689_);
v___y_761_ = v___x_784_;
goto v___jp_760_;
}
}
}
v_reusejp_791_:
{
lean_object* v___f_793_; lean_object* v___x_794_; 
v___f_793_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3___boxed), 2, 1);
lean_closure_set(v___f_793_, 0, v___x_792_);
v___x_794_ = lean_box(0);
if (v_logWrites_788_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_786_, v___x_790_, v___f_793_, v_asyncMode_787_, v___x_794_, v___x_689_);
v___y_774_ = v___x_795_;
goto v___jp_773_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_786_, v___x_790_);
lean_dec_ref(v___x_790_);
v___x_797_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_786_, v___x_796_, v___f_793_, v_asyncMode_787_, v___x_794_, v___x_689_);
v___y_774_ = v___x_797_;
goto v___jp_773_;
}
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_fst_699_);
lean_del_object(v___x_695_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v_configFile_683_);
lean_dec_ref(v_leanOpts_682_);
lean_dec(v_lakeOpts_681_);
lean_dec_ref(v_pkgDir_680_);
lean_dec(v_pkgName_679_);
lean_dec(v_pkgIdx_678_);
v_a_801_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_704_, 1);
v___x_802_ = lean_io_error_to_string(v_a_801_);
v___x_803_ = 3;
v___x_804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_803_);
v___x_805_ = lean_array_get_size(v_a_684_);
v___x_806_ = lean_array_push(v_a_684_, v___x_804_);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 1);
lean_ctor_set(v___x_702_, 1, v___x_806_);
lean_ctor_set(v___x_702_, 0, v___x_805_);
v___x_808_ = v___x_702_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec_ref(v___x_691_);
lean_dec_ref(v_configFile_683_);
lean_dec_ref(v_leanOpts_682_);
lean_dec(v_lakeOpts_681_);
lean_dec_ref(v_pkgDir_680_);
lean_dec(v_pkgName_679_);
lean_dec(v_pkgIdx_678_);
v_a_812_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_692_, 1);
v___x_813_ = lean_io_error_to_string(v_a_812_);
v___x_814_ = 3;
v___x_815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*1, v___x_814_);
v___x_816_ = lean_array_get_size(v_a_684_);
v___x_817_ = lean_array_push(v_a_684_, v___x_815_);
v___x_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
return v___x_818_;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v_configFile_683_);
lean_dec_ref(v_leanOpts_682_);
lean_dec(v_lakeOpts_681_);
lean_dec_ref(v_pkgDir_680_);
lean_dec(v_pkgName_679_);
lean_dec(v_pkgIdx_678_);
v_a_819_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_687_, 1);
v___x_820_ = lean_io_error_to_string(v_a_819_);
v___x_821_ = 3;
v___x_822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v___x_821_);
v___x_823_ = lean_array_get_size(v_a_684_);
v___x_824_ = lean_array_push(v_a_684_, v___x_822_);
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkgIdx_678_ = stack[0].m_obj;
lean_object* v_pkgName_679_ = stack[1].m_obj;
lean_object* v_pkgDir_680_ = stack[2].m_obj;
lean_object* v_lakeOpts_681_ = stack[3].m_obj;
lean_object* v_leanOpts_682_ = stack[4].m_obj;
lean_object* v_configFile_683_ = stack[5].m_obj;
lean_object* v_a_684_ = stack[6].m_obj;
lean_object* v_res_826_;
v_res_826_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_678_, v_pkgName_679_, v_pkgDir_680_, v_lakeOpts_681_, v_leanOpts_682_, v_configFile_683_, v_a_684_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_827_, lean_object* v_pkgName_828_, lean_object* v_pkgDir_829_, lean_object* v_lakeOpts_830_, lean_object* v_leanOpts_831_, lean_object* v_configFile_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_827_, v_pkgName_828_, v_pkgDir_829_, v_lakeOpts_830_, v_leanOpts_831_, v_configFile_832_, v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_836_ = stack[0].m_obj;
lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_837_ = stack[1].m_obj;
lean_object* v_res_838_;
v_res_838_ = lake_environment_add(v_env_836_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_837_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_839_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = lake_environment_add(v_env_839_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_840_);
return v_res_841_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_848_ = l_Lean_NameSet_empty;
v___x_849_ = l_Lean_NameSet_insert(v___x_848_, v___x_847_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_855_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_856_ = l_Lean_NameSet_insert(v___x_855_, v___x_854_);
return v___x_856_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_862_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_863_ = l_Lean_NameSet_insert(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_869_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_870_ = l_Lean_NameSet_insert(v___x_869_, v___x_868_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_876_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_877_ = l_Lean_NameSet_insert(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_883_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_884_ = l_Lean_NameSet_insert(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_890_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_891_ = l_Lean_NameSet_insert(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_897_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_898_ = l_Lean_NameSet_insert(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_904_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_905_ = l_Lean_NameSet_insert(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_911_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_912_ = l_Lean_NameSet_insert(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_918_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_919_ = l_Lean_NameSet_insert(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_925_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_926_ = l_Lean_NameSet_insert(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_932_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_933_ = l_Lean_NameSet_insert(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_939_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_940_ = l_Lean_NameSet_insert(v___x_939_, v___x_938_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_946_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_947_ = l_Lean_NameSet_insert(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_954_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_955_ = l_Lean_NameSet_insert(v___x_954_, v___x_953_);
return v___x_955_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53));
v___x_965_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_966_ = l_Lean_NameSet_insert(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0(lean_object* v___x_968_, lean_object* v___x_969_, lean_object* v_s_970_){
_start:
{
lean_object* v_addEntryFn_971_; lean_object* v_importedEntries_972_; lean_object* v_state_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_addEntryFn_971_ = lean_ctor_get(v___x_968_, 3);
lean_inc(v_addEntryFn_971_);
lean_dec_ref(v___x_968_);
v_importedEntries_972_ = lean_ctor_get(v_s_970_, 0);
v_state_973_ = lean_ctor_get(v_s_970_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_s_970_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v_s_970_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_state_973_);
lean_inc(v_importedEntries_972_);
lean_dec(v_s_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_state_977_; lean_object* v___x_979_; 
v_state_977_ = lean_apply_2(v_addEntryFn_971_, v_state_973_, v___x_969_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v_state_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_importedEntries_972_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_state_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_instInhabitedPersistentEnvExtension___redArg();
return v___x_982_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_983_, lean_object* v_val_984_, uint8_t v___x_985_, lean_object* v_as_986_, size_t v_i_987_, size_t v_stop_988_, lean_object* v_b_989_){
_start:
{
lean_object* v___y_991_; uint8_t v___x_995_; 
v___x_995_ = lean_usize_dec_eq(v_i_987_, v_stop_988_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_toEnvExtension_998_; uint8_t v_logWrites_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_996_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_997_ = lean_array_get_borrowed(v___x_996_, v_val_983_, v_val_984_);
v_toEnvExtension_998_ = lean_ctor_get(v___x_997_, 0);
v_logWrites_999_ = lean_ctor_get_uint8(v_toEnvExtension_998_, sizeof(void*)*6);
v___x_1000_ = lean_array_uget_borrowed(v_as_986_, v_i_987_);
lean_inc(v___x_1000_);
lean_inc(v___x_997_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_1001_, 0, v___x_997_);
lean_closure_set(v___f_1001_, 1, v___x_1000_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_box(0);
if (v_logWrites_999_ == 0)
{
lean_object* v___x_1004_; 
lean_inc_ref(v_toEnvExtension_998_);
v___x_1004_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_998_, v_b_989_, v___f_1001_, v___x_1002_, v___x_1003_, v___x_985_);
v___y_991_ = v___x_1004_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc_ref_n(v_toEnvExtension_998_, 2);
v___x_1005_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_998_, v_b_989_);
lean_dec_ref(v_b_989_);
v___x_1006_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_998_, v___x_1005_, v___f_1001_, v___x_1002_, v___x_1003_, v___x_985_);
v___y_991_ = v___x_1006_;
goto v___jp_990_;
}
}
else
{
return v_b_989_;
}
v___jp_990_:
{
size_t v___x_992_; size_t v___x_993_; 
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_987_, v___x_992_);
v_i_987_ = v___x_993_;
v_b_989_ = v___y_991_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_983_ = stack[0].m_obj;
lean_object* v_val_984_ = stack[1].m_obj;
uint8_t v___x_985_ = stack[2].m_num;
lean_object* v_as_986_ = stack[3].m_obj;
size_t v_i_987_ = stack[4].m_num;
size_t v_stop_988_ = stack[5].m_num;
lean_object* v_b_989_ = stack[6].m_obj;
lean_object* v_res_1007_;
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_983_, v_val_984_, v___x_985_, v_as_986_, v_i_987_, v_stop_988_, v_b_989_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_1008_, lean_object* v_val_1009_, lean_object* v___x_1010_, lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_stop_1013_, lean_object* v_b_1014_){
_start:
{
uint8_t v___x_1511__boxed_1015_; size_t v_i_boxed_1016_; size_t v_stop_boxed_1017_; lean_object* v_res_1018_; 
v___x_1511__boxed_1015_ = lean_unbox(v___x_1010_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_stop_boxed_1017_ = lean_unbox_usize(v_stop_1013_);
lean_dec(v_stop_1013_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1008_, v_val_1009_, v___x_1511__boxed_1015_, v_as_1011_, v_i_boxed_1016_, v_stop_boxed_1017_, v_b_1014_);
lean_dec_ref(v_as_1011_);
lean_dec(v_val_1009_);
lean_dec_ref(v_val_1008_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
else
{
lean_object* v_key_1022_; lean_object* v_value_1023_; lean_object* v_tail_1024_; uint8_t v___x_1025_; 
v_key_1022_ = lean_ctor_get(v_x_1020_, 0);
v_value_1023_ = lean_ctor_get(v_x_1020_, 1);
v_tail_1024_ = lean_ctor_get(v_x_1020_, 2);
v___x_1025_ = lean_name_eq(v_key_1022_, v_a_1019_);
if (v___x_1025_ == 0)
{
v_x_1020_ = v_tail_1024_;
goto _start;
}
else
{
lean_object* v___x_1027_; 
lean_inc(v_value_1023_);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_value_1023_);
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1028_, v_x_1029_);
lean_dec(v_x_1029_);
lean_dec(v_a_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_buckets_1033_; lean_object* v___x_1034_; uint64_t v___y_1036_; 
v_buckets_1033_ = lean_ctor_get(v_m_1031_, 1);
v___x_1034_ = lean_array_get_size(v_buckets_1033_);
if (lean_obj_tag(v_a_1032_) == 0)
{
uint64_t v___x_1050_; 
v___x_1050_ = 1723ULL;
v___y_1036_ = v___x_1050_;
goto v___jp_1035_;
}
else
{
uint64_t v_hash_1051_; 
v_hash_1051_ = lean_ctor_get_uint64(v_a_1032_, sizeof(void*)*2);
v___y_1036_ = v_hash_1051_;
goto v___jp_1035_;
}
v___jp_1035_:
{
uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v_fold_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1037_ = 32ULL;
v___x_1038_ = lean_uint64_shift_right(v___y_1036_, v___x_1037_);
v_fold_1039_ = lean_uint64_xor(v___y_1036_, v___x_1038_);
v___x_1040_ = 16ULL;
v___x_1041_ = lean_uint64_shift_right(v_fold_1039_, v___x_1040_);
v___x_1042_ = lean_uint64_xor(v_fold_1039_, v___x_1041_);
v___x_1043_ = lean_uint64_to_usize(v___x_1042_);
v___x_1044_ = lean_usize_of_nat(v___x_1034_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_sub(v___x_1044_, v___x_1045_);
v___x_1047_ = lean_usize_land(v___x_1043_, v___x_1046_);
v___x_1048_ = lean_array_uget_borrowed(v_buckets_1033_, v___x_1047_);
v___x_1049_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1032_, v___x_1048_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_m_1052_);
return v_res_1054_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_1055_, lean_object* v_val_1056_, lean_object* v_as_1057_, size_t v_i_1058_, size_t v_stop_1059_, lean_object* v_b_1060_){
_start:
{
lean_object* v___y_1062_; uint8_t v___x_1066_; 
v___x_1066_ = lean_usize_dec_eq(v_i_1058_, v_stop_1059_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1067_ = lean_array_uget_borrowed(v_as_1057_, v_i_1058_);
v_fst_1068_ = lean_ctor_get(v___x_1067_, 0);
v_snd_1069_ = lean_ctor_get(v___x_1067_, 1);
v___x_1070_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_1071_ = l_Lean_NameSet_contains(v___x_1070_, v_fst_1068_);
if (v___x_1071_ == 0)
{
v___y_1062_ = v_b_1060_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_1055_, v_fst_1068_);
if (lean_obj_tag(v___x_1072_) == 0)
{
v___y_1062_ = v_b_1060_;
goto v___jp_1061_;
}
else
{
lean_object* v_val_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_val_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_array_get_size(v_snd_1069_);
v___x_1076_ = lean_nat_dec_lt(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_val_1073_);
v___y_1062_ = v_b_1060_;
goto v___jp_1061_;
}
else
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_nat_dec_le(v___x_1075_, v___x_1075_);
if (v___x_1077_ == 0)
{
if (v___x_1076_ == 0)
{
lean_dec(v_val_1073_);
v___y_1062_ = v_b_1060_;
goto v___jp_1061_;
}
else
{
size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = lean_usize_of_nat(v___x_1075_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1056_, v_val_1073_, v___x_1071_, v_snd_1069_, v___x_1078_, v___x_1079_, v_b_1060_);
lean_dec(v_val_1073_);
v___y_1062_ = v___x_1080_;
goto v___jp_1061_;
}
}
else
{
size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1075_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1056_, v_val_1073_, v___x_1071_, v_snd_1069_, v___x_1081_, v___x_1082_, v_b_1060_);
lean_dec(v_val_1073_);
v___y_1062_ = v___x_1083_;
goto v___jp_1061_;
}
}
}
}
}
else
{
return v_b_1060_;
}
v___jp_1061_:
{
size_t v___x_1063_; size_t v___x_1064_; 
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_add(v_i_1058_, v___x_1063_);
v_i_1058_ = v___x_1064_;
v_b_1060_ = v___y_1062_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1055_ = stack[0].m_obj;
lean_object* v_val_1056_ = stack[1].m_obj;
lean_object* v_as_1057_ = stack[2].m_obj;
size_t v_i_1058_ = stack[3].m_num;
size_t v_stop_1059_ = stack[4].m_num;
lean_object* v_b_1060_ = stack[5].m_obj;
lean_object* v_res_1084_;
v_res_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1055_, v_val_1056_, v_as_1057_, v_i_1058_, v_stop_1059_, v_b_1060_);
stack->m_obj
 = v_res_1084_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1085_, lean_object* v_val_1086_, lean_object* v_as_1087_, lean_object* v_i_1088_, lean_object* v_stop_1089_, lean_object* v_b_1090_){
_start:
{
size_t v_i_boxed_1091_; size_t v_stop_boxed_1092_; lean_object* v_res_1093_; 
v_i_boxed_1091_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_stop_boxed_1092_ = lean_unbox_usize(v_stop_1089_);
lean_dec(v_stop_1089_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1085_, v_val_1086_, v_as_1087_, v_i_boxed_1091_, v_stop_boxed_1092_, v_b_1090_);
lean_dec_ref(v_as_1087_);
lean_dec_ref(v_val_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1093_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1094_, size_t v_i_1095_, size_t v_stop_1096_, lean_object* v_b_1097_){
_start:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_usize_dec_eq(v_i_1095_, v_stop_1096_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; 
v___x_1099_ = lean_array_uget_borrowed(v_as_1094_, v_i_1095_);
lean_inc(v___x_1099_);
v___x_1100_ = lake_environment_add(v_b_1097_, v___x_1099_);
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1095_, v___x_1101_);
v_i_1095_ = v___x_1102_;
v_b_1097_ = v___x_1100_;
goto _start;
}
else
{
return v_b_1097_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1094_ = stack[0].m_obj;
size_t v_i_1095_ = stack[1].m_num;
size_t v_stop_1096_ = stack[2].m_num;
lean_object* v_b_1097_ = stack[3].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1094_, v_i_1095_, v_stop_1096_, v_b_1097_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1105_, lean_object* v_i_1106_, lean_object* v_stop_1107_, lean_object* v_b_1108_){
_start:
{
size_t v_i_boxed_1109_; size_t v_stop_boxed_1110_; lean_object* v_res_1111_; 
v_i_boxed_1109_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_stop_boxed_1110_ = lean_unbox_usize(v_stop_1107_);
lean_dec(v_stop_1107_);
v_res_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1105_, v_i_boxed_1109_, v_stop_boxed_1110_, v_b_1108_);
lean_dec_ref(v_as_1105_);
return v_res_1111_;
}
}
lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1112_, lean_object* v_leanOpts_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_readModuleData(v_olean_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v_fst_1117_; lean_object* v_imports_1118_; lean_object* v_constants_1119_; lean_object* v_entries_1120_; uint32_t v___x_1121_; lean_object* v___x_1122_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v_fst_1117_ = lean_ctor_get(v_a_1116_, 0);
lean_inc(v_fst_1117_);
lean_dec(v_a_1116_);
v_imports_1118_ = lean_ctor_get(v_fst_1117_, 0);
lean_inc_ref(v_imports_1118_);
v_constants_1119_ = lean_ctor_get(v_fst_1117_, 2);
lean_inc_ref(v_constants_1119_);
v_entries_1120_ = lean_ctor_get(v_fst_1117_, 4);
lean_inc_ref(v_entries_1120_);
lean_dec(v_fst_1117_);
v___x_1121_ = 1024;
v___x_1122_ = l_Lake_importModulesUsingCache(v_imports_1118_, v_leanOpts_1113_, v___x_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___y_1126_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_array_get_size(v_constants_1119_);
v___x_1165_ = lean_nat_dec_lt(v___x_1124_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_dec_ref(v_constants_1119_);
v___y_1126_ = v_a_1123_;
goto v___jp_1125_;
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_nat_dec_le(v___x_1164_, v___x_1164_);
if (v___x_1166_ == 0)
{
if (v___x_1165_ == 0)
{
lean_dec_ref(v_constants_1119_);
v___y_1126_ = v_a_1123_;
goto v___jp_1125_;
}
else
{
size_t v___x_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = lean_usize_of_nat(v___x_1164_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1119_, v___x_1167_, v___x_1168_, v_a_1123_);
lean_dec_ref(v_constants_1119_);
v___y_1126_ = v___x_1169_;
goto v___jp_1125_;
}
}
else
{
size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = lean_usize_of_nat(v___x_1164_);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1119_, v___x_1170_, v___x_1171_, v_a_1123_);
lean_dec_ref(v_constants_1119_);
v___y_1126_ = v___x_1172_;
goto v___jp_1125_;
}
}
v___jp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_persistentEnvExtensionsRef;
v___x_1128_ = lean_st_ref_get(v___x_1127_);
v___x_1129_ = l_Lean_mkExtNameMap(v___x_1124_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1155_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1155_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1155_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_array_get_size(v_entries_1120_);
v___x_1135_ = lean_nat_dec_lt(v___x_1124_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1137_; 
lean_dec(v_a_1130_);
lean_dec(v___x_1128_);
lean_dec_ref(v_entries_1120_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___y_1126_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___y_1126_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
if (v___x_1139_ == 0)
{
if (v___x_1135_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v_a_1130_);
lean_dec(v___x_1128_);
lean_dec_ref(v_entries_1120_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___y_1126_);
v___x_1141_ = v___x_1132_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___y_1126_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
else
{
size_t v___x_1143_; size_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = lean_usize_of_nat(v___x_1134_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1130_, v___x_1128_, v_entries_1120_, v___x_1143_, v___x_1144_, v___y_1126_);
lean_dec_ref(v_entries_1120_);
lean_dec(v___x_1128_);
lean_dec(v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1145_);
v___x_1147_ = v___x_1132_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = lean_usize_of_nat(v___x_1134_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1130_, v___x_1128_, v_entries_1120_, v___x_1149_, v___x_1150_, v___y_1126_);
lean_dec_ref(v_entries_1120_);
lean_dec(v___x_1128_);
lean_dec(v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1151_);
v___x_1153_ = v___x_1132_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v___x_1128_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_entries_1120_);
v_a_1156_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1129_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1129_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_dec_ref(v_entries_1120_);
lean_dec_ref(v_constants_1119_);
return v___x_1122_;
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_leanOpts_1113_);
v_a_1173_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1115_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1115_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_olean_1112_ = stack[0].m_obj;
lean_object* v_leanOpts_1113_ = stack[1].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1112_, v_leanOpts_1113_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1182_, lean_object* v_leanOpts_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1182_, v_leanOpts_1183_);
lean_dec_ref(v_olean_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1186_, lean_object* v_m_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1187_, v_a_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1190_, lean_object* v_m_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1190_, v_m_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_m_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1194_, lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1195_, v_x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1198_, lean_object* v_a_1199_, lean_object* v_x_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1198_, v_a_1199_, v_x_1200_);
lean_dec(v_x_1200_);
lean_dec(v_a_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_box(1);
v___x_1204_ = lean_panic_fn_borrowed(v___x_1203_, v_msg_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1208_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1209_ = lean_unsigned_to_nat(35u);
v___x_1210_ = lean_unsigned_to_nat(182u);
v___x_1211_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1212_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1213_ = l_mkPanicMessageWithDecl(v___x_1212_, v___x_1211_, v___x_1210_, v___x_1209_, v___x_1208_);
return v___x_1213_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1214_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1215_ = lean_unsigned_to_nat(21u);
v___x_1216_ = lean_unsigned_to_nat(183u);
v___x_1217_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1218_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1219_ = l_mkPanicMessageWithDecl(v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_);
return v___x_1219_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1223_ = lean_unsigned_to_nat(35u);
v___x_1224_ = lean_unsigned_to_nat(276u);
v___x_1225_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1226_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1227_ = l_mkPanicMessageWithDecl(v___x_1226_, v___x_1225_, v___x_1224_, v___x_1223_, v___x_1222_);
return v___x_1227_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1228_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1229_ = lean_unsigned_to_nat(21u);
v___x_1230_ = lean_unsigned_to_nat(277u);
v___x_1231_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1233_ = l_mkPanicMessageWithDecl(v___x_1232_, v___x_1231_, v___x_1230_, v___x_1229_, v___x_1228_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1234_, lean_object* v_v_1235_, lean_object* v_t_1236_){
_start:
{
if (lean_obj_tag(v_t_1236_) == 0)
{
lean_object* v_size_1237_; lean_object* v_k_1238_; lean_object* v_v_1239_; lean_object* v_l_1240_; lean_object* v_r_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1597_; 
v_size_1237_ = lean_ctor_get(v_t_1236_, 0);
v_k_1238_ = lean_ctor_get(v_t_1236_, 1);
v_v_1239_ = lean_ctor_get(v_t_1236_, 2);
v_l_1240_ = lean_ctor_get(v_t_1236_, 3);
v_r_1241_ = lean_ctor_get(v_t_1236_, 4);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_t_1236_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1243_ = v_t_1236_;
v_isShared_1244_ = v_isSharedCheck_1597_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_r_1241_);
lean_inc(v_l_1240_);
lean_inc(v_v_1239_);
lean_inc(v_k_1238_);
lean_inc(v_size_1237_);
lean_dec(v_t_1236_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1597_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_string_compare(v_k_1234_, v_k_1238_);
switch(v___x_1245_)
{
case 0:
{
lean_object* v___x_1246_; 
lean_dec(v_size_1237_);
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1234_, v_v_1235_, v_l_1240_);
if (lean_obj_tag(v_r_1241_) == 0)
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_size_1247_; lean_object* v_size_1248_; lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v_l_1251_; lean_object* v_r_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_size_1247_ = lean_ctor_get(v_r_1241_, 0);
v_size_1248_ = lean_ctor_get(v___x_1246_, 0);
v_k_1249_ = lean_ctor_get(v___x_1246_, 1);
v_v_1250_ = lean_ctor_get(v___x_1246_, 2);
v_l_1251_ = lean_ctor_get(v___x_1246_, 3);
v_r_1252_ = lean_ctor_get(v___x_1246_, 4);
lean_inc(v_r_1252_);
v___x_1253_ = lean_unsigned_to_nat(3u);
v___x_1254_ = lean_nat_mul(v___x_1253_, v_size_1247_);
v___x_1255_ = lean_nat_dec_lt(v___x_1254_, v_size_1248_);
lean_dec(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_r_1252_);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v___x_1256_, v_size_1248_);
v___x_1258_ = lean_nat_add(v___x_1257_, v_size_1247_);
lean_dec(v___x_1257_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 3, v___x_1246_);
lean_ctor_set(v___x_1243_, 0, v___x_1258_);
v___x_1260_ = v___x_1243_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1241_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
else
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1333_; 
lean_inc(v_l_1251_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_inc(v_size_1248_);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; lean_object* v_unused_1335_; lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; 
v_unused_1334_ = lean_ctor_get(v___x_1246_, 4);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v___x_1246_, 3);
lean_dec(v_unused_1335_);
v_unused_1336_ = lean_ctor_get(v___x_1246_, 2);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v___x_1246_, 1);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v___x_1246_, 0);
lean_dec(v_unused_1338_);
v___x_1263_ = v___x_1246_;
v_isShared_1264_ = v_isSharedCheck_1333_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v___x_1246_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1333_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_l_1251_) == 0)
{
if (lean_obj_tag(v_r_1252_) == 0)
{
lean_object* v_size_1265_; lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_r_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_size_1265_ = lean_ctor_get(v_l_1251_, 0);
v_size_1266_ = lean_ctor_get(v_r_1252_, 0);
v_k_1267_ = lean_ctor_get(v_r_1252_, 1);
v_v_1268_ = lean_ctor_get(v_r_1252_, 2);
v_l_1269_ = lean_ctor_get(v_r_1252_, 3);
v_r_1270_ = lean_ctor_get(v_r_1252_, 4);
v___x_1271_ = lean_unsigned_to_nat(2u);
v___x_1272_ = lean_nat_mul(v___x_1271_, v_size_1265_);
v___x_1273_ = lean_nat_dec_lt(v_size_1266_, v___x_1272_);
lean_dec(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1303_; 
lean_inc(v_r_1270_);
lean_inc(v_l_1269_);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_r_1252_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; 
v_unused_1304_ = lean_ctor_get(v_r_1252_, 4);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_r_1252_, 3);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_r_1252_, 2);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_r_1252_, 1);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_r_1252_, 0);
lean_dec(v_unused_1308_);
v___x_1275_ = v_r_1252_;
v_isShared_1276_ = v_isSharedCheck_1303_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v_r_1252_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1303_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___x_1291_; lean_object* v___y_1293_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v___x_1277_, v_size_1248_);
lean_dec(v_size_1248_);
v___x_1279_ = lean_nat_add(v___x_1278_, v_size_1247_);
lean_dec(v___x_1278_);
v___x_1291_ = lean_nat_add(v___x_1277_, v_size_1265_);
if (lean_obj_tag(v_l_1269_) == 0)
{
lean_object* v_size_1301_; 
v_size_1301_ = lean_ctor_get(v_l_1269_, 0);
lean_inc(v_size_1301_);
v___y_1293_ = v_size_1301_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___y_1293_ = v___x_1302_;
goto v___jp_1292_;
}
v___jp_1280_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_nat_add(v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec(v___y_1282_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v_r_1241_);
lean_ctor_set(v___x_1275_, 3, v_r_1270_);
lean_ctor_set(v___x_1275_, 2, v_v_1239_);
lean_ctor_set(v___x_1275_, 1, v_k_1238_);
lean_ctor_set(v___x_1275_, 0, v___x_1284_);
v___x_1286_ = v___x_1275_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_r_1270_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_r_1241_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v___x_1286_);
lean_ctor_set(v___x_1263_, 3, v___y_1281_);
lean_ctor_set(v___x_1263_, 2, v_v_1268_);
lean_ctor_set(v___x_1263_, 1, v_k_1267_);
lean_ctor_set(v___x_1263_, 0, v___x_1279_);
v___x_1288_ = v___x_1263_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v___y_1281_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
v___jp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_nat_add(v___x_1291_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec(v___x_1291_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v_l_1269_);
lean_ctor_set(v___x_1243_, 3, v_l_1251_);
lean_ctor_set(v___x_1243_, 2, v_v_1250_);
lean_ctor_set(v___x_1243_, 1, v_k_1249_);
lean_ctor_set(v___x_1243_, 0, v___x_1294_);
v___x_1296_ = v___x_1243_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_l_1269_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_nat_add(v___x_1277_, v_size_1247_);
if (lean_obj_tag(v_r_1270_) == 0)
{
lean_object* v_size_1298_; 
v_size_1298_ = lean_ctor_get(v_r_1270_, 0);
lean_inc(v_size_1298_);
v___y_1281_ = v___x_1296_;
v___y_1282_ = v___x_1297_;
v___y_1283_ = v_size_1298_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___y_1281_ = v___x_1296_;
v___y_1282_ = v___x_1297_;
v___y_1283_ = v___x_1299_;
goto v___jp_1280_;
}
}
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_del_object(v___x_1243_);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = lean_nat_add(v___x_1309_, v_size_1248_);
lean_dec(v_size_1248_);
v___x_1311_ = lean_nat_add(v___x_1310_, v_size_1247_);
lean_dec(v___x_1310_);
v___x_1312_ = lean_nat_add(v___x_1309_, v_size_1247_);
v___x_1313_ = lean_nat_add(v___x_1312_, v_size_1266_);
lean_dec(v___x_1312_);
lean_inc_ref(v_r_1241_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v_r_1241_);
lean_ctor_set(v___x_1263_, 3, v_r_1252_);
lean_ctor_set(v___x_1263_, 2, v_v_1239_);
lean_ctor_set(v___x_1263_, 1, v_k_1238_);
lean_ctor_set(v___x_1263_, 0, v___x_1313_);
v___x_1315_ = v___x_1263_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_r_1252_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_r_1241_);
v___x_1315_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_isSharedCheck_1322_ = !lean_is_exclusive(v_r_1241_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; lean_object* v_unused_1327_; 
v_unused_1323_ = lean_ctor_get(v_r_1241_, 4);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_r_1241_, 3);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_r_1241_, 2);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_r_1241_, 1);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v_r_1241_, 0);
lean_dec(v_unused_1327_);
v___x_1317_ = v_r_1241_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v_r_1241_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___x_1315_);
lean_ctor_set(v___x_1317_, 3, v_l_1251_);
lean_ctor_set(v___x_1317_, 2, v_v_1250_);
lean_ctor_set(v___x_1317_, 1, v_k_1249_);
lean_ctor_set(v___x_1317_, 0, v___x_1311_);
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v___x_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref_known(v_l_1251_, 5);
lean_del_object(v___x_1263_);
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
lean_dec(v_size_1248_);
lean_dec_ref_known(v_r_1241_, 5);
lean_del_object(v___x_1243_);
lean_dec(v_v_1239_);
lean_dec(v_k_1238_);
v___x_1329_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1330_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1329_);
return v___x_1330_;
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_del_object(v___x_1263_);
lean_dec(v_r_1252_);
lean_dec(v_v_1250_);
lean_dec(v_k_1249_);
lean_dec(v_size_1248_);
lean_dec_ref_known(v_r_1241_, 5);
lean_del_object(v___x_1243_);
lean_dec(v_v_1239_);
lean_dec(v_k_1238_);
v___x_1331_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1332_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1331_);
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_size_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_size_1339_ = lean_ctor_get(v_r_1241_, 0);
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_nat_add(v___x_1340_, v_size_1339_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 3, v___x_1246_);
lean_ctor_set(v___x_1243_, 0, v___x_1341_);
v___x_1343_ = v___x_1243_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_r_1241_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_l_1345_; 
v_l_1345_ = lean_ctor_get(v___x_1246_, 3);
if (lean_obj_tag(v_l_1345_) == 0)
{
lean_object* v_r_1346_; 
lean_inc_ref(v_l_1345_);
v_r_1346_ = lean_ctor_get(v___x_1246_, 4);
lean_inc(v_r_1346_);
if (lean_obj_tag(v_r_1346_) == 0)
{
lean_object* v_size_1347_; lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1363_; 
v_size_1347_ = lean_ctor_get(v___x_1246_, 0);
v_k_1348_ = lean_ctor_get(v___x_1246_, 1);
v_v_1349_ = lean_ctor_get(v___x_1246_, 2);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1364_ = lean_ctor_get(v___x_1246_, 4);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v___x_1246_, 3);
lean_dec(v_unused_1365_);
v___x_1351_ = v___x_1246_;
v_isShared_1352_ = v_isSharedCheck_1363_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_v_1349_);
lean_inc(v_k_1348_);
lean_inc(v_size_1347_);
lean_dec(v___x_1246_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1363_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_size_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v_size_1353_ = lean_ctor_get(v_r_1346_, 0);
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v___x_1354_, v_size_1347_);
lean_dec(v_size_1347_);
v___x_1356_ = lean_nat_add(v___x_1354_, v_size_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 4, v_r_1241_);
lean_ctor_set(v___x_1351_, 3, v_r_1346_);
lean_ctor_set(v___x_1351_, 2, v_v_1239_);
lean_ctor_set(v___x_1351_, 1, v_k_1238_);
lean_ctor_set(v___x_1351_, 0, v___x_1356_);
v___x_1358_ = v___x_1351_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_r_1346_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1241_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1358_);
lean_ctor_set(v___x_1243_, 3, v_l_1345_);
lean_ctor_set(v___x_1243_, 2, v_v_1349_);
lean_ctor_set(v___x_1243_, 1, v_k_1348_);
lean_ctor_set(v___x_1243_, 0, v___x_1355_);
v___x_1360_ = v___x_1243_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_l_1345_);
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
else
{
lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1379_; 
v_k_1366_ = lean_ctor_get(v___x_1246_, 1);
v_v_1367_ = lean_ctor_get(v___x_1246_, 2);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; 
v_unused_1380_ = lean_ctor_get(v___x_1246_, 4);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v___x_1246_, 3);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v___x_1246_, 0);
lean_dec(v_unused_1382_);
v___x_1369_ = v___x_1246_;
v_isShared_1370_ = v_isSharedCheck_1379_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_v_1367_);
lean_inc(v_k_1366_);
lean_dec(v___x_1246_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1379_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(3u);
v___x_1372_ = lean_unsigned_to_nat(1u);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 3, v_r_1346_);
lean_ctor_set(v___x_1369_, 2, v_v_1239_);
lean_ctor_set(v___x_1369_, 1, v_k_1238_);
lean_ctor_set(v___x_1369_, 0, v___x_1372_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_r_1346_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_r_1346_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1374_);
lean_ctor_set(v___x_1243_, 3, v_l_1345_);
lean_ctor_set(v___x_1243_, 2, v_v_1367_);
lean_ctor_set(v___x_1243_, 1, v_k_1366_);
lean_ctor_set(v___x_1243_, 0, v___x_1371_);
v___x_1376_ = v___x_1243_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_r_1383_; 
v_r_1383_ = lean_ctor_get(v___x_1246_, 4);
lean_inc(v_r_1383_);
if (lean_obj_tag(v_r_1383_) == 0)
{
lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1409_; 
lean_inc(v_l_1345_);
v_k_1384_ = lean_ctor_get(v___x_1246_, 1);
v_v_1385_ = lean_ctor_get(v___x_1246_, 2);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; 
v_unused_1410_ = lean_ctor_get(v___x_1246_, 4);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v___x_1246_, 3);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v___x_1246_, 0);
lean_dec(v_unused_1412_);
v___x_1387_ = v___x_1246_;
v_isShared_1388_ = v_isSharedCheck_1409_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_dec(v___x_1246_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1409_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1405_; 
v_k_1389_ = lean_ctor_get(v_r_1383_, 1);
v_v_1390_ = lean_ctor_get(v_r_1383_, 2);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_r_1383_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; lean_object* v_unused_1407_; lean_object* v_unused_1408_; 
v_unused_1406_ = lean_ctor_get(v_r_1383_, 4);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_r_1383_, 3);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_r_1383_, 0);
lean_dec(v_unused_1408_);
v___x_1392_ = v_r_1383_;
v_isShared_1393_ = v_isSharedCheck_1405_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_v_1390_);
lean_inc(v_k_1389_);
lean_dec(v_r_1383_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1405_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = lean_unsigned_to_nat(3u);
v___x_1395_ = lean_unsigned_to_nat(1u);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1345_);
lean_ctor_set(v___x_1392_, 3, v_l_1345_);
lean_ctor_set(v___x_1392_, 2, v_v_1385_);
lean_ctor_set(v___x_1392_, 1, v_k_1384_);
lean_ctor_set(v___x_1392_, 0, v___x_1395_);
v___x_1397_ = v___x_1392_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_l_1345_);
v___x_1397_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 4, v_l_1345_);
lean_ctor_set(v___x_1387_, 2, v_v_1239_);
lean_ctor_set(v___x_1387_, 1, v_k_1238_);
lean_ctor_set(v___x_1387_, 0, v___x_1395_);
v___x_1399_ = v___x_1387_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_l_1345_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1399_);
lean_ctor_set(v___x_1243_, 3, v___x_1397_);
lean_ctor_set(v___x_1243_, 2, v_v_1390_);
lean_ctor_set(v___x_1243_, 1, v_k_1389_);
lean_ctor_set(v___x_1243_, 0, v___x_1394_);
v___x_1401_ = v___x_1243_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_unsigned_to_nat(2u);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v_r_1383_);
lean_ctor_set(v___x_1243_, 3, v___x_1246_);
lean_ctor_set(v___x_1243_, 0, v___x_1413_);
v___x_1415_ = v___x_1243_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_r_1383_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_unsigned_to_nat(1u);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1246_);
lean_ctor_set(v___x_1243_, 3, v___x_1246_);
lean_ctor_set(v___x_1243_, 0, v___x_1417_);
v___x_1419_ = v___x_1243_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v___x_1246_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
case 1:
{
lean_object* v___x_1422_; 
lean_dec(v_v_1239_);
lean_dec(v_k_1238_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 2, v_v_1235_);
lean_ctor_set(v___x_1243_, 1, v_k_1234_);
v___x_1422_ = v___x_1243_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_size_1237_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1234_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1235_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_r_1241_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
default: 
{
lean_object* v___x_1424_; 
lean_dec(v_size_1237_);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1234_, v_v_1235_, v_r_1241_);
if (lean_obj_tag(v_l_1240_) == 0)
{
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_size_1425_; lean_object* v_size_1426_; lean_object* v_k_1427_; lean_object* v_v_1428_; lean_object* v_l_1429_; lean_object* v_r_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_size_1425_ = lean_ctor_get(v_l_1240_, 0);
v_size_1426_ = lean_ctor_get(v___x_1424_, 0);
v_k_1427_ = lean_ctor_get(v___x_1424_, 1);
v_v_1428_ = lean_ctor_get(v___x_1424_, 2);
v_l_1429_ = lean_ctor_get(v___x_1424_, 3);
lean_inc(v_l_1429_);
v_r_1430_ = lean_ctor_get(v___x_1424_, 4);
v___x_1431_ = lean_unsigned_to_nat(3u);
v___x_1432_ = lean_nat_mul(v___x_1431_, v_size_1425_);
v___x_1433_ = lean_nat_dec_lt(v___x_1432_, v_size_1426_);
lean_dec(v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_dec(v_l_1429_);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v___x_1434_, v_size_1425_);
v___x_1436_ = lean_nat_add(v___x_1435_, v_size_1426_);
lean_dec(v___x_1435_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1424_);
lean_ctor_set(v___x_1243_, 0, v___x_1436_);
v___x_1438_ = v___x_1243_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v___x_1424_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1509_; 
lean_inc(v_r_1430_);
lean_inc(v_v_1428_);
lean_inc(v_k_1427_);
lean_inc(v_size_1426_);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1510_ = lean_ctor_get(v___x_1424_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v___x_1424_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v___x_1424_, 2);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v___x_1424_, 1);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v___x_1424_, 0);
lean_dec(v_unused_1514_);
v___x_1441_ = v___x_1424_;
v_isShared_1442_ = v_isSharedCheck_1509_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v___x_1424_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1509_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
if (lean_obj_tag(v_l_1429_) == 0)
{
if (lean_obj_tag(v_r_1430_) == 0)
{
lean_object* v_size_1443_; lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v_l_1446_; lean_object* v_r_1447_; lean_object* v_size_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_size_1443_ = lean_ctor_get(v_l_1429_, 0);
v_k_1444_ = lean_ctor_get(v_l_1429_, 1);
v_v_1445_ = lean_ctor_get(v_l_1429_, 2);
v_l_1446_ = lean_ctor_get(v_l_1429_, 3);
v_r_1447_ = lean_ctor_get(v_l_1429_, 4);
v_size_1448_ = lean_ctor_get(v_r_1430_, 0);
v___x_1449_ = lean_unsigned_to_nat(2u);
v___x_1450_ = lean_nat_mul(v___x_1449_, v_size_1448_);
v___x_1451_ = lean_nat_dec_lt(v_size_1443_, v___x_1450_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1480_; 
lean_inc(v_r_1447_);
lean_inc(v_l_1446_);
lean_inc(v_v_1445_);
lean_inc(v_k_1444_);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_l_1429_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1481_ = lean_ctor_get(v_l_1429_, 4);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_l_1429_, 3);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_l_1429_, 2);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1429_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_l_1429_, 0);
lean_dec(v_unused_1485_);
v___x_1453_ = v_l_1429_;
v_isShared_1454_ = v_isSharedCheck_1480_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_l_1429_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1480_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1470_; 
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v___x_1455_, v_size_1425_);
v___x_1457_ = lean_nat_add(v___x_1456_, v_size_1426_);
lean_dec(v_size_1426_);
if (lean_obj_tag(v_l_1446_) == 0)
{
lean_object* v_size_1478_; 
v_size_1478_ = lean_ctor_get(v_l_1446_, 0);
lean_inc(v_size_1478_);
v___y_1470_ = v_size_1478_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___y_1470_ = v___x_1479_;
goto v___jp_1469_;
}
v___jp_1458_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_nat_add(v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec(v___y_1460_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_r_1430_);
lean_ctor_set(v___x_1453_, 3, v_r_1447_);
lean_ctor_set(v___x_1453_, 2, v_v_1428_);
lean_ctor_set(v___x_1453_, 1, v_k_1427_);
lean_ctor_set(v___x_1453_, 0, v___x_1462_);
v___x_1464_ = v___x_1453_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1427_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1428_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_r_1430_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1464_);
lean_ctor_set(v___x_1441_, 3, v___y_1459_);
lean_ctor_set(v___x_1441_, 2, v_v_1445_);
lean_ctor_set(v___x_1441_, 1, v_k_1444_);
lean_ctor_set(v___x_1441_, 0, v___x_1457_);
v___x_1466_ = v___x_1441_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___y_1459_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
v___jp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_nat_add(v___x_1456_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec(v___x_1456_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v_l_1446_);
lean_ctor_set(v___x_1243_, 0, v___x_1471_);
v___x_1473_ = v___x_1243_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_l_1446_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_nat_add(v___x_1455_, v_size_1448_);
if (lean_obj_tag(v_r_1447_) == 0)
{
lean_object* v_size_1475_; 
v_size_1475_ = lean_ctor_get(v_r_1447_, 0);
lean_inc(v_size_1475_);
v___y_1459_ = v___x_1473_;
v___y_1460_ = v___x_1474_;
v___y_1461_ = v_size_1475_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_unsigned_to_nat(0u);
v___y_1459_ = v___x_1473_;
v___y_1460_ = v___x_1474_;
v___y_1461_ = v___x_1476_;
goto v___jp_1458_;
}
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_del_object(v___x_1243_);
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v___x_1486_, v_size_1425_);
v___x_1488_ = lean_nat_add(v___x_1487_, v_size_1426_);
lean_dec(v_size_1426_);
v___x_1489_ = lean_nat_add(v___x_1487_, v_size_1443_);
lean_dec(v___x_1487_);
lean_inc_ref(v_l_1240_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_l_1429_);
lean_ctor_set(v___x_1441_, 3, v_l_1240_);
lean_ctor_set(v___x_1441_, 2, v_v_1239_);
lean_ctor_set(v___x_1441_, 1, v_k_1238_);
lean_ctor_set(v___x_1441_, 0, v___x_1489_);
v___x_1491_ = v___x_1441_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_l_1429_);
v___x_1491_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
v_isSharedCheck_1498_ = !lean_is_exclusive(v_l_1240_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1499_ = lean_ctor_get(v_l_1240_, 4);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_l_1240_, 3);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_l_1240_, 2);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_l_1240_, 1);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_l_1240_, 0);
lean_dec(v_unused_1503_);
v___x_1493_ = v_l_1240_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_dec(v_l_1240_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_r_1430_);
lean_ctor_set(v___x_1493_, 3, v___x_1491_);
lean_ctor_set(v___x_1493_, 2, v_v_1428_);
lean_ctor_set(v___x_1493_, 1, v_k_1427_);
lean_ctor_set(v___x_1493_, 0, v___x_1488_);
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1427_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1428_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1430_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref_known(v_l_1429_, 5);
lean_del_object(v___x_1441_);
lean_dec(v_v_1428_);
lean_dec(v_k_1427_);
lean_dec(v_size_1426_);
lean_dec_ref_known(v_l_1240_, 5);
lean_del_object(v___x_1243_);
lean_dec(v_v_1239_);
lean_dec(v_k_1238_);
v___x_1505_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1506_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1505_);
return v___x_1506_;
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1441_);
lean_dec(v_r_1430_);
lean_dec(v_v_1428_);
lean_dec(v_k_1427_);
lean_dec(v_size_1426_);
lean_dec_ref_known(v_l_1240_, 5);
lean_del_object(v___x_1243_);
lean_dec(v_v_1239_);
lean_dec(v_k_1238_);
v___x_1507_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1508_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1507_);
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_size_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v_size_1515_ = lean_ctor_get(v_l_1240_, 0);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v___x_1516_, v_size_1515_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1424_);
lean_ctor_set(v___x_1243_, 0, v___x_1517_);
v___x_1519_ = v___x_1243_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v___x_1424_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_l_1521_; 
v_l_1521_ = lean_ctor_get(v___x_1424_, 3);
lean_inc(v_l_1521_);
if (lean_obj_tag(v_l_1521_) == 0)
{
lean_object* v_r_1522_; 
v_r_1522_ = lean_ctor_get(v___x_1424_, 4);
lean_inc(v_r_1522_);
if (lean_obj_tag(v_r_1522_) == 0)
{
lean_object* v_size_1523_; lean_object* v_k_1524_; lean_object* v_v_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1539_; 
v_size_1523_ = lean_ctor_get(v___x_1424_, 0);
v_k_1524_ = lean_ctor_get(v___x_1424_, 1);
v_v_1525_ = lean_ctor_get(v___x_1424_, 2);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; lean_object* v_unused_1541_; 
v_unused_1540_ = lean_ctor_get(v___x_1424_, 4);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v___x_1424_, 3);
lean_dec(v_unused_1541_);
v___x_1527_ = v___x_1424_;
v_isShared_1528_ = v_isSharedCheck_1539_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_v_1525_);
lean_inc(v_k_1524_);
lean_inc(v_size_1523_);
lean_dec(v___x_1424_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1539_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_size_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v_size_1529_ = lean_ctor_get(v_l_1521_, 0);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_nat_add(v___x_1530_, v_size_1523_);
lean_dec(v_size_1523_);
v___x_1532_ = lean_nat_add(v___x_1530_, v_size_1529_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 4, v_l_1521_);
lean_ctor_set(v___x_1527_, 3, v_l_1240_);
lean_ctor_set(v___x_1527_, 2, v_v_1239_);
lean_ctor_set(v___x_1527_, 1, v_k_1238_);
lean_ctor_set(v___x_1527_, 0, v___x_1532_);
v___x_1534_ = v___x_1527_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_l_1240_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_l_1521_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v_r_1522_);
lean_ctor_set(v___x_1243_, 3, v___x_1534_);
lean_ctor_set(v___x_1243_, 2, v_v_1525_);
lean_ctor_set(v___x_1243_, 1, v_k_1524_);
lean_ctor_set(v___x_1243_, 0, v___x_1531_);
v___x_1536_ = v___x_1243_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1524_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1525_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_r_1522_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1567_; 
v_k_1542_ = lean_ctor_get(v___x_1424_, 1);
v_v_1543_ = lean_ctor_get(v___x_1424_, 2);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1568_ = lean_ctor_get(v___x_1424_, 4);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v___x_1424_, 3);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v___x_1424_, 0);
lean_dec(v_unused_1570_);
v___x_1545_ = v___x_1424_;
v_isShared_1546_ = v_isSharedCheck_1567_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
lean_dec(v___x_1424_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1567_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1563_; 
v_k_1547_ = lean_ctor_get(v_l_1521_, 1);
v_v_1548_ = lean_ctor_get(v_l_1521_, 2);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_l_1521_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1564_ = lean_ctor_get(v_l_1521_, 4);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_l_1521_, 3);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_l_1521_, 0);
lean_dec(v_unused_1566_);
v___x_1550_ = v_l_1521_;
v_isShared_1551_ = v_isSharedCheck_1563_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_v_1548_);
lean_inc(v_k_1547_);
lean_dec(v_l_1521_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1563_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1552_ = lean_unsigned_to_nat(3u);
v___x_1553_ = lean_unsigned_to_nat(1u);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_r_1522_);
lean_ctor_set(v___x_1550_, 3, v_r_1522_);
lean_ctor_set(v___x_1550_, 2, v_v_1239_);
lean_ctor_set(v___x_1550_, 1, v_k_1238_);
lean_ctor_set(v___x_1550_, 0, v___x_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_r_1522_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_r_1522_);
v___x_1555_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 3, v_r_1522_);
lean_ctor_set(v___x_1545_, 0, v___x_1553_);
v___x_1557_ = v___x_1545_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_r_1522_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_r_1522_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1557_);
lean_ctor_set(v___x_1243_, 3, v___x_1555_);
lean_ctor_set(v___x_1243_, 2, v_v_1548_);
lean_ctor_set(v___x_1243_, 1, v_k_1547_);
lean_ctor_set(v___x_1243_, 0, v___x_1552_);
v___x_1559_ = v___x_1243_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1571_; 
v_r_1571_ = lean_ctor_get(v___x_1424_, 4);
lean_inc(v_r_1571_);
if (lean_obj_tag(v_r_1571_) == 0)
{
lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1585_; 
v_k_1572_ = lean_ctor_get(v___x_1424_, 1);
v_v_1573_ = lean_ctor_get(v___x_1424_, 2);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; 
v_unused_1586_ = lean_ctor_get(v___x_1424_, 4);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v___x_1424_, 3);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v___x_1424_, 0);
lean_dec(v_unused_1588_);
v___x_1575_ = v___x_1424_;
v_isShared_1576_ = v_isSharedCheck_1585_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
lean_dec(v___x_1424_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1585_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1577_ = lean_unsigned_to_nat(3u);
v___x_1578_ = lean_unsigned_to_nat(1u);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 4, v_l_1521_);
lean_ctor_set(v___x_1575_, 2, v_v_1239_);
lean_ctor_set(v___x_1575_, 1, v_k_1238_);
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_l_1521_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_l_1521_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v_r_1571_);
lean_ctor_set(v___x_1243_, 3, v___x_1580_);
lean_ctor_set(v___x_1243_, 2, v_v_1573_);
lean_ctor_set(v___x_1243_, 1, v_k_1572_);
lean_ctor_set(v___x_1243_, 0, v___x_1577_);
v___x_1582_ = v___x_1243_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_r_1571_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = lean_unsigned_to_nat(2u);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1424_);
lean_ctor_set(v___x_1243_, 3, v_r_1571_);
lean_ctor_set(v___x_1243_, 0, v___x_1589_);
v___x_1591_ = v___x_1243_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_r_1571_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v___x_1424_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 4, v___x_1424_);
lean_ctor_set(v___x_1243_, 3, v___x_1424_);
lean_ctor_set(v___x_1243_, 0, v___x_1593_);
v___x_1595_ = v___x_1243_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v___x_1424_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v_k_1234_);
lean_ctor_set(v___x_1599_, 2, v_v_1235_);
lean_ctor_set(v___x_1599_, 3, v_t_1236_);
lean_ctor_set(v___x_1599_, 4, v_t_1236_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1600_, lean_object* v_x_1601_){
_start:
{
if (lean_obj_tag(v_x_1601_) == 0)
{
lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v_l_1604_; lean_object* v_r_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_k_1602_ = lean_ctor_get(v_x_1601_, 1);
lean_inc(v_k_1602_);
v_v_1603_ = lean_ctor_get(v_x_1601_, 2);
lean_inc(v_v_1603_);
v_l_1604_ = lean_ctor_get(v_x_1601_, 3);
lean_inc(v_l_1604_);
v_r_1605_ = lean_ctor_get(v_x_1601_, 4);
lean_inc(v_r_1605_);
lean_dec_ref_known(v_x_1601_, 5);
v___x_1606_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1600_, v_l_1604_);
v___x_1607_ = 1;
v___x_1608_ = l_Lean_Name_toString(v_k_1602_, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_v_1603_);
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1608_, v___x_1609_, v___x_1606_);
v_init_1600_ = v___x_1610_;
v_x_1601_ = v_r_1605_;
goto _start;
}
else
{
return v_init_1600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_box(1);
v___x_1614_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1613_, v_m_1612_);
v___x_1615_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
if (lean_obj_tag(v_a_1616_) == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_array_to_list(v_a_1617_);
return v___x_1618_;
}
else
{
lean_object* v_head_1619_; lean_object* v_tail_1620_; lean_object* v___x_1621_; 
v_head_1619_ = lean_ctor_get(v_a_1616_, 0);
lean_inc(v_head_1619_);
v_tail_1620_ = lean_ctor_get(v_a_1616_, 1);
lean_inc(v_tail_1620_);
lean_dec_ref_known(v_a_1616_, 2);
v___x_1621_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1617_, v_head_1619_);
v_a_1616_ = v_tail_1620_;
v_a_1617_ = v___x_1621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1631_){
_start:
{
lean_object* v_idx_1632_; lean_object* v_name_1633_; lean_object* v_platform_1634_; lean_object* v_leanHash_1635_; uint64_t v_configHash_1636_; lean_object* v_options_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_idx_1632_ = lean_ctor_get(v_x_1631_, 0);
lean_inc(v_idx_1632_);
v_name_1633_ = lean_ctor_get(v_x_1631_, 1);
lean_inc(v_name_1633_);
v_platform_1634_ = lean_ctor_get(v_x_1631_, 2);
lean_inc_ref(v_platform_1634_);
v_leanHash_1635_ = lean_ctor_get(v_x_1631_, 3);
lean_inc_ref(v_leanHash_1635_);
v_configHash_1636_ = lean_ctor_get_uint64(v_x_1631_, sizeof(void*)*5);
v_options_1637_ = lean_ctor_get(v_x_1631_, 4);
lean_inc(v_options_1637_);
lean_dec_ref(v_x_1631_);
v___x_1638_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1639_ = l_Lean_JsonNumber_fromNat(v_idx_1632_);
v___x_1640_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1638_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_box(0);
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1645_ = 1;
v___x_1646_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1633_, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1644_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1642_);
v___x_1650_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_platform_1634_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1642_);
v___x_1654_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_leanHash_1635_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1642_);
v___x_1658_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1659_ = l_Lake_lowerHexUInt64(v_configHash_1636_);
v___x_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1658_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v___x_1642_);
v___x_1663_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1664_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1637_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1642_);
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v___x_1642_);
v___x_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1662_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1657_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1653_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1649_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1643_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1674_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1672_, v___x_1673_);
v___x_1675_ = l_Lean_Json_mkObj(v___x_1674_);
lean_dec(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1676_, lean_object* v_msg_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1679_, lean_object* v_k_1680_, lean_object* v_v_1681_, lean_object* v_t_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1680_, v_v_1681_, v_t_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1684_, lean_object* v_t_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1684_, v_t_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1689_, lean_object* v_k_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = l_Lean_Json_getObjValD(v_j_1689_, v_k_1690_);
v___x_1692_ = l_Lean_Json_getNat_x3f(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1693_, v_k_1694_);
lean_dec_ref(v_k_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1696_, lean_object* v_k_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = l_Lean_Json_getObjValD(v_j_1696_, v_k_1697_);
v___x_1699_ = l_Lean_Name_fromJson_x3f(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1700_, lean_object* v_k_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1700_, v_k_1701_);
lean_dec_ref(v_k_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1703_, lean_object* v_k_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = l_Lean_Json_getObjValD(v_j_1703_, v_k_1704_);
v___x_1706_ = l_Lean_Json_getStr_x3f(v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1707_, lean_object* v_k_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1707_, v_k_1708_);
lean_dec_ref(v_k_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1710_, lean_object* v_k_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = l_Lean_Json_getObjValD(v_j_1710_, v_k_1711_);
v___x_1713_ = l_Lake_Hash_fromJson_x3f(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1714_, lean_object* v_k_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1714_, v_k_1715_);
lean_dec_ref(v_k_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1720_, lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
lean_object* v_k_1722_; lean_object* v_v_1723_; lean_object* v_l_1724_; lean_object* v_r_1725_; lean_object* v___x_1726_; 
v_k_1722_ = lean_ctor_get(v_x_1721_, 1);
lean_inc(v_k_1722_);
v_v_1723_ = lean_ctor_get(v_x_1721_, 2);
lean_inc(v_v_1723_);
v_l_1724_ = lean_ctor_get(v_x_1721_, 3);
lean_inc(v_l_1724_);
v_r_1725_ = lean_ctor_get(v_x_1721_, 4);
lean_inc(v_r_1725_);
lean_dec_ref_known(v_x_1721_, 5);
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1720_, v_l_1724_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_dec(v_r_1725_);
lean_dec(v_v_1723_);
lean_dec(v_k_1722_);
return v___x_1726_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1767_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1767_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1767_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1732_ = lean_string_dec_eq(v_k_1722_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_object* v_n_1733_; uint8_t v___x_1734_; 
lean_inc(v_k_1722_);
v_n_1733_ = l_String_toName(v_k_1722_);
v___x_1734_ = l_Lean_Name_isAnonymous(v_n_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
lean_del_object(v___x_1729_);
lean_dec(v_k_1722_);
v___x_1735_ = l_Lean_Json_getStr_x3f(v_v_1723_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_n_1733_);
lean_dec(v_a_1727_);
lean_dec(v_r_1725_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1745_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1733_, v_a_1744_, v_a_1727_);
v_init_1720_ = v___x_1745_;
v_x_1721_ = v_r_1725_;
goto _start;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec(v_n_1733_);
lean_dec(v_a_1727_);
lean_dec(v_r_1725_);
lean_dec(v_v_1723_);
v___x_1747_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1748_ = lean_string_append(v___x_1747_, v_k_1722_);
lean_dec(v_k_1722_);
v___x_1749_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1750_);
v___x_1752_ = v___x_1729_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_object* v___x_1754_; 
lean_del_object(v___x_1729_);
lean_dec(v_k_1722_);
v___x_1754_ = l_Lean_Json_getStr_x3f(v_v_1723_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1727_);
lean_dec(v_r_1725_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_a_1763_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1764_ = lean_box(0);
v___x_1765_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1764_, v_a_1763_, v_a_1727_);
v_init_1720_ = v___x_1765_;
v_x_1721_ = v_r_1725_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_init_1720_);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 5)
{
lean_object* v_kvPairs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_kvPairs_1771_ = lean_ctor_get(v_x_1770_, 0);
lean_inc(v_kvPairs_1771_);
lean_dec_ref_known(v_x_1770_, 1);
v___x_1772_ = lean_box(1);
v___x_1773_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1772_, v_kvPairs_1771_);
return v___x_1773_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1774_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1775_ = lean_unsigned_to_nat(80u);
v___x_1776_ = l_Lean_Json_pretty(v_x_1770_, v___x_1775_);
v___x_1777_ = lean_string_append(v___x_1774_, v___x_1776_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1781_, lean_object* v_k_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = l_Lean_Json_getObjValD(v_j_1781_, v_k_1782_);
v___x_1784_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1785_, lean_object* v_k_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1785_, v_k_1786_);
lean_dec_ref(v_k_1786_);
return v_res_1787_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = 1;
v___x_1817_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1821_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1822_ = lean_string_append(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = 1;
v___x_1826_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1827_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1826_, v___x_1825_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1829_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1830_ = lean_string_append(v___x_1829_, v___x_1828_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1833_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1834_ = lean_string_append(v___x_1833_, v___x_1832_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = 1;
v___x_1838_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1841_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1842_ = lean_string_append(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1844_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1845_ = lean_string_append(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = 1;
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1852_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1853_ = lean_string_append(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1855_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1856_ = lean_string_append(v___x_1855_, v___x_1854_);
return v___x_1856_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = 1;
v___x_1860_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1860_, v___x_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1863_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1864_ = lean_string_append(v___x_1863_, v___x_1862_);
return v___x_1864_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1866_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1867_ = lean_string_append(v___x_1866_, v___x_1865_);
return v___x_1867_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = 1;
v___x_1871_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1871_, v___x_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1874_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1875_ = lean_string_append(v___x_1874_, v___x_1873_);
return v___x_1875_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1877_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1878_ = lean_string_append(v___x_1877_, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = 1;
v___x_1882_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1883_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1882_, v___x_1881_);
return v___x_1883_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1885_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1886_ = lean_string_append(v___x_1885_, v___x_1884_);
return v___x_1886_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1888_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1889_ = lean_string_append(v___x_1888_, v___x_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1890_);
v___x_1892_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1890_, v___x_1891_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_json_1890_);
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
v___x_1897_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
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
lean_dec(v_json_1890_);
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
lean_dec_ref_known(v___x_1892_, 1);
v___x_1912_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1890_);
v___x_1913_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1890_, v___x_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1911_);
lean_dec(v_json_1890_);
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
v___x_1918_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
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
lean_dec(v_json_1890_);
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
lean_dec_ref_known(v___x_1913_, 1);
v___x_1933_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1890_);
v___x_1934_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1890_, v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_json_1890_);
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
v___x_1939_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
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
lean_dec(v_json_1890_);
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
lean_dec_ref_known(v___x_1934_, 1);
v___x_1954_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1890_);
v___x_1955_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1890_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_json_1890_);
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
v___x_1960_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
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
lean_dec(v_json_1890_);
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
lean_dec_ref_known(v___x_1955_, 1);
v___x_1975_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1890_);
v___x_1976_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1890_, v___x_1975_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_a_1974_);
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
lean_dec(v_json_1890_);
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
v___x_1981_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
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
lean_dec(v_json_1890_);
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
lean_object* v_a_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_a_1995_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1996_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1997_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1890_, v___x_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1995_);
lean_dec(v_a_1974_);
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_2003_ = lean_string_append(v___x_2002_, v_a_1998_);
lean_dec(v_a_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1995_);
lean_dec(v_a_1974_);
lean_dec(v_a_1953_);
lean_dec(v_a_1932_);
lean_dec(v_a_1911_);
v_a_2008_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1997_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1997_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 0);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2025_; 
v_a_2016_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2018_ = v___x_1997_;
v_isShared_2019_ = v_isSharedCheck_2025_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1997_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2025_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; uint64_t v___x_2021_; lean_object* v___x_2023_; 
v___x_2020_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2020_, 0, v_a_1911_);
lean_ctor_set(v___x_2020_, 1, v_a_1932_);
lean_ctor_set(v___x_2020_, 2, v_a_1953_);
lean_ctor_set(v___x_2020_, 3, v_a_1974_);
lean_ctor_set(v___x_2020_, 4, v_a_2016_);
v___x_2021_ = lean_unbox_uint64(v_a_1995_);
lean_dec(v_a_1995_);
lean_ctor_set_uint64(v___x_2020_, sizeof(void*)*5, v___x_2021_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2023_ = v___x_2018_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2020_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
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
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_2030_ = lean_mk_io_user_error(v___x_2029_);
return v___x_2030_;
}
}
lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_2031_, lean_object* v___x_2032_, lean_object* v_h_2033_){
_start:
{
uint8_t v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = 1;
v___x_2036_ = lean_io_prim_handle_mk(v___x_2031_, v___x_2035_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = 1;
v___x_2039_ = lean_io_prim_handle_try_lock(v_a_2037_, v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; uint8_t v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec(v_a_2037_);
v___x_2042_ = lean_io_prim_handle_unlock(v_h_2033_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2042_, 0);
lean_dec(v_unused_2051_);
v___x_2044_ = v___x_2042_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v___x_2042_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 0, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
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
v_a_2052_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2042_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2042_);
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
lean_object* v___x_2060_; 
v___x_2060_ = lean_io_prim_handle_unlock(v_h_2033_);
if (lean_obj_tag(v___x_2060_) == 0)
{
uint8_t v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref_known(v___x_2060_, 1);
v___x_2061_ = 3;
v___x_2062_ = lean_io_prim_handle_mk(v___x_2032_, v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = lean_io_prim_handle_lock(v_a_2063_, v___x_2038_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2065_; 
lean_dec_ref_known(v___x_2064_, 1);
v___x_2065_ = lean_io_prim_handle_unlock(v_a_2037_);
lean_dec(v_a_2037_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2073_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v_a_2063_);
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2063_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2063_);
v_a_2074_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2065_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2065_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_2063_);
lean_dec(v_a_2037_);
v_a_2082_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2064_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2064_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_dec(v_a_2037_);
return v___x_2062_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_a_2037_);
v_a_2090_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2060_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2060_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_a_2037_);
v_a_2098_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2039_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2039_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
return v___x_2036_;
}
}
}
LEAN_EXPORT void l_Lake_importConfigFile___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2031_ = stack[0].m_obj;
lean_object* v___x_2032_ = stack[1].m_obj;
lean_object* v_h_2033_ = stack[2].m_obj;
lean_object* v_res_2106_;
v_res_2106_ = l_Lake_importConfigFile___lam__0(v___x_2031_, v___x_2032_, v_h_2033_);
stack->m_obj
 = v_res_2106_;
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v_h_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lake_importConfigFile___lam__0(v___x_2107_, v___x_2108_, v_h_2109_);
lean_dec(v_h_2109_);
lean_dec_ref(v___x_2108_);
lean_dec_ref(v___x_2107_);
return v_res_2111_;
}
}
lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___y_2124_; lean_object* v_a_2125_; lean_object* v_lakeEnv_2127_; lean_object* v_wsDir_2128_; lean_object* v_pkgIdx_2129_; lean_object* v_pkgName_2130_; lean_object* v_pkgDir_2131_; lean_object* v_configFile_2132_; lean_object* v_lakeOpts_2133_; lean_object* v_leanOpts_2134_; uint8_t v_reconfigure_2135_; lean_object* v___x_2136_; 
v_lakeEnv_2127_ = lean_ctor_get(v_cfg_2120_, 0);
lean_inc_ref(v_lakeEnv_2127_);
v_wsDir_2128_ = lean_ctor_get(v_cfg_2120_, 2);
lean_inc_ref(v_wsDir_2128_);
v_pkgIdx_2129_ = lean_ctor_get(v_cfg_2120_, 3);
lean_inc(v_pkgIdx_2129_);
v_pkgName_2130_ = lean_ctor_get(v_cfg_2120_, 4);
lean_inc(v_pkgName_2130_);
v_pkgDir_2131_ = lean_ctor_get(v_cfg_2120_, 6);
lean_inc_ref(v_pkgDir_2131_);
v_configFile_2132_ = lean_ctor_get(v_cfg_2120_, 8);
lean_inc_ref_n(v_configFile_2132_, 2);
v_lakeOpts_2133_ = lean_ctor_get(v_cfg_2120_, 12);
lean_inc(v_lakeOpts_2133_);
v_leanOpts_2134_ = lean_ctor_get(v_cfg_2120_, 13);
lean_inc_ref(v_leanOpts_2134_);
v_reconfigure_2135_ = lean_ctor_get_uint8(v_cfg_2120_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2120_);
v___x_2136_ = l_System_FilePath_fileName(v_configFile_2132_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_wsDir_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2137_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2138_ = lean_array_get_size(v_a_2121_);
v___x_2139_ = lean_array_push(v_a_2121_, v___x_2137_);
v___x_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
return v___x_2140_;
}
else
{
lean_object* v_val_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_configDir_2147_; lean_object* v___x_2148_; 
v_val_2141_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2142_ = l_Lake_defaultLakeDir;
v___x_2143_ = l_Lake_joinRelative(v_wsDir_2128_, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2145_ = l_Lake_joinRelative(v___x_2143_, v___x_2144_);
lean_inc(v_pkgIdx_2129_);
v___x_2146_ = l_Nat_reprFast(v_pkgIdx_2129_);
v_configDir_2147_ = l_Lake_joinRelative(v___x_2145_, v___x_2146_);
lean_inc_ref(v_configDir_2147_);
v___x_2148_ = l_IO_FS_createDirAll(v_configDir_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2149_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2141_, 2);
v___x_2150_ = l_System_FilePath_withExtension(v_val_2141_, v___x_2149_);
lean_inc_ref_n(v_configDir_2147_, 2);
v___x_2151_ = l_Lake_joinRelative(v_configDir_2147_, v___x_2150_);
v___x_2152_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2153_ = l_System_FilePath_withExtension(v_val_2141_, v___x_2152_);
v___x_2154_ = l_Lake_joinRelative(v_configDir_2147_, v___x_2153_);
v___x_2155_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2156_ = l_System_FilePath_withExtension(v_val_2141_, v___x_2155_);
v___x_2157_ = l_Lake_joinRelative(v_configDir_2147_, v___x_2156_);
v___x_2158_ = l_Lake_computeTextFileHash(v_configFile_2132_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_h_2161_; lean_object* v_lakeOpts_2162_; lean_object* v___y_2163_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v_h_2342_; lean_object* v___y_2343_; uint8_t v___x_2431_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2431_ = l_System_FilePath_pathExists(v___x_2154_);
if (v___x_2431_ == 0)
{
uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = 1;
lean_inc_ref(v_pkgDir_2131_);
v___x_2433_ = l_Lake_joinRelative(v_pkgDir_2131_, v___x_2142_);
v___x_2434_ = l_IO_FS_createDirAll(v___x_2433_);
if (lean_obj_tag(v___x_2434_) == 0)
{
uint8_t v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref_known(v___x_2434_, 1);
v___x_2435_ = 2;
v___x_2436_ = lean_io_prim_handle_mk(v___x_2154_, v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; 
lean_dec_ref(v___x_2157_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = lean_io_prim_handle_lock(v_a_2437_, v___x_2432_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_dec_ref_known(v___x_2438_, 1);
v_h_2161_ = v_a_2437_;
v_lakeOpts_2162_ = v_lakeOpts_2133_;
v___y_2163_ = v_a_2121_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_dec(v_a_2437_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___x_2440_ = lean_io_error_to_string(v_a_2439_);
v___x_2441_ = 3;
v___x_2442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*1, v___x_2441_);
v___x_2443_ = lean_array_get_size(v_a_2121_);
v___x_2444_ = lean_array_push(v_a_2121_, v___x_2442_);
v___x_2445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
return v___x_2445_;
}
}
else
{
lean_object* v_a_2446_; 
v_a_2446_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2436_, 1);
if (lean_obj_tag(v_a_2446_) == 0)
{
uint8_t v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref_known(v_a_2446_, 2);
v___x_2447_ = 0;
v___x_2448_ = lean_io_prim_handle_mk(v___x_2154_, v___x_2447_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v_h_2342_ = v_a_2449_;
v___y_2343_ = v_a_2121_;
goto v___jp_2341_;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2450_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2451_ = lean_io_error_to_string(v_a_2450_);
v___x_2452_ = 3;
v___x_2453_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*1, v___x_2452_);
v___x_2454_ = lean_array_get_size(v_a_2121_);
v___x_2455_ = lean_array_push(v_a_2121_, v___x_2453_);
v___x_2456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
return v___x_2456_;
}
}
else
{
lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2457_ = lean_io_error_to_string(v_a_2446_);
v___x_2458_ = 3;
v___x_2459_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1, v___x_2458_);
v___x_2460_ = lean_array_get_size(v_a_2121_);
v___x_2461_ = lean_array_push(v_a_2121_, v___x_2459_);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2463_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2464_ = lean_io_error_to_string(v_a_2463_);
v___x_2465_ = 3;
v___x_2466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*1, v___x_2465_);
v___x_2467_ = lean_array_get_size(v_a_2121_);
v___x_2468_ = lean_array_push(v_a_2121_, v___x_2466_);
v___x_2469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
return v___x_2469_;
}
}
else
{
uint8_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = 0;
v___x_2471_ = lean_io_prim_handle_mk(v___x_2154_, v___x_2470_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v_h_2342_ = v_a_2472_;
v___y_2343_ = v_a_2121_;
goto v___jp_2341_;
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2473_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2474_ = lean_io_error_to_string(v_a_2473_);
v___x_2475_ = 3;
v___x_2476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*1, v___x_2475_);
v___x_2477_ = lean_array_get_size(v_a_2121_);
v___x_2478_ = lean_array_push(v_a_2121_, v___x_2476_);
v___x_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
return v___x_2479_;
}
}
v___jp_2160_:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_io_remove_file(v___x_2151_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; uint64_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref_known(v___x_2164_, 1);
lean_dec_ref(v___x_2154_);
v___x_2165_ = l_System_Platform_target;
v___x_2166_ = l_Lake_Env_leanGithash(v_lakeEnv_2127_);
lean_dec_ref(v_lakeEnv_2127_);
lean_inc(v_lakeOpts_2162_);
lean_inc(v_pkgName_2130_);
lean_inc(v_pkgIdx_2129_);
v___x_2167_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2167_, 0, v_pkgIdx_2129_);
lean_ctor_set(v___x_2167_, 1, v_pkgName_2130_);
lean_ctor_set(v___x_2167_, 2, v___x_2165_);
lean_ctor_set(v___x_2167_, 3, v___x_2166_);
lean_ctor_set(v___x_2167_, 4, v_lakeOpts_2162_);
v___x_2168_ = lean_unbox_uint64(v_a_2159_);
lean_dec(v_a_2159_);
lean_ctor_set_uint64(v___x_2167_, sizeof(void*)*5, v___x_2168_);
v___x_2169_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2167_);
v___x_2170_ = lean_unsigned_to_nat(80u);
v___x_2171_ = l_Lean_Json_pretty(v___x_2169_, v___x_2170_);
v___x_2172_ = l_IO_FS_Handle_putStrLn(v_h_2161_, v___x_2171_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2173_; 
lean_dec_ref_known(v___x_2172_, 1);
v___x_2173_ = lean_io_prim_handle_flush(v_h_2161_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2174_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2174_ = lean_io_prim_handle_truncate(v_h_2161_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v___x_2175_; 
lean_dec_ref_known(v___x_2174_, 1);
v___x_2175_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2129_, v_pkgName_2130_, v_pkgDir_2131_, v_lakeOpts_2162_, v_leanOpts_2134_, v_configFile_2132_, v___y_2163_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
v___x_2178_ = 1;
lean_inc(v_a_2176_);
v___x_2179_ = l_Lean_writeModule(v_a_2176_, v___x_2151_, v___x_2178_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2180_; 
lean_dec_ref_known(v___x_2179_, 1);
v___x_2180_ = lean_io_prim_handle_unlock(v_h_2161_);
lean_dec(v_h_2161_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_dec_ref_known(v___x_2180_, 1);
return v___x_2175_;
}
else
{
lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2193_; 
lean_inc(v_a_2177_);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2194_ = lean_ctor_get(v___x_2175_, 1);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v___x_2175_, 0);
lean_dec(v_unused_2195_);
v___x_2182_ = v___x_2175_;
v_isShared_2183_ = v_isSharedCheck_2193_;
goto v_resetjp_2181_;
}
else
{
lean_dec(v___x_2175_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2193_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_a_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v_a_2184_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2185_ = lean_io_error_to_string(v_a_2184_);
v___x_2186_ = 3;
v___x_2187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*1, v___x_2186_);
v___x_2188_ = lean_array_get_size(v_a_2177_);
v___x_2189_ = lean_array_push(v_a_2177_, v___x_2187_);
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
lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2208_; 
lean_inc(v_a_2177_);
lean_dec(v_h_2161_);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2209_ = lean_ctor_get(v___x_2175_, 1);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v___x_2175_, 0);
lean_dec(v_unused_2210_);
v___x_2197_ = v___x_2175_;
v_isShared_2198_ = v_isSharedCheck_2208_;
goto v_resetjp_2196_;
}
else
{
lean_dec(v___x_2175_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2208_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_a_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v_a_2199_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2200_ = lean_io_error_to_string(v_a_2199_);
v___x_2201_ = 3;
v___x_2202_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1, v___x_2201_);
v___x_2203_ = lean_array_get_size(v_a_2177_);
v___x_2204_ = lean_array_push(v_a_2177_, v___x_2202_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set_tag(v___x_2197_, 1);
lean_ctor_set(v___x_2197_, 1, v___x_2204_);
lean_ctor_set(v___x_2197_, 0, v___x_2203_);
v___x_2206_ = v___x_2197_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
return v___x_2175_;
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
v_a_2211_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2212_ = lean_io_error_to_string(v_a_2211_);
v___x_2213_ = 3;
v___x_2214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*1, v___x_2213_);
v___x_2215_ = lean_array_get_size(v___y_2163_);
v___x_2216_ = lean_array_push(v___y_2163_, v___x_2214_);
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
return v___x_2217_;
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
v_a_2218_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2219_ = lean_io_error_to_string(v_a_2218_);
v___x_2220_ = 3;
v___x_2221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*1, v___x_2220_);
v___x_2222_ = lean_array_get_size(v___y_2163_);
v___x_2223_ = lean_array_push(v___y_2163_, v___x_2221_);
v___x_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
return v___x_2224_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
v_a_2225_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2226_ = lean_io_error_to_string(v_a_2225_);
v___x_2227_ = 3;
v___x_2228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*1, v___x_2227_);
v___x_2229_ = lean_array_get_size(v___y_2163_);
v___x_2230_ = lean_array_push(v___y_2163_, v___x_2228_);
v___x_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
return v___x_2231_;
}
}
else
{
lean_object* v_a_2232_; 
v_a_2232_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2164_, 1);
if (lean_obj_tag(v_a_2232_) == 11)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint64_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref_known(v_a_2232_, 2);
lean_dec_ref(v___x_2154_);
v___x_2233_ = l_System_Platform_target;
v___x_2234_ = l_Lake_Env_leanGithash(v_lakeEnv_2127_);
lean_dec_ref(v_lakeEnv_2127_);
lean_inc(v_lakeOpts_2162_);
lean_inc(v_pkgName_2130_);
lean_inc(v_pkgIdx_2129_);
v___x_2235_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2235_, 0, v_pkgIdx_2129_);
lean_ctor_set(v___x_2235_, 1, v_pkgName_2130_);
lean_ctor_set(v___x_2235_, 2, v___x_2233_);
lean_ctor_set(v___x_2235_, 3, v___x_2234_);
lean_ctor_set(v___x_2235_, 4, v_lakeOpts_2162_);
v___x_2236_ = lean_unbox_uint64(v_a_2159_);
lean_dec(v_a_2159_);
lean_ctor_set_uint64(v___x_2235_, sizeof(void*)*5, v___x_2236_);
v___x_2237_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2235_);
v___x_2238_ = lean_unsigned_to_nat(80u);
v___x_2239_ = l_Lean_Json_pretty(v___x_2237_, v___x_2238_);
v___x_2240_ = l_IO_FS_Handle_putStrLn(v_h_2161_, v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2241_; 
lean_dec_ref_known(v___x_2240_, 1);
v___x_2241_ = lean_io_prim_handle_flush(v_h_2161_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v___x_2242_; 
lean_dec_ref_known(v___x_2241_, 1);
v___x_2242_ = lean_io_prim_handle_truncate(v_h_2161_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; 
lean_dec_ref_known(v___x_2242_, 1);
v___x_2243_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2129_, v_pkgName_2130_, v_pkgDir_2131_, v_lakeOpts_2162_, v_leanOpts_2134_, v_configFile_2132_, v___y_2163_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v_a_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_a_2245_ = lean_ctor_get(v___x_2243_, 1);
v___x_2246_ = 1;
lean_inc(v_a_2244_);
v___x_2247_ = l_Lean_writeModule(v_a_2244_, v___x_2151_, v___x_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; 
lean_dec_ref_known(v___x_2247_, 1);
v___x_2248_ = lean_io_prim_handle_unlock(v_h_2161_);
lean_dec(v_h_2161_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_dec_ref_known(v___x_2248_, 1);
return v___x_2243_;
}
else
{
lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2261_; 
lean_inc(v_a_2245_);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2262_ = lean_ctor_get(v___x_2243_, 1);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v___x_2243_, 0);
lean_dec(v_unused_2263_);
v___x_2250_ = v___x_2243_;
v_isShared_2251_ = v_isSharedCheck_2261_;
goto v_resetjp_2249_;
}
else
{
lean_dec(v___x_2243_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2261_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_a_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v_a_2252_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2253_ = lean_io_error_to_string(v_a_2252_);
v___x_2254_ = 3;
v___x_2255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*1, v___x_2254_);
v___x_2256_ = lean_array_get_size(v_a_2245_);
v___x_2257_ = lean_array_push(v_a_2245_, v___x_2255_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set_tag(v___x_2250_, 1);
lean_ctor_set(v___x_2250_, 1, v___x_2257_);
lean_ctor_set(v___x_2250_, 0, v___x_2256_);
v___x_2259_ = v___x_2250_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2276_; 
lean_inc(v_a_2245_);
lean_dec(v_h_2161_);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2276_ == 0)
{
lean_object* v_unused_2277_; lean_object* v_unused_2278_; 
v_unused_2277_ = lean_ctor_get(v___x_2243_, 1);
lean_dec(v_unused_2277_);
v_unused_2278_ = lean_ctor_get(v___x_2243_, 0);
lean_dec(v_unused_2278_);
v___x_2265_ = v___x_2243_;
v_isShared_2266_ = v_isSharedCheck_2276_;
goto v_resetjp_2264_;
}
else
{
lean_dec(v___x_2243_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2276_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_a_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v_a_2267_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2247_, 1);
v___x_2268_ = lean_io_error_to_string(v_a_2267_);
v___x_2269_ = 3;
v___x_2270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2269_);
v___x_2271_ = lean_array_get_size(v_a_2245_);
v___x_2272_ = lean_array_push(v_a_2245_, v___x_2270_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 1);
lean_ctor_set(v___x_2265_, 1, v___x_2272_);
lean_ctor_set(v___x_2265_, 0, v___x_2271_);
v___x_2274_ = v___x_2265_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
return v___x_2243_;
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
v_a_2279_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2242_, 1);
v___x_2280_ = lean_io_error_to_string(v_a_2279_);
v___x_2281_ = 3;
v___x_2282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*1, v___x_2281_);
v___x_2283_ = lean_array_get_size(v___y_2163_);
v___x_2284_ = lean_array_push(v___y_2163_, v___x_2282_);
v___x_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
return v___x_2285_;
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
v_a_2286_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2287_ = lean_io_error_to_string(v_a_2286_);
v___x_2288_ = 3;
v___x_2289_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set_uint8(v___x_2289_, sizeof(void*)*1, v___x_2288_);
v___x_2290_ = lean_array_get_size(v___y_2163_);
v___x_2291_ = lean_array_push(v___y_2163_, v___x_2289_);
v___x_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
return v___x_2292_;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_h_2161_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
v_a_2293_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2294_ = lean_io_error_to_string(v_a_2293_);
v___x_2295_ = 3;
v___x_2296_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*1, v___x_2295_);
v___x_2297_ = lean_array_get_size(v___y_2163_);
v___x_2298_ = lean_array_push(v___y_2163_, v___x_2296_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
return v___x_2299_;
}
}
else
{
lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_dec(v_lakeOpts_2162_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2300_ = lean_io_error_to_string(v_a_2232_);
v___x_2301_ = 3;
v___x_2302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*1, v___x_2301_);
v___x_2303_ = lean_array_get_size(v___y_2163_);
v___x_2304_ = lean_array_push(v___y_2163_, v___x_2302_);
v___x_2305_ = lean_io_prim_handle_unlock(v_h_2161_);
lean_dec(v_h_2161_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2306_; 
lean_dec_ref_known(v___x_2305_, 1);
v___x_2306_ = lean_io_remove_file(v___x_2154_);
lean_dec_ref(v___x_2154_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_dec_ref_known(v___x_2306_, 1);
v___y_2124_ = v___x_2303_;
v_a_2125_ = v___x_2304_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_io_error_to_string(v_a_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*1, v___x_2301_);
v___x_2310_ = lean_array_push(v___x_2304_, v___x_2309_);
v___y_2124_ = v___x_2303_;
v_a_2125_ = v___x_2310_;
goto v___jp_2123_;
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v___x_2154_);
v_a_2311_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2312_ = lean_io_error_to_string(v_a_2311_);
v___x_2313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*1, v___x_2301_);
v___x_2314_ = lean_array_push(v___x_2304_, v___x_2313_);
v___y_2124_ = v___x_2303_;
v_a_2125_ = v___x_2314_;
goto v___jp_2123_;
}
}
}
}
v___jp_2315_:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lake_importConfigFile___lam__0(v___x_2157_, v___x_2154_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v_h_2161_ = v_a_2319_;
v_lakeOpts_2162_ = v_lakeOpts_2133_;
v___y_2163_ = v___y_2317_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2320_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2321_ = lean_io_error_to_string(v_a_2320_);
v___x_2322_ = 3;
v___x_2323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*1, v___x_2322_);
v___x_2324_ = lean_array_get_size(v___y_2317_);
v___x_2325_ = lean_array_push(v___y_2317_, v___x_2323_);
v___x_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
return v___x_2326_;
}
}
v___jp_2327_:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lake_importConfigFile___lam__0(v___x_2157_, v___x_2154_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v_options_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v_options_2333_ = lean_ctor_get(v___y_2330_, 4);
lean_inc(v_options_2333_);
lean_dec_ref(v___y_2330_);
v_h_2161_ = v_a_2332_;
v_lakeOpts_2162_ = v_options_2333_;
v___y_2163_ = v___y_2329_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec_ref(v___y_2330_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2334_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2335_ = lean_io_error_to_string(v_a_2334_);
v___x_2336_ = 3;
v___x_2337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2336_);
v___x_2338_ = lean_array_get_size(v___y_2329_);
v___x_2339_ = lean_array_push(v___y_2329_, v___x_2337_);
v___x_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
return v___x_2340_;
}
}
v___jp_2341_:
{
if (v_reconfigure_2135_ == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_io_prim_handle_lock(v_h_2342_, v_reconfigure_2135_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; 
lean_dec_ref_known(v___x_2344_, 1);
v___x_2345_ = l_IO_FS_Handle_readToEnd(v_h_2342_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = l_Lean_Json_parse(v_a_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref_known(v___x_2347_, 1);
v___x_2348_ = l_Lake_importConfigFile___lam__0(v___x_2157_, v___x_2154_, v_h_2342_);
lean_dec(v_h_2342_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v_h_2161_ = v_a_2349_;
v_lakeOpts_2162_ = v_lakeOpts_2133_;
v___y_2163_ = v___y_2343_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2350_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2351_ = lean_io_error_to_string(v_a_2350_);
v___x_2352_ = 3;
v___x_2353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*1, v___x_2352_);
v___x_2354_ = lean_array_get_size(v___y_2343_);
v___x_2355_ = lean_array_push(v___y_2343_, v___x_2353_);
v___x_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
return v___x_2356_;
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2347_, 0);
lean_inc_n(v_a_2357_, 2);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2358_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v___x_2359_; 
lean_dec_ref_known(v___x_2358_, 1);
v___x_2359_ = l_Lean_Json_getObj_x3f(v_a_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_dec_ref_known(v___x_2359_, 1);
v___y_2316_ = v_h_2342_;
v___y_2317_ = v___y_2343_;
goto v___jp_2315_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2362_ = l_Lake_JsonObject_getJson_x3f(v_a_2360_, v___x_2361_);
lean_dec(v_a_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
v___y_2316_ = v_h_2342_;
v___y_2317_ = v___y_2343_;
goto v___jp_2315_;
}
else
{
lean_object* v_val_2363_; lean_object* v___x_2364_; 
v_val_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_val_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_dec_ref_known(v___x_2364_, 1);
v___y_2316_ = v_h_2342_;
v___y_2317_ = v___y_2343_;
goto v___jp_2315_;
}
else
{
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_dec_ref_known(v___x_2364_, 1);
v___y_2316_ = v_h_2342_;
v___y_2317_ = v___y_2343_;
goto v___jp_2315_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2366_; 
lean_dec(v_lakeOpts_2133_);
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lake_importConfigFile___lam__0(v___x_2157_, v___x_2154_, v_h_2342_);
lean_dec(v_h_2342_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v_h_2161_ = v_a_2367_;
v_lakeOpts_2162_ = v_a_2365_;
v___y_2163_ = v___y_2343_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_a_2365_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2368_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2369_ = lean_io_error_to_string(v_a_2368_);
v___x_2370_ = 3;
v___x_2371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*1, v___x_2370_);
v___x_2372_ = lean_array_get_size(v___y_2343_);
v___x_2373_ = lean_array_push(v___y_2343_, v___x_2371_);
v___x_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
return v___x_2374_;
}
}
}
}
}
}
else
{
lean_object* v_a_2375_; uint8_t v___x_2376_; 
lean_dec(v_a_2357_);
lean_dec(v_lakeOpts_2133_);
v_a_2375_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2376_ = l_System_FilePath_pathExists(v___x_2151_);
if (v___x_2376_ == 0)
{
v___y_2328_ = v_h_2342_;
v___y_2329_ = v___y_2343_;
v___y_2330_ = v_a_2375_;
goto v___jp_2327_;
}
else
{
lean_object* v_idx_2377_; lean_object* v_name_2378_; lean_object* v_platform_2379_; lean_object* v_leanHash_2380_; uint64_t v_configHash_2381_; uint8_t v___x_2382_; 
v_idx_2377_ = lean_ctor_get(v_a_2375_, 0);
v_name_2378_ = lean_ctor_get(v_a_2375_, 1);
v_platform_2379_ = lean_ctor_get(v_a_2375_, 2);
v_leanHash_2380_ = lean_ctor_get(v_a_2375_, 3);
v_configHash_2381_ = lean_ctor_get_uint64(v_a_2375_, sizeof(void*)*5);
v___x_2382_ = lean_nat_dec_eq(v_idx_2377_, v_pkgIdx_2129_);
if (v___x_2382_ == 0)
{
v___y_2328_ = v_h_2342_;
v___y_2329_ = v___y_2343_;
v___y_2330_ = v_a_2375_;
goto v___jp_2327_;
}
else
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_name_eq(v_name_2378_, v_pkgName_2130_);
if (v___x_2383_ == 0)
{
v___y_2328_ = v_h_2342_;
v___y_2329_ = v___y_2343_;
v___y_2330_ = v_a_2375_;
goto v___jp_2327_;
}
else
{
uint64_t v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = lean_unbox_uint64(v_a_2159_);
v___x_2385_ = lean_uint64_dec_eq(v_configHash_2381_, v___x_2384_);
if (v___x_2385_ == 0)
{
v___y_2328_ = v_h_2342_;
v___y_2329_ = v___y_2343_;
v___y_2330_ = v_a_2375_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = l_System_Platform_target;
v___x_2387_ = lean_string_dec_eq(v_platform_2379_, v___x_2386_);
if (v___x_2387_ == 0)
{
v___y_2328_ = v_h_2342_;
v___y_2329_ = v___y_2343_;
v___y_2330_ = v_a_2375_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = l_Lake_Env_leanGithash(v_lakeEnv_2127_);
v___x_2389_ = lean_string_dec_eq(v_leanHash_2380_, v___x_2388_);
lean_dec_ref(v___x_2388_);
if (v___x_2389_ == 0)
{
v___y_2328_ = v_h_2342_;
v___y_2329_ = v___y_2343_;
v___y_2330_ = v_a_2375_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2390_; 
lean_dec(v_a_2375_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2390_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2151_, v_leanOpts_2134_);
lean_dec_ref(v___x_2151_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = lean_io_prim_handle_unlock(v_h_2342_);
lean_dec(v_h_2342_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref_known(v___x_2392_, 1);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_a_2391_);
lean_ctor_set(v___x_2393_, 1, v___y_2343_);
return v___x_2393_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec(v_a_2391_);
v_a_2394_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2395_ = lean_io_error_to_string(v_a_2394_);
v___x_2396_ = 3;
v___x_2397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2396_);
v___x_2398_ = lean_array_get_size(v___y_2343_);
v___x_2399_ = lean_array_push(v___y_2343_, v___x_2397_);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
return v___x_2400_;
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_h_2342_);
v_a_2401_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2402_ = lean_io_error_to_string(v_a_2401_);
v___x_2403_ = 3;
v___x_2404_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*1, v___x_2403_);
v___x_2405_ = lean_array_get_size(v___y_2343_);
v___x_2406_ = lean_array_push(v___y_2343_, v___x_2404_);
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
return v___x_2407_;
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
lean_object* v_a_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec(v_h_2342_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2408_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2409_ = lean_io_error_to_string(v_a_2408_);
v___x_2410_ = 3;
v___x_2411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*1, v___x_2410_);
v___x_2412_ = lean_array_get_size(v___y_2343_);
v___x_2413_ = lean_array_push(v___y_2343_, v___x_2411_);
v___x_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
return v___x_2414_;
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec(v_h_2342_);
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2415_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2416_ = lean_io_error_to_string(v_a_2415_);
v___x_2417_ = 3;
v___x_2418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*1, v___x_2417_);
v___x_2419_ = lean_array_get_size(v___y_2343_);
v___x_2420_ = lean_array_push(v___y_2343_, v___x_2418_);
v___x_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
return v___x_2421_;
}
}
else
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lake_importConfigFile___lam__0(v___x_2157_, v___x_2154_, v_h_2342_);
lean_dec(v_h_2342_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v_h_2161_ = v_a_2423_;
v_lakeOpts_2162_ = v_lakeOpts_2133_;
v___y_2163_ = v___y_2343_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec(v_a_2159_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2424_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2425_ = lean_io_error_to_string(v_a_2424_);
v___x_2426_ = 3;
v___x_2427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*1, v___x_2426_);
v___x_2428_ = lean_array_get_size(v___y_2343_);
v___x_2429_ = lean_array_push(v___y_2343_, v___x_2427_);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v___x_2157_);
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2480_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2481_ = lean_io_error_to_string(v_a_2480_);
v___x_2482_ = 3;
v___x_2483_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*1, v___x_2482_);
v___x_2484_ = lean_array_get_size(v_a_2121_);
v___x_2485_ = lean_array_push(v_a_2121_, v___x_2483_);
v___x_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
return v___x_2486_;
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec_ref(v_configDir_2147_);
lean_dec(v_val_2141_);
lean_dec_ref(v_leanOpts_2134_);
lean_dec(v_lakeOpts_2133_);
lean_dec_ref(v_configFile_2132_);
lean_dec_ref(v_pkgDir_2131_);
lean_dec(v_pkgName_2130_);
lean_dec(v_pkgIdx_2129_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2487_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2488_ = lean_io_error_to_string(v_a_2487_);
v___x_2489_ = 3;
v___x_2490_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*1, v___x_2489_);
v___x_2491_ = lean_array_get_size(v_a_2121_);
v___x_2492_ = lean_array_push(v_a_2121_, v___x_2490_);
v___x_2493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
return v___x_2493_;
}
}
v___jp_2123_:
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___y_2124_);
lean_ctor_set(v___x_2126_, 1, v_a_2125_);
return v___x_2126_;
}
}
}
LEAN_EXPORT void l_Lake_importConfigFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2120_ = stack[0].m_obj;
lean_object* v_a_2121_ = stack[1].m_obj;
lean_object* v_res_2494_;
v_res_2494_ = l_Lake_importConfigFile(v_cfg_2120_, v_a_2121_);
stack->m_obj
 = v_res_2494_;
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lake_importConfigFile(v_cfg_2495_, v_a_2496_);
return v_res_2498_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
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
res = runtime_initialize_Lean_Compiler_Bytecode_Basic(builtin);
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
lean_object* initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
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
res = initialize_Lean_Compiler_Bytecode_Basic(builtin);
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
