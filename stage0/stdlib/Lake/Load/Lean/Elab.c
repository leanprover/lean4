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
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; uint8_t v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v___x_265_);
v___x_274_ = lean_enable_initializer_execution();
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
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* v_imports_292_, lean_object* v_opts_293_, lean_object* v_trustLevel_294_, lean_object* v_a_295_){
_start:
{
uint32_t v_trustLevel_boxed_296_; lean_object* v_res_297_; 
v_trustLevel_boxed_296_ = lean_unbox_uint32(v_trustLevel_294_);
lean_dec(v_trustLevel_294_);
v_res_297_ = l_Lake_importModulesUsingCache(v_imports_292_, v_opts_293_, v_trustLevel_boxed_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object* v_00_u03b2_298_, lean_object* v_m_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_299_, v_a_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object* v_00_u03b2_302_, lean_object* v_m_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_302_, v_m_303_, v_a_304_);
lean_dec_ref(v_a_304_);
lean_dec_ref(v_m_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_307_, v_a_308_, v_b_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_312_, v_x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_315_, v_a_316_, v_x_317_);
lean_dec(v_x_317_);
lean_dec_ref(v_a_316_);
return v_res_318_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_320_, v_x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object* v_00_u03b2_323_, lean_object* v_a_324_, lean_object* v_x_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_00_u03b2_323_, v_a_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec_ref(v_a_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(lean_object* v_00_u03b2_328_, lean_object* v_data_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_data_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_b_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_332_, v_b_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(lean_object* v_xs_336_, lean_object* v_ys_337_, lean_object* v_hsz_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_336_, v_ys_337_, v_x_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_342_, lean_object* v_ys_343_, lean_object* v_hsz_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_342_, v_ys_343_, v_hsz_344_, v_x_345_, v_x_346_);
lean_dec_ref(v_ys_343_);
lean_dec_ref(v_xs_342_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_349_, lean_object* v_i_350_, lean_object* v_source_351_, lean_object* v_target_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v_i_350_, v_source_351_, v_target_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_x_355_, v_x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object* v_header_359_, lean_object* v_opts_360_, lean_object* v_inputCtx_361_, lean_object* v_a_362_){
_start:
{
uint8_t v___x_364_; lean_object* v_imports_365_; uint32_t v___x_366_; lean_object* v___x_367_; 
v___x_364_ = 1;
lean_inc(v_header_359_);
v_imports_365_ = l_Lean_Elab_HeaderSyntax_imports(v_header_359_, v___x_364_);
v___x_366_ = 1024;
v___x_367_ = l_Lake_importModulesUsingCache(v_imports_365_, v_opts_360_, v___x_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v_inputCtx_361_);
lean_dec(v_header_359_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_a_368_);
lean_ctor_set(v___x_372_, 1, v_a_362_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v_fileName_378_; lean_object* v_fileMap_379_; uint8_t v___x_380_; lean_object* v___y_382_; lean_object* v___x_411_; 
v_a_377_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_367_, 1);
v_fileName_378_ = lean_ctor_get(v_inputCtx_361_, 1);
lean_inc_ref(v_fileName_378_);
v_fileMap_379_ = lean_ctor_get(v_inputCtx_361_, 2);
lean_inc_ref(v_fileMap_379_);
lean_dec_ref(v_inputCtx_361_);
v___x_380_ = 0;
v___x_411_ = l_Lean_Syntax_getPos_x3f(v_header_359_, v___x_380_);
lean_dec(v_header_359_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___y_382_ = v___x_412_;
goto v___jp_381_;
}
else
{
lean_object* v_val_413_; 
v_val_413_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v___x_411_, 1);
v___y_382_ = v_val_413_;
goto v___jp_381_;
}
v___jp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint32_t v___x_391_; lean_object* v___x_392_; 
v___x_383_ = l_Lean_FileMap_toPosition(v_fileMap_379_, v___y_382_);
lean_dec(v___y_382_);
v___x_384_ = lean_box(0);
v___x_385_ = 2;
v___x_386_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0));
v___x_387_ = lean_io_error_to_string(v_a_377_);
v___x_388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = l_Lean_MessageData_ofFormat(v___x_388_);
v___x_390_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_390_, 0, v_fileName_378_);
lean_ctor_set(v___x_390_, 1, v___x_383_);
lean_ctor_set(v___x_390_, 2, v___x_384_);
lean_ctor_set(v___x_390_, 3, v___x_386_);
lean_ctor_set(v___x_390_, 4, v___x_389_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*5, v___x_380_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*5 + 1, v___x_385_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*5 + 2, v___x_380_);
v___x_391_ = 0;
v___x_392_ = l_Lean_mkEmptyEnvironment(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_402_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_402_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_402_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_402_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = l_Lean_MessageLog_add(v___x_390_, v_a_362_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_a_393_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref_known(v___x_390_, 5);
lean_dec_ref(v_a_362_);
v_a_403_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_392_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_392_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object* v_header_414_, lean_object* v_opts_415_, lean_object* v_inputCtx_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_414_, v_opts_415_, v_inputCtx_416_, v_a_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object* v_x_424_, lean_object* v___y_425_){
_start:
{
uint8_t v_isSilent_427_; 
v_isSilent_427_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5 + 2);
if (v_isSilent_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = l_Lake_LogEntry_ofMessage(v_x_424_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_array_push(v___y_425_, v___x_428_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v_x_424_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___y_425_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object* v_x_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_434_, v___y_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_438_, lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
lean_inc_ref(v_f_438_);
lean_inc(v___x_446_);
v___x_447_ = lean_apply_3(v_f_438_, v___x_446_, v___y_443_, lean_box(0));
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v_a_449_; size_t v___x_450_; size_t v___x_451_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
v_a_449_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_447_, 2);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_440_, v___x_450_);
v_i_440_ = v___x_451_;
v_b_442_ = v_a_448_;
v___y_443_ = v_a_449_;
goto _start;
}
else
{
lean_dec_ref(v_f_438_);
return v___x_447_;
}
}
else
{
lean_object* v___x_453_; 
lean_dec_ref(v_f_438_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_b_442_);
lean_ctor_set(v___x_453_, 1, v___y_443_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_454_, lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_stop_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_457_);
lean_dec(v_stop_457_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_454_, v_as_455_, v_i_boxed_461_, v_stop_boxed_462_, v_b_458_, v___y_459_);
lean_dec_ref(v_as_455_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_464_, lean_object* v_x_465_, lean_object* v___y_466_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v_cs_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_cs_468_ = lean_ctor_get(v_x_465_, 0);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_get_size(v_cs_468_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
lean_dec_ref(v_f_464_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___y_466_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_le(v___x_470_, v___x_470_);
if (v___x_474_ == 0)
{
if (v___x_472_ == 0)
{
lean_object* v___x_475_; 
lean_dec_ref(v_f_464_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_471_);
lean_ctor_set(v___x_475_, 1, v___y_466_);
return v___x_475_;
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((size_t)0ULL);
v___x_477_ = lean_usize_of_nat(v___x_470_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_464_, v_cs_468_, v___x_476_, v___x_477_, v___x_471_, v___y_466_);
return v___x_478_;
}
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___x_470_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_464_, v_cs_468_, v___x_479_, v___x_480_, v___x_471_, v___y_466_);
return v___x_481_;
}
}
}
else
{
lean_object* v_vs_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_vs_482_ = lean_ctor_get(v_x_465_, 0);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_array_get_size(v_vs_482_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_nat_dec_lt(v___x_483_, v___x_484_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_f_464_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___y_466_);
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = lean_nat_dec_le(v___x_484_, v___x_484_);
if (v___x_488_ == 0)
{
if (v___x_486_ == 0)
{
lean_object* v___x_489_; 
lean_dec_ref(v_f_464_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_485_);
lean_ctor_set(v___x_489_, 1, v___y_466_);
return v___x_489_;
}
else
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((size_t)0ULL);
v___x_491_ = lean_usize_of_nat(v___x_484_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_464_, v_vs_482_, v___x_490_, v___x_491_, v___x_485_, v___y_466_);
return v___x_492_;
}
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_usize_of_nat(v___x_484_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_464_, v_vs_482_, v___x_493_, v___x_494_, v___x_485_, v___y_466_);
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_496_, lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_, lean_object* v_b_500_, lean_object* v___y_501_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_eq(v_i_498_, v_stop_499_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_array_uget_borrowed(v_as_497_, v_i_498_);
lean_inc_ref(v_f_496_);
v___x_505_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_496_, v___x_504_, v___y_501_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
v_a_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_505_, 2);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_498_, v___x_508_);
v_i_498_ = v___x_509_;
v_b_500_ = v_a_506_;
v___y_501_ = v_a_507_;
goto _start;
}
else
{
lean_dec_ref(v_f_496_);
return v___x_505_;
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_f_496_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_b_500_);
lean_ctor_set(v___x_511_, 1, v___y_501_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_512_, lean_object* v_as_513_, lean_object* v_i_514_, lean_object* v_stop_515_, lean_object* v_b_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
size_t v_i_boxed_519_; size_t v_stop_boxed_520_; lean_object* v_res_521_; 
v_i_boxed_519_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_stop_boxed_520_ = lean_unbox_usize(v_stop_515_);
lean_dec(v_stop_515_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_512_, v_as_513_, v_i_boxed_519_, v_stop_boxed_520_, v_b_516_, v___y_517_);
lean_dec_ref(v_as_513_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_522_, lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_522_, v_x_523_, v___y_524_);
lean_dec_ref(v_x_523_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_527_, lean_object* v_t_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_root_531_; lean_object* v_tail_532_; lean_object* v___x_533_; 
v_root_531_ = lean_ctor_get(v_t_528_, 0);
v_tail_532_ = lean_ctor_get(v_t_528_, 1);
lean_inc_ref(v_f_527_);
v___x_533_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_527_, v_root_531_, v___y_529_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_555_; 
v_a_534_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_533_, 0);
lean_dec(v_unused_556_);
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_555_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_555_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_tail_532_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_541_ == 0)
{
lean_object* v___x_543_; 
lean_dec_ref(v_f_527_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_543_ = v___x_536_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_a_534_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
uint8_t v___x_545_; 
v___x_545_ = lean_nat_dec_le(v___x_539_, v___x_539_);
if (v___x_545_ == 0)
{
if (v___x_541_ == 0)
{
lean_object* v___x_547_; 
lean_dec_ref(v_f_527_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_547_ = v___x_536_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_a_534_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
lean_del_object(v___x_536_);
v___x_549_ = ((size_t)0ULL);
v___x_550_ = lean_usize_of_nat(v___x_539_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_527_, v_tail_532_, v___x_549_, v___x_550_, v___x_540_, v_a_534_);
return v___x_551_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
lean_del_object(v___x_536_);
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_539_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_527_, v_tail_532_, v___x_552_, v___x_553_, v___x_540_, v_a_534_);
return v___x_554_;
}
}
}
}
else
{
lean_dec_ref(v_f_527_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_557_, lean_object* v_t_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_557_, v_t_558_, v___y_559_);
lean_dec_ref(v_t_558_);
return v_res_561_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_563_, lean_object* v_x_564_, size_t v_x_565_, size_t v_x_566_, lean_object* v___y_567_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v_cs_569_; lean_object* v___x_570_; size_t v___x_571_; lean_object* v_j_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v_cs_569_ = lean_ctor_get(v_x_564_, 0);
v___x_570_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_571_ = lean_usize_shift_right(v_x_565_, v_x_566_);
v_j_572_ = lean_usize_to_nat(v___x_571_);
v___x_573_ = lean_array_get_borrowed(v___x_570_, v_cs_569_, v_j_572_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_shift_left(v___x_574_, v_x_566_);
v___x_576_ = lean_usize_sub(v___x_575_, v___x_574_);
v___x_577_ = lean_usize_land(v_x_565_, v___x_576_);
v___x_578_ = ((size_t)5ULL);
v___x_579_ = lean_usize_sub(v_x_566_, v___x_578_);
lean_inc_ref(v_f_563_);
v___x_580_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_563_, v___x_573_, v___x_577_, v___x_579_, v___y_567_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_603_; 
v_a_581_ = lean_ctor_get(v___x_580_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_604_);
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_603_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_603_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v_j_572_, v___x_585_);
lean_dec(v_j_572_);
v___x_587_ = lean_array_get_size(v_cs_569_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_589_ == 0)
{
lean_object* v___x_591_; 
lean_dec(v___x_586_);
lean_dec_ref(v_f_563_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_588_);
v___x_591_ = v___x_583_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_581_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
uint8_t v___x_593_; 
v___x_593_ = lean_nat_dec_le(v___x_587_, v___x_587_);
if (v___x_593_ == 0)
{
if (v___x_589_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v___x_586_);
lean_dec_ref(v_f_563_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_588_);
v___x_595_ = v___x_583_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_a_581_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
lean_del_object(v___x_583_);
v___x_597_ = lean_usize_of_nat(v___x_586_);
lean_dec(v___x_586_);
v___x_598_ = lean_usize_of_nat(v___x_587_);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_563_, v_cs_569_, v___x_597_, v___x_598_, v___x_588_, v_a_581_);
return v___x_599_;
}
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
lean_del_object(v___x_583_);
v___x_600_ = lean_usize_of_nat(v___x_586_);
lean_dec(v___x_586_);
v___x_601_ = lean_usize_of_nat(v___x_587_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_563_, v_cs_569_, v___x_600_, v___x_601_, v___x_588_, v_a_581_);
return v___x_602_;
}
}
}
}
else
{
lean_dec(v_j_572_);
lean_dec_ref(v_f_563_);
return v___x_580_;
}
}
else
{
lean_object* v_vs_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_vs_605_ = lean_ctor_get(v_x_564_, 0);
v___x_606_ = lean_usize_to_nat(v_x_565_);
v___x_607_ = lean_array_get_size(v_vs_605_);
v___x_608_ = lean_box(0);
v___x_609_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_dec(v___x_606_);
lean_dec_ref(v_f_563_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___y_567_);
return v___x_610_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_le(v___x_607_, v___x_607_);
if (v___x_611_ == 0)
{
if (v___x_609_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v___x_606_);
lean_dec_ref(v_f_563_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_608_);
lean_ctor_set(v___x_612_, 1, v___y_567_);
return v___x_612_;
}
else
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_usize_of_nat(v___x_606_);
lean_dec(v___x_606_);
v___x_614_ = lean_usize_of_nat(v___x_607_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_563_, v_vs_605_, v___x_613_, v___x_614_, v___x_608_, v___y_567_);
return v___x_615_;
}
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_usize_of_nat(v___x_606_);
lean_dec(v___x_606_);
v___x_617_ = lean_usize_of_nat(v___x_607_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_563_, v_vs_605_, v___x_616_, v___x_617_, v___x_608_, v___y_567_);
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
size_t v_x_13978__boxed_625_; size_t v_x_13979__boxed_626_; lean_object* v_res_627_; 
v_x_13978__boxed_625_ = lean_unbox_usize(v_x_621_);
lean_dec(v_x_621_);
v_x_13979__boxed_626_ = lean_unbox_usize(v_x_622_);
lean_dec(v_x_622_);
v_res_627_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_619_, v_x_620_, v_x_13978__boxed_625_, v_x_13979__boxed_626_, v___y_623_);
lean_dec_ref(v_x_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_628_, lean_object* v_t_629_, lean_object* v_start_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_nat_dec_eq(v_start_630_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v_root_635_; lean_object* v_tail_636_; size_t v_shift_637_; lean_object* v_tailOff_638_; uint8_t v___x_639_; 
v_root_635_ = lean_ctor_get(v_t_629_, 0);
v_tail_636_ = lean_ctor_get(v_t_629_, 1);
v_shift_637_ = lean_ctor_get_usize(v_t_629_, 4);
v_tailOff_638_ = lean_ctor_get(v_t_629_, 3);
v___x_639_ = lean_nat_dec_le(v_tailOff_638_, v_start_630_);
if (v___x_639_ == 0)
{
size_t v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_usize_of_nat(v_start_630_);
lean_inc_ref(v_f_628_);
v___x_641_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_628_, v_root_635_, v___x_640_, v_shift_637_, v___y_631_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_662_; 
v_a_642_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_641_, 0);
lean_dec(v_unused_663_);
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_662_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_662_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_array_get_size(v_tail_636_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_nat_dec_lt(v___x_633_, v___x_646_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v_f_628_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_647_);
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_642_);
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
lean_dec_ref(v_f_628_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_647_);
v___x_654_ = v___x_644_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_a_642_);
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
lean_del_object(v___x_644_);
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_646_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_628_, v_tail_636_, v___x_656_, v___x_657_, v___x_647_, v_a_642_);
return v___x_658_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
lean_del_object(v___x_644_);
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_646_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_628_, v_tail_636_, v___x_659_, v___x_660_, v___x_647_, v_a_642_);
return v___x_661_;
}
}
}
}
else
{
lean_dec_ref(v_f_628_);
return v___x_641_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_nat_sub(v_start_630_, v_tailOff_638_);
v___x_665_ = lean_array_get_size(v_tail_636_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v___x_664_);
lean_dec_ref(v_f_628_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___y_631_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_le(v___x_665_, v___x_665_);
if (v___x_669_ == 0)
{
if (v___x_667_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_664_);
lean_dec_ref(v_f_628_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_666_);
lean_ctor_set(v___x_670_, 1, v___y_631_);
return v___x_670_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_usize_of_nat(v___x_664_);
lean_dec(v___x_664_);
v___x_672_ = lean_usize_of_nat(v___x_665_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_628_, v_tail_636_, v___x_671_, v___x_672_, v___x_666_, v___y_631_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_usize_of_nat(v___x_664_);
lean_dec(v___x_664_);
v___x_675_ = lean_usize_of_nat(v___x_665_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_628_, v_tail_636_, v___x_674_, v___x_675_, v___x_666_, v___y_631_);
return v___x_676_;
}
}
}
}
else
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_628_, v_t_629_, v___y_631_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_678_, lean_object* v_t_679_, lean_object* v_start_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_678_, v_t_679_, v_start_680_, v___y_681_);
lean_dec(v_start_680_);
lean_dec_ref(v_t_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_684_, lean_object* v_f_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_unreported_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_unreported_688_ = lean_ctor_get(v_log_684_, 1);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_685_, v_unreported_688_, v___x_689_, v___y_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_691_, lean_object* v_f_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_691_, v_f_692_, v___y_693_);
lean_dec_ref(v_log_691_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_698_, lean_object* v_pkgName_699_, lean_object* v_pkgDir_700_, lean_object* v_lakeOpts_701_, lean_object* v_leanOpts_702_, lean_object* v_configFile_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_IO_FS_readFile(v_configFile_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = 1;
v___x_709_ = lean_string_utf8_byte_size(v_a_707_);
lean_inc_ref(v_configFile_703_);
v___x_710_ = l_Lean_Parser_mkInputContext___redArg(v_a_707_, v_configFile_703_, v___x_708_, v___x_709_);
lean_inc_ref(v___x_710_);
v___x_711_ = l_Lean_Parser_parseHeader(v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_810_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_810_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_810_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_810_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_snd_716_; lean_object* v_fst_717_; lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_809_; 
v_snd_716_ = lean_ctor_get(v_a_712_, 1);
lean_inc(v_snd_716_);
v_fst_717_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_fst_717_);
lean_dec(v_a_712_);
v_fst_718_ = lean_ctor_get(v_snd_716_, 0);
v_snd_719_ = lean_ctor_get(v_snd_716_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_snd_716_);
if (v_isSharedCheck_809_ == 0)
{
v___x_721_ = v_snd_716_;
v_isShared_722_ = v_isSharedCheck_809_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snd_719_);
lean_inc(v_fst_718_);
lean_dec(v_snd_716_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_809_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; 
lean_inc_ref(v___x_710_);
lean_inc_ref(v_leanOpts_702_);
v___x_723_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_717_, v_leanOpts_702_, v___x_710_, v_snd_719_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_799_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_799_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_799_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_799_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_798_; 
v_fst_728_ = lean_ctor_get(v_a_724_, 0);
v_snd_729_ = lean_ctor_get(v_a_724_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_798_ == 0)
{
v___x_731_ = v_a_724_;
v_isShared_732_ = v_isSharedCheck_798_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v_a_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_798_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_asyncMode_734_; lean_object* v___x_735_; lean_object* v_asyncMode_736_; lean_object* v___x_737_; lean_object* v_asyncMode_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_733_ = l_Lake_nameExt;
v_asyncMode_734_ = lean_ctor_get(v___x_733_, 2);
v___x_735_ = l_Lake_dirExt;
v_asyncMode_736_ = lean_ctor_get(v___x_735_, 2);
v___x_737_ = l_Lake_optsExt;
v_asyncMode_738_ = lean_ctor_get(v___x_737_, 2);
v___x_739_ = ((lean_object*)(l_Lake_configModuleName));
v___x_740_ = l_Lean_Environment_setMainModule(v_fst_728_, v___x_739_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_pkgName_699_);
lean_ctor_set(v___x_731_, 0, v_pkgIdx_698_);
v___x_742_ = v___x_731_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_pkgIdx_698_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_pkgName_699_);
v___x_742_ = v_reuseFailAlloc_797_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = l_Lean_EnvExtension_setState___redArg(v___x_733_, v___x_740_, v___x_742_, v_asyncMode_734_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
lean_ctor_set(v___x_726_, 0, v_pkgDir_700_);
v___x_745_ = v___x_726_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_pkgDir_700_);
v___x_745_ = v_reuseFailAlloc_796_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = l_Lean_EnvExtension_setState___redArg(v___x_735_, v___x_743_, v___x_745_, v_asyncMode_736_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 1);
lean_ctor_set(v___x_714_, 0, v_lakeOpts_701_);
v___x_748_ = v___x_714_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_lakeOpts_701_);
v___x_748_ = v_reuseFailAlloc_795_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_EnvExtension_setState___redArg(v___x_737_, v___x_746_, v___x_748_, v_asyncMode_738_);
v___x_750_ = l_Lean_Elab_Command_mkState(v___x_749_, v_snd_729_, v_leanOpts_702_);
v___x_751_ = l_Lean_Elab_IO_processCommands(v___x_710_, v_fst_718_, v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_commandState_753_; lean_object* v_env_754_; lean_object* v_messages_755_; lean_object* v___f_756_; lean_object* v___x_757_; 
lean_del_object(v___x_721_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_commandState_753_ = lean_ctor_get(v_a_752_, 0);
lean_inc_ref(v_commandState_753_);
lean_dec(v_a_752_);
v_env_754_ = lean_ctor_get(v_commandState_753_, 0);
lean_inc_ref(v_env_754_);
v_messages_755_ = lean_ctor_get(v_commandState_753_, 1);
lean_inc_ref(v_messages_755_);
lean_dec_ref(v_commandState_753_);
v___f_756_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_757_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_755_, v___f_756_, v_a_704_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_775_; 
v_a_758_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_757_, 0);
lean_dec(v_unused_776_);
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_775_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_775_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_MessageLog_hasErrors(v_messages_755_);
lean_dec_ref(v_messages_755_);
if (v___x_762_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v_configFile_703_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v_env_754_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_env_754_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_a_758_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec_ref(v_env_754_);
v___x_766_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1));
v___x_767_ = lean_string_append(v_configFile_703_, v___x_766_);
v___x_768_ = 3;
v___x_769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_768_);
v___x_770_ = lean_array_get_size(v_a_758_);
v___x_771_ = lean_array_push(v_a_758_, v___x_769_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 1);
lean_ctor_set(v___x_760_, 1, v___x_771_);
lean_ctor_set(v___x_760_, 0, v___x_770_);
v___x_773_ = v___x_760_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_messages_755_);
lean_dec_ref(v_env_754_);
lean_dec_ref(v_configFile_703_);
v_a_777_ = lean_ctor_get(v___x_757_, 0);
v_a_778_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_757_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_inc(v_a_777_);
lean_dec(v___x_757_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_dec_ref(v_configFile_703_);
v_a_786_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_751_, 1);
v___x_787_ = lean_io_error_to_string(v_a_786_);
v___x_788_ = 3;
v___x_789_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*1, v___x_788_);
v___x_790_ = lean_array_get_size(v_a_704_);
v___x_791_ = lean_array_push(v_a_704_, v___x_789_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 1);
lean_ctor_set(v___x_721_, 1, v___x_791_);
lean_ctor_set(v___x_721_, 0, v___x_790_);
v___x_793_ = v___x_721_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
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
lean_object* v_a_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_fst_718_);
lean_del_object(v___x_714_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_configFile_703_);
lean_dec_ref(v_leanOpts_702_);
lean_dec(v_lakeOpts_701_);
lean_dec_ref(v_pkgDir_700_);
lean_dec(v_pkgName_699_);
lean_dec(v_pkgIdx_698_);
v_a_800_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_723_, 1);
v___x_801_ = lean_io_error_to_string(v_a_800_);
v___x_802_ = 3;
v___x_803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_802_);
v___x_804_ = lean_array_get_size(v_a_704_);
v___x_805_ = lean_array_push(v_a_704_, v___x_803_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 1);
lean_ctor_set(v___x_721_, 1, v___x_805_);
lean_ctor_set(v___x_721_, 0, v___x_804_);
v___x_807_ = v___x_721_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v_configFile_703_);
lean_dec_ref(v_leanOpts_702_);
lean_dec(v_lakeOpts_701_);
lean_dec_ref(v_pkgDir_700_);
lean_dec(v_pkgName_699_);
lean_dec(v_pkgIdx_698_);
v_a_811_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_711_, 1);
v___x_812_ = lean_io_error_to_string(v_a_811_);
v___x_813_ = 3;
v___x_814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_813_);
v___x_815_ = lean_array_get_size(v_a_704_);
v___x_816_ = lean_array_push(v_a_704_, v___x_814_);
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
return v___x_817_;
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref(v_configFile_703_);
lean_dec_ref(v_leanOpts_702_);
lean_dec(v_lakeOpts_701_);
lean_dec_ref(v_pkgDir_700_);
lean_dec(v_pkgName_699_);
lean_dec(v_pkgIdx_698_);
v_a_818_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_706_, 1);
v___x_819_ = lean_io_error_to_string(v_a_818_);
v___x_820_ = 3;
v___x_821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v___x_820_);
v___x_822_ = lean_array_get_size(v_a_704_);
v___x_823_ = lean_array_push(v_a_704_, v___x_821_);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_825_, lean_object* v_pkgName_826_, lean_object* v_pkgDir_827_, lean_object* v_lakeOpts_828_, lean_object* v_leanOpts_829_, lean_object* v_configFile_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_825_, v_pkgName_826_, v_pkgDir_827_, v_lakeOpts_828_, v_leanOpts_829_, v_configFile_830_, v_a_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_836_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = lake_environment_add(v_env_836_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_837_);
return v_res_838_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_845_ = l_Lean_NameSet_empty;
v___x_846_ = l_Lean_NameSet_insert(v___x_845_, v___x_844_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_852_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_853_ = l_Lean_NameSet_insert(v___x_852_, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_859_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_860_ = l_Lean_NameSet_insert(v___x_859_, v___x_858_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_866_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_867_ = l_Lean_NameSet_insert(v___x_866_, v___x_865_);
return v___x_867_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_873_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_874_ = l_Lean_NameSet_insert(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_880_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_881_ = l_Lean_NameSet_insert(v___x_880_, v___x_879_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_887_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_888_ = l_Lean_NameSet_insert(v___x_887_, v___x_886_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_894_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_895_ = l_Lean_NameSet_insert(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_901_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_902_ = l_Lean_NameSet_insert(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_908_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_909_ = l_Lean_NameSet_insert(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_915_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_916_ = l_Lean_NameSet_insert(v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_922_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_923_ = l_Lean_NameSet_insert(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_929_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_930_ = l_Lean_NameSet_insert(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_936_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_937_ = l_Lean_NameSet_insert(v___x_936_, v___x_935_);
return v___x_937_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_943_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_944_ = l_Lean_NameSet_insert(v___x_943_, v___x_942_);
return v___x_944_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_951_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_952_ = l_Lean_NameSet_insert(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52));
v___x_960_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_961_ = l_Lean_NameSet_insert(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53);
return v___x_962_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l_Lean_instInhabitedEnvExtensionState;
v___x_964_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_965_, lean_object* v_val_966_, lean_object* v_as_967_, size_t v_i_968_, size_t v_stop_969_, lean_object* v_b_970_){
_start:
{
uint8_t v___x_971_; 
v___x_971_ = lean_usize_dec_eq(v_i_968_, v_stop_969_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; size_t v___x_978_; size_t v___x_979_; 
v___x_972_ = lean_array_uget_borrowed(v_as_967_, v_i_968_);
v___x_973_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_974_ = lean_array_get_borrowed(v___x_973_, v_val_965_, v_val_966_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_box(0);
lean_inc(v___x_972_);
lean_inc(v___x_974_);
v___x_977_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_974_, v_b_970_, v___x_972_, v___x_975_, v___x_976_);
v___x_978_ = ((size_t)1ULL);
v___x_979_ = lean_usize_add(v_i_968_, v___x_978_);
v_i_968_ = v___x_979_;
v_b_970_ = v___x_977_;
goto _start;
}
else
{
return v_b_970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_981_, lean_object* v_val_982_, lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; lean_object* v_res_989_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_981_, v_val_982_, v_as_983_, v_i_boxed_987_, v_stop_boxed_988_, v_b_986_);
lean_dec_ref(v_as_983_);
lean_dec(v_val_982_);
lean_dec_ref(v_val_981_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_990_, lean_object* v_x_991_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_box(0);
return v___x_992_;
}
else
{
lean_object* v_key_993_; lean_object* v_value_994_; lean_object* v_tail_995_; uint8_t v___x_996_; 
v_key_993_ = lean_ctor_get(v_x_991_, 0);
v_value_994_ = lean_ctor_get(v_x_991_, 1);
v_tail_995_ = lean_ctor_get(v_x_991_, 2);
v___x_996_ = lean_name_eq(v_key_993_, v_a_990_);
if (v___x_996_ == 0)
{
v_x_991_ = v_tail_995_;
goto _start;
}
else
{
lean_object* v___x_998_; 
lean_inc(v_value_994_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_value_994_);
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_999_, v_x_1000_);
lean_dec(v_x_1000_);
lean_dec(v_a_999_);
return v_res_1001_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1002_; uint64_t v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1723u);
v___x_1003_ = lean_uint64_of_nat(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_buckets_1006_; lean_object* v___x_1007_; uint64_t v___y_1009_; 
v_buckets_1006_ = lean_ctor_get(v_m_1004_, 1);
v___x_1007_ = lean_array_get_size(v_buckets_1006_);
if (lean_obj_tag(v_a_1005_) == 0)
{
uint64_t v___x_1023_; 
v___x_1023_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___closed__0);
v___y_1009_ = v___x_1023_;
goto v___jp_1008_;
}
else
{
uint64_t v_hash_1024_; 
v_hash_1024_ = lean_ctor_get_uint64(v_a_1005_, sizeof(void*)*2);
v___y_1009_ = v_hash_1024_;
goto v___jp_1008_;
}
v___jp_1008_:
{
uint64_t v___x_1010_; uint64_t v___x_1011_; uint64_t v_fold_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1010_ = 32ULL;
v___x_1011_ = lean_uint64_shift_right(v___y_1009_, v___x_1010_);
v_fold_1012_ = lean_uint64_xor(v___y_1009_, v___x_1011_);
v___x_1013_ = 16ULL;
v___x_1014_ = lean_uint64_shift_right(v_fold_1012_, v___x_1013_);
v___x_1015_ = lean_uint64_xor(v_fold_1012_, v___x_1014_);
v___x_1016_ = lean_uint64_to_usize(v___x_1015_);
v___x_1017_ = lean_usize_of_nat(v___x_1007_);
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_sub(v___x_1017_, v___x_1018_);
v___x_1020_ = lean_usize_land(v___x_1016_, v___x_1019_);
v___x_1021_ = lean_array_uget_borrowed(v_buckets_1006_, v___x_1020_);
v___x_1022_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1005_, v___x_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_m_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_1028_, lean_object* v_val_1029_, lean_object* v_as_1030_, size_t v_i_1031_, size_t v_stop_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v___y_1035_; uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1031_, v_stop_1032_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v_fst_1041_; lean_object* v_snd_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1030_, v_i_1031_);
v_fst_1041_ = lean_ctor_get(v___x_1040_, 0);
v_snd_1042_ = lean_ctor_get(v___x_1040_, 1);
v___x_1043_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_1044_ = l_Lean_NameSet_contains(v___x_1043_, v_fst_1041_);
if (v___x_1044_ == 0)
{
v___y_1035_ = v_b_1033_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_1028_, v_fst_1041_);
if (lean_obj_tag(v___x_1045_) == 0)
{
v___y_1035_ = v_b_1033_;
goto v___jp_1034_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_val_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_array_get_size(v_snd_1042_);
v___x_1049_ = lean_nat_dec_lt(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec(v_val_1046_);
v___y_1035_ = v_b_1033_;
goto v___jp_1034_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_nat_dec_le(v___x_1048_, v___x_1048_);
if (v___x_1050_ == 0)
{
if (v___x_1049_ == 0)
{
lean_dec(v_val_1046_);
v___y_1035_ = v_b_1033_;
goto v___jp_1034_;
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = lean_usize_of_nat(v___x_1048_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1029_, v_val_1046_, v_snd_1042_, v___x_1051_, v___x_1052_, v_b_1033_);
lean_dec(v_val_1046_);
v___y_1035_ = v___x_1053_;
goto v___jp_1034_;
}
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = lean_usize_of_nat(v___x_1048_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1029_, v_val_1046_, v_snd_1042_, v___x_1054_, v___x_1055_, v_b_1033_);
lean_dec(v_val_1046_);
v___y_1035_ = v___x_1056_;
goto v___jp_1034_;
}
}
}
}
}
else
{
return v_b_1033_;
}
v___jp_1034_:
{
size_t v___x_1036_; size_t v___x_1037_; 
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_add(v_i_1031_, v___x_1036_);
v_i_1031_ = v___x_1037_;
v_b_1033_ = v___y_1035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1057_, lean_object* v_val_1058_, lean_object* v_as_1059_, lean_object* v_i_1060_, lean_object* v_stop_1061_, lean_object* v_b_1062_){
_start:
{
size_t v_i_boxed_1063_; size_t v_stop_boxed_1064_; lean_object* v_res_1065_; 
v_i_boxed_1063_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_stop_boxed_1064_ = lean_unbox_usize(v_stop_1061_);
lean_dec(v_stop_1061_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1057_, v_val_1058_, v_as_1059_, v_i_boxed_1063_, v_stop_boxed_1064_, v_b_1062_);
lean_dec_ref(v_as_1059_);
lean_dec_ref(v_val_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1066_, size_t v_i_1067_, size_t v_stop_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_eq(v_i_1067_, v_stop_1068_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; 
v___x_1071_ = lean_array_uget_borrowed(v_as_1066_, v_i_1067_);
lean_inc(v___x_1071_);
v___x_1072_ = lake_environment_add(v_b_1069_, v___x_1071_);
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_add(v_i_1067_, v___x_1073_);
v_i_1067_ = v___x_1074_;
v_b_1069_ = v___x_1072_;
goto _start;
}
else
{
return v_b_1069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1076_, lean_object* v_i_1077_, lean_object* v_stop_1078_, lean_object* v_b_1079_){
_start:
{
size_t v_i_boxed_1080_; size_t v_stop_boxed_1081_; lean_object* v_res_1082_; 
v_i_boxed_1080_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_stop_boxed_1081_ = lean_unbox_usize(v_stop_1078_);
lean_dec(v_stop_1078_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1076_, v_i_boxed_1080_, v_stop_boxed_1081_, v_b_1079_);
lean_dec_ref(v_as_1076_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1083_, lean_object* v_leanOpts_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_readModuleData(v_olean_1083_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v_fst_1088_; lean_object* v_imports_1089_; lean_object* v_constants_1090_; lean_object* v_entries_1091_; uint32_t v___x_1092_; lean_object* v___x_1093_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v_fst_1088_ = lean_ctor_get(v_a_1087_, 0);
lean_inc(v_fst_1088_);
lean_dec(v_a_1087_);
v_imports_1089_ = lean_ctor_get(v_fst_1088_, 0);
lean_inc_ref(v_imports_1089_);
v_constants_1090_ = lean_ctor_get(v_fst_1088_, 2);
lean_inc_ref(v_constants_1090_);
v_entries_1091_ = lean_ctor_get(v_fst_1088_, 4);
lean_inc_ref(v_entries_1091_);
lean_dec(v_fst_1088_);
v___x_1092_ = 1024;
v___x_1093_ = l_Lake_importModulesUsingCache(v_imports_1089_, v_leanOpts_1084_, v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___y_1097_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_array_get_size(v_constants_1090_);
v___x_1136_ = lean_nat_dec_lt(v___x_1095_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v_constants_1090_);
v___y_1097_ = v_a_1094_;
goto v___jp_1096_;
}
else
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_le(v___x_1135_, v___x_1135_);
if (v___x_1137_ == 0)
{
if (v___x_1136_ == 0)
{
lean_dec_ref(v_constants_1090_);
v___y_1097_ = v_a_1094_;
goto v___jp_1096_;
}
else
{
size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = lean_usize_of_nat(v___x_1135_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1090_, v___x_1138_, v___x_1139_, v_a_1094_);
lean_dec_ref(v_constants_1090_);
v___y_1097_ = v___x_1140_;
goto v___jp_1096_;
}
}
else
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1135_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1090_, v___x_1141_, v___x_1142_, v_a_1094_);
lean_dec_ref(v_constants_1090_);
v___y_1097_ = v___x_1143_;
goto v___jp_1096_;
}
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = l_Lean_persistentEnvExtensionsRef;
v___x_1099_ = lean_st_ref_get(v___x_1098_);
v___x_1100_ = l_Lean_mkExtNameMap(v___x_1095_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1126_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1126_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1126_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_array_get_size(v_entries_1091_);
v___x_1106_ = lean_nat_dec_lt(v___x_1095_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_a_1101_);
lean_dec(v___x_1099_);
lean_dec_ref(v_entries_1091_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___y_1097_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___y_1097_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
else
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_nat_dec_le(v___x_1105_, v___x_1105_);
if (v___x_1110_ == 0)
{
if (v___x_1106_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_a_1101_);
lean_dec(v___x_1099_);
lean_dec_ref(v_entries_1091_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___y_1097_);
v___x_1112_ = v___x_1103_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___y_1097_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = lean_usize_of_nat(v___x_1105_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1101_, v___x_1099_, v_entries_1091_, v___x_1114_, v___x_1115_, v___y_1097_);
lean_dec_ref(v_entries_1091_);
lean_dec(v___x_1099_);
lean_dec(v_a_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1116_);
v___x_1118_ = v___x_1103_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = lean_usize_of_nat(v___x_1105_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1101_, v___x_1099_, v_entries_1091_, v___x_1120_, v___x_1121_, v___y_1097_);
lean_dec_ref(v_entries_1091_);
lean_dec(v___x_1099_);
lean_dec(v_a_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1122_);
v___x_1124_ = v___x_1103_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v___x_1099_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v_entries_1091_);
v_a_1127_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1100_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1100_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
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
lean_dec_ref(v_entries_1091_);
lean_dec_ref(v_constants_1090_);
return v___x_1093_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_leanOpts_1084_);
v_a_1144_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1086_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1086_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1152_, lean_object* v_leanOpts_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1152_, v_leanOpts_1153_);
lean_dec_ref(v_olean_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1156_, lean_object* v_m_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1157_, v_a_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1160_, v_m_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_m_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1164_, lean_object* v_a_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1165_, v_x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1168_, lean_object* v_a_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1168_, v_a_1169_, v_x_1170_);
lean_dec(v_x_1170_);
lean_dec(v_a_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_box(1);
v___x_1174_ = lean_panic_fn_borrowed(v___x_1173_, v_msg_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1179_ = lean_unsigned_to_nat(35u);
v___x_1180_ = lean_unsigned_to_nat(182u);
v___x_1181_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1183_ = l_mkPanicMessageWithDecl(v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_);
return v___x_1183_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1184_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1185_ = lean_unsigned_to_nat(21u);
v___x_1186_ = lean_unsigned_to_nat(183u);
v___x_1187_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1188_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1189_ = l_mkPanicMessageWithDecl(v___x_1188_, v___x_1187_, v___x_1186_, v___x_1185_, v___x_1184_);
return v___x_1189_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1193_ = lean_unsigned_to_nat(35u);
v___x_1194_ = lean_unsigned_to_nat(276u);
v___x_1195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1197_ = l_mkPanicMessageWithDecl(v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_, v___x_1192_);
return v___x_1197_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1199_ = lean_unsigned_to_nat(21u);
v___x_1200_ = lean_unsigned_to_nat(277u);
v___x_1201_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1202_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1203_ = l_mkPanicMessageWithDecl(v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_, v___x_1198_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1204_, lean_object* v_v_1205_, lean_object* v_t_1206_){
_start:
{
if (lean_obj_tag(v_t_1206_) == 0)
{
lean_object* v_size_1207_; lean_object* v_k_1208_; lean_object* v_v_1209_; lean_object* v_l_1210_; lean_object* v_r_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1567_; 
v_size_1207_ = lean_ctor_get(v_t_1206_, 0);
v_k_1208_ = lean_ctor_get(v_t_1206_, 1);
v_v_1209_ = lean_ctor_get(v_t_1206_, 2);
v_l_1210_ = lean_ctor_get(v_t_1206_, 3);
v_r_1211_ = lean_ctor_get(v_t_1206_, 4);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_t_1206_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1213_ = v_t_1206_;
v_isShared_1214_ = v_isSharedCheck_1567_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_r_1211_);
lean_inc(v_l_1210_);
lean_inc(v_v_1209_);
lean_inc(v_k_1208_);
lean_inc(v_size_1207_);
lean_dec(v_t_1206_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1567_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_string_compare(v_k_1204_, v_k_1208_);
switch(v___x_1215_)
{
case 0:
{
lean_object* v___x_1216_; 
lean_dec(v_size_1207_);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1204_, v_v_1205_, v_l_1210_);
if (lean_obj_tag(v_r_1211_) == 0)
{
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_size_1217_; lean_object* v_size_1218_; lean_object* v_k_1219_; lean_object* v_v_1220_; lean_object* v_l_1221_; lean_object* v_r_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_size_1217_ = lean_ctor_get(v_r_1211_, 0);
v_size_1218_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_size_1218_);
v_k_1219_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_k_1219_);
v_v_1220_ = lean_ctor_get(v___x_1216_, 2);
lean_inc(v_v_1220_);
v_l_1221_ = lean_ctor_get(v___x_1216_, 3);
lean_inc(v_l_1221_);
v_r_1222_ = lean_ctor_get(v___x_1216_, 4);
lean_inc(v_r_1222_);
v___x_1223_ = lean_unsigned_to_nat(3u);
v___x_1224_ = lean_nat_mul(v___x_1223_, v_size_1217_);
v___x_1225_ = lean_nat_dec_lt(v___x_1224_, v_size_1218_);
lean_dec(v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec(v_r_1222_);
lean_dec(v_l_1221_);
lean_dec(v_v_1220_);
lean_dec(v_k_1219_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v___x_1226_, v_size_1218_);
lean_dec(v_size_1218_);
v___x_1228_ = lean_nat_add(v___x_1227_, v_size_1217_);
lean_dec(v___x_1227_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 3, v___x_1216_);
lean_ctor_set(v___x_1213_, 0, v___x_1228_);
v___x_1230_ = v___x_1213_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_r_1211_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
else
{
lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1303_; 
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; 
v_unused_1304_ = lean_ctor_get(v___x_1216_, 4);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v___x_1216_, 3);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v___x_1216_, 2);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v___x_1216_, 1);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1308_);
v___x_1233_ = v___x_1216_;
v_isShared_1234_ = v_isSharedCheck_1303_;
goto v_resetjp_1232_;
}
else
{
lean_dec(v___x_1216_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1303_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
if (lean_obj_tag(v_l_1221_) == 0)
{
if (lean_obj_tag(v_r_1222_) == 0)
{
lean_object* v_size_1235_; lean_object* v_size_1236_; lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v_l_1239_; lean_object* v_r_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_size_1235_ = lean_ctor_get(v_l_1221_, 0);
v_size_1236_ = lean_ctor_get(v_r_1222_, 0);
v_k_1237_ = lean_ctor_get(v_r_1222_, 1);
v_v_1238_ = lean_ctor_get(v_r_1222_, 2);
v_l_1239_ = lean_ctor_get(v_r_1222_, 3);
v_r_1240_ = lean_ctor_get(v_r_1222_, 4);
v___x_1241_ = lean_unsigned_to_nat(2u);
v___x_1242_ = lean_nat_mul(v___x_1241_, v_size_1235_);
v___x_1243_ = lean_nat_dec_lt(v_size_1236_, v___x_1242_);
lean_dec(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1273_; 
lean_inc(v_r_1240_);
lean_inc(v_l_1239_);
lean_inc(v_v_1238_);
lean_inc(v_k_1237_);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_r_1222_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; lean_object* v_unused_1275_; lean_object* v_unused_1276_; lean_object* v_unused_1277_; lean_object* v_unused_1278_; 
v_unused_1274_ = lean_ctor_get(v_r_1222_, 4);
lean_dec(v_unused_1274_);
v_unused_1275_ = lean_ctor_get(v_r_1222_, 3);
lean_dec(v_unused_1275_);
v_unused_1276_ = lean_ctor_get(v_r_1222_, 2);
lean_dec(v_unused_1276_);
v_unused_1277_ = lean_ctor_get(v_r_1222_, 1);
lean_dec(v_unused_1277_);
v_unused_1278_ = lean_ctor_get(v_r_1222_, 0);
lean_dec(v_unused_1278_);
v___x_1245_ = v_r_1222_;
v_isShared_1246_ = v_isSharedCheck_1273_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v_r_1222_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1273_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___x_1261_; lean_object* v___y_1263_; 
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v___x_1247_, v_size_1218_);
lean_dec(v_size_1218_);
v___x_1249_ = lean_nat_add(v___x_1248_, v_size_1217_);
lean_dec(v___x_1248_);
v___x_1261_ = lean_nat_add(v___x_1247_, v_size_1235_);
if (lean_obj_tag(v_l_1239_) == 0)
{
lean_object* v_size_1271_; 
v_size_1271_ = lean_ctor_get(v_l_1239_, 0);
lean_inc(v_size_1271_);
v___y_1263_ = v_size_1271_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_unsigned_to_nat(0u);
v___y_1263_ = v___x_1272_;
goto v___jp_1262_;
}
v___jp_1250_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_nat_add(v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec(v___y_1252_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 4, v_r_1211_);
lean_ctor_set(v___x_1245_, 3, v_r_1240_);
lean_ctor_set(v___x_1245_, 2, v_v_1209_);
lean_ctor_set(v___x_1245_, 1, v_k_1208_);
lean_ctor_set(v___x_1245_, 0, v___x_1254_);
v___x_1256_ = v___x_1245_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_r_1240_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_r_1211_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v___x_1256_);
lean_ctor_set(v___x_1233_, 3, v___y_1251_);
lean_ctor_set(v___x_1233_, 2, v_v_1238_);
lean_ctor_set(v___x_1233_, 1, v_k_1237_);
lean_ctor_set(v___x_1233_, 0, v___x_1249_);
v___x_1258_ = v___x_1233_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v___y_1251_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_nat_add(v___x_1261_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec(v___x_1261_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_l_1239_);
lean_ctor_set(v___x_1213_, 3, v_l_1221_);
lean_ctor_set(v___x_1213_, 2, v_v_1220_);
lean_ctor_set(v___x_1213_, 1, v_k_1219_);
lean_ctor_set(v___x_1213_, 0, v___x_1264_);
v___x_1266_ = v___x_1213_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_l_1221_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_l_1239_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_nat_add(v___x_1247_, v_size_1217_);
if (lean_obj_tag(v_r_1240_) == 0)
{
lean_object* v_size_1268_; 
v_size_1268_ = lean_ctor_get(v_r_1240_, 0);
lean_inc(v_size_1268_);
v___y_1251_ = v___x_1266_;
v___y_1252_ = v___x_1267_;
v___y_1253_ = v_size_1268_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
v___y_1251_ = v___x_1266_;
v___y_1252_ = v___x_1267_;
v___y_1253_ = v___x_1269_;
goto v___jp_1250_;
}
}
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_del_object(v___x_1213_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_add(v___x_1279_, v_size_1218_);
lean_dec(v_size_1218_);
v___x_1281_ = lean_nat_add(v___x_1280_, v_size_1217_);
lean_dec(v___x_1280_);
v___x_1282_ = lean_nat_add(v___x_1279_, v_size_1217_);
v___x_1283_ = lean_nat_add(v___x_1282_, v_size_1236_);
lean_dec(v___x_1282_);
lean_inc_ref(v_r_1211_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v_r_1211_);
lean_ctor_set(v___x_1233_, 3, v_r_1222_);
lean_ctor_set(v___x_1233_, 2, v_v_1209_);
lean_ctor_set(v___x_1233_, 1, v_k_1208_);
lean_ctor_set(v___x_1233_, 0, v___x_1283_);
v___x_1285_ = v___x_1233_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_r_1222_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v_r_1211_);
v___x_1285_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v_r_1211_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1293_ = lean_ctor_get(v_r_1211_, 4);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_r_1211_, 3);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_r_1211_, 2);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_r_1211_, 1);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_r_1211_, 0);
lean_dec(v_unused_1297_);
v___x_1287_ = v_r_1211_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v_r_1211_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1285_);
lean_ctor_set(v___x_1287_, 3, v_l_1221_);
lean_ctor_set(v___x_1287_, 2, v_v_1220_);
lean_ctor_set(v___x_1287_, 1, v_k_1219_);
lean_ctor_set(v___x_1287_, 0, v___x_1281_);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_l_1221_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v___x_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref_known(v_l_1221_, 5);
lean_del_object(v___x_1233_);
lean_dec(v_v_1220_);
lean_dec(v_k_1219_);
lean_dec(v_size_1218_);
lean_dec_ref_known(v_r_1211_, 5);
lean_del_object(v___x_1213_);
lean_dec(v_v_1209_);
lean_dec(v_k_1208_);
v___x_1299_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1300_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1299_);
return v___x_1300_;
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_del_object(v___x_1233_);
lean_dec(v_r_1222_);
lean_dec(v_v_1220_);
lean_dec(v_k_1219_);
lean_dec(v_size_1218_);
lean_dec_ref_known(v_r_1211_, 5);
lean_del_object(v___x_1213_);
lean_dec(v_v_1209_);
lean_dec(v_k_1208_);
v___x_1301_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1302_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1301_);
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_size_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v_size_1309_ = lean_ctor_get(v_r_1211_, 0);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v___x_1310_, v_size_1309_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 3, v___x_1216_);
lean_ctor_set(v___x_1213_, 0, v___x_1311_);
v___x_1313_ = v___x_1213_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_r_1211_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_l_1315_; 
v_l_1315_ = lean_ctor_get(v___x_1216_, 3);
lean_inc(v_l_1315_);
if (lean_obj_tag(v_l_1315_) == 0)
{
lean_object* v_r_1316_; 
v_r_1316_ = lean_ctor_get(v___x_1216_, 4);
lean_inc(v_r_1316_);
if (lean_obj_tag(v_r_1316_) == 0)
{
lean_object* v_size_1317_; lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1333_; 
v_size_1317_ = lean_ctor_get(v___x_1216_, 0);
v_k_1318_ = lean_ctor_get(v___x_1216_, 1);
v_v_1319_ = lean_ctor_get(v___x_1216_, 2);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; lean_object* v_unused_1335_; 
v_unused_1334_ = lean_ctor_get(v___x_1216_, 4);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v___x_1216_, 3);
lean_dec(v_unused_1335_);
v___x_1321_ = v___x_1216_;
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_v_1319_);
lean_inc(v_k_1318_);
lean_inc(v_size_1317_);
lean_dec(v___x_1216_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_size_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v_size_1323_ = lean_ctor_get(v_r_1316_, 0);
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_nat_add(v___x_1324_, v_size_1317_);
lean_dec(v_size_1317_);
v___x_1326_ = lean_nat_add(v___x_1324_, v_size_1323_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 4, v_r_1211_);
lean_ctor_set(v___x_1321_, 3, v_r_1316_);
lean_ctor_set(v___x_1321_, 2, v_v_1209_);
lean_ctor_set(v___x_1321_, 1, v_k_1208_);
lean_ctor_set(v___x_1321_, 0, v___x_1326_);
v___x_1328_ = v___x_1321_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_r_1316_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_r_1211_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1328_);
lean_ctor_set(v___x_1213_, 3, v_l_1315_);
lean_ctor_set(v___x_1213_, 2, v_v_1319_);
lean_ctor_set(v___x_1213_, 1, v_k_1318_);
lean_ctor_set(v___x_1213_, 0, v___x_1325_);
v___x_1330_ = v___x_1213_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_l_1315_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v___x_1328_);
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
lean_object* v_k_1336_; lean_object* v_v_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1349_; 
v_k_1336_ = lean_ctor_get(v___x_1216_, 1);
v_v_1337_ = lean_ctor_get(v___x_1216_, 2);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1350_ = lean_ctor_get(v___x_1216_, 4);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v___x_1216_, 3);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1352_);
v___x_1339_ = v___x_1216_;
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_v_1337_);
lean_inc(v_k_1336_);
lean_dec(v___x_1216_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = lean_unsigned_to_nat(3u);
v___x_1342_ = lean_unsigned_to_nat(1u);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 3, v_r_1316_);
lean_ctor_set(v___x_1339_, 2, v_v_1209_);
lean_ctor_set(v___x_1339_, 1, v_k_1208_);
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_r_1316_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v_r_1316_);
v___x_1344_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1344_);
lean_ctor_set(v___x_1213_, 3, v_l_1315_);
lean_ctor_set(v___x_1213_, 2, v_v_1337_);
lean_ctor_set(v___x_1213_, 1, v_k_1336_);
lean_ctor_set(v___x_1213_, 0, v___x_1341_);
v___x_1346_ = v___x_1213_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_k_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_v_1337_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_l_1315_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
else
{
lean_object* v_r_1353_; 
v_r_1353_ = lean_ctor_get(v___x_1216_, 4);
lean_inc(v_r_1353_);
if (lean_obj_tag(v_r_1353_) == 0)
{
lean_object* v_k_1354_; lean_object* v_v_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1379_; 
v_k_1354_ = lean_ctor_get(v___x_1216_, 1);
v_v_1355_ = lean_ctor_get(v___x_1216_, 2);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; 
v_unused_1380_ = lean_ctor_get(v___x_1216_, 4);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v___x_1216_, 3);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1382_);
v___x_1357_ = v___x_1216_;
v_isShared_1358_ = v_isSharedCheck_1379_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_v_1355_);
lean_inc(v_k_1354_);
lean_dec(v___x_1216_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1379_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1375_; 
v_k_1359_ = lean_ctor_get(v_r_1353_, 1);
v_v_1360_ = lean_ctor_get(v_r_1353_, 2);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_r_1353_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1376_ = lean_ctor_get(v_r_1353_, 4);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_r_1353_, 3);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1353_, 0);
lean_dec(v_unused_1378_);
v___x_1362_ = v_r_1353_;
v_isShared_1363_ = v_isSharedCheck_1375_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
lean_dec(v_r_1353_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1375_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1364_ = lean_unsigned_to_nat(3u);
v___x_1365_ = lean_unsigned_to_nat(1u);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_l_1315_);
lean_ctor_set(v___x_1362_, 3, v_l_1315_);
lean_ctor_set(v___x_1362_, 2, v_v_1355_);
lean_ctor_set(v___x_1362_, 1, v_k_1354_);
lean_ctor_set(v___x_1362_, 0, v___x_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1354_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1355_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_l_1315_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_l_1315_);
v___x_1367_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1369_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1315_);
lean_ctor_set(v___x_1357_, 2, v_v_1209_);
lean_ctor_set(v___x_1357_, 1, v_k_1208_);
lean_ctor_set(v___x_1357_, 0, v___x_1365_);
v___x_1369_ = v___x_1357_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_l_1315_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_l_1315_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1369_);
lean_ctor_set(v___x_1213_, 3, v___x_1367_);
lean_ctor_set(v___x_1213_, 2, v_v_1360_);
lean_ctor_set(v___x_1213_, 1, v_k_1359_);
lean_ctor_set(v___x_1213_, 0, v___x_1364_);
v___x_1371_ = v___x_1213_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_unsigned_to_nat(2u);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_r_1353_);
lean_ctor_set(v___x_1213_, 3, v___x_1216_);
lean_ctor_set(v___x_1213_, 0, v___x_1383_);
v___x_1385_ = v___x_1213_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_r_1353_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_unsigned_to_nat(1u);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1216_);
lean_ctor_set(v___x_1213_, 3, v___x_1216_);
lean_ctor_set(v___x_1213_, 0, v___x_1387_);
v___x_1389_ = v___x_1213_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v___x_1216_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
case 1:
{
lean_object* v___x_1392_; 
lean_dec(v_v_1209_);
lean_dec(v_k_1208_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 2, v_v_1205_);
lean_ctor_set(v___x_1213_, 1, v_k_1204_);
v___x_1392_ = v___x_1213_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_size_1207_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1204_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1205_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_l_1210_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1211_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
default: 
{
lean_object* v___x_1394_; 
lean_dec(v_size_1207_);
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1204_, v_v_1205_, v_r_1211_);
if (lean_obj_tag(v_l_1210_) == 0)
{
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_size_1395_; lean_object* v_size_1396_; lean_object* v_k_1397_; lean_object* v_v_1398_; lean_object* v_l_1399_; lean_object* v_r_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_size_1395_ = lean_ctor_get(v_l_1210_, 0);
v_size_1396_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_size_1396_);
v_k_1397_ = lean_ctor_get(v___x_1394_, 1);
lean_inc(v_k_1397_);
v_v_1398_ = lean_ctor_get(v___x_1394_, 2);
lean_inc(v_v_1398_);
v_l_1399_ = lean_ctor_get(v___x_1394_, 3);
lean_inc(v_l_1399_);
v_r_1400_ = lean_ctor_get(v___x_1394_, 4);
lean_inc(v_r_1400_);
v___x_1401_ = lean_unsigned_to_nat(3u);
v___x_1402_ = lean_nat_mul(v___x_1401_, v_size_1395_);
v___x_1403_ = lean_nat_dec_lt(v___x_1402_, v_size_1396_);
lean_dec(v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_dec(v_r_1400_);
lean_dec(v_l_1399_);
lean_dec(v_v_1398_);
lean_dec(v_k_1397_);
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_nat_add(v___x_1404_, v_size_1395_);
v___x_1406_ = lean_nat_add(v___x_1405_, v_size_1396_);
lean_dec(v_size_1396_);
lean_dec(v___x_1405_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1394_);
lean_ctor_set(v___x_1213_, 0, v___x_1406_);
v___x_1408_ = v___x_1213_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1409_, 3, v_l_1210_);
lean_ctor_set(v_reuseFailAlloc_1409_, 4, v___x_1394_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1479_; 
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1480_ = lean_ctor_get(v___x_1394_, 4);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v___x_1394_, 3);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v___x_1394_, 2);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v___x_1394_, 1);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1484_);
v___x_1411_ = v___x_1394_;
v_isShared_1412_ = v_isSharedCheck_1479_;
goto v_resetjp_1410_;
}
else
{
lean_dec(v___x_1394_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1479_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
if (lean_obj_tag(v_l_1399_) == 0)
{
if (lean_obj_tag(v_r_1400_) == 0)
{
lean_object* v_size_1413_; lean_object* v_k_1414_; lean_object* v_v_1415_; lean_object* v_l_1416_; lean_object* v_r_1417_; lean_object* v_size_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_size_1413_ = lean_ctor_get(v_l_1399_, 0);
v_k_1414_ = lean_ctor_get(v_l_1399_, 1);
v_v_1415_ = lean_ctor_get(v_l_1399_, 2);
v_l_1416_ = lean_ctor_get(v_l_1399_, 3);
v_r_1417_ = lean_ctor_get(v_l_1399_, 4);
v_size_1418_ = lean_ctor_get(v_r_1400_, 0);
v___x_1419_ = lean_unsigned_to_nat(2u);
v___x_1420_ = lean_nat_mul(v___x_1419_, v_size_1418_);
v___x_1421_ = lean_nat_dec_lt(v_size_1413_, v___x_1420_);
lean_dec(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1450_; 
lean_inc(v_r_1417_);
lean_inc(v_l_1416_);
lean_inc(v_v_1415_);
lean_inc(v_k_1414_);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_l_1399_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; 
v_unused_1451_ = lean_ctor_get(v_l_1399_, 4);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1399_, 3);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_l_1399_, 2);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_l_1399_, 1);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_l_1399_, 0);
lean_dec(v_unused_1455_);
v___x_1423_ = v_l_1399_;
v_isShared_1424_ = v_isSharedCheck_1450_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v_l_1399_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1450_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1440_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_add(v___x_1425_, v_size_1395_);
v___x_1427_ = lean_nat_add(v___x_1426_, v_size_1396_);
lean_dec(v_size_1396_);
if (lean_obj_tag(v_l_1416_) == 0)
{
lean_object* v_size_1448_; 
v_size_1448_ = lean_ctor_get(v_l_1416_, 0);
lean_inc(v_size_1448_);
v___y_1440_ = v_size_1448_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___y_1440_ = v___x_1449_;
goto v___jp_1439_;
}
v___jp_1428_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_nat_add(v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec(v___y_1430_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_r_1400_);
lean_ctor_set(v___x_1423_, 3, v_r_1417_);
lean_ctor_set(v___x_1423_, 2, v_v_1398_);
lean_ctor_set(v___x_1423_, 1, v_k_1397_);
lean_ctor_set(v___x_1423_, 0, v___x_1432_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_r_1417_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_r_1400_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 4, v___x_1434_);
lean_ctor_set(v___x_1411_, 3, v___y_1429_);
lean_ctor_set(v___x_1411_, 2, v_v_1415_);
lean_ctor_set(v___x_1411_, 1, v_k_1414_);
lean_ctor_set(v___x_1411_, 0, v___x_1427_);
v___x_1436_ = v___x_1411_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1414_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1415_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___y_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
v___jp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_nat_add(v___x_1426_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec(v___x_1426_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_l_1416_);
lean_ctor_set(v___x_1213_, 0, v___x_1441_);
v___x_1443_ = v___x_1213_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_l_1210_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_l_1416_);
v___x_1443_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_nat_add(v___x_1425_, v_size_1418_);
if (lean_obj_tag(v_r_1417_) == 0)
{
lean_object* v_size_1445_; 
v_size_1445_ = lean_ctor_get(v_r_1417_, 0);
lean_inc(v_size_1445_);
v___y_1429_ = v___x_1443_;
v___y_1430_ = v___x_1444_;
v___y_1431_ = v_size_1445_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___y_1429_ = v___x_1443_;
v___y_1430_ = v___x_1444_;
v___y_1431_ = v___x_1446_;
goto v___jp_1428_;
}
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_del_object(v___x_1213_);
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v___x_1456_, v_size_1395_);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1396_);
lean_dec(v_size_1396_);
v___x_1459_ = lean_nat_add(v___x_1457_, v_size_1413_);
lean_dec(v___x_1457_);
lean_inc_ref(v_l_1210_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 4, v_l_1399_);
lean_ctor_set(v___x_1411_, 3, v_l_1210_);
lean_ctor_set(v___x_1411_, 2, v_v_1209_);
lean_ctor_set(v___x_1411_, 1, v_k_1208_);
lean_ctor_set(v___x_1411_, 0, v___x_1459_);
v___x_1461_ = v___x_1411_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_l_1210_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_l_1399_);
v___x_1461_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v_l_1210_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; 
v_unused_1469_ = lean_ctor_get(v_l_1210_, 4);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_l_1210_, 3);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_l_1210_, 2);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_l_1210_, 1);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_l_1210_, 0);
lean_dec(v_unused_1473_);
v___x_1463_ = v_l_1210_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v_l_1210_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v_r_1400_);
lean_ctor_set(v___x_1463_, 3, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v_v_1398_);
lean_ctor_set(v___x_1463_, 1, v_k_1397_);
lean_ctor_set(v___x_1463_, 0, v___x_1458_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1397_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1398_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_r_1400_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref_known(v_l_1399_, 5);
lean_del_object(v___x_1411_);
lean_dec(v_v_1398_);
lean_dec(v_k_1397_);
lean_dec(v_size_1396_);
lean_dec_ref_known(v_l_1210_, 5);
lean_del_object(v___x_1213_);
lean_dec(v_v_1209_);
lean_dec(v_k_1208_);
v___x_1475_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1476_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1475_);
return v___x_1476_;
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_del_object(v___x_1411_);
lean_dec(v_r_1400_);
lean_dec(v_v_1398_);
lean_dec(v_k_1397_);
lean_dec(v_size_1396_);
lean_dec_ref_known(v_l_1210_, 5);
lean_del_object(v___x_1213_);
lean_dec(v_v_1209_);
lean_dec(v_k_1208_);
v___x_1477_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1478_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1477_);
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_size_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v_size_1485_ = lean_ctor_get(v_l_1210_, 0);
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v___x_1486_, v_size_1485_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1394_);
lean_ctor_set(v___x_1213_, 0, v___x_1487_);
v___x_1489_ = v___x_1213_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_l_1210_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___x_1394_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_l_1491_; 
v_l_1491_ = lean_ctor_get(v___x_1394_, 3);
lean_inc(v_l_1491_);
if (lean_obj_tag(v_l_1491_) == 0)
{
lean_object* v_r_1492_; 
v_r_1492_ = lean_ctor_get(v___x_1394_, 4);
lean_inc(v_r_1492_);
if (lean_obj_tag(v_r_1492_) == 0)
{
lean_object* v_size_1493_; lean_object* v_k_1494_; lean_object* v_v_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1509_; 
v_size_1493_ = lean_ctor_get(v___x_1394_, 0);
v_k_1494_ = lean_ctor_get(v___x_1394_, 1);
v_v_1495_ = lean_ctor_get(v___x_1394_, 2);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1510_ = lean_ctor_get(v___x_1394_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v___x_1394_, 3);
lean_dec(v_unused_1511_);
v___x_1497_ = v___x_1394_;
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_v_1495_);
lean_inc(v_k_1494_);
lean_inc(v_size_1493_);
lean_dec(v___x_1394_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_size_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v_size_1499_ = lean_ctor_get(v_l_1491_, 0);
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = lean_nat_add(v___x_1500_, v_size_1493_);
lean_dec(v_size_1493_);
v___x_1502_ = lean_nat_add(v___x_1500_, v_size_1499_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v_l_1491_);
lean_ctor_set(v___x_1497_, 3, v_l_1210_);
lean_ctor_set(v___x_1497_, 2, v_v_1209_);
lean_ctor_set(v___x_1497_, 1, v_k_1208_);
lean_ctor_set(v___x_1497_, 0, v___x_1502_);
v___x_1504_ = v___x_1497_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_l_1210_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_l_1491_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_r_1492_);
lean_ctor_set(v___x_1213_, 3, v___x_1504_);
lean_ctor_set(v___x_1213_, 2, v_v_1495_);
lean_ctor_set(v___x_1213_, 1, v_k_1494_);
lean_ctor_set(v___x_1213_, 0, v___x_1501_);
v___x_1506_ = v___x_1213_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1494_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1495_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_r_1492_);
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
lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1537_; 
v_k_1512_ = lean_ctor_get(v___x_1394_, 1);
v_v_1513_ = lean_ctor_get(v___x_1394_, 2);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1538_ = lean_ctor_get(v___x_1394_, 4);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v___x_1394_, 3);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1540_);
v___x_1515_ = v___x_1394_;
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_v_1513_);
lean_inc(v_k_1512_);
lean_dec(v___x_1394_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1533_; 
v_k_1517_ = lean_ctor_get(v_l_1491_, 1);
v_v_1518_ = lean_ctor_get(v_l_1491_, 2);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_l_1491_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1534_ = lean_ctor_get(v_l_1491_, 4);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1491_, 3);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1491_, 0);
lean_dec(v_unused_1536_);
v___x_1520_ = v_l_1491_;
v_isShared_1521_ = v_isSharedCheck_1533_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_v_1518_);
lean_inc(v_k_1517_);
lean_dec(v_l_1491_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1533_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = lean_unsigned_to_nat(3u);
v___x_1523_ = lean_unsigned_to_nat(1u);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 4, v_r_1492_);
lean_ctor_set(v___x_1520_, 3, v_r_1492_);
lean_ctor_set(v___x_1520_, 2, v_v_1209_);
lean_ctor_set(v___x_1520_, 1, v_k_1208_);
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_r_1492_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_r_1492_);
v___x_1525_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 3, v_r_1492_);
lean_ctor_set(v___x_1515_, 0, v___x_1523_);
v___x_1527_ = v___x_1515_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_r_1492_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1492_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1527_);
lean_ctor_set(v___x_1213_, 3, v___x_1525_);
lean_ctor_set(v___x_1213_, 2, v_v_1518_);
lean_ctor_set(v___x_1213_, 1, v_k_1517_);
lean_ctor_set(v___x_1213_, 0, v___x_1522_);
v___x_1529_ = v___x_1213_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1517_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1541_; 
v_r_1541_ = lean_ctor_get(v___x_1394_, 4);
lean_inc(v_r_1541_);
if (lean_obj_tag(v_r_1541_) == 0)
{
lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1555_; 
v_k_1542_ = lean_ctor_get(v___x_1394_, 1);
v_v_1543_ = lean_ctor_get(v___x_1394_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1556_ = lean_ctor_get(v___x_1394_, 4);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v___x_1394_, 3);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1558_);
v___x_1545_ = v___x_1394_;
v_isShared_1546_ = v_isSharedCheck_1555_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
lean_dec(v___x_1394_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1555_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1547_ = lean_unsigned_to_nat(3u);
v___x_1548_ = lean_unsigned_to_nat(1u);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v_l_1491_);
lean_ctor_set(v___x_1545_, 2, v_v_1209_);
lean_ctor_set(v___x_1545_, 1, v_k_1208_);
lean_ctor_set(v___x_1545_, 0, v___x_1548_);
v___x_1550_ = v___x_1545_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_l_1491_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_l_1491_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_r_1541_);
lean_ctor_set(v___x_1213_, 3, v___x_1550_);
lean_ctor_set(v___x_1213_, 2, v_v_1543_);
lean_ctor_set(v___x_1213_, 1, v_k_1542_);
lean_ctor_set(v___x_1213_, 0, v___x_1547_);
v___x_1552_ = v___x_1213_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_r_1541_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = lean_unsigned_to_nat(2u);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1394_);
lean_ctor_set(v___x_1213_, 3, v_r_1541_);
lean_ctor_set(v___x_1213_, 0, v___x_1559_);
v___x_1561_ = v___x_1213_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v___x_1394_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1394_);
lean_ctor_set(v___x_1213_, 3, v___x_1394_);
lean_ctor_set(v___x_1213_, 0, v___x_1563_);
v___x_1565_ = v___x_1213_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1208_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1209_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v___x_1394_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v_k_1204_);
lean_ctor_set(v___x_1569_, 2, v_v_1205_);
lean_ctor_set(v___x_1569_, 3, v_t_1206_);
lean_ctor_set(v___x_1569_, 4, v_t_1206_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1570_, lean_object* v_x_1571_){
_start:
{
if (lean_obj_tag(v_x_1571_) == 0)
{
lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v_l_1574_; lean_object* v_r_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_k_1572_ = lean_ctor_get(v_x_1571_, 1);
lean_inc(v_k_1572_);
v_v_1573_ = lean_ctor_get(v_x_1571_, 2);
lean_inc(v_v_1573_);
v_l_1574_ = lean_ctor_get(v_x_1571_, 3);
lean_inc(v_l_1574_);
v_r_1575_ = lean_ctor_get(v_x_1571_, 4);
lean_inc(v_r_1575_);
lean_dec_ref_known(v_x_1571_, 5);
v___x_1576_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1570_, v_l_1574_);
v___x_1577_ = 1;
v___x_1578_ = l_Lean_Name_toString(v_k_1572_, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_v_1573_);
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1578_, v___x_1579_, v___x_1576_);
v_init_1570_ = v___x_1580_;
v_x_1571_ = v_r_1575_;
goto _start;
}
else
{
return v_init_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1582_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = lean_box(1);
v___x_1584_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1583_, v_m_1582_);
v___x_1585_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
if (lean_obj_tag(v_a_1586_) == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_array_to_list(v_a_1587_);
return v___x_1588_;
}
else
{
lean_object* v_head_1589_; lean_object* v_tail_1590_; lean_object* v___x_1591_; 
v_head_1589_ = lean_ctor_get(v_a_1586_, 0);
lean_inc(v_head_1589_);
v_tail_1590_ = lean_ctor_get(v_a_1586_, 1);
lean_inc(v_tail_1590_);
lean_dec_ref_known(v_a_1586_, 2);
v___x_1591_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1587_, v_head_1589_);
v_a_1586_ = v_tail_1590_;
v_a_1587_ = v___x_1591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1601_){
_start:
{
lean_object* v_idx_1602_; lean_object* v_name_1603_; lean_object* v_platform_1604_; lean_object* v_leanHash_1605_; uint64_t v_configHash_1606_; lean_object* v_options_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_idx_1602_ = lean_ctor_get(v_x_1601_, 0);
lean_inc(v_idx_1602_);
v_name_1603_ = lean_ctor_get(v_x_1601_, 1);
lean_inc(v_name_1603_);
v_platform_1604_ = lean_ctor_get(v_x_1601_, 2);
lean_inc_ref(v_platform_1604_);
v_leanHash_1605_ = lean_ctor_get(v_x_1601_, 3);
lean_inc_ref(v_leanHash_1605_);
v_configHash_1606_ = lean_ctor_get_uint64(v_x_1601_, sizeof(void*)*5);
v_options_1607_ = lean_ctor_get(v_x_1601_, 4);
lean_inc(v_options_1607_);
lean_dec_ref(v_x_1601_);
v___x_1608_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1609_ = l_Lean_JsonNumber_fromNat(v_idx_1602_);
v___x_1610_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1615_ = 1;
v___x_1616_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1603_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___x_1612_);
v___x_1620_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_platform_1604_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___x_1612_);
v___x_1624_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_leanHash_1605_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1612_);
v___x_1628_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1629_ = l_Lake_lowerHexUInt64(v_configHash_1606_);
v___x_1630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1612_);
v___x_1633_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1634_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1607_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1612_);
v___x_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1612_);
v___x_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1632_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1627_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1623_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1619_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1613_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1644_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1642_, v___x_1643_);
v___x_1645_ = l_Lean_Json_mkObj(v___x_1644_);
lean_dec(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1646_, lean_object* v_msg_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1649_, lean_object* v_k_1650_, lean_object* v_v_1651_, lean_object* v_t_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1650_, v_v_1651_, v_t_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1654_, lean_object* v_t_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1654_, v_t_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1659_, lean_object* v_k_1660_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = l_Lean_Json_getObjValD(v_j_1659_, v_k_1660_);
v___x_1662_ = l_Lean_Json_getNat_x3f(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1663_, lean_object* v_k_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1663_, v_k_1664_);
lean_dec_ref(v_k_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1666_, lean_object* v_k_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = l_Lean_Json_getObjValD(v_j_1666_, v_k_1667_);
v___x_1669_ = l_Lean_Name_fromJson_x3f(v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1670_, lean_object* v_k_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1670_, v_k_1671_);
lean_dec_ref(v_k_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1673_, lean_object* v_k_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = l_Lean_Json_getObjValD(v_j_1673_, v_k_1674_);
v___x_1676_ = l_Lean_Json_getStr_x3f(v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1677_, lean_object* v_k_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1677_, v_k_1678_);
lean_dec_ref(v_k_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1680_, lean_object* v_k_1681_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = l_Lean_Json_getObjValD(v_j_1680_, v_k_1681_);
v___x_1683_ = l_Lake_Hash_fromJson_x3f(v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1684_, lean_object* v_k_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1684_, v_k_1685_);
lean_dec_ref(v_k_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_object* v_k_1692_; lean_object* v_v_1693_; lean_object* v_l_1694_; lean_object* v_r_1695_; lean_object* v___x_1696_; 
v_k_1692_ = lean_ctor_get(v_x_1691_, 1);
lean_inc(v_k_1692_);
v_v_1693_ = lean_ctor_get(v_x_1691_, 2);
lean_inc(v_v_1693_);
v_l_1694_ = lean_ctor_get(v_x_1691_, 3);
lean_inc(v_l_1694_);
v_r_1695_ = lean_ctor_get(v_x_1691_, 4);
lean_inc(v_r_1695_);
lean_dec_ref_known(v_x_1691_, 5);
v___x_1696_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1690_, v_l_1694_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_dec(v_r_1695_);
lean_dec(v_v_1693_);
lean_dec(v_k_1692_);
return v___x_1696_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1737_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1737_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1737_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1702_ = lean_string_dec_eq(v_k_1692_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v_n_1703_; uint8_t v___x_1704_; 
lean_inc(v_k_1692_);
v_n_1703_ = l_String_toName(v_k_1692_);
v___x_1704_ = l_Lean_Name_isAnonymous(v_n_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_del_object(v___x_1699_);
lean_dec(v_k_1692_);
v___x_1705_ = l_Lean_Json_getStr_x3f(v_v_1693_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_n_1703_);
lean_dec(v_a_1697_);
lean_dec(v_r_1695_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1715_; 
v_a_1714_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1703_, v_a_1714_, v_a_1697_);
v_init_1690_ = v___x_1715_;
v_x_1691_ = v_r_1695_;
goto _start;
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec(v_n_1703_);
lean_dec(v_a_1697_);
lean_dec(v_r_1695_);
lean_dec(v_v_1693_);
v___x_1717_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1718_ = lean_string_append(v___x_1717_, v_k_1692_);
lean_dec(v_k_1692_);
v___x_1719_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1720_);
v___x_1722_ = v___x_1699_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v___x_1724_; 
lean_del_object(v___x_1699_);
lean_dec(v_k_1692_);
v___x_1724_ = l_Lean_Json_getStr_x3f(v_v_1693_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1697_);
lean_dec(v_r_1695_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
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
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_a_1733_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1734_ = lean_box(0);
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1734_, v_a_1733_, v_a_1697_);
v_init_1690_ = v___x_1735_;
v_x_1691_ = v_r_1695_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_init_1690_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 5)
{
lean_object* v_kvPairs_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_kvPairs_1741_ = lean_ctor_get(v_x_1740_, 0);
lean_inc(v_kvPairs_1741_);
lean_dec_ref_known(v_x_1740_, 1);
v___x_1742_ = lean_box(1);
v___x_1743_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1742_, v_kvPairs_1741_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1744_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1745_ = lean_unsigned_to_nat(80u);
v___x_1746_ = l_Lean_Json_pretty(v_x_1740_, v___x_1745_);
v___x_1747_ = lean_string_append(v___x_1744_, v___x_1746_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1749_ = lean_string_append(v___x_1747_, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1751_, lean_object* v_k_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = l_Lean_Json_getObjValD(v_j_1751_, v_k_1752_);
v___x_1754_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1755_, lean_object* v_k_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1755_, v_k_1756_);
lean_dec_ref(v_k_1756_);
return v_res_1757_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = 1;
v___x_1787_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1787_, v___x_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1791_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1792_ = lean_string_append(v___x_1791_, v___x_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = 1;
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1796_, v___x_1795_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1799_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1800_ = lean_string_append(v___x_1799_, v___x_1798_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1803_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1804_ = lean_string_append(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = 1;
v___x_1808_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1811_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1812_ = lean_string_append(v___x_1811_, v___x_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1814_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1815_ = lean_string_append(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = 1;
v___x_1819_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1820_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1819_, v___x_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1822_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1823_ = lean_string_append(v___x_1822_, v___x_1821_);
return v___x_1823_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1825_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1826_ = lean_string_append(v___x_1825_, v___x_1824_);
return v___x_1826_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = 1;
v___x_1830_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1831_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1833_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1834_ = lean_string_append(v___x_1833_, v___x_1832_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1836_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1837_ = lean_string_append(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = 1;
v___x_1841_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1842_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1844_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1845_ = lean_string_append(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1847_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1848_ = lean_string_append(v___x_1847_, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = 1;
v___x_1852_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1853_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1855_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1856_ = lean_string_append(v___x_1855_, v___x_1854_);
return v___x_1856_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1858_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1859_ = lean_string_append(v___x_1858_, v___x_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1860_);
v___x_1862_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1860_, v___x_1861_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_json_1860_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_1868_ = lean_string_append(v___x_1867_, v_a_1863_);
lean_dec(v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1868_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_json_1860_);
v_a_1873_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1862_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1862_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 0);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
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
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1882_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1860_);
v___x_1883_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1860_, v___x_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_1889_ = lean_string_append(v___x_1888_, v_a_1884_);
lean_dec(v_a_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1889_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1894_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1883_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1883_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
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
lean_object* v_a_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_a_1902_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1903_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1860_);
v___x_1904_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1860_, v___x_1903_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1909_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1910_ = lean_string_append(v___x_1909_, v_a_1905_);
lean_dec(v_a_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1910_);
v___x_1912_ = v___x_1907_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1915_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1904_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1904_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 0);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
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
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_a_1923_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1924_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1860_);
v___x_1925_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1860_, v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1923_);
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1935_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1935_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
v___x_1931_ = lean_string_append(v___x_1930_, v_a_1926_);
lean_dec(v_a_1926_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
else
{
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1923_);
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1936_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1925_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1925_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 0);
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
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
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_a_1944_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1945_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1860_);
v___x_1946_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1860_, v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_a_1944_);
lean_dec(v_a_1923_);
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1956_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1956_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1951_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
v___x_1952_ = lean_string_append(v___x_1951_, v_a_1947_);
lean_dec(v_a_1947_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1944_);
lean_dec(v_a_1923_);
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1957_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1946_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1946_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 0);
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
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
lean_object* v_a_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_a_1965_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_1966_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1967_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1860_, v___x_1966_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v_a_1965_);
lean_dec(v_a_1944_);
lean_dec(v_a_1923_);
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1977_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1977_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_1973_ = lean_string_append(v___x_1972_, v_a_1968_);
lean_dec(v_a_1968_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1973_);
v___x_1975_ = v___x_1970_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
else
{
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_a_1965_);
lean_dec(v_a_1944_);
lean_dec(v_a_1923_);
lean_dec(v_a_1902_);
lean_dec(v_a_1881_);
v_a_1978_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1967_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1967_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 0);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
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
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1995_; 
v_a_1986_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1988_ = v___x_1967_;
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1967_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; uint64_t v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1990_, 0, v_a_1881_);
lean_ctor_set(v___x_1990_, 1, v_a_1902_);
lean_ctor_set(v___x_1990_, 2, v_a_1923_);
lean_ctor_set(v___x_1990_, 3, v_a_1944_);
lean_ctor_set(v___x_1990_, 4, v_a_1986_);
v___x_1991_ = lean_unbox_uint64(v_a_1965_);
lean_dec(v_a_1965_);
lean_ctor_set_uint64(v___x_1990_, sizeof(void*)*5, v___x_1991_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
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
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_2000_ = lean_mk_io_user_error(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_2001_, lean_object* v___x_2002_, lean_object* v_h_2003_){
_start:
{
uint8_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = 1;
v___x_2006_ = lean_io_prim_handle_mk(v___x_2001_, v___x_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = 1;
v___x_2009_ = lean_io_prim_handle_try_lock(v_a_2007_, v___x_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; uint8_t v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec(v_a_2007_);
v___x_2012_ = lean_io_prim_handle_unlock(v_h_2003_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_2012_, 0);
lean_dec(v_unused_2021_);
v___x_2014_ = v___x_2012_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v___x_2012_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2012_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2012_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_io_prim_handle_unlock(v_h_2003_);
if (lean_obj_tag(v___x_2030_) == 0)
{
uint8_t v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref_known(v___x_2030_, 1);
v___x_2031_ = 3;
v___x_2032_ = lean_io_prim_handle_mk(v___x_2002_, v___x_2031_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = lean_io_prim_handle_lock(v_a_2033_, v___x_2008_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2035_; 
lean_dec_ref_known(v___x_2034_, 1);
v___x_2035_ = lean_io_prim_handle_unlock(v_a_2007_);
lean_dec(v_a_2007_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2043_);
v___x_2037_ = v___x_2035_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___x_2035_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v_a_2033_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2033_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_2033_);
v_a_2044_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2035_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2035_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_a_2033_);
lean_dec(v_a_2007_);
v_a_2052_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2034_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2034_);
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
lean_dec(v_a_2007_);
return v___x_2032_;
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2007_);
v_a_2060_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2030_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2030_);
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
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2007_);
v_a_2068_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2009_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2009_);
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
else
{
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v_h_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lake_importConfigFile___lam__0(v___x_2076_, v___x_2077_, v_h_2078_);
lean_dec(v_h_2078_);
lean_dec_ref(v___x_2077_);
lean_dec_ref(v___x_2076_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___y_2093_; lean_object* v_a_2094_; lean_object* v_lakeEnv_2096_; lean_object* v_wsDir_2097_; lean_object* v_pkgIdx_2098_; lean_object* v_pkgName_2099_; lean_object* v_pkgDir_2100_; lean_object* v_configFile_2101_; lean_object* v_lakeOpts_2102_; lean_object* v_leanOpts_2103_; uint8_t v_reconfigure_2104_; lean_object* v___x_2105_; 
v_lakeEnv_2096_ = lean_ctor_get(v_cfg_2089_, 0);
lean_inc_ref(v_lakeEnv_2096_);
v_wsDir_2097_ = lean_ctor_get(v_cfg_2089_, 2);
lean_inc_ref(v_wsDir_2097_);
v_pkgIdx_2098_ = lean_ctor_get(v_cfg_2089_, 3);
lean_inc(v_pkgIdx_2098_);
v_pkgName_2099_ = lean_ctor_get(v_cfg_2089_, 4);
lean_inc(v_pkgName_2099_);
v_pkgDir_2100_ = lean_ctor_get(v_cfg_2089_, 6);
lean_inc_ref(v_pkgDir_2100_);
v_configFile_2101_ = lean_ctor_get(v_cfg_2089_, 8);
lean_inc_ref_n(v_configFile_2101_, 2);
v_lakeOpts_2102_ = lean_ctor_get(v_cfg_2089_, 12);
lean_inc(v_lakeOpts_2102_);
v_leanOpts_2103_ = lean_ctor_get(v_cfg_2089_, 13);
lean_inc_ref(v_leanOpts_2103_);
v_reconfigure_2104_ = lean_ctor_get_uint8(v_cfg_2089_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2089_);
v___x_2105_ = l_System_FilePath_fileName(v_configFile_2101_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_wsDir_2097_);
lean_dec_ref(v_lakeEnv_2096_);
v___x_2106_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2107_ = lean_array_get_size(v_a_2090_);
v___x_2108_ = lean_array_push(v_a_2090_, v___x_2106_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
return v___x_2109_;
}
else
{
lean_object* v_val_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_configDir_2116_; lean_object* v___x_2117_; 
v_val_2110_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2111_ = l_Lake_defaultLakeDir;
v___x_2112_ = l_Lake_joinRelative(v_wsDir_2097_, v___x_2111_);
v___x_2113_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2114_ = l_Lake_joinRelative(v___x_2112_, v___x_2113_);
lean_inc(v_pkgIdx_2098_);
v___x_2115_ = l_Nat_reprFast(v_pkgIdx_2098_);
v_configDir_2116_ = l_Lake_joinRelative(v___x_2114_, v___x_2115_);
lean_inc_ref(v_configDir_2116_);
v___x_2117_ = l_IO_FS_createDirAll(v_configDir_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = l_Lake_computeTextFileHash(v_configFile_2101_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_h_2127_; lean_object* v_lakeOpts_2128_; lean_object* v___y_2129_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v_h_2312_; lean_object* v___y_2313_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2110_, 2);
v___x_2121_ = l_System_FilePath_withExtension(v_val_2110_, v___x_2120_);
lean_inc_ref_n(v_configDir_2116_, 2);
v___x_2122_ = l_Lake_joinRelative(v_configDir_2116_, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2124_ = l_System_FilePath_withExtension(v_val_2110_, v___x_2123_);
v___x_2125_ = l_Lake_joinRelative(v_configDir_2116_, v___x_2124_);
v___x_2281_ = l_System_FilePath_pathExists(v___x_2125_);
v___x_2282_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2283_ = l_System_FilePath_withExtension(v_val_2110_, v___x_2282_);
v___x_2284_ = l_Lake_joinRelative(v_configDir_2116_, v___x_2283_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_inc_ref(v_pkgDir_2100_);
v___x_2401_ = l_Lake_joinRelative(v_pkgDir_2100_, v___x_2111_);
v___x_2402_ = l_IO_FS_createDirAll(v___x_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
uint8_t v___x_2403_; lean_object* v___x_2404_; 
lean_dec_ref_known(v___x_2402_, 1);
v___x_2403_ = 2;
v___x_2404_ = lean_io_prim_handle_mk(v___x_2125_, v___x_2403_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; 
lean_dec_ref(v___x_2284_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = 1;
v___x_2407_ = lean_io_prim_handle_lock(v_a_2405_, v___x_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_dec_ref_known(v___x_2407_, 1);
v_h_2127_ = v_a_2405_;
v_lakeOpts_2128_ = v_lakeOpts_2102_;
v___y_2129_ = v_a_2090_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec(v_a_2405_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = lean_io_error_to_string(v_a_2408_);
v___x_2410_ = 3;
v___x_2411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*1, v___x_2410_);
v___x_2412_ = lean_array_get_size(v_a_2090_);
v___x_2413_ = lean_array_push(v_a_2090_, v___x_2411_);
v___x_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
return v___x_2414_;
}
}
else
{
lean_object* v_a_2415_; 
v_a_2415_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2404_, 1);
if (lean_obj_tag(v_a_2415_) == 0)
{
uint8_t v___x_2416_; lean_object* v___x_2417_; 
lean_dec_ref_known(v_a_2415_, 2);
v___x_2416_ = 0;
v___x_2417_ = lean_io_prim_handle_mk(v___x_2125_, v___x_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v_h_2312_ = v_a_2418_;
v___y_2313_ = v_a_2090_;
goto v___jp_2311_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2419_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2420_ = lean_io_error_to_string(v_a_2419_);
v___x_2421_ = 3;
v___x_2422_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1, v___x_2421_);
v___x_2423_ = lean_array_get_size(v_a_2090_);
v___x_2424_ = lean_array_push(v_a_2090_, v___x_2422_);
v___x_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
return v___x_2425_;
}
}
else
{
lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v___x_2426_ = lean_io_error_to_string(v_a_2415_);
v___x_2427_ = 3;
v___x_2428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*1, v___x_2427_);
v___x_2429_ = lean_array_get_size(v_a_2090_);
v___x_2430_ = lean_array_push(v_a_2090_, v___x_2428_);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2432_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2433_ = lean_io_error_to_string(v_a_2432_);
v___x_2434_ = 3;
v___x_2435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*1, v___x_2434_);
v___x_2436_ = lean_array_get_size(v_a_2090_);
v___x_2437_ = lean_array_push(v_a_2090_, v___x_2435_);
v___x_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
return v___x_2438_;
}
}
else
{
uint8_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = 0;
v___x_2440_ = lean_io_prim_handle_mk(v___x_2125_, v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v_h_2312_ = v_a_2441_;
v___y_2313_ = v_a_2090_;
goto v___jp_2311_;
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2442_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2443_ = lean_io_error_to_string(v_a_2442_);
v___x_2444_ = 3;
v___x_2445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set_uint8(v___x_2445_, sizeof(void*)*1, v___x_2444_);
v___x_2446_ = lean_array_get_size(v_a_2090_);
v___x_2447_ = lean_array_push(v_a_2090_, v___x_2445_);
v___x_2448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
return v___x_2448_;
}
}
v___jp_2126_:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_io_remove_file(v___x_2122_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint64_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2130_, 1);
lean_dec_ref(v___x_2125_);
v___x_2131_ = l_System_Platform_target;
v___x_2132_ = l_Lake_Env_leanGithash(v_lakeEnv_2096_);
lean_dec_ref(v_lakeEnv_2096_);
lean_inc(v_lakeOpts_2128_);
lean_inc(v_pkgName_2099_);
lean_inc(v_pkgIdx_2098_);
v___x_2133_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2133_, 0, v_pkgIdx_2098_);
lean_ctor_set(v___x_2133_, 1, v_pkgName_2099_);
lean_ctor_set(v___x_2133_, 2, v___x_2131_);
lean_ctor_set(v___x_2133_, 3, v___x_2132_);
lean_ctor_set(v___x_2133_, 4, v_lakeOpts_2128_);
v___x_2134_ = lean_unbox_uint64(v_a_2119_);
lean_dec(v_a_2119_);
lean_ctor_set_uint64(v___x_2133_, sizeof(void*)*5, v___x_2134_);
v___x_2135_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2133_);
v___x_2136_ = lean_unsigned_to_nat(80u);
v___x_2137_ = l_Lean_Json_pretty(v___x_2135_, v___x_2136_);
v___x_2138_ = l_IO_FS_Handle_putStrLn(v_h_2127_, v___x_2137_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref_known(v___x_2138_, 1);
v___x_2139_ = lean_io_prim_handle_flush(v_h_2127_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v___x_2140_; 
lean_dec_ref_known(v___x_2139_, 1);
v___x_2140_ = lean_io_prim_handle_truncate(v_h_2127_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v___x_2141_; 
lean_dec_ref_known(v___x_2140_, 1);
v___x_2141_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2098_, v_pkgName_2099_, v_pkgDir_2100_, v_lakeOpts_2128_, v_leanOpts_2103_, v_configFile_2101_, v___y_2129_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v_a_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
v_a_2143_ = lean_ctor_get(v___x_2141_, 1);
lean_inc(v_a_2143_);
v___x_2144_ = 1;
v___x_2145_ = l_Lean_writeModule(v_a_2142_, v___x_2122_, v___x_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; 
lean_dec_ref_known(v___x_2145_, 1);
v___x_2146_ = lean_io_prim_handle_unlock(v_h_2127_);
lean_dec(v_h_2127_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_dec_ref_known(v___x_2146_, 1);
lean_dec(v_a_2143_);
return v___x_2141_;
}
else
{
lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2159_; 
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2160_ = lean_ctor_get(v___x_2141_, 1);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v___x_2141_, 0);
lean_dec(v_unused_2161_);
v___x_2148_ = v___x_2141_;
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v___x_2141_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_a_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2151_ = lean_io_error_to_string(v_a_2150_);
v___x_2152_ = 3;
v___x_2153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*1, v___x_2152_);
v___x_2154_ = lean_array_get_size(v_a_2143_);
v___x_2155_ = lean_array_push(v_a_2143_, v___x_2153_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set_tag(v___x_2148_, 1);
lean_ctor_set(v___x_2148_, 1, v___x_2155_);
lean_ctor_set(v___x_2148_, 0, v___x_2154_);
v___x_2157_ = v___x_2148_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_h_2127_);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; lean_object* v_unused_2176_; 
v_unused_2175_ = lean_ctor_get(v___x_2141_, 1);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v___x_2141_, 0);
lean_dec(v_unused_2176_);
v___x_2163_ = v___x_2141_;
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v___x_2141_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_a_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v_a_2165_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2166_ = lean_io_error_to_string(v_a_2165_);
v___x_2167_ = 3;
v___x_2168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*1, v___x_2167_);
v___x_2169_ = lean_array_get_size(v_a_2143_);
v___x_2170_ = lean_array_push(v_a_2143_, v___x_2168_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 1);
lean_ctor_set(v___x_2163_, 1, v___x_2170_);
lean_ctor_set(v___x_2163_, 0, v___x_2169_);
v___x_2172_ = v___x_2163_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
return v___x_2141_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v_lakeOpts_2128_);
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
v_a_2177_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2178_ = lean_io_error_to_string(v_a_2177_);
v___x_2179_ = 3;
v___x_2180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*1, v___x_2179_);
v___x_2181_ = lean_array_get_size(v___y_2129_);
v___x_2182_ = lean_array_push(v___y_2129_, v___x_2180_);
v___x_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
return v___x_2183_;
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_lakeOpts_2128_);
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
v_a_2184_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2185_ = lean_io_error_to_string(v_a_2184_);
v___x_2186_ = 3;
v___x_2187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*1, v___x_2186_);
v___x_2188_ = lean_array_get_size(v___y_2129_);
v___x_2189_ = lean_array_push(v___y_2129_, v___x_2187_);
v___x_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
return v___x_2190_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_lakeOpts_2128_);
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
v_a_2191_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2192_ = lean_io_error_to_string(v_a_2191_);
v___x_2193_ = 3;
v___x_2194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*1, v___x_2193_);
v___x_2195_ = lean_array_get_size(v___y_2129_);
v___x_2196_ = lean_array_push(v___y_2129_, v___x_2194_);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
return v___x_2197_;
}
}
else
{
lean_object* v_a_2198_; 
v_a_2198_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2130_, 1);
if (lean_obj_tag(v_a_2198_) == 11)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint64_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref_known(v_a_2198_, 2);
lean_dec_ref(v___x_2125_);
v___x_2199_ = l_System_Platform_target;
v___x_2200_ = l_Lake_Env_leanGithash(v_lakeEnv_2096_);
lean_dec_ref(v_lakeEnv_2096_);
lean_inc(v_lakeOpts_2128_);
lean_inc(v_pkgName_2099_);
lean_inc(v_pkgIdx_2098_);
v___x_2201_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2201_, 0, v_pkgIdx_2098_);
lean_ctor_set(v___x_2201_, 1, v_pkgName_2099_);
lean_ctor_set(v___x_2201_, 2, v___x_2199_);
lean_ctor_set(v___x_2201_, 3, v___x_2200_);
lean_ctor_set(v___x_2201_, 4, v_lakeOpts_2128_);
v___x_2202_ = lean_unbox_uint64(v_a_2119_);
lean_dec(v_a_2119_);
lean_ctor_set_uint64(v___x_2201_, sizeof(void*)*5, v___x_2202_);
v___x_2203_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2201_);
v___x_2204_ = lean_unsigned_to_nat(80u);
v___x_2205_ = l_Lean_Json_pretty(v___x_2203_, v___x_2204_);
v___x_2206_ = l_IO_FS_Handle_putStrLn(v_h_2127_, v___x_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2207_; 
lean_dec_ref_known(v___x_2206_, 1);
v___x_2207_ = lean_io_prim_handle_flush(v_h_2127_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; 
lean_dec_ref_known(v___x_2207_, 1);
v___x_2208_ = lean_io_prim_handle_truncate(v_h_2127_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref_known(v___x_2208_, 1);
v___x_2209_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2098_, v_pkgName_2099_, v_pkgDir_2100_, v_lakeOpts_2128_, v_leanOpts_2103_, v_configFile_2101_, v___y_2129_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_a_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
v_a_2211_ = lean_ctor_get(v___x_2209_, 1);
lean_inc(v_a_2211_);
v___x_2212_ = 1;
v___x_2213_ = l_Lean_writeModule(v_a_2210_, v___x_2122_, v___x_2212_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; 
lean_dec_ref_known(v___x_2213_, 1);
v___x_2214_ = lean_io_prim_handle_unlock(v_h_2127_);
lean_dec(v_h_2127_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_dec_ref_known(v___x_2214_, 1);
lean_dec(v_a_2211_);
return v___x_2209_;
}
else
{
lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2227_; 
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2228_ = lean_ctor_get(v___x_2209_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v___x_2209_, 0);
lean_dec(v_unused_2229_);
v___x_2216_ = v___x_2209_;
v_isShared_2217_ = v_isSharedCheck_2227_;
goto v_resetjp_2215_;
}
else
{
lean_dec(v___x_2209_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2227_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_a_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v_a_2218_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2219_ = lean_io_error_to_string(v_a_2218_);
v___x_2220_ = 3;
v___x_2221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*1, v___x_2220_);
v___x_2222_ = lean_array_get_size(v_a_2211_);
v___x_2223_ = lean_array_push(v_a_2211_, v___x_2221_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 1);
lean_ctor_set(v___x_2216_, 1, v___x_2223_);
lean_ctor_set(v___x_2216_, 0, v___x_2222_);
v___x_2225_ = v___x_2216_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_h_2127_);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; 
v_unused_2243_ = lean_ctor_get(v___x_2209_, 1);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v___x_2209_, 0);
lean_dec(v_unused_2244_);
v___x_2231_ = v___x_2209_;
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
else
{
lean_dec(v___x_2209_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_a_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2234_ = lean_io_error_to_string(v_a_2233_);
v___x_2235_ = 3;
v___x_2236_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2236_, 0, v___x_2234_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1, v___x_2235_);
v___x_2237_ = lean_array_get_size(v_a_2211_);
v___x_2238_ = lean_array_push(v_a_2211_, v___x_2236_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 1);
lean_ctor_set(v___x_2231_, 1, v___x_2238_);
lean_ctor_set(v___x_2231_, 0, v___x_2237_);
v___x_2240_ = v___x_2231_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
return v___x_2209_;
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec(v_lakeOpts_2128_);
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
v_a_2245_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2246_ = lean_io_error_to_string(v_a_2245_);
v___x_2247_ = 3;
v___x_2248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1, v___x_2247_);
v___x_2249_ = lean_array_get_size(v___y_2129_);
v___x_2250_ = lean_array_push(v___y_2129_, v___x_2248_);
v___x_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
return v___x_2251_;
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_dec(v_lakeOpts_2128_);
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
v_a_2252_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2253_ = lean_io_error_to_string(v_a_2252_);
v___x_2254_ = 3;
v___x_2255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*1, v___x_2254_);
v___x_2256_ = lean_array_get_size(v___y_2129_);
v___x_2257_ = lean_array_push(v___y_2129_, v___x_2255_);
v___x_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
return v___x_2258_;
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v_lakeOpts_2128_);
lean_dec(v_h_2127_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
v_a_2259_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2206_, 1);
v___x_2260_ = lean_io_error_to_string(v_a_2259_);
v___x_2261_ = 3;
v___x_2262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*1, v___x_2261_);
v___x_2263_ = lean_array_get_size(v___y_2129_);
v___x_2264_ = lean_array_push(v___y_2129_, v___x_2262_);
v___x_2265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
return v___x_2265_;
}
}
else
{
lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_lakeOpts_2128_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v___x_2266_ = lean_io_error_to_string(v_a_2198_);
v___x_2267_ = 3;
v___x_2268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set_uint8(v___x_2268_, sizeof(void*)*1, v___x_2267_);
v___x_2269_ = lean_array_get_size(v___y_2129_);
v___x_2270_ = lean_array_push(v___y_2129_, v___x_2268_);
v___x_2271_ = lean_io_prim_handle_unlock(v_h_2127_);
lean_dec(v_h_2127_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v___x_2272_; 
lean_dec_ref_known(v___x_2271_, 1);
v___x_2272_ = lean_io_remove_file(v___x_2125_);
lean_dec_ref(v___x_2125_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec_ref_known(v___x_2272_, 1);
v___y_2093_ = v___x_2269_;
v_a_2094_ = v___x_2270_;
goto v___jp_2092_;
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = lean_io_error_to_string(v_a_2273_);
v___x_2275_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*1, v___x_2267_);
v___x_2276_ = lean_array_push(v___x_2270_, v___x_2275_);
v___y_2093_ = v___x_2269_;
v_a_2094_ = v___x_2276_;
goto v___jp_2092_;
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v___x_2125_);
v_a_2277_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2278_ = lean_io_error_to_string(v_a_2277_);
v___x_2279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*1, v___x_2267_);
v___x_2280_ = lean_array_push(v___x_2270_, v___x_2279_);
v___y_2093_ = v___x_2269_;
v_a_2094_ = v___x_2280_;
goto v___jp_2092_;
}
}
}
}
v___jp_2285_:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lake_importConfigFile___lam__0(v___x_2284_, v___x_2125_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___x_2284_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v_options_2291_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_options_2291_ = lean_ctor_get(v___y_2286_, 4);
lean_inc(v_options_2291_);
lean_dec_ref(v___y_2286_);
v_h_2127_ = v_a_2290_;
v_lakeOpts_2128_ = v_options_2291_;
v___y_2129_ = v___y_2288_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v___y_2286_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2292_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2293_ = lean_io_error_to_string(v_a_2292_);
v___x_2294_ = 3;
v___x_2295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2294_);
v___x_2296_ = lean_array_get_size(v___y_2288_);
v___x_2297_ = lean_array_push(v___y_2288_, v___x_2295_);
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
return v___x_2298_;
}
}
v___jp_2299_:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lake_importConfigFile___lam__0(v___x_2284_, v___x_2125_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___x_2284_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v_h_2127_ = v_a_2303_;
v_lakeOpts_2128_ = v_lakeOpts_2102_;
v___y_2129_ = v___y_2301_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2304_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2305_ = lean_io_error_to_string(v_a_2304_);
v___x_2306_ = 3;
v___x_2307_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*1, v___x_2306_);
v___x_2308_ = lean_array_get_size(v___y_2301_);
v___x_2309_ = lean_array_push(v___y_2301_, v___x_2307_);
v___x_2310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
return v___x_2310_;
}
}
v___jp_2311_:
{
if (v_reconfigure_2104_ == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_io_prim_handle_lock(v_h_2312_, v_reconfigure_2104_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v___x_2315_; 
lean_dec_ref_known(v___x_2314_, 1);
v___x_2315_ = l_IO_FS_Handle_readToEnd(v_h_2312_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = l_Lean_Json_parse(v_a_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v___x_2318_; 
lean_dec_ref_known(v___x_2317_, 1);
v___x_2318_ = l_Lake_importConfigFile___lam__0(v___x_2284_, v___x_2125_, v_h_2312_);
lean_dec(v_h_2312_);
lean_dec_ref(v___x_2284_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v_h_2127_ = v_a_2319_;
v_lakeOpts_2128_ = v_lakeOpts_2102_;
v___y_2129_ = v___y_2313_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2320_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2321_ = lean_io_error_to_string(v_a_2320_);
v___x_2322_ = 3;
v___x_2323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*1, v___x_2322_);
v___x_2324_ = lean_array_get_size(v___y_2313_);
v___x_2325_ = lean_array_push(v___y_2313_, v___x_2323_);
v___x_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
return v___x_2326_;
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2317_, 0);
lean_inc_n(v_a_2327_, 2);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2328_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2327_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v___x_2329_; 
lean_dec_ref_known(v___x_2328_, 1);
v___x_2329_ = l_Lean_Json_getObj_x3f(v_a_2327_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_dec_ref_known(v___x_2329_, 1);
v___y_2300_ = v_h_2312_;
v___y_2301_ = v___y_2313_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2332_ = l_Lake_JsonObject_getJson_x3f(v_a_2330_, v___x_2331_);
lean_dec(v_a_2330_);
if (lean_obj_tag(v___x_2332_) == 0)
{
v___y_2300_ = v_h_2312_;
v___y_2301_ = v___y_2313_;
goto v___jp_2299_;
}
else
{
lean_object* v_val_2333_; lean_object* v___x_2334_; 
v_val_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_val_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v___y_2300_ = v_h_2312_;
v___y_2301_ = v___y_2313_;
goto v___jp_2299_;
}
else
{
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v___y_2300_ = v_h_2312_;
v___y_2301_ = v___y_2313_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
lean_dec(v_lakeOpts_2102_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lake_importConfigFile___lam__0(v___x_2284_, v___x_2125_, v_h_2312_);
lean_dec(v_h_2312_);
lean_dec_ref(v___x_2284_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v_h_2127_ = v_a_2337_;
v_lakeOpts_2128_ = v_a_2335_;
v___y_2129_ = v___y_2313_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec(v_a_2335_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2338_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2339_ = lean_io_error_to_string(v_a_2338_);
v___x_2340_ = 3;
v___x_2341_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1, v___x_2340_);
v___x_2342_ = lean_array_get_size(v___y_2313_);
v___x_2343_ = lean_array_push(v___y_2313_, v___x_2341_);
v___x_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
return v___x_2344_;
}
}
}
}
}
}
else
{
lean_object* v_a_2345_; uint8_t v___x_2346_; 
lean_dec(v_a_2327_);
lean_dec(v_lakeOpts_2102_);
v_a_2345_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2346_ = l_System_FilePath_pathExists(v___x_2122_);
if (v___x_2346_ == 0)
{
v___y_2286_ = v_a_2345_;
v___y_2287_ = v_h_2312_;
v___y_2288_ = v___y_2313_;
goto v___jp_2285_;
}
else
{
lean_object* v_idx_2347_; lean_object* v_name_2348_; lean_object* v_platform_2349_; lean_object* v_leanHash_2350_; uint64_t v_configHash_2351_; uint8_t v___x_2352_; 
v_idx_2347_ = lean_ctor_get(v_a_2345_, 0);
v_name_2348_ = lean_ctor_get(v_a_2345_, 1);
v_platform_2349_ = lean_ctor_get(v_a_2345_, 2);
v_leanHash_2350_ = lean_ctor_get(v_a_2345_, 3);
v_configHash_2351_ = lean_ctor_get_uint64(v_a_2345_, sizeof(void*)*5);
v___x_2352_ = lean_nat_dec_eq(v_idx_2347_, v_pkgIdx_2098_);
if (v___x_2352_ == 0)
{
v___y_2286_ = v_a_2345_;
v___y_2287_ = v_h_2312_;
v___y_2288_ = v___y_2313_;
goto v___jp_2285_;
}
else
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_name_eq(v_name_2348_, v_pkgName_2099_);
if (v___x_2353_ == 0)
{
v___y_2286_ = v_a_2345_;
v___y_2287_ = v_h_2312_;
v___y_2288_ = v___y_2313_;
goto v___jp_2285_;
}
else
{
uint64_t v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_unbox_uint64(v_a_2119_);
v___x_2355_ = lean_uint64_dec_eq(v_configHash_2351_, v___x_2354_);
if (v___x_2355_ == 0)
{
v___y_2286_ = v_a_2345_;
v___y_2287_ = v_h_2312_;
v___y_2288_ = v___y_2313_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = l_System_Platform_target;
v___x_2357_ = lean_string_dec_eq(v_platform_2349_, v___x_2356_);
if (v___x_2357_ == 0)
{
v___y_2286_ = v_a_2345_;
v___y_2287_ = v_h_2312_;
v___y_2288_ = v___y_2313_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = l_Lake_Env_leanGithash(v_lakeEnv_2096_);
v___x_2359_ = lean_string_dec_eq(v_leanHash_2350_, v___x_2358_);
lean_dec_ref(v___x_2358_);
if (v___x_2359_ == 0)
{
v___y_2286_ = v_a_2345_;
v___y_2287_ = v_h_2312_;
v___y_2288_ = v___y_2313_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2360_; 
lean_dec(v_a_2345_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec(v_a_2119_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v___x_2360_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2122_, v_leanOpts_2103_);
lean_dec_ref(v___x_2122_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = lean_io_prim_handle_unlock(v_h_2312_);
lean_dec(v_h_2312_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; 
lean_dec_ref_known(v___x_2362_, 1);
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v_a_2361_);
lean_ctor_set(v___x_2363_, 1, v___y_2313_);
return v___x_2363_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec(v_a_2361_);
v_a_2364_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2365_ = lean_io_error_to_string(v_a_2364_);
v___x_2366_ = 3;
v___x_2367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2366_);
v___x_2368_ = lean_array_get_size(v___y_2313_);
v___x_2369_ = lean_array_push(v___y_2313_, v___x_2367_);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
return v___x_2370_;
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec(v_h_2312_);
v_a_2371_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2372_ = lean_io_error_to_string(v_a_2371_);
v___x_2373_ = 3;
v___x_2374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1, v___x_2373_);
v___x_2375_ = lean_array_get_size(v___y_2313_);
v___x_2376_ = lean_array_push(v___y_2313_, v___x_2374_);
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
return v___x_2377_;
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
lean_object* v_a_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec(v_h_2312_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2378_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2379_ = lean_io_error_to_string(v_a_2378_);
v___x_2380_ = 3;
v___x_2381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2380_);
v___x_2382_ = lean_array_get_size(v___y_2313_);
v___x_2383_ = lean_array_push(v___y_2313_, v___x_2381_);
v___x_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
return v___x_2384_;
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v_h_2312_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2385_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2386_ = lean_io_error_to_string(v_a_2385_);
v___x_2387_ = 3;
v___x_2388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*1, v___x_2387_);
v___x_2389_ = lean_array_get_size(v___y_2313_);
v___x_2390_ = lean_array_push(v___y_2313_, v___x_2388_);
v___x_2391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
return v___x_2391_;
}
}
else
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lake_importConfigFile___lam__0(v___x_2284_, v___x_2125_, v_h_2312_);
lean_dec(v_h_2312_);
lean_dec_ref(v___x_2284_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v_h_2127_ = v_a_2393_;
v_lakeOpts_2128_ = v_lakeOpts_2102_;
v___y_2129_ = v___y_2313_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2122_);
lean_dec(v_a_2119_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2394_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2395_ = lean_io_error_to_string(v_a_2394_);
v___x_2396_ = 3;
v___x_2397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2396_);
v___x_2398_ = lean_array_get_size(v___y_2313_);
v___x_2399_ = lean_array_push(v___y_2313_, v___x_2397_);
v___x_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
return v___x_2400_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec_ref(v_configDir_2116_);
lean_dec(v_val_2110_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2449_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2450_ = lean_io_error_to_string(v_a_2449_);
v___x_2451_ = 3;
v___x_2452_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set_uint8(v___x_2452_, sizeof(void*)*1, v___x_2451_);
v___x_2453_ = lean_array_get_size(v_a_2090_);
v___x_2454_ = lean_array_push(v_a_2090_, v___x_2452_);
v___x_2455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
return v___x_2455_;
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref(v_configDir_2116_);
lean_dec(v_val_2110_);
lean_dec_ref(v_leanOpts_2103_);
lean_dec(v_lakeOpts_2102_);
lean_dec_ref(v_configFile_2101_);
lean_dec_ref(v_pkgDir_2100_);
lean_dec(v_pkgName_2099_);
lean_dec(v_pkgIdx_2098_);
lean_dec_ref(v_lakeEnv_2096_);
v_a_2456_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2457_ = lean_io_error_to_string(v_a_2456_);
v___x_2458_ = 3;
v___x_2459_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1, v___x_2458_);
v___x_2460_ = lean_array_get_size(v_a_2090_);
v___x_2461_ = lean_array_push(v_a_2090_, v___x_2459_);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
return v___x_2462_;
}
}
v___jp_2092_:
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___y_2093_);
lean_ctor_set(v___x_2095_, 1, v_a_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lake_importConfigFile(v_cfg_2463_, v_a_2464_);
return v_res_2466_;
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
