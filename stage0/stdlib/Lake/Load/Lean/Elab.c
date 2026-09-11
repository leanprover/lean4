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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_nbuckets_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_137_ = lean_array_get_size(v_data_136_);
v___x_138_ = lean_unsigned_to_nat(2u);
v_nbuckets_139_ = lean_nat_mul(v___x_137_, v___x_138_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_box(0);
v___x_142_ = lean_mk_array(v_nbuckets_139_, v___x_141_);
v___x_143_ = lean_array_propagate_mark(v_data_136_, v___x_142_);
v___x_144_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v___x_140_, v_data_136_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(lean_object* v_m_145_, lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_size_148_; lean_object* v_buckets_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_200_; 
v_size_148_ = lean_ctor_get(v_m_145_, 0);
v_buckets_149_ = lean_ctor_get(v_m_145_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_m_145_);
if (v_isSharedCheck_200_ == 0)
{
v___x_151_ = v_m_145_;
v_isShared_152_ = v_isSharedCheck_200_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_buckets_149_);
lean_inc(v_size_148_);
lean_dec(v_m_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_200_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; uint64_t v___y_155_; uint64_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_153_ = lean_array_get_size(v_buckets_149_);
v___x_193_ = 7ULL;
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_array_get_size(v_a_146_);
v___x_196_ = lean_nat_dec_lt(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
v___y_155_ = v___x_193_;
goto v___jp_154_;
}
else
{
size_t v___x_197_; size_t v___x_198_; uint64_t v___x_199_; 
v___x_197_ = ((size_t)0ULL);
v___x_198_ = lean_usize_of_nat(v___x_195_);
v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_146_, v___x_197_, v___x_198_, v___x_193_);
v___y_155_ = v___x_199_;
goto v___jp_154_;
}
v___jp_154_:
{
uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v_fold_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v_bkt_167_; uint8_t v___x_168_; 
v___x_156_ = 32ULL;
v___x_157_ = lean_uint64_shift_right(v___y_155_, v___x_156_);
v_fold_158_ = lean_uint64_xor(v___y_155_, v___x_157_);
v___x_159_ = 16ULL;
v___x_160_ = lean_uint64_shift_right(v_fold_158_, v___x_159_);
v___x_161_ = lean_uint64_xor(v_fold_158_, v___x_160_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = lean_usize_of_nat(v___x_153_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_sub(v___x_163_, v___x_164_);
v___x_166_ = lean_usize_land(v___x_162_, v___x_165_);
v_bkt_167_ = lean_array_uget_borrowed(v_buckets_149_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_146_, v_bkt_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v_size_x27_170_; lean_object* v___x_171_; lean_object* v_buckets_x27_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v_size_x27_170_ = lean_nat_add(v_size_148_, v___x_169_);
lean_dec(v_size_148_);
lean_inc(v_bkt_167_);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v_a_146_);
lean_ctor_set(v___x_171_, 1, v_b_147_);
lean_ctor_set(v___x_171_, 2, v_bkt_167_);
v_buckets_x27_172_ = lean_array_uset(v_buckets_149_, v___x_166_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(4u);
v___x_174_ = lean_nat_mul(v_size_x27_170_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(3u);
v___x_176_ = lean_nat_div(v___x_174_, v___x_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_array_get_size(v_buckets_x27_172_);
v___x_178_ = lean_nat_dec_le(v___x_176_, v___x_177_);
lean_dec(v___x_176_);
if (v___x_178_ == 0)
{
lean_object* v_val_179_; lean_object* v___x_181_; 
v_val_179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_buckets_x27_172_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_val_179_);
lean_ctor_set(v___x_151_, 0, v_size_x27_170_);
v___x_181_ = v___x_151_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_size_x27_170_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_val_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
else
{
lean_object* v___x_184_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_buckets_x27_172_);
lean_ctor_set(v___x_151_, 0, v_size_x27_170_);
v___x_184_ = v___x_151_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_size_x27_170_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_buckets_x27_172_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v___x_186_; lean_object* v_buckets_x27_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
lean_inc(v_bkt_167_);
v___x_186_ = lean_box(0);
v_buckets_x27_187_ = lean_array_uset(v_buckets_149_, v___x_166_, v___x_186_);
v___x_188_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_146_, v_b_147_, v_bkt_167_);
v___x_189_ = lean_array_uset(v_buckets_x27_187_, v___x_166_, v___x_188_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_189_);
v___x_191_ = v___x_151_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_size_148_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v_key_204_; lean_object* v_value_205_; lean_object* v_tail_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_key_204_ = lean_ctor_get(v_x_202_, 0);
v_value_205_ = lean_ctor_get(v_x_202_, 1);
v_tail_206_ = lean_ctor_get(v_x_202_, 2);
v___x_207_ = lean_array_get_size(v_key_204_);
v___x_208_ = lean_array_get_size(v_a_201_);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
v_x_202_ = v_tail_206_;
goto _start;
}
else
{
uint8_t v___x_211_; 
v___x_211_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_key_204_, v_a_201_, v___x_207_);
if (v___x_211_ == 0)
{
v_x_202_ = v_tail_206_;
goto _start;
}
else
{
lean_object* v___x_213_; 
lean_inc(v_value_205_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v_value_205_);
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_214_, v_x_215_);
lean_dec(v_x_215_);
lean_dec_ref(v_a_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(lean_object* v_m_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_buckets_219_; lean_object* v___x_220_; uint64_t v___y_222_; uint64_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_buckets_219_ = lean_ctor_get(v_m_217_, 1);
v___x_220_ = lean_array_get_size(v_buckets_219_);
v___x_236_ = 7ULL;
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_array_get_size(v_a_218_);
v___x_239_ = lean_nat_dec_lt(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
v___y_222_ = v___x_236_;
goto v___jp_221_;
}
else
{
size_t v___x_240_; size_t v___x_241_; uint64_t v___x_242_; 
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_usize_of_nat(v___x_238_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__1(v_a_218_, v___x_240_, v___x_241_, v___x_236_);
v___y_222_ = v___x_242_;
goto v___jp_221_;
}
v___jp_221_:
{
uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v_fold_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_223_ = 32ULL;
v___x_224_ = lean_uint64_shift_right(v___y_222_, v___x_223_);
v_fold_225_ = lean_uint64_xor(v___y_222_, v___x_224_);
v___x_226_ = 16ULL;
v___x_227_ = lean_uint64_shift_right(v_fold_225_, v___x_226_);
v___x_228_ = lean_uint64_xor(v_fold_225_, v___x_227_);
v___x_229_ = lean_uint64_to_usize(v___x_228_);
v___x_230_ = lean_usize_of_nat(v___x_220_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_sub(v___x_230_, v___x_231_);
v___x_233_ = lean_usize_land(v___x_229_, v___x_232_);
v___x_234_ = lean_array_uget_borrowed(v_buckets_219_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_218_, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object* v_m_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_243_, v_a_244_);
lean_dec_ref(v_a_244_);
lean_dec_ref(v_m_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* v_imports_248_, lean_object* v_opts_249_, uint32_t v_trustLevel_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = l___private_Lake_Load_Lean_Elab_0__Lake_importEnvCache;
v___x_253_ = lean_st_ref_get(v___x_252_);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v___x_253_, v_imports_248_);
lean_dec(v___x_253_);
if (lean_obj_tag(v___x_254_) == 1)
{
lean_object* v_val_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_opts_249_);
lean_dec_ref(v_imports_248_);
v_val_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_val_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 0);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_val_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; uint8_t v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_254_);
v___x_263_ = lean_enable_initializer_execution();
v___x_264_ = ((lean_object*)(l_Lake_importModulesUsingCache___closed__0));
v___x_265_ = 0;
v___x_266_ = 1;
v___x_267_ = 2;
v___x_268_ = lean_box(1);
lean_inc_ref(v_imports_248_);
v___x_269_ = l_Lean_importModules(v_imports_248_, v_opts_249_, v_trustLevel_250_, v___x_264_, v___x_265_, v___x_266_, v___x_267_, v___x_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_280_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_280_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_280_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_274_ = lean_st_ref_take(v___x_252_);
lean_inc(v_a_270_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v___x_274_, v_imports_248_, v_a_270_);
v___x_276_ = lean_st_ref_put(v___x_252_, v___x_275_);
if (v_isShared_273_ == 0)
{
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_270_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_dec_ref(v_imports_248_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* v_imports_281_, lean_object* v_opts_282_, lean_object* v_trustLevel_283_, lean_object* v_a_284_){
_start:
{
uint32_t v_trustLevel_boxed_285_; lean_object* v_res_286_; 
v_trustLevel_boxed_285_ = lean_unbox_uint32(v_trustLevel_283_);
lean_dec(v_trustLevel_283_);
v_res_286_ = l_Lake_importModulesUsingCache(v_imports_281_, v_opts_282_, v_trustLevel_boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(lean_object* v_00_u03b2_287_, lean_object* v_m_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___redArg(v_m_288_, v_a_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0___boxed(lean_object* v_00_u03b2_291_, lean_object* v_m_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0(v_00_u03b2_291_, v_m_292_, v_a_293_);
lean_dec_ref(v_a_293_);
lean_dec_ref(v_m_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1(lean_object* v_00_u03b2_295_, lean_object* v_m_296_, lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1___redArg(v_m_296_, v_a_297_, v_b_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(lean_object* v_00_u03b2_300_, lean_object* v_a_301_, lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___redArg(v_a_301_, v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* v_00_u03b2_304_, lean_object* v_a_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0(v_00_u03b2_304_, v_a_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(lean_object* v_00_u03b2_308_, lean_object* v_a_309_, lean_object* v_x_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___redArg(v_a_309_, v_x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3___boxed(lean_object* v_00_u03b2_312_, lean_object* v_a_313_, lean_object* v_x_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__3(v_00_u03b2_312_, v_a_313_, v_x_314_);
lean_dec(v_x_314_);
lean_dec_ref(v_a_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4(lean_object* v_00_u03b2_317_, lean_object* v_data_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4___redArg(v_data_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5(lean_object* v_00_u03b2_320_, lean_object* v_a_321_, lean_object* v_b_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__5___redArg(v_a_321_, v_b_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(lean_object* v_xs_325_, lean_object* v_ys_326_, lean_object* v_hsz_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___redArg(v_xs_325_, v_ys_326_, v_x_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_331_, lean_object* v_ys_332_, lean_object* v_hsz_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_importModulesUsingCache_spec__0_spec__0_spec__1(v_xs_331_, v_ys_332_, v_hsz_333_, v_x_334_, v_x_335_);
lean_dec_ref(v_ys_332_);
lean_dec_ref(v_xs_331_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_338_, lean_object* v_i_339_, lean_object* v_source_340_, lean_object* v_target_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6___redArg(v_i_339_, v_source_340_, v_target_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lake_importModulesUsingCache_spec__1_spec__4_spec__6_spec__7___redArg(v_x_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(lean_object* v_header_348_, lean_object* v_opts_349_, lean_object* v_inputCtx_350_, lean_object* v_a_351_){
_start:
{
uint8_t v___x_353_; lean_object* v_imports_354_; uint32_t v___x_355_; lean_object* v___x_356_; 
v___x_353_ = 1;
lean_inc(v_header_348_);
v_imports_354_ = l_Lean_Elab_HeaderSyntax_imports(v_header_348_, v___x_353_);
v___x_355_ = 1024;
v___x_356_ = l_Lake_importModulesUsingCache(v_imports_354_, v_opts_349_, v___x_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_inputCtx_350_);
lean_dec(v_header_348_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_a_357_);
lean_ctor_set(v___x_361_, 1, v_a_351_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v_fileName_367_; lean_object* v_fileMap_368_; uint8_t v___x_369_; lean_object* v___y_371_; lean_object* v___x_400_; 
v_a_366_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_356_, 1);
v_fileName_367_ = lean_ctor_get(v_inputCtx_350_, 1);
lean_inc_ref(v_fileName_367_);
v_fileMap_368_ = lean_ctor_get(v_inputCtx_350_, 2);
lean_inc_ref(v_fileMap_368_);
lean_dec_ref(v_inputCtx_350_);
v___x_369_ = 0;
v___x_400_ = l_Lean_Syntax_getPos_x3f(v_header_348_, v___x_369_);
lean_dec(v_header_348_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___y_371_ = v___x_401_;
goto v___jp_370_;
}
else
{
lean_object* v_val_402_; 
v_val_402_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_400_, 1);
v___y_371_ = v_val_402_;
goto v___jp_370_;
}
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint32_t v___x_380_; lean_object* v___x_381_; 
v___x_372_ = l_Lean_FileMap_toPosition(v_fileMap_368_, v___y_371_);
lean_dec(v___y_371_);
v___x_373_ = lean_box(0);
v___x_374_ = 2;
v___x_375_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___closed__0));
v___x_376_ = lean_io_error_to_string(v_a_366_);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___x_378_ = l_Lean_MessageData_ofFormat(v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_379_, 0, v_fileName_367_);
lean_ctor_set(v___x_379_, 1, v___x_372_);
lean_ctor_set(v___x_379_, 2, v___x_373_);
lean_ctor_set(v___x_379_, 3, v___x_375_);
lean_ctor_set(v___x_379_, 4, v___x_378_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*5, v___x_369_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*5 + 1, v___x_374_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*5 + 2, v___x_369_);
v___x_380_ = 0;
v___x_381_ = l_Lean_mkEmptyEnvironment(v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_391_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_391_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = l_Lean_MessageLog_add(v___x_379_, v_a_351_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_a_382_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_387_);
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref_known(v___x_379_, 5);
lean_dec_ref(v_a_351_);
v_a_392_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_381_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_381_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_processHeader___boxed(lean_object* v_header_403_, lean_object* v_opts_404_, lean_object* v_inputCtx_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_header_403_, v_opts_404_, v_inputCtx_405_, v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(lean_object* v_x_413_, lean_object* v___y_414_){
_start:
{
uint8_t v_isSilent_416_; 
v_isSilent_416_ = lean_ctor_get_uint8(v_x_413_, sizeof(void*)*5 + 2);
if (v_isSilent_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = l_Lake_LogEntry_ofMessage(v_x_413_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_array_push(v___y_414_, v___x_417_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v_x_413_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___y_414_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0___boxed(lean_object* v_x_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__0(v_x_423_, v___y_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_427_, lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
lean_inc_ref(v_f_427_);
lean_inc(v___x_435_);
v___x_436_ = lean_apply_3(v_f_427_, v___x_435_, v___y_432_, lean_box(0));
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v_a_438_; size_t v___x_439_; size_t v___x_440_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
v_a_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_436_, 2);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_429_, v___x_439_);
v_i_429_ = v___x_440_;
v_b_431_ = v_a_437_;
v___y_432_ = v_a_438_;
goto _start;
}
else
{
lean_dec_ref(v_f_427_);
return v___x_436_;
}
}
else
{
lean_object* v___x_442_; 
lean_dec_ref(v_f_427_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_b_431_);
lean_ctor_set(v___x_442_, 1, v___y_432_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_443_, lean_object* v_as_444_, lean_object* v_i_445_, lean_object* v_stop_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
size_t v_i_boxed_450_; size_t v_stop_boxed_451_; lean_object* v_res_452_; 
v_i_boxed_450_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_stop_boxed_451_ = lean_unbox_usize(v_stop_446_);
lean_dec(v_stop_446_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_443_, v_as_444_, v_i_boxed_450_, v_stop_boxed_451_, v_b_447_, v___y_448_);
lean_dec_ref(v_as_444_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_453_, lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v_cs_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_cs_457_ = lean_ctor_get(v_x_454_, 0);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_array_get_size(v_cs_457_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec_ref(v_f_453_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___y_455_);
return v___x_462_;
}
else
{
size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((size_t)0ULL);
v___x_464_ = lean_usize_of_nat(v___x_459_);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_453_, v_cs_457_, v___x_463_, v___x_464_, v___x_460_, v___y_455_);
return v___x_465_;
}
}
else
{
lean_object* v_vs_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_vs_466_ = lean_ctor_get(v_x_454_, 0);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_array_get_size(v_vs_466_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_dec_ref(v_f_453_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___y_455_);
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_468_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_453_, v_vs_466_, v___x_472_, v___x_473_, v___x_469_, v___y_455_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_475_, lean_object* v_as_476_, size_t v_i_477_, size_t v_stop_478_, lean_object* v_b_479_, lean_object* v___y_480_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_eq(v_i_477_, v_stop_478_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_array_uget_borrowed(v_as_476_, v_i_477_);
lean_inc_ref(v_f_475_);
v___x_484_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_475_, v___x_483_, v___y_480_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v_a_486_; size_t v___x_487_; size_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
v_a_486_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_484_, 2);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_i_477_, v___x_487_);
v_i_477_ = v___x_488_;
v_b_479_ = v_a_485_;
v___y_480_ = v_a_486_;
goto _start;
}
else
{
lean_dec_ref(v_f_475_);
return v___x_484_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v_f_475_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_b_479_);
lean_ctor_set(v___x_490_, 1, v___y_480_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_491_, lean_object* v_as_492_, lean_object* v_i_493_, lean_object* v_stop_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
size_t v_i_boxed_498_; size_t v_stop_boxed_499_; lean_object* v_res_500_; 
v_i_boxed_498_ = lean_unbox_usize(v_i_493_);
lean_dec(v_i_493_);
v_stop_boxed_499_ = lean_unbox_usize(v_stop_494_);
lean_dec(v_stop_494_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_491_, v_as_492_, v_i_boxed_498_, v_stop_boxed_499_, v_b_495_, v___y_496_);
lean_dec_ref(v_as_492_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_501_, lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_501_, v_x_502_, v___y_503_);
lean_dec_ref(v_x_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_506_, lean_object* v_t_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_root_510_; lean_object* v_tail_511_; lean_object* v___x_512_; 
v_root_510_ = lean_ctor_get(v_t_507_, 0);
v_tail_511_ = lean_ctor_get(v_t_507_, 1);
lean_inc_ref(v_f_506_);
v___x_512_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_506_, v_root_510_, v___y_508_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_527_; 
v_a_513_ = lean_ctor_get(v___x_512_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_512_, 0);
lean_dec(v_unused_528_);
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_527_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_527_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_array_get_size(v_tail_511_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_nat_dec_lt(v___x_517_, v___x_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_f_506_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_519_);
v___x_522_ = v___x_515_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_a_513_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
lean_del_object(v___x_515_);
v___x_524_ = ((size_t)0ULL);
v___x_525_ = lean_usize_of_nat(v___x_518_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_506_, v_tail_511_, v___x_524_, v___x_525_, v___x_519_, v_a_513_);
return v___x_526_;
}
}
}
else
{
lean_dec_ref(v_f_506_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_529_, lean_object* v_t_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_529_, v_t_530_, v___y_531_);
lean_dec_ref(v_t_530_);
return v_res_533_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_535_, lean_object* v_x_536_, size_t v_x_537_, size_t v_x_538_, lean_object* v___y_539_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_cs_541_; lean_object* v___x_542_; size_t v___x_543_; lean_object* v_j_544_; lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v_cs_541_ = lean_ctor_get(v_x_536_, 0);
v___x_542_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_543_ = lean_usize_shift_right(v_x_537_, v_x_538_);
v_j_544_ = lean_usize_to_nat(v___x_543_);
v___x_545_ = lean_array_get_borrowed(v___x_542_, v_cs_541_, v_j_544_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_shift_left(v___x_546_, v_x_538_);
v___x_548_ = lean_usize_sub(v___x_547_, v___x_546_);
v___x_549_ = lean_usize_land(v_x_537_, v___x_548_);
v___x_550_ = ((size_t)5ULL);
v___x_551_ = lean_usize_sub(v_x_538_, v___x_550_);
lean_inc_ref(v_f_535_);
v___x_552_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_535_, v___x_545_, v___x_549_, v___x_551_, v___y_539_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_568_; 
v_a_553_ = lean_ctor_get(v___x_552_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_569_);
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_568_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_568_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_j_544_, v___x_557_);
lean_dec(v_j_544_);
v___x_559_ = lean_array_get_size(v_cs_541_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
if (v___x_561_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v___x_558_);
lean_dec_ref(v_f_535_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_560_);
v___x_563_ = v___x_555_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_553_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
lean_del_object(v___x_555_);
v___x_565_ = lean_usize_of_nat(v___x_558_);
lean_dec(v___x_558_);
v___x_566_ = lean_usize_of_nat(v___x_559_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_535_, v_cs_541_, v___x_565_, v___x_566_, v___x_560_, v_a_553_);
return v___x_567_;
}
}
}
else
{
lean_dec(v_j_544_);
lean_dec_ref(v_f_535_);
return v___x_552_;
}
}
else
{
lean_object* v_vs_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_vs_570_ = lean_ctor_get(v_x_536_, 0);
v___x_571_ = lean_usize_to_nat(v_x_537_);
v___x_572_ = lean_array_get_size(v_vs_570_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_571_);
lean_dec_ref(v_f_535_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___y_539_);
return v___x_575_;
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_usize_of_nat(v___x_571_);
lean_dec(v___x_571_);
v___x_577_ = lean_usize_of_nat(v___x_572_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_535_, v_vs_570_, v___x_576_, v___x_577_, v___x_573_, v___y_539_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_x_12359__boxed_585_; size_t v_x_12360__boxed_586_; lean_object* v_res_587_; 
v_x_12359__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_x_12360__boxed_586_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_res_587_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_579_, v_x_580_, v_x_12359__boxed_585_, v_x_12360__boxed_586_, v___y_583_);
lean_dec_ref(v_x_580_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_588_, lean_object* v_t_589_, lean_object* v_start_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_nat_dec_eq(v_start_590_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v_root_595_; lean_object* v_tail_596_; size_t v_shift_597_; lean_object* v_tailOff_598_; uint8_t v___x_599_; 
v_root_595_ = lean_ctor_get(v_t_589_, 0);
v_tail_596_ = lean_ctor_get(v_t_589_, 1);
v_shift_597_ = lean_ctor_get_usize(v_t_589_, 4);
v_tailOff_598_ = lean_ctor_get(v_t_589_, 3);
v___x_599_ = lean_nat_dec_le(v_tailOff_598_, v_start_590_);
if (v___x_599_ == 0)
{
size_t v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_usize_of_nat(v_start_590_);
lean_inc_ref(v_f_588_);
v___x_601_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_588_, v_root_595_, v___x_600_, v_shift_597_, v___y_591_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_615_; 
v_a_602_ = lean_ctor_get(v___x_601_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_616_);
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_array_get_size(v_tail_596_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_nat_dec_lt(v___x_593_, v___x_606_);
if (v___x_608_ == 0)
{
lean_object* v___x_610_; 
lean_dec_ref(v_f_588_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_607_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_a_602_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
lean_del_object(v___x_604_);
v___x_612_ = ((size_t)0ULL);
v___x_613_ = lean_usize_of_nat(v___x_606_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_588_, v_tail_596_, v___x_612_, v___x_613_, v___x_607_, v_a_602_);
return v___x_614_;
}
}
}
else
{
lean_dec_ref(v_f_588_);
return v___x_601_;
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_617_ = lean_nat_sub(v_start_590_, v_tailOff_598_);
v___x_618_ = lean_array_get_size(v_tail_596_);
v___x_619_ = lean_box(0);
v___x_620_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v___x_617_);
lean_dec_ref(v_f_588_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___y_591_);
return v___x_621_;
}
else
{
size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_usize_of_nat(v___x_617_);
lean_dec(v___x_617_);
v___x_623_ = lean_usize_of_nat(v___x_618_);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_588_, v_tail_596_, v___x_622_, v___x_623_, v___x_619_, v___y_591_);
return v___x_624_;
}
}
}
else
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_588_, v_t_589_, v___y_591_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_626_, lean_object* v_t_627_, lean_object* v_start_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_626_, v_t_627_, v_start_628_, v___y_629_);
lean_dec(v_start_628_);
lean_dec_ref(v_t_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_632_, lean_object* v_f_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_unreported_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_unreported_636_ = lean_ctor_get(v_log_632_, 1);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_633_, v_unreported_636_, v___x_637_, v___y_634_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_639_, lean_object* v_f_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_639_, v_f_640_, v___y_641_);
lean_dec_ref(v_log_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_646_, lean_object* v_pkgName_647_, lean_object* v_pkgDir_648_, lean_object* v_lakeOpts_649_, lean_object* v_leanOpts_650_, lean_object* v_configFile_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_IO_FS_readFile(v_configFile_651_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = 1;
v___x_657_ = lean_string_utf8_byte_size(v_a_655_);
lean_inc_ref(v_configFile_651_);
v___x_658_ = l_Lean_Parser_mkInputContext___redArg(v_a_655_, v_configFile_651_, v___x_656_, v___x_657_);
lean_inc_ref(v___x_658_);
v___x_659_ = l_Lean_Parser_parseHeader(v___x_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_758_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_758_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_758_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_758_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_snd_664_; lean_object* v_fst_665_; lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_757_; 
v_snd_664_ = lean_ctor_get(v_a_660_, 1);
lean_inc(v_snd_664_);
v_fst_665_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_fst_665_);
lean_dec(v_a_660_);
v_fst_666_ = lean_ctor_get(v_snd_664_, 0);
v_snd_667_ = lean_ctor_get(v_snd_664_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_snd_664_);
if (v_isSharedCheck_757_ == 0)
{
v___x_669_ = v_snd_664_;
v_isShared_670_ = v_isSharedCheck_757_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snd_667_);
lean_inc(v_fst_666_);
lean_dec(v_snd_664_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_757_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; 
lean_inc_ref(v___x_658_);
lean_inc_ref(v_leanOpts_650_);
v___x_671_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_665_, v_leanOpts_650_, v___x_658_, v_snd_667_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_747_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_747_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_747_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_747_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_fst_676_; lean_object* v_snd_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_746_; 
v_fst_676_ = lean_ctor_get(v_a_672_, 0);
v_snd_677_ = lean_ctor_get(v_a_672_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_672_);
if (v_isSharedCheck_746_ == 0)
{
v___x_679_ = v_a_672_;
v_isShared_680_ = v_isSharedCheck_746_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snd_677_);
lean_inc(v_fst_676_);
lean_dec(v_a_672_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_746_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v_asyncMode_682_; lean_object* v___x_683_; lean_object* v_asyncMode_684_; lean_object* v___x_685_; lean_object* v_asyncMode_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_681_ = l_Lake_nameExt;
v_asyncMode_682_ = lean_ctor_get(v___x_681_, 2);
v___x_683_ = l_Lake_dirExt;
v_asyncMode_684_ = lean_ctor_get(v___x_683_, 2);
v___x_685_ = l_Lake_optsExt;
v_asyncMode_686_ = lean_ctor_get(v___x_685_, 2);
v___x_687_ = ((lean_object*)(l_Lake_configModuleName));
v___x_688_ = l_Lean_Environment_setMainModule(v_fst_676_, v___x_687_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v_pkgName_647_);
lean_ctor_set(v___x_679_, 0, v_pkgIdx_646_);
v___x_690_ = v___x_679_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_pkgIdx_646_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_pkgName_647_);
v___x_690_ = v_reuseFailAlloc_745_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_EnvExtension_setState___redArg(v___x_681_, v___x_688_, v___x_690_, v_asyncMode_682_);
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 1);
lean_ctor_set(v___x_674_, 0, v_pkgDir_648_);
v___x_693_ = v___x_674_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_pkgDir_648_);
v___x_693_ = v_reuseFailAlloc_744_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_EnvExtension_setState___redArg(v___x_683_, v___x_691_, v___x_693_, v_asyncMode_684_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v_lakeOpts_649_);
v___x_696_ = v___x_662_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_lakeOpts_649_);
v___x_696_ = v_reuseFailAlloc_743_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_EnvExtension_setState___redArg(v___x_685_, v___x_694_, v___x_696_, v_asyncMode_686_);
v___x_698_ = l_Lean_Elab_Command_mkState(v___x_697_, v_snd_677_, v_leanOpts_650_);
v___x_699_ = l_Lean_Elab_IO_processCommands(v___x_658_, v_fst_666_, v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v_commandState_701_; lean_object* v_env_702_; lean_object* v_messages_703_; lean_object* v___f_704_; lean_object* v___x_705_; 
lean_del_object(v___x_669_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v_commandState_701_ = lean_ctor_get(v_a_700_, 0);
lean_inc_ref(v_commandState_701_);
lean_dec(v_a_700_);
v_env_702_ = lean_ctor_get(v_commandState_701_, 0);
lean_inc_ref(v_env_702_);
v_messages_703_ = lean_ctor_get(v_commandState_701_, 1);
lean_inc_ref(v_messages_703_);
lean_dec_ref(v_commandState_701_);
v___f_704_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_705_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_703_, v___f_704_, v_a_652_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_723_; 
v_a_706_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_705_, 0);
lean_dec(v_unused_724_);
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_723_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_723_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_MessageLog_hasErrors(v_messages_703_);
lean_dec_ref(v_messages_703_);
if (v___x_710_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_configFile_651_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_env_702_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_env_702_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_a_706_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec_ref(v_env_702_);
v___x_714_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__1));
v___x_715_ = lean_string_append(v_configFile_651_, v___x_714_);
v___x_716_ = 3;
v___x_717_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*1, v___x_716_);
v___x_718_ = lean_array_get_size(v_a_706_);
v___x_719_ = lean_array_push(v_a_706_, v___x_717_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
lean_ctor_set(v___x_708_, 1, v___x_719_);
lean_ctor_set(v___x_708_, 0, v___x_718_);
v___x_721_ = v___x_708_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_messages_703_);
lean_dec_ref(v_env_702_);
lean_dec_ref(v_configFile_651_);
v_a_725_ = lean_ctor_get(v___x_705_, 0);
v_a_726_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_705_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_inc(v_a_725_);
lean_dec(v___x_705_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_725_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec_ref(v_configFile_651_);
v_a_734_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_699_, 1);
v___x_735_ = lean_io_error_to_string(v_a_734_);
v___x_736_ = 3;
v___x_737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*1, v___x_736_);
v___x_738_ = lean_array_get_size(v_a_652_);
v___x_739_ = lean_array_push(v_a_652_, v___x_737_);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 1);
lean_ctor_set(v___x_669_, 1, v___x_739_);
lean_ctor_set(v___x_669_, 0, v___x_738_);
v___x_741_ = v___x_669_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
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
lean_object* v_a_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_fst_666_);
lean_del_object(v___x_662_);
lean_dec_ref(v___x_658_);
lean_dec_ref(v_configFile_651_);
lean_dec_ref(v_leanOpts_650_);
lean_dec(v_lakeOpts_649_);
lean_dec_ref(v_pkgDir_648_);
lean_dec(v_pkgName_647_);
lean_dec(v_pkgIdx_646_);
v_a_748_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_671_, 1);
v___x_749_ = lean_io_error_to_string(v_a_748_);
v___x_750_ = 3;
v___x_751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*1, v___x_750_);
v___x_752_ = lean_array_get_size(v_a_652_);
v___x_753_ = lean_array_push(v_a_652_, v___x_751_);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 1);
lean_ctor_set(v___x_669_, 1, v___x_753_);
lean_ctor_set(v___x_669_, 0, v___x_752_);
v___x_755_ = v___x_669_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v___x_658_);
lean_dec_ref(v_configFile_651_);
lean_dec_ref(v_leanOpts_650_);
lean_dec(v_lakeOpts_649_);
lean_dec_ref(v_pkgDir_648_);
lean_dec(v_pkgName_647_);
lean_dec(v_pkgIdx_646_);
v_a_759_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_659_, 1);
v___x_760_ = lean_io_error_to_string(v_a_759_);
v___x_761_ = 3;
v___x_762_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*1, v___x_761_);
v___x_763_ = lean_array_get_size(v_a_652_);
v___x_764_ = lean_array_push(v_a_652_, v___x_762_);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
return v___x_765_;
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v_configFile_651_);
lean_dec_ref(v_leanOpts_650_);
lean_dec(v_lakeOpts_649_);
lean_dec_ref(v_pkgDir_648_);
lean_dec(v_pkgName_647_);
lean_dec(v_pkgIdx_646_);
v_a_766_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_654_, 1);
v___x_767_ = lean_io_error_to_string(v_a_766_);
v___x_768_ = 3;
v___x_769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_768_);
v___x_770_ = lean_array_get_size(v_a_652_);
v___x_771_ = lean_array_push(v_a_652_, v___x_769_);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_773_, lean_object* v_pkgName_774_, lean_object* v_pkgDir_775_, lean_object* v_lakeOpts_776_, lean_object* v_leanOpts_777_, lean_object* v_configFile_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_773_, v_pkgName_774_, v_pkgDir_775_, v_lakeOpts_776_, v_leanOpts_777_, v_configFile_778_, v_a_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_784_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = lake_environment_add(v_env_784_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_785_);
return v_res_786_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_793_ = l_Lean_NameSet_empty;
v___x_794_ = l_Lean_NameSet_insert(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_800_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_801_ = l_Lean_NameSet_insert(v___x_800_, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_807_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_808_ = l_Lean_NameSet_insert(v___x_807_, v___x_806_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_814_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_815_ = l_Lean_NameSet_insert(v___x_814_, v___x_813_);
return v___x_815_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_821_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_822_ = l_Lean_NameSet_insert(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_828_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_829_ = l_Lean_NameSet_insert(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_835_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_836_ = l_Lean_NameSet_insert(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_842_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_843_ = l_Lean_NameSet_insert(v___x_842_, v___x_841_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_849_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_850_ = l_Lean_NameSet_insert(v___x_849_, v___x_848_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_856_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_857_ = l_Lean_NameSet_insert(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_863_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_864_ = l_Lean_NameSet_insert(v___x_863_, v___x_862_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_870_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_871_ = l_Lean_NameSet_insert(v___x_870_, v___x_869_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_877_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_878_ = l_Lean_NameSet_insert(v___x_877_, v___x_876_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_884_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_885_ = l_Lean_NameSet_insert(v___x_884_, v___x_883_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_891_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_892_ = l_Lean_NameSet_insert(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_899_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_900_ = l_Lean_NameSet_insert(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52));
v___x_908_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_909_ = l_Lean_NameSet_insert(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53);
return v___x_910_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_instInhabitedEnvExtensionState;
v___x_912_ = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_913_, lean_object* v_val_914_, lean_object* v_as_915_, size_t v_i_916_, size_t v_stop_917_, lean_object* v_b_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = lean_usize_dec_eq(v_i_916_, v_stop_917_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; 
v___x_920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_921_ = lean_array_uget_borrowed(v_as_915_, v_i_916_);
v___x_922_ = lean_array_get_borrowed(v___x_920_, v_val_913_, v_val_914_);
v___x_923_ = lean_box(0);
v___x_924_ = lean_box(0);
lean_inc(v___x_921_);
lean_inc(v___x_922_);
v___x_925_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_922_, v_b_918_, v___x_921_, v___x_923_, v___x_924_);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_916_, v___x_926_);
v_i_916_ = v___x_927_;
v_b_918_ = v___x_925_;
goto _start;
}
else
{
return v_b_918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_929_, lean_object* v_val_930_, lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_stop_933_, lean_object* v_b_934_){
_start:
{
size_t v_i_boxed_935_; size_t v_stop_boxed_936_; lean_object* v_res_937_; 
v_i_boxed_935_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_stop_boxed_936_ = lean_unbox_usize(v_stop_933_);
lean_dec(v_stop_933_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_929_, v_val_930_, v_as_931_, v_i_boxed_935_, v_stop_boxed_936_, v_b_934_);
lean_dec_ref(v_as_931_);
lean_dec(v_val_930_);
lean_dec_ref(v_val_929_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
lean_object* v_key_941_; lean_object* v_value_942_; lean_object* v_tail_943_; uint8_t v___x_944_; 
v_key_941_ = lean_ctor_get(v_x_939_, 0);
v_value_942_ = lean_ctor_get(v_x_939_, 1);
v_tail_943_ = lean_ctor_get(v_x_939_, 2);
v___x_944_ = lean_name_eq(v_key_941_, v_a_938_);
if (v___x_944_ == 0)
{
v_x_939_ = v_tail_943_;
goto _start;
}
else
{
lean_object* v___x_946_; 
lean_inc(v_value_942_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_value_942_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_947_, lean_object* v_x_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_947_, v_x_948_);
lean_dec(v_x_948_);
lean_dec(v_a_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_buckets_952_; lean_object* v___x_953_; uint64_t v___y_955_; 
v_buckets_952_ = lean_ctor_get(v_m_950_, 1);
v___x_953_ = lean_array_get_size(v_buckets_952_);
if (lean_obj_tag(v_a_951_) == 0)
{
uint64_t v___x_969_; 
v___x_969_ = 1723ULL;
v___y_955_ = v___x_969_;
goto v___jp_954_;
}
else
{
uint64_t v_hash_970_; 
v_hash_970_ = lean_ctor_get_uint64(v_a_951_, sizeof(void*)*2);
v___y_955_ = v_hash_970_;
goto v___jp_954_;
}
v___jp_954_:
{
uint64_t v___x_956_; uint64_t v___x_957_; uint64_t v_fold_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_956_ = 32ULL;
v___x_957_ = lean_uint64_shift_right(v___y_955_, v___x_956_);
v_fold_958_ = lean_uint64_xor(v___y_955_, v___x_957_);
v___x_959_ = 16ULL;
v___x_960_ = lean_uint64_shift_right(v_fold_958_, v___x_959_);
v___x_961_ = lean_uint64_xor(v_fold_958_, v___x_960_);
v___x_962_ = lean_uint64_to_usize(v___x_961_);
v___x_963_ = lean_usize_of_nat(v___x_953_);
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_sub(v___x_963_, v___x_964_);
v___x_966_ = lean_usize_land(v___x_962_, v___x_965_);
v___x_967_ = lean_array_uget_borrowed(v_buckets_952_, v___x_966_);
v___x_968_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_951_, v___x_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_m_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_974_, lean_object* v_val_975_, lean_object* v_as_976_, size_t v_i_977_, size_t v_stop_978_, lean_object* v_b_979_){
_start:
{
lean_object* v___y_981_; uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_eq(v_i_977_, v_stop_978_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_986_ = lean_array_uget_borrowed(v_as_976_, v_i_977_);
v_fst_987_ = lean_ctor_get(v___x_986_, 0);
v_snd_988_ = lean_ctor_get(v___x_986_, 1);
v___x_989_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_990_ = l_Lean_NameSet_contains(v___x_989_, v_fst_987_);
if (v___x_990_ == 0)
{
v___y_981_ = v_b_979_;
goto v___jp_980_;
}
else
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_974_, v_fst_987_);
if (lean_obj_tag(v___x_991_) == 0)
{
v___y_981_ = v_b_979_;
goto v___jp_980_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_snd_988_);
v___x_995_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec(v_val_992_);
v___y_981_ = v_b_979_;
goto v___jp_980_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = lean_nat_dec_le(v___x_994_, v___x_994_);
if (v___x_996_ == 0)
{
if (v___x_995_ == 0)
{
lean_dec(v_val_992_);
v___y_981_ = v_b_979_;
goto v___jp_980_;
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_994_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_975_, v_val_992_, v_snd_988_, v___x_997_, v___x_998_, v_b_979_);
lean_dec(v_val_992_);
v___y_981_ = v___x_999_;
goto v___jp_980_;
}
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = lean_usize_of_nat(v___x_994_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_975_, v_val_992_, v_snd_988_, v___x_1000_, v___x_1001_, v_b_979_);
lean_dec(v_val_992_);
v___y_981_ = v___x_1002_;
goto v___jp_980_;
}
}
}
}
}
else
{
return v_b_979_;
}
v___jp_980_:
{
size_t v___x_982_; size_t v___x_983_; 
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_977_, v___x_982_);
v_i_977_ = v___x_983_;
v_b_979_ = v___y_981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1003_, lean_object* v_val_1004_, lean_object* v_as_1005_, lean_object* v_i_1006_, lean_object* v_stop_1007_, lean_object* v_b_1008_){
_start:
{
size_t v_i_boxed_1009_; size_t v_stop_boxed_1010_; lean_object* v_res_1011_; 
v_i_boxed_1009_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_stop_boxed_1010_ = lean_unbox_usize(v_stop_1007_);
lean_dec(v_stop_1007_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1003_, v_val_1004_, v_as_1005_, v_i_boxed_1009_, v_stop_boxed_1010_, v_b_1008_);
lean_dec_ref(v_as_1005_);
lean_dec_ref(v_val_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1012_, size_t v_i_1013_, size_t v_stop_1014_, lean_object* v_b_1015_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_eq(v_i_1013_, v_stop_1014_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; 
v___x_1017_ = lean_array_uget_borrowed(v_as_1012_, v_i_1013_);
lean_inc(v___x_1017_);
v___x_1018_ = lake_environment_add(v_b_1015_, v___x_1017_);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_add(v_i_1013_, v___x_1019_);
v_i_1013_ = v___x_1020_;
v_b_1015_ = v___x_1018_;
goto _start;
}
else
{
return v_b_1015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1022_, lean_object* v_i_1023_, lean_object* v_stop_1024_, lean_object* v_b_1025_){
_start:
{
size_t v_i_boxed_1026_; size_t v_stop_boxed_1027_; lean_object* v_res_1028_; 
v_i_boxed_1026_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_stop_boxed_1027_ = lean_unbox_usize(v_stop_1024_);
lean_dec(v_stop_1024_);
v_res_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1022_, v_i_boxed_1026_, v_stop_boxed_1027_, v_b_1025_);
lean_dec_ref(v_as_1022_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1029_, lean_object* v_leanOpts_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_readModuleData(v_olean_1029_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v_fst_1034_; lean_object* v_imports_1035_; lean_object* v_constants_1036_; lean_object* v_entries_1037_; uint32_t v___x_1038_; lean_object* v___x_1039_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v_fst_1034_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_fst_1034_);
lean_dec(v_a_1033_);
v_imports_1035_ = lean_ctor_get(v_fst_1034_, 0);
lean_inc_ref(v_imports_1035_);
v_constants_1036_ = lean_ctor_get(v_fst_1034_, 2);
lean_inc_ref(v_constants_1036_);
v_entries_1037_ = lean_ctor_get(v_fst_1034_, 4);
lean_inc_ref(v_entries_1037_);
lean_dec(v_fst_1034_);
v___x_1038_ = 1024;
v___x_1039_ = l_Lake_importModulesUsingCache(v_imports_1035_, v_leanOpts_1030_, v___x_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___y_1043_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_array_get_size(v_constants_1036_);
v___x_1082_ = lean_nat_dec_lt(v___x_1041_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v_constants_1036_);
v___y_1043_ = v_a_1040_;
goto v___jp_1042_;
}
else
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_le(v___x_1081_, v___x_1081_);
if (v___x_1083_ == 0)
{
if (v___x_1082_ == 0)
{
lean_dec_ref(v_constants_1036_);
v___y_1043_ = v_a_1040_;
goto v___jp_1042_;
}
else
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1081_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1036_, v___x_1084_, v___x_1085_, v_a_1040_);
lean_dec_ref(v_constants_1036_);
v___y_1043_ = v___x_1086_;
goto v___jp_1042_;
}
}
else
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1081_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1036_, v___x_1087_, v___x_1088_, v_a_1040_);
lean_dec_ref(v_constants_1036_);
v___y_1043_ = v___x_1089_;
goto v___jp_1042_;
}
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = l_Lean_persistentEnvExtensionsRef;
v___x_1045_ = lean_st_ref_get(v___x_1044_);
v___x_1046_ = l_Lean_mkExtNameMap(v___x_1041_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1072_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1072_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1072_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_array_get_size(v_entries_1037_);
v___x_1052_ = lean_nat_dec_lt(v___x_1041_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1054_; 
lean_dec(v_a_1047_);
lean_dec(v___x_1045_);
lean_dec_ref(v_entries_1037_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___y_1043_);
v___x_1054_ = v___x_1049_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___y_1043_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_le(v___x_1051_, v___x_1051_);
if (v___x_1056_ == 0)
{
if (v___x_1052_ == 0)
{
lean_object* v___x_1058_; 
lean_dec(v_a_1047_);
lean_dec(v___x_1045_);
lean_dec_ref(v_entries_1037_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___y_1043_);
v___x_1058_ = v___x_1049_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___y_1043_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = lean_usize_of_nat(v___x_1051_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1047_, v___x_1045_, v_entries_1037_, v___x_1060_, v___x_1061_, v___y_1043_);
lean_dec_ref(v_entries_1037_);
lean_dec(v___x_1045_);
lean_dec(v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1062_);
v___x_1064_ = v___x_1049_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
size_t v___x_1066_; size_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1066_ = ((size_t)0ULL);
v___x_1067_ = lean_usize_of_nat(v___x_1051_);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1047_, v___x_1045_, v_entries_1037_, v___x_1066_, v___x_1067_, v___y_1043_);
lean_dec_ref(v_entries_1037_);
lean_dec(v___x_1045_);
lean_dec(v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1068_);
v___x_1070_ = v___x_1049_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v___x_1045_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v_entries_1037_);
v_a_1073_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1046_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1046_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
else
{
lean_dec_ref(v_entries_1037_);
lean_dec_ref(v_constants_1036_);
return v___x_1039_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v_leanOpts_1030_);
v_a_1090_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1032_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1032_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1098_, lean_object* v_leanOpts_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1098_, v_leanOpts_1099_);
lean_dec_ref(v_olean_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1102_, lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1103_, v_a_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1106_, v_m_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_m_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec(v_a_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_box(1);
v___x_1120_ = lean_panic_fn_borrowed(v___x_1119_, v_msg_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1124_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1125_ = lean_unsigned_to_nat(35u);
v___x_1126_ = lean_unsigned_to_nat(182u);
v___x_1127_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1128_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1129_ = l_mkPanicMessageWithDecl(v___x_1128_, v___x_1127_, v___x_1126_, v___x_1125_, v___x_1124_);
return v___x_1129_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1130_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1131_ = lean_unsigned_to_nat(21u);
v___x_1132_ = lean_unsigned_to_nat(183u);
v___x_1133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1134_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1135_ = l_mkPanicMessageWithDecl(v___x_1134_, v___x_1133_, v___x_1132_, v___x_1131_, v___x_1130_);
return v___x_1135_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1138_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1139_ = lean_unsigned_to_nat(35u);
v___x_1140_ = lean_unsigned_to_nat(276u);
v___x_1141_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1142_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1143_ = l_mkPanicMessageWithDecl(v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_);
return v___x_1143_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1144_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1145_ = lean_unsigned_to_nat(21u);
v___x_1146_ = lean_unsigned_to_nat(277u);
v___x_1147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1148_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1149_ = l_mkPanicMessageWithDecl(v___x_1148_, v___x_1147_, v___x_1146_, v___x_1145_, v___x_1144_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1150_, lean_object* v_v_1151_, lean_object* v_t_1152_){
_start:
{
if (lean_obj_tag(v_t_1152_) == 0)
{
lean_object* v_size_1153_; lean_object* v_k_1154_; lean_object* v_v_1155_; lean_object* v_l_1156_; lean_object* v_r_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1513_; 
v_size_1153_ = lean_ctor_get(v_t_1152_, 0);
v_k_1154_ = lean_ctor_get(v_t_1152_, 1);
v_v_1155_ = lean_ctor_get(v_t_1152_, 2);
v_l_1156_ = lean_ctor_get(v_t_1152_, 3);
v_r_1157_ = lean_ctor_get(v_t_1152_, 4);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_t_1152_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1159_ = v_t_1152_;
v_isShared_1160_ = v_isSharedCheck_1513_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_r_1157_);
lean_inc(v_l_1156_);
lean_inc(v_v_1155_);
lean_inc(v_k_1154_);
lean_inc(v_size_1153_);
lean_dec(v_t_1152_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1513_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_string_compare(v_k_1150_, v_k_1154_);
switch(v___x_1161_)
{
case 0:
{
lean_object* v___x_1162_; 
lean_dec(v_size_1153_);
v___x_1162_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1150_, v_v_1151_, v_l_1156_);
if (lean_obj_tag(v_r_1157_) == 0)
{
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_size_1163_; lean_object* v_size_1164_; lean_object* v_k_1165_; lean_object* v_v_1166_; lean_object* v_l_1167_; lean_object* v_r_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_size_1163_ = lean_ctor_get(v_r_1157_, 0);
v_size_1164_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_size_1164_);
v_k_1165_ = lean_ctor_get(v___x_1162_, 1);
lean_inc(v_k_1165_);
v_v_1166_ = lean_ctor_get(v___x_1162_, 2);
lean_inc(v_v_1166_);
v_l_1167_ = lean_ctor_get(v___x_1162_, 3);
lean_inc(v_l_1167_);
v_r_1168_ = lean_ctor_get(v___x_1162_, 4);
lean_inc(v_r_1168_);
v___x_1169_ = lean_unsigned_to_nat(3u);
v___x_1170_ = lean_nat_mul(v___x_1169_, v_size_1163_);
v___x_1171_ = lean_nat_dec_lt(v___x_1170_, v_size_1164_);
lean_dec(v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_dec(v_r_1168_);
lean_dec(v_l_1167_);
lean_dec(v_v_1166_);
lean_dec(v_k_1165_);
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_add(v___x_1172_, v_size_1164_);
lean_dec(v_size_1164_);
v___x_1174_ = lean_nat_add(v___x_1173_, v_size_1163_);
lean_dec(v___x_1173_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 3, v___x_1162_);
lean_ctor_set(v___x_1159_, 0, v___x_1174_);
v___x_1176_ = v___x_1159_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_r_1157_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1249_; 
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; lean_object* v_unused_1251_; lean_object* v_unused_1252_; lean_object* v_unused_1253_; lean_object* v_unused_1254_; 
v_unused_1250_ = lean_ctor_get(v___x_1162_, 4);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v___x_1162_, 3);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v___x_1162_, 2);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v___x_1162_, 1);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1254_);
v___x_1179_ = v___x_1162_;
v_isShared_1180_ = v_isSharedCheck_1249_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v___x_1162_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1249_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
if (lean_obj_tag(v_l_1167_) == 0)
{
if (lean_obj_tag(v_r_1168_) == 0)
{
lean_object* v_size_1181_; lean_object* v_size_1182_; lean_object* v_k_1183_; lean_object* v_v_1184_; lean_object* v_l_1185_; lean_object* v_r_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_size_1181_ = lean_ctor_get(v_l_1167_, 0);
v_size_1182_ = lean_ctor_get(v_r_1168_, 0);
v_k_1183_ = lean_ctor_get(v_r_1168_, 1);
v_v_1184_ = lean_ctor_get(v_r_1168_, 2);
v_l_1185_ = lean_ctor_get(v_r_1168_, 3);
v_r_1186_ = lean_ctor_get(v_r_1168_, 4);
v___x_1187_ = lean_unsigned_to_nat(2u);
v___x_1188_ = lean_nat_mul(v___x_1187_, v_size_1181_);
v___x_1189_ = lean_nat_dec_lt(v_size_1182_, v___x_1188_);
lean_dec(v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1219_; 
lean_inc(v_r_1186_);
lean_inc(v_l_1185_);
lean_inc(v_v_1184_);
lean_inc(v_k_1183_);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_r_1168_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1220_ = lean_ctor_get(v_r_1168_, 4);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_r_1168_, 3);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_r_1168_, 2);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_r_1168_, 1);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_r_1168_, 0);
lean_dec(v_unused_1224_);
v___x_1191_ = v_r_1168_;
v_isShared_1192_ = v_isSharedCheck_1219_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v_r_1168_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1219_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___x_1207_; lean_object* v___y_1209_; 
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = lean_nat_add(v___x_1193_, v_size_1164_);
lean_dec(v_size_1164_);
v___x_1195_ = lean_nat_add(v___x_1194_, v_size_1163_);
lean_dec(v___x_1194_);
v___x_1207_ = lean_nat_add(v___x_1193_, v_size_1181_);
if (lean_obj_tag(v_l_1185_) == 0)
{
lean_object* v_size_1217_; 
v_size_1217_ = lean_ctor_get(v_l_1185_, 0);
lean_inc(v_size_1217_);
v___y_1209_ = v_size_1217_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___y_1209_ = v___x_1218_;
goto v___jp_1208_;
}
v___jp_1196_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_nat_add(v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec(v___y_1198_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 4, v_r_1157_);
lean_ctor_set(v___x_1191_, 3, v_r_1186_);
lean_ctor_set(v___x_1191_, 2, v_v_1155_);
lean_ctor_set(v___x_1191_, 1, v_k_1154_);
lean_ctor_set(v___x_1191_, 0, v___x_1200_);
v___x_1202_ = v___x_1191_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_r_1186_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_r_1157_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 4, v___x_1202_);
lean_ctor_set(v___x_1179_, 3, v___y_1197_);
lean_ctor_set(v___x_1179_, 2, v_v_1184_);
lean_ctor_set(v___x_1179_, 1, v_k_1183_);
lean_ctor_set(v___x_1179_, 0, v___x_1195_);
v___x_1204_ = v___x_1179_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1183_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1184_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v___y_1197_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
v___jp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_nat_add(v___x_1207_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec(v___x_1207_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_l_1185_);
lean_ctor_set(v___x_1159_, 3, v_l_1167_);
lean_ctor_set(v___x_1159_, 2, v_v_1166_);
lean_ctor_set(v___x_1159_, 1, v_k_1165_);
lean_ctor_set(v___x_1159_, 0, v___x_1210_);
v___x_1212_ = v___x_1159_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1165_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1166_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_l_1167_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_l_1185_);
v___x_1212_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_nat_add(v___x_1193_, v_size_1163_);
if (lean_obj_tag(v_r_1186_) == 0)
{
lean_object* v_size_1214_; 
v_size_1214_ = lean_ctor_get(v_r_1186_, 0);
lean_inc(v_size_1214_);
v___y_1197_ = v___x_1212_;
v___y_1198_ = v___x_1213_;
v___y_1199_ = v_size_1214_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___y_1197_ = v___x_1212_;
v___y_1198_ = v___x_1213_;
v___y_1199_ = v___x_1215_;
goto v___jp_1196_;
}
}
}
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_del_object(v___x_1159_);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_add(v___x_1225_, v_size_1164_);
lean_dec(v_size_1164_);
v___x_1227_ = lean_nat_add(v___x_1226_, v_size_1163_);
lean_dec(v___x_1226_);
v___x_1228_ = lean_nat_add(v___x_1225_, v_size_1163_);
v___x_1229_ = lean_nat_add(v___x_1228_, v_size_1182_);
lean_dec(v___x_1228_);
lean_inc_ref(v_r_1157_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 4, v_r_1157_);
lean_ctor_set(v___x_1179_, 3, v_r_1168_);
lean_ctor_set(v___x_1179_, 2, v_v_1155_);
lean_ctor_set(v___x_1179_, 1, v_k_1154_);
lean_ctor_set(v___x_1179_, 0, v___x_1229_);
v___x_1231_ = v___x_1179_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_r_1168_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_r_1157_);
v___x_1231_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
v_isSharedCheck_1238_ = !lean_is_exclusive(v_r_1157_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; lean_object* v_unused_1240_; lean_object* v_unused_1241_; lean_object* v_unused_1242_; lean_object* v_unused_1243_; 
v_unused_1239_ = lean_ctor_get(v_r_1157_, 4);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_r_1157_, 3);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v_r_1157_, 2);
lean_dec(v_unused_1241_);
v_unused_1242_ = lean_ctor_get(v_r_1157_, 1);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_r_1157_, 0);
lean_dec(v_unused_1243_);
v___x_1233_ = v_r_1157_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_dec(v_r_1157_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v___x_1231_);
lean_ctor_set(v___x_1233_, 3, v_l_1167_);
lean_ctor_set(v___x_1233_, 2, v_v_1166_);
lean_ctor_set(v___x_1233_, 1, v_k_1165_);
lean_ctor_set(v___x_1233_, 0, v___x_1227_);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_k_1165_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_v_1166_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_l_1167_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v___x_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref_known(v_l_1167_, 5);
lean_del_object(v___x_1179_);
lean_dec(v_v_1166_);
lean_dec(v_k_1165_);
lean_dec(v_size_1164_);
lean_dec_ref_known(v_r_1157_, 5);
lean_del_object(v___x_1159_);
lean_dec(v_v_1155_);
lean_dec(v_k_1154_);
v___x_1245_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1246_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1245_);
return v___x_1246_;
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_del_object(v___x_1179_);
lean_dec(v_r_1168_);
lean_dec(v_v_1166_);
lean_dec(v_k_1165_);
lean_dec(v_size_1164_);
lean_dec_ref_known(v_r_1157_, 5);
lean_del_object(v___x_1159_);
lean_dec(v_v_1155_);
lean_dec(v_k_1154_);
v___x_1247_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1248_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1247_);
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_size_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_size_1255_ = lean_ctor_get(v_r_1157_, 0);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v___x_1256_, v_size_1255_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 3, v___x_1162_);
lean_ctor_set(v___x_1159_, 0, v___x_1257_);
v___x_1259_ = v___x_1159_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_r_1157_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_l_1261_; 
v_l_1261_ = lean_ctor_get(v___x_1162_, 3);
lean_inc(v_l_1261_);
if (lean_obj_tag(v_l_1261_) == 0)
{
lean_object* v_r_1262_; 
v_r_1262_ = lean_ctor_get(v___x_1162_, 4);
lean_inc(v_r_1262_);
if (lean_obj_tag(v_r_1262_) == 0)
{
lean_object* v_size_1263_; lean_object* v_k_1264_; lean_object* v_v_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1279_; 
v_size_1263_ = lean_ctor_get(v___x_1162_, 0);
v_k_1264_ = lean_ctor_get(v___x_1162_, 1);
v_v_1265_ = lean_ctor_get(v___x_1162_, 2);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; lean_object* v_unused_1281_; 
v_unused_1280_ = lean_ctor_get(v___x_1162_, 4);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v___x_1162_, 3);
lean_dec(v_unused_1281_);
v___x_1267_ = v___x_1162_;
v_isShared_1268_ = v_isSharedCheck_1279_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_v_1265_);
lean_inc(v_k_1264_);
lean_inc(v_size_1263_);
lean_dec(v___x_1162_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1279_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_size_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v_size_1269_ = lean_ctor_get(v_r_1262_, 0);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v___x_1270_, v_size_1263_);
lean_dec(v_size_1263_);
v___x_1272_ = lean_nat_add(v___x_1270_, v_size_1269_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 4, v_r_1157_);
lean_ctor_set(v___x_1267_, 3, v_r_1262_);
lean_ctor_set(v___x_1267_, 2, v_v_1155_);
lean_ctor_set(v___x_1267_, 1, v_k_1154_);
lean_ctor_set(v___x_1267_, 0, v___x_1272_);
v___x_1274_ = v___x_1267_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_r_1262_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_r_1157_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1274_);
lean_ctor_set(v___x_1159_, 3, v_l_1261_);
lean_ctor_set(v___x_1159_, 2, v_v_1265_);
lean_ctor_set(v___x_1159_, 1, v_k_1264_);
lean_ctor_set(v___x_1159_, 0, v___x_1271_);
v___x_1276_ = v___x_1159_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1264_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1265_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_l_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_k_1282_; lean_object* v_v_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1295_; 
v_k_1282_ = lean_ctor_get(v___x_1162_, 1);
v_v_1283_ = lean_ctor_get(v___x_1162_, 2);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; lean_object* v_unused_1297_; lean_object* v_unused_1298_; 
v_unused_1296_ = lean_ctor_get(v___x_1162_, 4);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v___x_1162_, 3);
lean_dec(v_unused_1297_);
v_unused_1298_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1298_);
v___x_1285_ = v___x_1162_;
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_v_1283_);
lean_inc(v_k_1282_);
lean_dec(v___x_1162_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = lean_unsigned_to_nat(3u);
v___x_1288_ = lean_unsigned_to_nat(1u);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 3, v_r_1262_);
lean_ctor_set(v___x_1285_, 2, v_v_1155_);
lean_ctor_set(v___x_1285_, 1, v_k_1154_);
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_r_1262_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_r_1262_);
v___x_1290_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1290_);
lean_ctor_set(v___x_1159_, 3, v_l_1261_);
lean_ctor_set(v___x_1159_, 2, v_v_1283_);
lean_ctor_set(v___x_1159_, 1, v_k_1282_);
lean_ctor_set(v___x_1159_, 0, v___x_1287_);
v___x_1292_ = v___x_1159_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_l_1261_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_r_1299_; 
v_r_1299_ = lean_ctor_get(v___x_1162_, 4);
lean_inc(v_r_1299_);
if (lean_obj_tag(v_r_1299_) == 0)
{
lean_object* v_k_1300_; lean_object* v_v_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1325_; 
v_k_1300_ = lean_ctor_get(v___x_1162_, 1);
v_v_1301_ = lean_ctor_get(v___x_1162_, 2);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; lean_object* v_unused_1327_; lean_object* v_unused_1328_; 
v_unused_1326_ = lean_ctor_get(v___x_1162_, 4);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v___x_1162_, 3);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1328_);
v___x_1303_ = v___x_1162_;
v_isShared_1304_ = v_isSharedCheck_1325_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_v_1301_);
lean_inc(v_k_1300_);
lean_dec(v___x_1162_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1325_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_k_1305_; lean_object* v_v_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1321_; 
v_k_1305_ = lean_ctor_get(v_r_1299_, 1);
v_v_1306_ = lean_ctor_get(v_r_1299_, 2);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_r_1299_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; 
v_unused_1322_ = lean_ctor_get(v_r_1299_, 4);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_r_1299_, 3);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_r_1299_, 0);
lean_dec(v_unused_1324_);
v___x_1308_ = v_r_1299_;
v_isShared_1309_ = v_isSharedCheck_1321_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_v_1306_);
lean_inc(v_k_1305_);
lean_dec(v_r_1299_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1321_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1310_ = lean_unsigned_to_nat(3u);
v___x_1311_ = lean_unsigned_to_nat(1u);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 4, v_l_1261_);
lean_ctor_set(v___x_1308_, 3, v_l_1261_);
lean_ctor_set(v___x_1308_, 2, v_v_1301_);
lean_ctor_set(v___x_1308_, 1, v_k_1300_);
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1313_ = v___x_1308_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_k_1300_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_v_1301_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_l_1261_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_l_1261_);
v___x_1313_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 4, v_l_1261_);
lean_ctor_set(v___x_1303_, 2, v_v_1155_);
lean_ctor_set(v___x_1303_, 1, v_k_1154_);
lean_ctor_set(v___x_1303_, 0, v___x_1311_);
v___x_1315_ = v___x_1303_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_l_1261_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_l_1261_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1315_);
lean_ctor_set(v___x_1159_, 3, v___x_1313_);
lean_ctor_set(v___x_1159_, 2, v_v_1306_);
lean_ctor_set(v___x_1159_, 1, v_k_1305_);
lean_ctor_set(v___x_1159_, 0, v___x_1310_);
v___x_1317_ = v___x_1159_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_k_1305_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_v_1306_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(2u);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_r_1299_);
lean_ctor_set(v___x_1159_, 3, v___x_1162_);
lean_ctor_set(v___x_1159_, 0, v___x_1329_);
v___x_1331_ = v___x_1159_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_r_1299_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(1u);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1162_);
lean_ctor_set(v___x_1159_, 3, v___x_1162_);
lean_ctor_set(v___x_1159_, 0, v___x_1333_);
v___x_1335_ = v___x_1159_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v___x_1162_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
case 1:
{
lean_object* v___x_1338_; 
lean_dec(v_v_1155_);
lean_dec(v_k_1154_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 2, v_v_1151_);
lean_ctor_set(v___x_1159_, 1, v_k_1150_);
v___x_1338_ = v___x_1159_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_size_1153_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1150_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1151_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_l_1156_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_r_1157_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
default: 
{
lean_object* v___x_1340_; 
lean_dec(v_size_1153_);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1150_, v_v_1151_, v_r_1157_);
if (lean_obj_tag(v_l_1156_) == 0)
{
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_size_1341_; lean_object* v_size_1342_; lean_object* v_k_1343_; lean_object* v_v_1344_; lean_object* v_l_1345_; lean_object* v_r_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_size_1341_ = lean_ctor_get(v_l_1156_, 0);
v_size_1342_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_size_1342_);
v_k_1343_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_k_1343_);
v_v_1344_ = lean_ctor_get(v___x_1340_, 2);
lean_inc(v_v_1344_);
v_l_1345_ = lean_ctor_get(v___x_1340_, 3);
lean_inc(v_l_1345_);
v_r_1346_ = lean_ctor_get(v___x_1340_, 4);
lean_inc(v_r_1346_);
v___x_1347_ = lean_unsigned_to_nat(3u);
v___x_1348_ = lean_nat_mul(v___x_1347_, v_size_1341_);
v___x_1349_ = lean_nat_dec_lt(v___x_1348_, v_size_1342_);
lean_dec(v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_dec(v_r_1346_);
lean_dec(v_l_1345_);
lean_dec(v_v_1344_);
lean_dec(v_k_1343_);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_add(v___x_1350_, v_size_1341_);
v___x_1352_ = lean_nat_add(v___x_1351_, v_size_1342_);
lean_dec(v_size_1342_);
lean_dec(v___x_1351_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1340_);
lean_ctor_set(v___x_1159_, 0, v___x_1352_);
v___x_1354_ = v___x_1159_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_l_1156_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1340_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1426_ = lean_ctor_get(v___x_1340_, 4);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v___x_1340_, 3);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v___x_1340_, 2);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v___x_1340_, 1);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1430_);
v___x_1357_ = v___x_1340_;
v_isShared_1358_ = v_isSharedCheck_1425_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v___x_1340_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1425_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
if (lean_obj_tag(v_l_1345_) == 0)
{
if (lean_obj_tag(v_r_1346_) == 0)
{
lean_object* v_size_1359_; lean_object* v_k_1360_; lean_object* v_v_1361_; lean_object* v_l_1362_; lean_object* v_r_1363_; lean_object* v_size_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_size_1359_ = lean_ctor_get(v_l_1345_, 0);
v_k_1360_ = lean_ctor_get(v_l_1345_, 1);
v_v_1361_ = lean_ctor_get(v_l_1345_, 2);
v_l_1362_ = lean_ctor_get(v_l_1345_, 3);
v_r_1363_ = lean_ctor_get(v_l_1345_, 4);
v_size_1364_ = lean_ctor_get(v_r_1346_, 0);
v___x_1365_ = lean_unsigned_to_nat(2u);
v___x_1366_ = lean_nat_mul(v___x_1365_, v_size_1364_);
v___x_1367_ = lean_nat_dec_lt(v_size_1359_, v___x_1366_);
lean_dec(v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1396_; 
lean_inc(v_r_1363_);
lean_inc(v_l_1362_);
lean_inc(v_v_1361_);
lean_inc(v_k_1360_);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1397_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_l_1345_, 2);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_l_1345_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1401_);
v___x_1369_ = v_l_1345_;
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v_l_1345_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1386_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v___x_1371_, v_size_1341_);
v___x_1373_ = lean_nat_add(v___x_1372_, v_size_1342_);
lean_dec(v_size_1342_);
if (lean_obj_tag(v_l_1362_) == 0)
{
lean_object* v_size_1394_; 
v_size_1394_ = lean_ctor_get(v_l_1362_, 0);
lean_inc(v_size_1394_);
v___y_1386_ = v_size_1394_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___y_1386_ = v___x_1395_;
goto v___jp_1385_;
}
v___jp_1374_:
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1378_ = lean_nat_add(v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec(v___y_1376_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 4, v_r_1346_);
lean_ctor_set(v___x_1369_, 3, v_r_1363_);
lean_ctor_set(v___x_1369_, 2, v_v_1344_);
lean_ctor_set(v___x_1369_, 1, v_k_1343_);
lean_ctor_set(v___x_1369_, 0, v___x_1378_);
v___x_1380_ = v___x_1369_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_r_1363_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_r_1346_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v___x_1380_);
lean_ctor_set(v___x_1357_, 3, v___y_1375_);
lean_ctor_set(v___x_1357_, 2, v_v_1361_);
lean_ctor_set(v___x_1357_, 1, v_k_1360_);
lean_ctor_set(v___x_1357_, 0, v___x_1373_);
v___x_1382_ = v___x_1357_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1360_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1361_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v___y_1375_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
v___jp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_nat_add(v___x_1372_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec(v___x_1372_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_l_1362_);
lean_ctor_set(v___x_1159_, 0, v___x_1387_);
v___x_1389_ = v___x_1159_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_l_1156_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_l_1362_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_nat_add(v___x_1371_, v_size_1364_);
if (lean_obj_tag(v_r_1363_) == 0)
{
lean_object* v_size_1391_; 
v_size_1391_ = lean_ctor_get(v_r_1363_, 0);
lean_inc(v_size_1391_);
v___y_1375_ = v___x_1389_;
v___y_1376_ = v___x_1390_;
v___y_1377_ = v_size_1391_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_unsigned_to_nat(0u);
v___y_1375_ = v___x_1389_;
v___y_1376_ = v___x_1390_;
v___y_1377_ = v___x_1392_;
goto v___jp_1374_;
}
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_del_object(v___x_1159_);
v___x_1402_ = lean_unsigned_to_nat(1u);
v___x_1403_ = lean_nat_add(v___x_1402_, v_size_1341_);
v___x_1404_ = lean_nat_add(v___x_1403_, v_size_1342_);
lean_dec(v_size_1342_);
v___x_1405_ = lean_nat_add(v___x_1403_, v_size_1359_);
lean_dec(v___x_1403_);
lean_inc_ref(v_l_1156_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1345_);
lean_ctor_set(v___x_1357_, 3, v_l_1156_);
lean_ctor_set(v___x_1357_, 2, v_v_1155_);
lean_ctor_set(v___x_1357_, 1, v_k_1154_);
lean_ctor_set(v___x_1357_, 0, v___x_1405_);
v___x_1407_ = v___x_1357_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_l_1156_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_l_1345_);
v___x_1407_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_isSharedCheck_1414_ = !lean_is_exclusive(v_l_1156_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; lean_object* v_unused_1416_; lean_object* v_unused_1417_; lean_object* v_unused_1418_; lean_object* v_unused_1419_; 
v_unused_1415_ = lean_ctor_get(v_l_1156_, 4);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_l_1156_, 3);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_l_1156_, 2);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_l_1156_, 1);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_l_1156_, 0);
lean_dec(v_unused_1419_);
v___x_1409_ = v_l_1156_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_l_1156_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_1346_);
lean_ctor_set(v___x_1409_, 3, v___x_1407_);
lean_ctor_set(v___x_1409_, 2, v_v_1344_);
lean_ctor_set(v___x_1409_, 1, v_k_1343_);
lean_ctor_set(v___x_1409_, 0, v___x_1404_);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_r_1346_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref_known(v_l_1345_, 5);
lean_del_object(v___x_1357_);
lean_dec(v_v_1344_);
lean_dec(v_k_1343_);
lean_dec(v_size_1342_);
lean_dec_ref_known(v_l_1156_, 5);
lean_del_object(v___x_1159_);
lean_dec(v_v_1155_);
lean_dec(v_k_1154_);
v___x_1421_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1422_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1421_);
return v___x_1422_;
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_del_object(v___x_1357_);
lean_dec(v_r_1346_);
lean_dec(v_v_1344_);
lean_dec(v_k_1343_);
lean_dec(v_size_1342_);
lean_dec_ref_known(v_l_1156_, 5);
lean_del_object(v___x_1159_);
lean_dec(v_v_1155_);
lean_dec(v_k_1154_);
v___x_1423_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1424_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1423_);
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_size_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_size_1431_ = lean_ctor_get(v_l_1156_, 0);
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_add(v___x_1432_, v_size_1431_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1340_);
lean_ctor_set(v___x_1159_, 0, v___x_1433_);
v___x_1435_ = v___x_1159_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_l_1156_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v___x_1340_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_l_1437_; 
v_l_1437_ = lean_ctor_get(v___x_1340_, 3);
lean_inc(v_l_1437_);
if (lean_obj_tag(v_l_1437_) == 0)
{
lean_object* v_r_1438_; 
v_r_1438_ = lean_ctor_get(v___x_1340_, 4);
lean_inc(v_r_1438_);
if (lean_obj_tag(v_r_1438_) == 0)
{
lean_object* v_size_1439_; lean_object* v_k_1440_; lean_object* v_v_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1455_; 
v_size_1439_ = lean_ctor_get(v___x_1340_, 0);
v_k_1440_ = lean_ctor_get(v___x_1340_, 1);
v_v_1441_ = lean_ctor_get(v___x_1340_, 2);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; lean_object* v_unused_1457_; 
v_unused_1456_ = lean_ctor_get(v___x_1340_, 4);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v___x_1340_, 3);
lean_dec(v_unused_1457_);
v___x_1443_ = v___x_1340_;
v_isShared_1444_ = v_isSharedCheck_1455_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_v_1441_);
lean_inc(v_k_1440_);
lean_inc(v_size_1439_);
lean_dec(v___x_1340_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1455_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_size_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v_size_1445_ = lean_ctor_get(v_l_1437_, 0);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1439_);
lean_dec(v_size_1439_);
v___x_1448_ = lean_nat_add(v___x_1446_, v_size_1445_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_l_1437_);
lean_ctor_set(v___x_1443_, 3, v_l_1156_);
lean_ctor_set(v___x_1443_, 2, v_v_1155_);
lean_ctor_set(v___x_1443_, 1, v_k_1154_);
lean_ctor_set(v___x_1443_, 0, v___x_1448_);
v___x_1450_ = v___x_1443_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_l_1156_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_l_1437_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_r_1438_);
lean_ctor_set(v___x_1159_, 3, v___x_1450_);
lean_ctor_set(v___x_1159_, 2, v_v_1441_);
lean_ctor_set(v___x_1159_, 1, v_k_1440_);
lean_ctor_set(v___x_1159_, 0, v___x_1447_);
v___x_1452_ = v___x_1159_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_r_1438_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_k_1458_; lean_object* v_v_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1483_; 
v_k_1458_ = lean_ctor_get(v___x_1340_, 1);
v_v_1459_ = lean_ctor_get(v___x_1340_, 2);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1484_ = lean_ctor_get(v___x_1340_, 4);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v___x_1340_, 3);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1486_);
v___x_1461_ = v___x_1340_;
v_isShared_1462_ = v_isSharedCheck_1483_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_v_1459_);
lean_inc(v_k_1458_);
lean_dec(v___x_1340_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1483_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_k_1463_; lean_object* v_v_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1479_; 
v_k_1463_ = lean_ctor_get(v_l_1437_, 1);
v_v_1464_ = lean_ctor_get(v_l_1437_, 2);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_l_1437_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; 
v_unused_1480_ = lean_ctor_get(v_l_1437_, 4);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1437_, 3);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_l_1437_, 0);
lean_dec(v_unused_1482_);
v___x_1466_ = v_l_1437_;
v_isShared_1467_ = v_isSharedCheck_1479_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
lean_dec(v_l_1437_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1479_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1468_ = lean_unsigned_to_nat(3u);
v___x_1469_ = lean_unsigned_to_nat(1u);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 4, v_r_1438_);
lean_ctor_set(v___x_1466_, 3, v_r_1438_);
lean_ctor_set(v___x_1466_, 2, v_v_1155_);
lean_ctor_set(v___x_1466_, 1, v_k_1154_);
lean_ctor_set(v___x_1466_, 0, v___x_1469_);
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_r_1438_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_r_1438_);
v___x_1471_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 3, v_r_1438_);
lean_ctor_set(v___x_1461_, 0, v___x_1469_);
v___x_1473_ = v___x_1461_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1458_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1459_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_r_1438_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1438_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1473_);
lean_ctor_set(v___x_1159_, 3, v___x_1471_);
lean_ctor_set(v___x_1159_, 2, v_v_1464_);
lean_ctor_set(v___x_1159_, 1, v_k_1463_);
lean_ctor_set(v___x_1159_, 0, v___x_1468_);
v___x_1475_ = v___x_1159_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v___x_1473_);
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
}
}
else
{
lean_object* v_r_1487_; 
v_r_1487_ = lean_ctor_get(v___x_1340_, 4);
lean_inc(v_r_1487_);
if (lean_obj_tag(v_r_1487_) == 0)
{
lean_object* v_k_1488_; lean_object* v_v_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1501_; 
v_k_1488_ = lean_ctor_get(v___x_1340_, 1);
v_v_1489_ = lean_ctor_get(v___x_1340_, 2);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1502_ = lean_ctor_get(v___x_1340_, 4);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v___x_1340_, 3);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1504_);
v___x_1491_ = v___x_1340_;
v_isShared_1492_ = v_isSharedCheck_1501_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_v_1489_);
lean_inc(v_k_1488_);
lean_dec(v___x_1340_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1501_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_unsigned_to_nat(1u);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v_l_1437_);
lean_ctor_set(v___x_1491_, 2, v_v_1155_);
lean_ctor_set(v___x_1491_, 1, v_k_1154_);
lean_ctor_set(v___x_1491_, 0, v___x_1494_);
v___x_1496_ = v___x_1491_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1437_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v_r_1487_);
lean_ctor_set(v___x_1159_, 3, v___x_1496_);
lean_ctor_set(v___x_1159_, 2, v_v_1489_);
lean_ctor_set(v___x_1159_, 1, v_k_1488_);
lean_ctor_set(v___x_1159_, 0, v___x_1493_);
v___x_1498_ = v___x_1159_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1488_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1487_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(2u);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1340_);
lean_ctor_set(v___x_1159_, 3, v_r_1487_);
lean_ctor_set(v___x_1159_, 0, v___x_1505_);
v___x_1507_ = v___x_1159_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1340_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(1u);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1340_);
lean_ctor_set(v___x_1159_, 3, v___x_1340_);
lean_ctor_set(v___x_1159_, 0, v___x_1509_);
v___x_1511_ = v___x_1159_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v___x_1340_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v_k_1150_);
lean_ctor_set(v___x_1515_, 2, v_v_1151_);
lean_ctor_set(v___x_1515_, 3, v_t_1152_);
lean_ctor_set(v___x_1515_, 4, v_t_1152_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1516_, lean_object* v_x_1517_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 0)
{
lean_object* v_k_1518_; lean_object* v_v_1519_; lean_object* v_l_1520_; lean_object* v_r_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_k_1518_ = lean_ctor_get(v_x_1517_, 1);
lean_inc(v_k_1518_);
v_v_1519_ = lean_ctor_get(v_x_1517_, 2);
lean_inc(v_v_1519_);
v_l_1520_ = lean_ctor_get(v_x_1517_, 3);
lean_inc(v_l_1520_);
v_r_1521_ = lean_ctor_get(v_x_1517_, 4);
lean_inc(v_r_1521_);
lean_dec_ref_known(v_x_1517_, 5);
v___x_1522_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1516_, v_l_1520_);
v___x_1523_ = 1;
v___x_1524_ = l_Lean_Name_toString(v_k_1518_, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_v_1519_);
v___x_1526_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1524_, v___x_1525_, v___x_1522_);
v_init_1516_ = v___x_1526_;
v_x_1517_ = v_r_1521_;
goto _start;
}
else
{
return v_init_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_box(1);
v___x_1530_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1529_, v_m_1528_);
v___x_1531_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
if (lean_obj_tag(v_a_1532_) == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_array_to_list(v_a_1533_);
return v___x_1534_;
}
else
{
lean_object* v_head_1535_; lean_object* v_tail_1536_; lean_object* v___x_1537_; 
v_head_1535_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_head_1535_);
v_tail_1536_ = lean_ctor_get(v_a_1532_, 1);
lean_inc(v_tail_1536_);
lean_dec_ref_known(v_a_1532_, 2);
v___x_1537_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1533_, v_head_1535_);
v_a_1532_ = v_tail_1536_;
v_a_1533_ = v___x_1537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1547_){
_start:
{
lean_object* v_idx_1548_; lean_object* v_name_1549_; lean_object* v_platform_1550_; lean_object* v_leanHash_1551_; uint64_t v_configHash_1552_; lean_object* v_options_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_idx_1548_ = lean_ctor_get(v_x_1547_, 0);
lean_inc(v_idx_1548_);
v_name_1549_ = lean_ctor_get(v_x_1547_, 1);
lean_inc(v_name_1549_);
v_platform_1550_ = lean_ctor_get(v_x_1547_, 2);
lean_inc_ref(v_platform_1550_);
v_leanHash_1551_ = lean_ctor_get(v_x_1547_, 3);
lean_inc_ref(v_leanHash_1551_);
v_configHash_1552_ = lean_ctor_get_uint64(v_x_1547_, sizeof(void*)*5);
v_options_1553_ = lean_ctor_get(v_x_1547_, 4);
lean_inc(v_options_1553_);
lean_dec_ref(v_x_1547_);
v___x_1554_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1555_ = l_Lean_JsonNumber_fromNat(v_idx_1548_);
v___x_1556_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1554_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1561_ = 1;
v___x_1562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1549_, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1560_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v___x_1558_);
v___x_1566_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_platform_1550_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v___x_1558_);
v___x_1570_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_leanHash_1551_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1558_);
v___x_1574_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1575_ = l_Lake_lowerHexUInt64(v_configHash_1552_);
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1574_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___x_1558_);
v___x_1579_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1580_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1553_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___x_1558_);
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v___x_1558_);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1578_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1573_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1569_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1565_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1559_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1590_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1588_, v___x_1589_);
v___x_1591_ = l_Lean_Json_mkObj(v___x_1590_);
lean_dec(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1592_, lean_object* v_msg_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1595_, lean_object* v_k_1596_, lean_object* v_v_1597_, lean_object* v_t_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1596_, v_v_1597_, v_t_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1600_, lean_object* v_t_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1600_, v_t_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1605_, lean_object* v_k_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = l_Lean_Json_getObjValD(v_j_1605_, v_k_1606_);
v___x_1608_ = l_Lean_Json_getNat_x3f(v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1609_, lean_object* v_k_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1609_, v_k_1610_);
lean_dec_ref(v_k_1610_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1612_, lean_object* v_k_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_Lean_Json_getObjValD(v_j_1612_, v_k_1613_);
v___x_1615_ = l_Lean_Name_fromJson_x3f(v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1616_, lean_object* v_k_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1616_, v_k_1617_);
lean_dec_ref(v_k_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1619_, lean_object* v_k_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_Json_getObjValD(v_j_1619_, v_k_1620_);
v___x_1622_ = l_Lean_Json_getStr_x3f(v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1623_, lean_object* v_k_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1623_, v_k_1624_);
lean_dec_ref(v_k_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1626_, lean_object* v_k_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = l_Lean_Json_getObjValD(v_j_1626_, v_k_1627_);
v___x_1629_ = l_Lake_Hash_fromJson_x3f(v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1630_, lean_object* v_k_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1630_, v_k_1631_);
lean_dec_ref(v_k_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1636_, lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 0)
{
lean_object* v_k_1638_; lean_object* v_v_1639_; lean_object* v_l_1640_; lean_object* v_r_1641_; lean_object* v___x_1642_; 
v_k_1638_ = lean_ctor_get(v_x_1637_, 1);
lean_inc(v_k_1638_);
v_v_1639_ = lean_ctor_get(v_x_1637_, 2);
lean_inc(v_v_1639_);
v_l_1640_ = lean_ctor_get(v_x_1637_, 3);
lean_inc(v_l_1640_);
v_r_1641_ = lean_ctor_get(v_x_1637_, 4);
lean_inc(v_r_1641_);
lean_dec_ref_known(v_x_1637_, 5);
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1636_, v_l_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec(v_r_1641_);
lean_dec(v_v_1639_);
lean_dec(v_k_1638_);
return v___x_1642_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1683_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1683_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1683_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1648_ = lean_string_dec_eq(v_k_1638_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v_n_1649_; uint8_t v___x_1650_; 
lean_inc(v_k_1638_);
v_n_1649_ = l_String_toName(v_k_1638_);
v___x_1650_ = l_Lean_Name_isAnonymous(v_n_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_del_object(v___x_1645_);
lean_dec(v_k_1638_);
v___x_1651_ = l_Lean_Json_getStr_x3f(v_v_1639_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_n_1649_);
lean_dec(v_a_1643_);
lean_dec(v_r_1641_);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1649_, v_a_1660_, v_a_1643_);
v_init_1636_ = v___x_1661_;
v_x_1637_ = v_r_1641_;
goto _start;
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec(v_n_1649_);
lean_dec(v_a_1643_);
lean_dec(v_r_1641_);
lean_dec(v_v_1639_);
v___x_1663_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1664_ = lean_string_append(v___x_1663_, v_k_1638_);
lean_dec(v_k_1638_);
v___x_1665_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1666_);
v___x_1668_ = v___x_1645_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
else
{
lean_object* v___x_1670_; 
lean_del_object(v___x_1645_);
lean_dec(v_k_1638_);
v___x_1670_ = l_Lean_Json_getStr_x3f(v_v_1639_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1643_);
lean_dec(v_r_1641_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1679_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1680_ = lean_box(0);
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1680_, v_a_1679_, v_a_1643_);
v_init_1636_ = v___x_1681_;
v_x_1637_ = v_r_1641_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_init_1636_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1686_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 5)
{
lean_object* v_kvPairs_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_kvPairs_1687_ = lean_ctor_get(v_x_1686_, 0);
lean_inc(v_kvPairs_1687_);
lean_dec_ref_known(v_x_1686_, 1);
v___x_1688_ = lean_box(1);
v___x_1689_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1688_, v_kvPairs_1687_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1690_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1691_ = lean_unsigned_to_nat(80u);
v___x_1692_ = l_Lean_Json_pretty(v_x_1686_, v___x_1691_);
v___x_1693_ = lean_string_append(v___x_1690_, v___x_1692_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1695_ = lean_string_append(v___x_1693_, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1697_, lean_object* v_k_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = l_Lean_Json_getObjValD(v_j_1697_, v_k_1698_);
v___x_1700_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1701_, lean_object* v_k_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1701_, v_k_1702_);
lean_dec_ref(v_k_1702_);
return v_res_1703_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = 1;
v___x_1733_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1734_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1733_, v___x_1732_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1737_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1738_ = lean_string_append(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = 1;
v___x_1742_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1743_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1745_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1746_ = lean_string_append(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1749_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1750_ = lean_string_append(v___x_1749_, v___x_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = 1;
v___x_1754_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1755_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1757_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1758_ = lean_string_append(v___x_1757_, v___x_1756_);
return v___x_1758_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1760_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1761_ = lean_string_append(v___x_1760_, v___x_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = 1;
v___x_1765_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1768_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1769_ = lean_string_append(v___x_1768_, v___x_1767_);
return v___x_1769_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1771_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = 1;
v___x_1776_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1776_, v___x_1775_);
return v___x_1777_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1779_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1780_ = lean_string_append(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1782_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1783_ = lean_string_append(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = 1;
v___x_1787_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1787_, v___x_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1790_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1791_ = lean_string_append(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1793_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1794_ = lean_string_append(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = 1;
v___x_1798_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1801_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1802_ = lean_string_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1804_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1805_ = lean_string_append(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1806_);
v___x_1808_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1806_, v___x_1807_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_json_1806_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_1814_ = lean_string_append(v___x_1813_, v_a_1809_);
lean_dec(v_a_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_json_1806_);
v_a_1819_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1808_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1808_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 0);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_a_1827_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1828_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1806_);
v___x_1829_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1806_, v___x_1828_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_1835_ = lean_string_append(v___x_1834_, v_a_1830_);
lean_dec(v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
v_a_1840_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1829_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1829_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 0);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1848_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1806_);
v___x_1850_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1806_, v___x_1849_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1855_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1856_ = lean_string_append(v___x_1855_, v_a_1851_);
lean_dec(v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1856_);
v___x_1858_ = v___x_1853_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
v_a_1861_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1850_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1850_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 0);
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_a_1869_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1850_, 1);
v___x_1870_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1806_);
v___x_1871_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1806_, v___x_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_a_1869_);
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
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
v___x_1876_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
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
lean_dec(v_a_1869_);
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
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
lean_dec_ref_known(v___x_1871_, 1);
v___x_1891_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1806_);
v___x_1892_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1806_, v___x_1891_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1890_);
lean_dec(v_a_1869_);
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
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
v___x_1897_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
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
lean_dec(v_a_1869_);
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
lean_dec(v_json_1806_);
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
v___x_1912_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1913_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1806_, v___x_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1911_);
lean_dec(v_a_1890_);
lean_dec(v_a_1869_);
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
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
v___x_1918_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
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
lean_dec(v_a_1869_);
lean_dec(v_a_1848_);
lean_dec(v_a_1827_);
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
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1941_; 
v_a_1932_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1934_ = v___x_1913_;
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1913_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; uint64_t v___x_1937_; lean_object* v___x_1939_; 
v___x_1936_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1936_, 0, v_a_1827_);
lean_ctor_set(v___x_1936_, 1, v_a_1848_);
lean_ctor_set(v___x_1936_, 2, v_a_1869_);
lean_ctor_set(v___x_1936_, 3, v_a_1890_);
lean_ctor_set(v___x_1936_, 4, v_a_1932_);
v___x_1937_ = lean_unbox_uint64(v_a_1911_);
lean_dec(v_a_1911_);
lean_ctor_set_uint64(v___x_1936_, sizeof(void*)*5, v___x_1937_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1936_);
v___x_1939_ = v___x_1934_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1936_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
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
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_1946_ = lean_mk_io_user_error(v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v_h_1949_){
_start:
{
uint8_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = 1;
v___x_1952_ = lean_io_prim_handle_mk(v___x_1947_, v___x_1951_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; uint8_t v___x_1954_; lean_object* v___x_1955_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = 1;
v___x_1955_ = lean_io_prim_handle_try_lock(v_a_1953_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; uint8_t v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = lean_unbox(v_a_1956_);
lean_dec(v_a_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_dec(v_a_1953_);
v___x_1958_ = lean_io_prim_handle_unlock(v_h_1949_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1966_; 
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1967_);
v___x_1960_ = v___x_1958_;
v_isShared_1961_ = v_isSharedCheck_1966_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1966_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1962_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
lean_ctor_set(v___x_1960_, 0, v___x_1962_);
v___x_1964_ = v___x_1960_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_a_1968_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1958_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1958_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_io_prim_handle_unlock(v_h_1949_);
if (lean_obj_tag(v___x_1976_) == 0)
{
uint8_t v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref_known(v___x_1976_, 1);
v___x_1977_ = 3;
v___x_1978_ = lean_io_prim_handle_mk(v___x_1948_, v___x_1977_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = lean_io_prim_handle_lock(v_a_1979_, v___x_1954_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1981_; 
lean_dec_ref_known(v___x_1980_, 1);
v___x_1981_ = lean_io_prim_handle_unlock(v_a_1953_);
lean_dec(v_a_1953_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1981_, 0);
lean_dec(v_unused_1989_);
v___x_1983_ = v___x_1981_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v___x_1981_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v_a_1979_);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1979_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1979_);
v_a_1990_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1981_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1981_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_a_1979_);
lean_dec(v_a_1953_);
v_a_1998_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1980_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1980_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_dec(v_a_1953_);
return v___x_1978_;
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_a_1953_);
v_a_2006_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1976_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1976_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_a_1953_);
v_a_2014_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1955_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1955_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2022_, lean_object* v___x_2023_, lean_object* v_h_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lake_importConfigFile___lam__0(v___x_2022_, v___x_2023_, v_h_2024_);
lean_dec(v_h_2024_);
lean_dec_ref(v___x_2023_);
lean_dec_ref(v___x_2022_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___y_2039_; lean_object* v_a_2040_; lean_object* v_lakeEnv_2042_; lean_object* v_wsDir_2043_; lean_object* v_pkgIdx_2044_; lean_object* v_pkgName_2045_; lean_object* v_pkgDir_2046_; lean_object* v_configFile_2047_; lean_object* v_lakeOpts_2048_; lean_object* v_leanOpts_2049_; uint8_t v_reconfigure_2050_; lean_object* v___x_2051_; 
v_lakeEnv_2042_ = lean_ctor_get(v_cfg_2035_, 0);
lean_inc_ref(v_lakeEnv_2042_);
v_wsDir_2043_ = lean_ctor_get(v_cfg_2035_, 2);
lean_inc_ref(v_wsDir_2043_);
v_pkgIdx_2044_ = lean_ctor_get(v_cfg_2035_, 3);
lean_inc(v_pkgIdx_2044_);
v_pkgName_2045_ = lean_ctor_get(v_cfg_2035_, 4);
lean_inc(v_pkgName_2045_);
v_pkgDir_2046_ = lean_ctor_get(v_cfg_2035_, 6);
lean_inc_ref(v_pkgDir_2046_);
v_configFile_2047_ = lean_ctor_get(v_cfg_2035_, 8);
lean_inc_ref_n(v_configFile_2047_, 2);
v_lakeOpts_2048_ = lean_ctor_get(v_cfg_2035_, 12);
lean_inc(v_lakeOpts_2048_);
v_leanOpts_2049_ = lean_ctor_get(v_cfg_2035_, 13);
lean_inc_ref(v_leanOpts_2049_);
v_reconfigure_2050_ = lean_ctor_get_uint8(v_cfg_2035_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2035_);
v___x_2051_ = l_System_FilePath_fileName(v_configFile_2047_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_wsDir_2043_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2052_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2053_ = lean_array_get_size(v_a_2036_);
v___x_2054_ = lean_array_push(v_a_2036_, v___x_2052_);
v___x_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
return v___x_2055_;
}
else
{
lean_object* v_val_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v_configDir_2062_; lean_object* v___x_2063_; 
v_val_2056_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2057_ = l_Lake_defaultLakeDir;
v___x_2058_ = l_Lake_joinRelative(v_wsDir_2043_, v___x_2057_);
v___x_2059_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2060_ = l_Lake_joinRelative(v___x_2058_, v___x_2059_);
lean_inc(v_pkgIdx_2044_);
v___x_2061_ = l_Nat_reprFast(v_pkgIdx_2044_);
v_configDir_2062_ = l_Lake_joinRelative(v___x_2060_, v___x_2061_);
lean_inc_ref(v_configDir_2062_);
v___x_2063_ = l_IO_FS_createDirAll(v_configDir_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref_known(v___x_2063_, 1);
v___x_2064_ = l_Lake_computeTextFileHash(v_configFile_2047_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_h_2073_; lean_object* v_lakeOpts_2074_; lean_object* v___y_2075_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2245_; uint8_t v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; uint8_t v___y_2249_; uint8_t v___y_2269_; lean_object* v___y_2270_; uint8_t v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2276_; uint8_t v___y_2277_; uint8_t v___y_2278_; uint8_t v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; uint8_t v___y_2282_; uint8_t v___y_2284_; uint8_t v___y_2285_; lean_object* v___y_2286_; uint8_t v___y_2287_; uint8_t v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; uint8_t v___y_2291_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v_h_2305_; lean_object* v___y_2306_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2056_, 2);
v___x_2067_ = l_System_FilePath_withExtension(v_val_2056_, v___x_2066_);
lean_inc_ref_n(v_configDir_2062_, 2);
v___x_2068_ = l_Lake_joinRelative(v_configDir_2062_, v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2070_ = l_System_FilePath_withExtension(v_val_2056_, v___x_2069_);
v___x_2071_ = l_Lake_joinRelative(v_configDir_2062_, v___x_2070_);
v___x_2227_ = l_System_FilePath_pathExists(v___x_2071_);
v___x_2228_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2229_ = l_System_FilePath_withExtension(v_val_2056_, v___x_2228_);
v___x_2230_ = l_Lake_joinRelative(v_configDir_2062_, v___x_2229_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_inc_ref(v_pkgDir_2046_);
v___x_2377_ = l_Lake_joinRelative(v_pkgDir_2046_, v___x_2057_);
v___x_2378_ = l_IO_FS_createDirAll(v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
uint8_t v___x_2379_; lean_object* v___x_2380_; 
lean_dec_ref_known(v___x_2378_, 1);
v___x_2379_ = 2;
v___x_2380_ = lean_io_prim_handle_mk(v___x_2071_, v___x_2379_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref(v___x_2230_);
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = 1;
v___x_2383_ = lean_io_prim_handle_lock(v_a_2381_, v___x_2382_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_dec_ref_known(v___x_2383_, 1);
v_h_2073_ = v_a_2381_;
v_lakeOpts_2074_ = v_lakeOpts_2048_;
v___y_2075_ = v_a_2036_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec(v_a_2381_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = lean_io_error_to_string(v_a_2384_);
v___x_2386_ = 3;
v___x_2387_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*1, v___x_2386_);
v___x_2388_ = lean_array_get_size(v_a_2036_);
v___x_2389_ = lean_array_push(v_a_2036_, v___x_2387_);
v___x_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
return v___x_2390_;
}
}
else
{
lean_object* v_a_2391_; 
v_a_2391_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2380_, 1);
if (lean_obj_tag(v_a_2391_) == 0)
{
uint8_t v___x_2392_; lean_object* v___x_2393_; 
lean_dec_ref_known(v_a_2391_, 2);
v___x_2392_ = 0;
v___x_2393_ = lean_io_prim_handle_mk(v___x_2071_, v___x_2392_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v_h_2305_ = v_a_2394_;
v___y_2306_ = v_a_2036_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2395_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2396_ = lean_io_error_to_string(v_a_2395_);
v___x_2397_ = 3;
v___x_2398_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*1, v___x_2397_);
v___x_2399_ = lean_array_get_size(v_a_2036_);
v___x_2400_ = lean_array_push(v_a_2036_, v___x_2398_);
v___x_2401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
return v___x_2401_;
}
}
else
{
lean_object* v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2402_ = lean_io_error_to_string(v_a_2391_);
v___x_2403_ = 3;
v___x_2404_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*1, v___x_2403_);
v___x_2405_ = lean_array_get_size(v_a_2036_);
v___x_2406_ = lean_array_push(v_a_2036_, v___x_2404_);
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
return v___x_2407_;
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2408_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2409_ = lean_io_error_to_string(v_a_2408_);
v___x_2410_ = 3;
v___x_2411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*1, v___x_2410_);
v___x_2412_ = lean_array_get_size(v_a_2036_);
v___x_2413_ = lean_array_push(v_a_2036_, v___x_2411_);
v___x_2414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
return v___x_2414_;
}
}
else
{
uint8_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = 0;
v___x_2416_ = lean_io_prim_handle_mk(v___x_2071_, v___x_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v_h_2305_ = v_a_2417_;
v___y_2306_ = v_a_2036_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2418_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2419_ = lean_io_error_to_string(v_a_2418_);
v___x_2420_ = 3;
v___x_2421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*1, v___x_2420_);
v___x_2422_ = lean_array_get_size(v_a_2036_);
v___x_2423_ = lean_array_push(v_a_2036_, v___x_2421_);
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
return v___x_2424_;
}
}
v___jp_2072_:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_io_remove_file(v___x_2068_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint64_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref_known(v___x_2076_, 1);
lean_dec_ref(v___x_2071_);
v___x_2077_ = l_System_Platform_target;
v___x_2078_ = l_Lake_Env_leanGithash(v_lakeEnv_2042_);
lean_dec_ref(v_lakeEnv_2042_);
lean_inc(v_lakeOpts_2074_);
lean_inc(v_pkgName_2045_);
lean_inc(v_pkgIdx_2044_);
v___x_2079_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2079_, 0, v_pkgIdx_2044_);
lean_ctor_set(v___x_2079_, 1, v_pkgName_2045_);
lean_ctor_set(v___x_2079_, 2, v___x_2077_);
lean_ctor_set(v___x_2079_, 3, v___x_2078_);
lean_ctor_set(v___x_2079_, 4, v_lakeOpts_2074_);
v___x_2080_ = lean_unbox_uint64(v_a_2065_);
lean_dec(v_a_2065_);
lean_ctor_set_uint64(v___x_2079_, sizeof(void*)*5, v___x_2080_);
v___x_2081_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2079_);
v___x_2082_ = lean_unsigned_to_nat(80u);
v___x_2083_ = l_Lean_Json_pretty(v___x_2081_, v___x_2082_);
v___x_2084_ = l_IO_FS_Handle_putStrLn(v_h_2073_, v___x_2083_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref_known(v___x_2084_, 1);
v___x_2085_ = lean_io_prim_handle_flush(v_h_2073_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2086_; 
lean_dec_ref_known(v___x_2085_, 1);
v___x_2086_ = lean_io_prim_handle_truncate(v_h_2073_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2086_, 1);
v___x_2087_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2044_, v_pkgName_2045_, v_pkgDir_2046_, v_lakeOpts_2074_, v_leanOpts_2049_, v_configFile_2047_, v___y_2075_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v_a_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
v_a_2089_ = lean_ctor_get(v___x_2087_, 1);
lean_inc(v_a_2089_);
v___x_2090_ = 1;
v___x_2091_ = l_Lean_writeModule(v_a_2088_, v___x_2068_, v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref_known(v___x_2091_, 1);
v___x_2092_ = lean_io_prim_handle_unlock(v_h_2073_);
lean_dec(v_h_2073_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_dec_ref_known(v___x_2092_, 1);
lean_dec(v_a_2089_);
return v___x_2087_;
}
else
{
lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2105_; 
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; lean_object* v_unused_2107_; 
v_unused_2106_ = lean_ctor_get(v___x_2087_, 1);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2107_);
v___x_2094_ = v___x_2087_;
v_isShared_2095_ = v_isSharedCheck_2105_;
goto v_resetjp_2093_;
}
else
{
lean_dec(v___x_2087_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2105_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_a_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_a_2096_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2097_ = lean_io_error_to_string(v_a_2096_);
v___x_2098_ = 3;
v___x_2099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*1, v___x_2098_);
v___x_2100_ = lean_array_get_size(v_a_2089_);
v___x_2101_ = lean_array_push(v_a_2089_, v___x_2099_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 1);
lean_ctor_set(v___x_2094_, 1, v___x_2101_);
lean_ctor_set(v___x_2094_, 0, v___x_2100_);
v___x_2103_ = v___x_2094_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
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
lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_h_2073_);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; lean_object* v_unused_2122_; 
v_unused_2121_ = lean_ctor_get(v___x_2087_, 1);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2122_);
v___x_2109_ = v___x_2087_;
v_isShared_2110_ = v_isSharedCheck_2120_;
goto v_resetjp_2108_;
}
else
{
lean_dec(v___x_2087_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2120_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_a_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2112_ = lean_io_error_to_string(v_a_2111_);
v___x_2113_ = 3;
v___x_2114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*1, v___x_2113_);
v___x_2115_ = lean_array_get_size(v_a_2089_);
v___x_2116_ = lean_array_push(v_a_2089_, v___x_2114_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 1);
lean_ctor_set(v___x_2109_, 1, v___x_2116_);
lean_ctor_set(v___x_2109_, 0, v___x_2115_);
v___x_2118_ = v___x_2109_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
return v___x_2087_;
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec(v_lakeOpts_2074_);
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2123_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2124_ = lean_io_error_to_string(v_a_2123_);
v___x_2125_ = 3;
v___x_2126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*1, v___x_2125_);
v___x_2127_ = lean_array_get_size(v___y_2075_);
v___x_2128_ = lean_array_push(v___y_2075_, v___x_2126_);
v___x_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
return v___x_2129_;
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v_lakeOpts_2074_);
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2130_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2131_ = lean_io_error_to_string(v_a_2130_);
v___x_2132_ = 3;
v___x_2133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set_uint8(v___x_2133_, sizeof(void*)*1, v___x_2132_);
v___x_2134_ = lean_array_get_size(v___y_2075_);
v___x_2135_ = lean_array_push(v___y_2075_, v___x_2133_);
v___x_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
return v___x_2136_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_lakeOpts_2074_);
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2137_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2138_ = lean_io_error_to_string(v_a_2137_);
v___x_2139_ = 3;
v___x_2140_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*1, v___x_2139_);
v___x_2141_ = lean_array_get_size(v___y_2075_);
v___x_2142_ = lean_array_push(v___y_2075_, v___x_2140_);
v___x_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
return v___x_2143_;
}
}
else
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2076_, 1);
if (lean_obj_tag(v_a_2144_) == 11)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint64_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref_known(v_a_2144_, 2);
lean_dec_ref(v___x_2071_);
v___x_2145_ = l_System_Platform_target;
v___x_2146_ = l_Lake_Env_leanGithash(v_lakeEnv_2042_);
lean_dec_ref(v_lakeEnv_2042_);
lean_inc(v_lakeOpts_2074_);
lean_inc(v_pkgName_2045_);
lean_inc(v_pkgIdx_2044_);
v___x_2147_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2147_, 0, v_pkgIdx_2044_);
lean_ctor_set(v___x_2147_, 1, v_pkgName_2045_);
lean_ctor_set(v___x_2147_, 2, v___x_2145_);
lean_ctor_set(v___x_2147_, 3, v___x_2146_);
lean_ctor_set(v___x_2147_, 4, v_lakeOpts_2074_);
v___x_2148_ = lean_unbox_uint64(v_a_2065_);
lean_dec(v_a_2065_);
lean_ctor_set_uint64(v___x_2147_, sizeof(void*)*5, v___x_2148_);
v___x_2149_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2147_);
v___x_2150_ = lean_unsigned_to_nat(80u);
v___x_2151_ = l_Lean_Json_pretty(v___x_2149_, v___x_2150_);
v___x_2152_ = l_IO_FS_Handle_putStrLn(v_h_2073_, v___x_2151_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2153_; 
lean_dec_ref_known(v___x_2152_, 1);
v___x_2153_ = lean_io_prim_handle_flush(v_h_2073_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; 
lean_dec_ref_known(v___x_2153_, 1);
v___x_2154_ = lean_io_prim_handle_truncate(v_h_2073_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2155_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2044_, v_pkgName_2045_, v_pkgDir_2046_, v_lakeOpts_2074_, v_leanOpts_2049_, v_configFile_2047_, v___y_2075_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v_a_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
v_a_2157_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_a_2157_);
v___x_2158_ = 1;
v___x_2159_ = l_Lean_writeModule(v_a_2156_, v___x_2068_, v___x_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref_known(v___x_2159_, 1);
v___x_2160_ = lean_io_prim_handle_unlock(v_h_2073_);
lean_dec(v_h_2073_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_dec_ref_known(v___x_2160_, 1);
lean_dec(v_a_2157_);
return v___x_2155_;
}
else
{
lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2173_; 
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; 
v_unused_2174_ = lean_ctor_get(v___x_2155_, 1);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v___x_2155_, 0);
lean_dec(v_unused_2175_);
v___x_2162_ = v___x_2155_;
v_isShared_2163_ = v_isSharedCheck_2173_;
goto v_resetjp_2161_;
}
else
{
lean_dec(v___x_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2173_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_a_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2165_ = lean_io_error_to_string(v_a_2164_);
v___x_2166_ = 3;
v___x_2167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1, v___x_2166_);
v___x_2168_ = lean_array_get_size(v_a_2157_);
v___x_2169_ = lean_array_push(v_a_2157_, v___x_2167_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set_tag(v___x_2162_, 1);
lean_ctor_set(v___x_2162_, 1, v___x_2169_);
lean_ctor_set(v___x_2162_, 0, v___x_2168_);
v___x_2171_ = v___x_2162_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_h_2073_);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2189_ = lean_ctor_get(v___x_2155_, 1);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v___x_2155_, 0);
lean_dec(v_unused_2190_);
v___x_2177_ = v___x_2155_;
v_isShared_2178_ = v_isSharedCheck_2188_;
goto v_resetjp_2176_;
}
else
{
lean_dec(v___x_2155_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2188_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_a_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v_a_2179_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2180_ = lean_io_error_to_string(v_a_2179_);
v___x_2181_ = 3;
v___x_2182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2182_, 0, v___x_2180_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*1, v___x_2181_);
v___x_2183_ = lean_array_get_size(v_a_2157_);
v___x_2184_ = lean_array_push(v_a_2157_, v___x_2182_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
lean_ctor_set(v___x_2177_, 1, v___x_2184_);
lean_ctor_set(v___x_2177_, 0, v___x_2183_);
v___x_2186_ = v___x_2177_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
return v___x_2155_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_lakeOpts_2074_);
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2191_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2192_ = lean_io_error_to_string(v_a_2191_);
v___x_2193_ = 3;
v___x_2194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*1, v___x_2193_);
v___x_2195_ = lean_array_get_size(v___y_2075_);
v___x_2196_ = lean_array_push(v___y_2075_, v___x_2194_);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
return v___x_2197_;
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_lakeOpts_2074_);
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2198_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2199_ = lean_io_error_to_string(v_a_2198_);
v___x_2200_ = 3;
v___x_2201_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set_uint8(v___x_2201_, sizeof(void*)*1, v___x_2200_);
v___x_2202_ = lean_array_get_size(v___y_2075_);
v___x_2203_ = lean_array_push(v___y_2075_, v___x_2201_);
v___x_2204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
return v___x_2204_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_lakeOpts_2074_);
lean_dec(v_h_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2205_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2206_ = lean_io_error_to_string(v_a_2205_);
v___x_2207_ = 3;
v___x_2208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*1, v___x_2207_);
v___x_2209_ = lean_array_get_size(v___y_2075_);
v___x_2210_ = lean_array_push(v___y_2075_, v___x_2208_);
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
return v___x_2211_;
}
}
else
{
lean_object* v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_lakeOpts_2074_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2212_ = lean_io_error_to_string(v_a_2144_);
v___x_2213_ = 3;
v___x_2214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*1, v___x_2213_);
v___x_2215_ = lean_array_get_size(v___y_2075_);
v___x_2216_ = lean_array_push(v___y_2075_, v___x_2214_);
v___x_2217_ = lean_io_prim_handle_unlock(v_h_2073_);
lean_dec(v_h_2073_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2217_, 1);
v___x_2218_ = lean_io_remove_file(v___x_2071_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_dec_ref_known(v___x_2218_, 1);
v___y_2039_ = v___x_2215_;
v_a_2040_ = v___x_2216_;
goto v___jp_2038_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = lean_io_error_to_string(v_a_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*1, v___x_2213_);
v___x_2222_ = lean_array_push(v___x_2216_, v___x_2221_);
v___y_2039_ = v___x_2215_;
v_a_2040_ = v___x_2222_;
goto v___jp_2038_;
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec_ref(v___x_2071_);
v_a_2223_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2224_ = lean_io_error_to_string(v_a_2223_);
v___x_2225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*1, v___x_2213_);
v___x_2226_ = lean_array_push(v___x_2216_, v___x_2225_);
v___y_2039_ = v___x_2215_;
v_a_2040_ = v___x_2226_;
goto v___jp_2038_;
}
}
}
}
v___jp_2231_:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lake_importConfigFile___lam__0(v___x_2230_, v___x_2071_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___x_2230_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v_h_2073_ = v_a_2236_;
v_lakeOpts_2074_ = v___y_2233_;
v___y_2075_ = v___y_2232_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v___y_2233_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2237_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2238_ = lean_io_error_to_string(v_a_2237_);
v___x_2239_ = 3;
v___x_2240_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1, v___x_2239_);
v___x_2241_ = lean_array_get_size(v___y_2232_);
v___x_2242_ = lean_array_push(v___y_2232_, v___x_2240_);
v___x_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
return v___x_2243_;
}
}
v___jp_2244_:
{
if (v___y_2246_ == 0)
{
v___y_2232_ = v___y_2245_;
v___y_2233_ = v___y_2248_;
v___y_2234_ = v___y_2247_;
goto v___jp_2231_;
}
else
{
if (v___y_2249_ == 0)
{
v___y_2232_ = v___y_2245_;
v___y_2233_ = v___y_2248_;
v___y_2234_ = v___y_2247_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2250_; 
lean_dec(v___y_2248_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec(v_a_2065_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2250_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2068_, v_leanOpts_2049_);
lean_dec_ref(v___x_2068_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2252_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
v___x_2252_ = lean_io_prim_handle_unlock(v___y_2247_);
lean_dec(v___y_2247_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref_known(v___x_2252_, 1);
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v_a_2251_);
lean_ctor_set(v___x_2253_, 1, v___y_2245_);
return v___x_2253_;
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v_a_2251_);
v_a_2254_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2255_ = lean_io_error_to_string(v_a_2254_);
v___x_2256_ = 3;
v___x_2257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1, v___x_2256_);
v___x_2258_ = lean_array_get_size(v___y_2245_);
v___x_2259_ = lean_array_push(v___y_2245_, v___x_2257_);
v___x_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
return v___x_2260_;
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v___y_2247_);
v_a_2261_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2250_, 1);
v___x_2262_ = lean_io_error_to_string(v_a_2261_);
v___x_2263_ = 3;
v___x_2264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1, v___x_2263_);
v___x_2265_ = lean_array_get_size(v___y_2245_);
v___x_2266_ = lean_array_push(v___y_2245_, v___x_2264_);
v___x_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
return v___x_2267_;
}
}
}
}
v___jp_2268_:
{
if (v___y_2269_ == 0)
{
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2271_;
v___y_2247_ = v___y_2273_;
v___y_2248_ = v___y_2272_;
v___y_2249_ = v___y_2269_;
goto v___jp_2244_;
}
else
{
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2271_;
v___y_2247_ = v___y_2273_;
v___y_2248_ = v___y_2272_;
v___y_2249_ = v___y_2274_;
goto v___jp_2244_;
}
}
v___jp_2275_:
{
if (v___y_2278_ == 0)
{
v___y_2269_ = v___y_2277_;
v___y_2270_ = v___y_2276_;
v___y_2271_ = v___y_2279_;
v___y_2272_ = v___y_2281_;
v___y_2273_ = v___y_2280_;
v___y_2274_ = v___y_2278_;
goto v___jp_2268_;
}
else
{
v___y_2269_ = v___y_2277_;
v___y_2270_ = v___y_2276_;
v___y_2271_ = v___y_2279_;
v___y_2272_ = v___y_2281_;
v___y_2273_ = v___y_2280_;
v___y_2274_ = v___y_2282_;
goto v___jp_2268_;
}
}
v___jp_2283_:
{
if (v___y_2284_ == 0)
{
v___y_2276_ = v___y_2286_;
v___y_2277_ = v___y_2285_;
v___y_2278_ = v___y_2287_;
v___y_2279_ = v___y_2288_;
v___y_2280_ = v___y_2290_;
v___y_2281_ = v___y_2289_;
v___y_2282_ = v___y_2284_;
goto v___jp_2275_;
}
else
{
v___y_2276_ = v___y_2286_;
v___y_2277_ = v___y_2285_;
v___y_2278_ = v___y_2287_;
v___y_2279_ = v___y_2288_;
v___y_2280_ = v___y_2290_;
v___y_2281_ = v___y_2289_;
v___y_2282_ = v___y_2291_;
goto v___jp_2275_;
}
}
v___jp_2292_:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lake_importConfigFile___lam__0(v___x_2230_, v___x_2071_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___x_2230_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v_h_2073_ = v_a_2296_;
v_lakeOpts_2074_ = v_lakeOpts_2048_;
v___y_2075_ = v___y_2293_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2297_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2298_ = lean_io_error_to_string(v_a_2297_);
v___x_2299_ = 3;
v___x_2300_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*1, v___x_2299_);
v___x_2301_ = lean_array_get_size(v___y_2293_);
v___x_2302_ = lean_array_push(v___y_2293_, v___x_2300_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
return v___x_2303_;
}
}
v___jp_2304_:
{
if (v_reconfigure_2050_ == 0)
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_io_prim_handle_lock(v_h_2305_, v_reconfigure_2050_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2308_; 
lean_dec_ref_known(v___x_2307_, 1);
v___x_2308_ = l_IO_FS_Handle_readToEnd(v_h_2305_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = l_Lean_Json_parse(v_a_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; 
lean_dec_ref_known(v___x_2310_, 1);
v___x_2311_ = l_Lake_importConfigFile___lam__0(v___x_2230_, v___x_2071_, v_h_2305_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2230_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v_h_2073_ = v_a_2312_;
v_lakeOpts_2074_ = v_lakeOpts_2048_;
v___y_2075_ = v___y_2306_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2313_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2314_ = lean_io_error_to_string(v_a_2313_);
v___x_2315_ = 3;
v___x_2316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*1, v___x_2315_);
v___x_2317_ = lean_array_get_size(v___y_2306_);
v___x_2318_ = lean_array_push(v___y_2306_, v___x_2316_);
v___x_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
return v___x_2319_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_n(v_a_2320_, 2);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2321_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v___x_2322_; 
lean_dec_ref_known(v___x_2321_, 1);
v___x_2322_ = l_Lean_Json_getObj_x3f(v_a_2320_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_dec_ref_known(v___x_2322_, 1);
v___y_2293_ = v___y_2306_;
v___y_2294_ = v_h_2305_;
goto v___jp_2292_;
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2325_ = l_Lake_JsonObject_getJson_x3f(v_a_2323_, v___x_2324_);
lean_dec(v_a_2323_);
if (lean_obj_tag(v___x_2325_) == 0)
{
v___y_2293_ = v___y_2306_;
v___y_2294_ = v_h_2305_;
goto v___jp_2292_;
}
else
{
lean_object* v_val_2326_; lean_object* v___x_2327_; 
v_val_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_val_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2326_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_dec_ref_known(v___x_2327_, 1);
v___y_2293_ = v___y_2306_;
v___y_2294_ = v_h_2305_;
goto v___jp_2292_;
}
else
{
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_dec_ref_known(v___x_2327_, 1);
v___y_2293_ = v___y_2306_;
v___y_2294_ = v_h_2305_;
goto v___jp_2292_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
lean_dec(v_lakeOpts_2048_);
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lake_importConfigFile___lam__0(v___x_2230_, v___x_2071_, v_h_2305_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2230_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v_h_2073_ = v_a_2330_;
v_lakeOpts_2074_ = v_a_2328_;
v___y_2075_ = v___y_2306_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2331_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2332_ = lean_io_error_to_string(v_a_2331_);
v___x_2333_ = 3;
v___x_2334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*1, v___x_2333_);
v___x_2335_ = lean_array_get_size(v___y_2306_);
v___x_2336_ = lean_array_push(v___y_2306_, v___x_2334_);
v___x_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
return v___x_2337_;
}
}
}
}
}
}
else
{
lean_object* v_a_2338_; uint8_t v___x_2339_; lean_object* v_idx_2340_; lean_object* v_name_2341_; lean_object* v_platform_2342_; lean_object* v_leanHash_2343_; uint64_t v_configHash_2344_; lean_object* v_options_2345_; uint8_t v___x_2346_; uint8_t v___x_2347_; uint64_t v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
lean_dec(v_a_2320_);
lean_dec(v_lakeOpts_2048_);
v_a_2338_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2339_ = l_System_FilePath_pathExists(v___x_2068_);
v_idx_2340_ = lean_ctor_get(v_a_2338_, 0);
lean_inc(v_idx_2340_);
v_name_2341_ = lean_ctor_get(v_a_2338_, 1);
lean_inc(v_name_2341_);
v_platform_2342_ = lean_ctor_get(v_a_2338_, 2);
lean_inc_ref(v_platform_2342_);
v_leanHash_2343_ = lean_ctor_get(v_a_2338_, 3);
lean_inc_ref(v_leanHash_2343_);
v_configHash_2344_ = lean_ctor_get_uint64(v_a_2338_, sizeof(void*)*5);
v_options_2345_ = lean_ctor_get(v_a_2338_, 4);
lean_inc(v_options_2345_);
lean_dec(v_a_2338_);
v___x_2346_ = lean_nat_dec_eq(v_idx_2340_, v_pkgIdx_2044_);
lean_dec(v_idx_2340_);
v___x_2347_ = lean_name_eq(v_name_2341_, v_pkgName_2045_);
lean_dec(v_name_2341_);
v___x_2348_ = lean_unbox_uint64(v_a_2065_);
v___x_2349_ = lean_uint64_dec_eq(v_configHash_2344_, v___x_2348_);
v___x_2350_ = l_System_Platform_target;
v___x_2351_ = lean_string_dec_eq(v_platform_2342_, v___x_2350_);
lean_dec_ref(v_platform_2342_);
if (v___x_2351_ == 0)
{
lean_dec_ref(v_leanHash_2343_);
v___y_2284_ = v___x_2349_;
v___y_2285_ = v___x_2346_;
v___y_2286_ = v___y_2306_;
v___y_2287_ = v___x_2347_;
v___y_2288_ = v___x_2339_;
v___y_2289_ = v_options_2345_;
v___y_2290_ = v_h_2305_;
v___y_2291_ = v___x_2351_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = l_Lake_Env_leanGithash(v_lakeEnv_2042_);
v___x_2353_ = lean_string_dec_eq(v_leanHash_2343_, v___x_2352_);
lean_dec_ref(v___x_2352_);
lean_dec_ref(v_leanHash_2343_);
v___y_2284_ = v___x_2349_;
v___y_2285_ = v___x_2346_;
v___y_2286_ = v___y_2306_;
v___y_2287_ = v___x_2347_;
v___y_2288_ = v___x_2339_;
v___y_2289_ = v_options_2345_;
v___y_2290_ = v_h_2305_;
v___y_2291_ = v___x_2353_;
goto v___jp_2283_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2354_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2355_ = lean_io_error_to_string(v_a_2354_);
v___x_2356_ = 3;
v___x_2357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*1, v___x_2356_);
v___x_2358_ = lean_array_get_size(v___y_2306_);
v___x_2359_ = lean_array_push(v___y_2306_, v___x_2357_);
v___x_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
return v___x_2360_;
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2230_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2361_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2362_ = lean_io_error_to_string(v_a_2361_);
v___x_2363_ = 3;
v___x_2364_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*1, v___x_2363_);
v___x_2365_ = lean_array_get_size(v___y_2306_);
v___x_2366_ = lean_array_push(v___y_2306_, v___x_2364_);
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
return v___x_2367_;
}
}
else
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lake_importConfigFile___lam__0(v___x_2230_, v___x_2071_, v_h_2305_);
lean_dec(v_h_2305_);
lean_dec_ref(v___x_2230_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v_h_2073_ = v_a_2369_;
v_lakeOpts_2074_ = v_lakeOpts_2048_;
v___y_2075_ = v___y_2306_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec(v_a_2065_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2370_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2371_ = lean_io_error_to_string(v_a_2370_);
v___x_2372_ = 3;
v___x_2373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*1, v___x_2372_);
v___x_2374_ = lean_array_get_size(v___y_2306_);
v___x_2375_ = lean_array_push(v___y_2306_, v___x_2373_);
v___x_2376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
return v___x_2376_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v_configDir_2062_);
lean_dec(v_val_2056_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2425_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2426_ = lean_io_error_to_string(v_a_2425_);
v___x_2427_ = 3;
v___x_2428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*1, v___x_2427_);
v___x_2429_ = lean_array_get_size(v_a_2036_);
v___x_2430_ = lean_array_push(v_a_2036_, v___x_2428_);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
return v___x_2431_;
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec_ref(v_configDir_2062_);
lean_dec(v_val_2056_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2432_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2433_ = lean_io_error_to_string(v_a_2432_);
v___x_2434_ = 3;
v___x_2435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set_uint8(v___x_2435_, sizeof(void*)*1, v___x_2434_);
v___x_2436_ = lean_array_get_size(v_a_2036_);
v___x_2437_ = lean_array_push(v_a_2036_, v___x_2435_);
v___x_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
return v___x_2438_;
}
}
v___jp_2038_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___y_2039_);
lean_ctor_set(v___x_2041_, 1, v_a_2040_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lake_importConfigFile(v_cfg_2439_, v_a_2440_);
return v_res_2442_;
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
