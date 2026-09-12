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
lean_object* l_Lean_instInhabitedPersistentEnvExtension___redArg();
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
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
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
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint32_t v___x_381_; lean_object* v___x_382_; 
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
v___x_380_ = l_Lean_MessageLog_add(v___x_379_, v_a_351_);
v___x_381_ = 0;
v___x_382_ = l_Lean_mkEmptyEnvironment(v___x_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_391_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_a_383_);
lean_ctor_set(v___x_387_, 1, v___x_380_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_387_);
v___x_389_ = v___x_385_;
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
lean_dec_ref(v___x_380_);
v_a_392_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_382_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_382_);
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
v___x_534_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
size_t v_x_12363__boxed_585_; size_t v_x_12364__boxed_586_; lean_object* v_res_587_; 
v_x_12363__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_x_12364__boxed_586_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_res_587_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_579_, v_x_580_, v_x_12363__boxed_585_, v_x_12364__boxed_586_, v___y_583_);
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
lean_object* v___f_654_; lean_object* v___x_655_; 
v___f_654_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_655_ = l_IO_FS_readFile(v_configFile_651_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = 1;
v___x_658_ = lean_string_utf8_byte_size(v_a_656_);
lean_inc_ref(v_configFile_651_);
v___x_659_ = l_Lean_Parser_mkInputContext___redArg(v_a_656_, v_configFile_651_, v___x_657_, v___x_658_);
lean_inc_ref(v___x_659_);
v___x_660_ = l_Lean_Parser_parseHeader(v___x_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_758_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_758_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_758_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_758_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_snd_665_; lean_object* v_fst_666_; lean_object* v_fst_667_; lean_object* v_snd_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_757_; 
v_snd_665_ = lean_ctor_get(v_a_661_, 1);
lean_inc(v_snd_665_);
v_fst_666_ = lean_ctor_get(v_a_661_, 0);
lean_inc(v_fst_666_);
lean_dec(v_a_661_);
v_fst_667_ = lean_ctor_get(v_snd_665_, 0);
v_snd_668_ = lean_ctor_get(v_snd_665_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_snd_665_);
if (v_isSharedCheck_757_ == 0)
{
v___x_670_ = v_snd_665_;
v_isShared_671_ = v_isSharedCheck_757_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_snd_668_);
lean_inc(v_fst_667_);
lean_dec(v_snd_665_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_757_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; 
lean_inc_ref(v___x_659_);
lean_inc_ref(v_leanOpts_650_);
v___x_672_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_666_, v_leanOpts_650_, v___x_659_, v_snd_668_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_747_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_747_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_747_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_747_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_746_; 
v_fst_677_ = lean_ctor_get(v_a_673_, 0);
v_snd_678_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_746_ == 0)
{
v___x_680_ = v_a_673_;
v_isShared_681_ = v_isSharedCheck_746_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_678_);
lean_inc(v_fst_677_);
lean_dec(v_a_673_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_746_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v_asyncMode_683_; lean_object* v___x_684_; lean_object* v_asyncMode_685_; lean_object* v___x_686_; lean_object* v_asyncMode_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_682_ = l_Lake_nameExt;
v_asyncMode_683_ = lean_ctor_get(v___x_682_, 2);
v___x_684_ = l_Lake_dirExt;
v_asyncMode_685_ = lean_ctor_get(v___x_684_, 2);
v___x_686_ = l_Lake_optsExt;
v_asyncMode_687_ = lean_ctor_get(v___x_686_, 2);
v___x_688_ = ((lean_object*)(l_Lake_configModuleName));
v___x_689_ = l_Lean_Environment_setMainModule(v_fst_677_, v___x_688_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_pkgName_647_);
lean_ctor_set(v___x_680_, 0, v_pkgIdx_646_);
v___x_691_ = v___x_680_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_pkgIdx_646_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_pkgName_647_);
v___x_691_ = v_reuseFailAlloc_745_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_EnvExtension_setState___redArg(v___x_682_, v___x_689_, v___x_691_, v_asyncMode_683_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 0, v_pkgDir_648_);
v___x_694_ = v___x_675_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_pkgDir_648_);
v___x_694_ = v_reuseFailAlloc_744_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_EnvExtension_setState___redArg(v___x_684_, v___x_692_, v___x_694_, v_asyncMode_685_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 0, v_lakeOpts_649_);
v___x_697_ = v___x_663_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_lakeOpts_649_);
v___x_697_ = v_reuseFailAlloc_743_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_EnvExtension_setState___redArg(v___x_686_, v___x_695_, v___x_697_, v_asyncMode_687_);
v___x_699_ = l_Lean_Elab_Command_mkState(v___x_698_, v_snd_678_, v_leanOpts_650_);
v___x_700_ = l_Lean_Elab_IO_processCommands(v___x_659_, v_fst_667_, v___x_699_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v_commandState_702_; lean_object* v_env_703_; lean_object* v_messages_704_; lean_object* v___x_705_; 
lean_del_object(v___x_670_);
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v_commandState_702_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_commandState_702_);
lean_dec(v_a_701_);
v_env_703_ = lean_ctor_get(v_commandState_702_, 0);
lean_inc_ref(v_env_703_);
v_messages_704_ = lean_ctor_get(v_commandState_702_, 1);
lean_inc_ref(v_messages_704_);
lean_dec_ref(v_commandState_702_);
v___x_705_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_704_, v___f_654_, v_a_652_);
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
v___x_710_ = l_Lean_MessageLog_hasErrors(v_messages_704_);
lean_dec_ref(v_messages_704_);
if (v___x_710_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_configFile_651_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_env_703_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_env_703_);
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
lean_dec_ref(v_env_703_);
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
lean_dec_ref(v_messages_704_);
lean_dec_ref(v_env_703_);
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
v_a_734_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_700_, 1);
v___x_735_ = lean_io_error_to_string(v_a_734_);
v___x_736_ = 3;
v___x_737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*1, v___x_736_);
v___x_738_ = lean_array_get_size(v_a_652_);
v___x_739_ = lean_array_push(v_a_652_, v___x_737_);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 1);
lean_ctor_set(v___x_670_, 1, v___x_739_);
lean_ctor_set(v___x_670_, 0, v___x_738_);
v___x_741_ = v___x_670_;
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
lean_dec(v_fst_667_);
lean_del_object(v___x_663_);
lean_dec_ref(v___x_659_);
lean_dec_ref(v_configFile_651_);
lean_dec_ref(v_leanOpts_650_);
lean_dec(v_lakeOpts_649_);
lean_dec_ref(v_pkgDir_648_);
lean_dec(v_pkgName_647_);
lean_dec(v_pkgIdx_646_);
v_a_748_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_672_, 1);
v___x_749_ = lean_io_error_to_string(v_a_748_);
v___x_750_ = 3;
v___x_751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*1, v___x_750_);
v___x_752_ = lean_array_get_size(v_a_652_);
v___x_753_ = lean_array_push(v_a_652_, v___x_751_);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 1);
lean_ctor_set(v___x_670_, 1, v___x_753_);
lean_ctor_set(v___x_670_, 0, v___x_752_);
v___x_755_ = v___x_670_;
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
lean_dec_ref(v___x_659_);
lean_dec_ref(v_configFile_651_);
lean_dec_ref(v_leanOpts_650_);
lean_dec(v_lakeOpts_649_);
lean_dec_ref(v_pkgDir_648_);
lean_dec(v_pkgName_647_);
lean_dec(v_pkgIdx_646_);
v_a_759_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_660_, 1);
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
v_a_766_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_655_, 1);
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
lean_object* v___x_911_; 
v___x_911_ = l_Lean_instInhabitedPersistentEnvExtension___redArg();
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
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2063_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2055_, 2);
v___x_2064_ = l_System_FilePath_withExtension(v_val_2055_, v___x_2063_);
lean_inc_ref_n(v_configDir_2061_, 2);
v___x_2065_ = l_Lake_joinRelative(v_configDir_2061_, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2067_ = l_System_FilePath_withExtension(v_val_2055_, v___x_2066_);
v___x_2068_ = l_Lake_joinRelative(v_configDir_2061_, v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2070_ = l_System_FilePath_withExtension(v_val_2055_, v___x_2069_);
v___x_2071_ = l_Lake_joinRelative(v_configDir_2061_, v___x_2070_);
v___x_2072_ = l_Lake_computeTextFileHash(v_configFile_2046_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v_h_2075_; lean_object* v_lakeOpts_2076_; lean_object* v___y_2077_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2255_; uint8_t v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; uint8_t v___y_2259_; uint8_t v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; uint8_t v___y_2284_; lean_object* v___y_2286_; uint8_t v___y_2287_; uint8_t v___y_2288_; uint8_t v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; uint8_t v___y_2294_; uint8_t v___y_2295_; lean_object* v___y_2296_; uint8_t v___y_2297_; uint8_t v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; uint8_t v___y_2301_; lean_object* v_h_2303_; lean_object* v___y_2304_; uint8_t v___x_2375_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2375_ = l_System_FilePath_pathExists(v___x_2068_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = 1;
lean_inc_ref(v_pkgDir_2045_);
v___x_2377_ = l_Lake_joinRelative(v_pkgDir_2045_, v___x_2056_);
v___x_2378_ = l_IO_FS_createDirAll(v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
uint8_t v___x_2379_; lean_object* v___x_2380_; 
lean_dec_ref_known(v___x_2378_, 1);
v___x_2379_ = 2;
v___x_2380_ = lean_io_prim_handle_mk(v___x_2068_, v___x_2379_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v___x_2071_);
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = lean_io_prim_handle_lock(v_a_2381_, v___x_2376_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_dec_ref_known(v___x_2382_, 1);
v_h_2075_ = v_a_2381_;
v_lakeOpts_2076_ = v_lakeOpts_2047_;
v___y_2077_ = v_a_2035_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v_a_2381_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
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
v_a_2390_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2380_, 1);
if (lean_obj_tag(v_a_2390_) == 0)
{
uint8_t v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v_a_2390_, 2);
v___x_2391_ = 0;
v___x_2392_ = lean_io_prim_handle_mk(v___x_2068_, v___x_2391_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v_h_2303_ = v_a_2393_;
v___y_2304_ = v_a_2035_;
goto v___jp_2302_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
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
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
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
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2407_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2378_, 1);
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
v___x_2415_ = lean_io_prim_handle_mk(v___x_2068_, v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_h_2303_ = v_a_2416_;
v___y_2304_ = v_a_2035_;
goto v___jp_2302_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
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
v___jp_2074_:
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_io_remove_file(v___x_2065_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint64_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec_ref_known(v___x_2078_, 1);
lean_dec_ref(v___x_2068_);
v___x_2079_ = l_System_Platform_target;
v___x_2080_ = l_Lake_Env_leanGithash(v_lakeEnv_2041_);
lean_dec_ref(v_lakeEnv_2041_);
lean_inc(v_lakeOpts_2076_);
lean_inc(v_pkgName_2044_);
lean_inc(v_pkgIdx_2043_);
v___x_2081_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2081_, 0, v_pkgIdx_2043_);
lean_ctor_set(v___x_2081_, 1, v_pkgName_2044_);
lean_ctor_set(v___x_2081_, 2, v___x_2079_);
lean_ctor_set(v___x_2081_, 3, v___x_2080_);
lean_ctor_set(v___x_2081_, 4, v_lakeOpts_2076_);
v___x_2082_ = lean_unbox_uint64(v_a_2073_);
lean_dec(v_a_2073_);
lean_ctor_set_uint64(v___x_2081_, sizeof(void*)*5, v___x_2082_);
v___x_2083_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2081_);
v___x_2084_ = lean_unsigned_to_nat(80u);
v___x_2085_ = l_Lean_Json_pretty(v___x_2083_, v___x_2084_);
v___x_2086_ = l_IO_FS_Handle_putStrLn(v_h_2075_, v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2086_, 1);
v___x_2087_ = lean_io_prim_handle_flush(v_h_2075_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2088_ = lean_io_prim_handle_truncate(v_h_2075_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2089_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2043_, v_pkgName_2044_, v_pkgDir_2045_, v_lakeOpts_2076_, v_leanOpts_2048_, v_configFile_2046_, v___y_2077_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_a_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
v_a_2091_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_a_2091_);
v___x_2092_ = 1;
v___x_2093_ = l_Lean_writeModule(v_a_2090_, v___x_2065_, v___x_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; 
lean_dec_ref_known(v___x_2093_, 1);
v___x_2094_ = lean_io_prim_handle_unlock(v_h_2075_);
lean_dec(v_h_2075_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
lean_dec(v_a_2091_);
return v___x_2089_;
}
else
{
lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2107_; 
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; lean_object* v_unused_2109_; 
v_unused_2108_ = lean_ctor_get(v___x_2089_, 1);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v___x_2089_, 0);
lean_dec(v_unused_2109_);
v___x_2096_ = v___x_2089_;
v_isShared_2097_ = v_isSharedCheck_2107_;
goto v_resetjp_2095_;
}
else
{
lean_dec(v___x_2089_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2107_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_a_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2099_ = lean_io_error_to_string(v_a_2098_);
v___x_2100_ = 3;
v___x_2101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*1, v___x_2100_);
v___x_2102_ = lean_array_get_size(v_a_2091_);
v___x_2103_ = lean_array_push(v_a_2091_, v___x_2101_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 1);
lean_ctor_set(v___x_2096_, 1, v___x_2103_);
lean_ctor_set(v___x_2096_, 0, v___x_2102_);
v___x_2105_ = v___x_2096_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_h_2075_);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; lean_object* v_unused_2124_; 
v_unused_2123_ = lean_ctor_get(v___x_2089_, 1);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v___x_2089_, 0);
lean_dec(v_unused_2124_);
v___x_2111_ = v___x_2089_;
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2089_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_a_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v_a_2113_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2114_ = lean_io_error_to_string(v_a_2113_);
v___x_2115_ = 3;
v___x_2116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*1, v___x_2115_);
v___x_2117_ = lean_array_get_size(v_a_2091_);
v___x_2118_ = lean_array_push(v_a_2091_, v___x_2116_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set_tag(v___x_2111_, 1);
lean_ctor_set(v___x_2111_, 1, v___x_2118_);
lean_ctor_set(v___x_2111_, 0, v___x_2117_);
v___x_2120_ = v___x_2111_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
return v___x_2089_;
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2125_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2126_ = lean_io_error_to_string(v_a_2125_);
v___x_2127_ = 3;
v___x_2128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*1, v___x_2127_);
v___x_2129_ = lean_array_get_size(v___y_2077_);
v___x_2130_ = lean_array_push(v___y_2077_, v___x_2128_);
v___x_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
return v___x_2131_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2132_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2133_ = lean_io_error_to_string(v_a_2132_);
v___x_2134_ = 3;
v___x_2135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*1, v___x_2134_);
v___x_2136_ = lean_array_get_size(v___y_2077_);
v___x_2137_ = lean_array_push(v___y_2077_, v___x_2135_);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
return v___x_2138_;
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2139_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2140_ = lean_io_error_to_string(v_a_2139_);
v___x_2141_ = 3;
v___x_2142_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set_uint8(v___x_2142_, sizeof(void*)*1, v___x_2141_);
v___x_2143_ = lean_array_get_size(v___y_2077_);
v___x_2144_ = lean_array_push(v___y_2077_, v___x_2142_);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
return v___x_2145_;
}
}
else
{
lean_object* v_a_2146_; 
v_a_2146_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2078_, 1);
if (lean_obj_tag(v_a_2146_) == 11)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint64_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref_known(v_a_2146_, 2);
lean_dec_ref(v___x_2068_);
v___x_2147_ = l_System_Platform_target;
v___x_2148_ = l_Lake_Env_leanGithash(v_lakeEnv_2041_);
lean_dec_ref(v_lakeEnv_2041_);
lean_inc(v_lakeOpts_2076_);
lean_inc(v_pkgName_2044_);
lean_inc(v_pkgIdx_2043_);
v___x_2149_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2149_, 0, v_pkgIdx_2043_);
lean_ctor_set(v___x_2149_, 1, v_pkgName_2044_);
lean_ctor_set(v___x_2149_, 2, v___x_2147_);
lean_ctor_set(v___x_2149_, 3, v___x_2148_);
lean_ctor_set(v___x_2149_, 4, v_lakeOpts_2076_);
v___x_2150_ = lean_unbox_uint64(v_a_2073_);
lean_dec(v_a_2073_);
lean_ctor_set_uint64(v___x_2149_, sizeof(void*)*5, v___x_2150_);
v___x_2151_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2149_);
v___x_2152_ = lean_unsigned_to_nat(80u);
v___x_2153_ = l_Lean_Json_pretty(v___x_2151_, v___x_2152_);
v___x_2154_ = l_IO_FS_Handle_putStrLn(v_h_2075_, v___x_2153_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2155_ = lean_io_prim_handle_flush(v_h_2075_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref_known(v___x_2155_, 1);
v___x_2156_ = lean_io_prim_handle_truncate(v_h_2075_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v___x_2157_; 
lean_dec_ref_known(v___x_2156_, 1);
v___x_2157_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2043_, v_pkgName_2044_, v_pkgDir_2045_, v_lakeOpts_2076_, v_leanOpts_2048_, v_configFile_2046_, v___y_2077_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v_a_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
v_a_2159_ = lean_ctor_get(v___x_2157_, 1);
lean_inc(v_a_2159_);
v___x_2160_ = 1;
v___x_2161_ = l_Lean_writeModule(v_a_2158_, v___x_2065_, v___x_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = lean_io_prim_handle_unlock(v_h_2075_);
lean_dec(v_h_2075_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_dec_ref_known(v___x_2162_, 1);
lean_dec(v_a_2159_);
return v___x_2157_;
}
else
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2175_; 
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; lean_object* v_unused_2177_; 
v_unused_2176_ = lean_ctor_get(v___x_2157_, 1);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v___x_2157_, 0);
lean_dec(v_unused_2177_);
v___x_2164_ = v___x_2157_;
v_isShared_2165_ = v_isSharedCheck_2175_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2157_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2175_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_a_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v_a_2166_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2167_ = lean_io_error_to_string(v_a_2166_);
v___x_2168_ = 3;
v___x_2169_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*1, v___x_2168_);
v___x_2170_ = lean_array_get_size(v_a_2159_);
v___x_2171_ = lean_array_push(v_a_2159_, v___x_2169_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set_tag(v___x_2164_, 1);
lean_ctor_set(v___x_2164_, 1, v___x_2171_);
lean_ctor_set(v___x_2164_, 0, v___x_2170_);
v___x_2173_ = v___x_2164_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_h_2075_);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; lean_object* v_unused_2192_; 
v_unused_2191_ = lean_ctor_get(v___x_2157_, 1);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v___x_2157_, 0);
lean_dec(v_unused_2192_);
v___x_2179_ = v___x_2157_;
v_isShared_2180_ = v_isSharedCheck_2190_;
goto v_resetjp_2178_;
}
else
{
lean_dec(v___x_2157_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2190_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_a_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
v_a_2181_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2182_ = lean_io_error_to_string(v_a_2181_);
v___x_2183_ = 3;
v___x_2184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*1, v___x_2183_);
v___x_2185_ = lean_array_get_size(v_a_2159_);
v___x_2186_ = lean_array_push(v_a_2159_, v___x_2184_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set_tag(v___x_2179_, 1);
lean_ctor_set(v___x_2179_, 1, v___x_2186_);
lean_ctor_set(v___x_2179_, 0, v___x_2185_);
v___x_2188_ = v___x_2179_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
return v___x_2157_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2193_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2194_ = lean_io_error_to_string(v_a_2193_);
v___x_2195_ = 3;
v___x_2196_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*1, v___x_2195_);
v___x_2197_ = lean_array_get_size(v___y_2077_);
v___x_2198_ = lean_array_push(v___y_2077_, v___x_2196_);
v___x_2199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
return v___x_2199_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2200_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2201_ = lean_io_error_to_string(v_a_2200_);
v___x_2202_ = 3;
v___x_2203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*1, v___x_2202_);
v___x_2204_ = lean_array_get_size(v___y_2077_);
v___x_2205_ = lean_array_push(v___y_2077_, v___x_2203_);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
return v___x_2206_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_h_2075_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
v_a_2207_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2208_ = lean_io_error_to_string(v_a_2207_);
v___x_2209_ = 3;
v___x_2210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*1, v___x_2209_);
v___x_2211_ = lean_array_get_size(v___y_2077_);
v___x_2212_ = lean_array_push(v___y_2077_, v___x_2210_);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_lakeOpts_2076_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v___x_2214_ = lean_io_error_to_string(v_a_2146_);
v___x_2215_ = 3;
v___x_2216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*1, v___x_2215_);
v___x_2217_ = lean_array_get_size(v___y_2077_);
v___x_2218_ = lean_array_push(v___y_2077_, v___x_2216_);
v___x_2219_ = lean_io_prim_handle_unlock(v_h_2075_);
lean_dec(v_h_2075_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref_known(v___x_2219_, 1);
v___x_2220_ = lean_io_remove_file(v___x_2068_);
lean_dec_ref(v___x_2068_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_dec_ref_known(v___x_2220_, 1);
v___y_2038_ = v___x_2217_;
v_a_2039_ = v___x_2218_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2222_ = lean_io_error_to_string(v_a_2221_);
v___x_2223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*1, v___x_2215_);
v___x_2224_ = lean_array_push(v___x_2218_, v___x_2223_);
v___y_2038_ = v___x_2217_;
v_a_2039_ = v___x_2224_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v___x_2068_);
v_a_2225_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2226_ = lean_io_error_to_string(v_a_2225_);
v___x_2227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___x_2215_);
v___x_2228_ = lean_array_push(v___x_2218_, v___x_2227_);
v___y_2038_ = v___x_2217_;
v_a_2039_ = v___x_2228_;
goto v___jp_2037_;
}
}
}
}
v___jp_2229_:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lake_importConfigFile___lam__0(v___x_2071_, v___x_2068_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_h_2075_ = v_a_2233_;
v_lakeOpts_2076_ = v_lakeOpts_2047_;
v___y_2077_ = v___y_2230_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2234_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2235_ = lean_io_error_to_string(v_a_2234_);
v___x_2236_ = 3;
v___x_2237_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*1, v___x_2236_);
v___x_2238_ = lean_array_get_size(v___y_2230_);
v___x_2239_ = lean_array_push(v___y_2230_, v___x_2237_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
return v___x_2240_;
}
}
v___jp_2241_:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lake_importConfigFile___lam__0(v___x_2071_, v___x_2068_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v_h_2075_ = v_a_2246_;
v_lakeOpts_2076_ = v___y_2243_;
v___y_2077_ = v___y_2242_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v___y_2243_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2247_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2245_, 1);
v___x_2248_ = lean_io_error_to_string(v_a_2247_);
v___x_2249_ = 3;
v___x_2250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*1, v___x_2249_);
v___x_2251_ = lean_array_get_size(v___y_2242_);
v___x_2252_ = lean_array_push(v___y_2242_, v___x_2250_);
v___x_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
return v___x_2253_;
}
}
v___jp_2254_:
{
if (v___y_2256_ == 0)
{
v___y_2242_ = v___y_2255_;
v___y_2243_ = v___y_2258_;
v___y_2244_ = v___y_2257_;
goto v___jp_2241_;
}
else
{
if (v___y_2259_ == 0)
{
v___y_2242_ = v___y_2255_;
v___y_2243_ = v___y_2258_;
v___y_2244_ = v___y_2257_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2260_; 
lean_dec(v___y_2258_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v___x_2260_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2065_, v_leanOpts_2048_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = lean_io_prim_handle_unlock(v___y_2257_);
lean_dec(v___y_2257_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___x_2263_; 
lean_dec_ref_known(v___x_2262_, 1);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_a_2261_);
lean_ctor_set(v___x_2263_, 1, v___y_2255_);
return v___x_2263_;
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_a_2261_);
v_a_2264_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2265_ = lean_io_error_to_string(v_a_2264_);
v___x_2266_ = 3;
v___x_2267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*1, v___x_2266_);
v___x_2268_ = lean_array_get_size(v___y_2255_);
v___x_2269_ = lean_array_push(v___y_2255_, v___x_2267_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
return v___x_2270_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec(v___y_2257_);
v_a_2271_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2272_ = lean_io_error_to_string(v_a_2271_);
v___x_2273_ = 3;
v___x_2274_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*1, v___x_2273_);
v___x_2275_ = lean_array_get_size(v___y_2255_);
v___x_2276_ = lean_array_push(v___y_2255_, v___x_2274_);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
return v___x_2277_;
}
}
}
}
v___jp_2278_:
{
if (v___y_2279_ == 0)
{
v___y_2255_ = v___y_2280_;
v___y_2256_ = v___y_2281_;
v___y_2257_ = v___y_2283_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2279_;
goto v___jp_2254_;
}
else
{
v___y_2255_ = v___y_2280_;
v___y_2256_ = v___y_2281_;
v___y_2257_ = v___y_2283_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2284_;
goto v___jp_2254_;
}
}
v___jp_2285_:
{
if (v___y_2288_ == 0)
{
v___y_2279_ = v___y_2287_;
v___y_2280_ = v___y_2286_;
v___y_2281_ = v___y_2289_;
v___y_2282_ = v___y_2291_;
v___y_2283_ = v___y_2290_;
v___y_2284_ = v___y_2288_;
goto v___jp_2278_;
}
else
{
v___y_2279_ = v___y_2287_;
v___y_2280_ = v___y_2286_;
v___y_2281_ = v___y_2289_;
v___y_2282_ = v___y_2291_;
v___y_2283_ = v___y_2290_;
v___y_2284_ = v___y_2292_;
goto v___jp_2278_;
}
}
v___jp_2293_:
{
if (v___y_2294_ == 0)
{
v___y_2286_ = v___y_2296_;
v___y_2287_ = v___y_2295_;
v___y_2288_ = v___y_2297_;
v___y_2289_ = v___y_2298_;
v___y_2290_ = v___y_2300_;
v___y_2291_ = v___y_2299_;
v___y_2292_ = v___y_2294_;
goto v___jp_2285_;
}
else
{
v___y_2286_ = v___y_2296_;
v___y_2287_ = v___y_2295_;
v___y_2288_ = v___y_2297_;
v___y_2289_ = v___y_2298_;
v___y_2290_ = v___y_2300_;
v___y_2291_ = v___y_2299_;
v___y_2292_ = v___y_2301_;
goto v___jp_2285_;
}
}
v___jp_2302_:
{
if (v_reconfigure_2049_ == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_io_prim_handle_lock(v_h_2303_, v_reconfigure_2049_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2306_; 
lean_dec_ref_known(v___x_2305_, 1);
v___x_2306_ = l_IO_FS_Handle_readToEnd(v_h_2303_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = l_Lean_Json_parse(v_a_2307_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v___x_2309_; 
lean_dec_ref_known(v___x_2308_, 1);
v___x_2309_ = l_Lake_importConfigFile___lam__0(v___x_2071_, v___x_2068_, v_h_2303_);
lean_dec(v_h_2303_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v_h_2075_ = v_a_2310_;
v_lakeOpts_2076_ = v_lakeOpts_2047_;
v___y_2077_ = v___y_2304_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2311_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2312_ = lean_io_error_to_string(v_a_2311_);
v___x_2313_ = 3;
v___x_2314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*1, v___x_2313_);
v___x_2315_ = lean_array_get_size(v___y_2304_);
v___x_2316_ = lean_array_push(v___y_2304_, v___x_2314_);
v___x_2317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
return v___x_2317_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_n(v_a_2318_, 2);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2319_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; 
lean_dec_ref_known(v___x_2319_, 1);
v___x_2320_ = l_Lean_Json_getObj_x3f(v_a_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec_ref_known(v___x_2320_, 1);
v___y_2230_ = v___y_2304_;
v___y_2231_ = v_h_2303_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2323_ = l_Lake_JsonObject_getJson_x3f(v_a_2321_, v___x_2322_);
lean_dec(v_a_2321_);
if (lean_obj_tag(v___x_2323_) == 0)
{
v___y_2230_ = v___y_2304_;
v___y_2231_ = v_h_2303_;
goto v___jp_2229_;
}
else
{
lean_object* v_val_2324_; lean_object* v___x_2325_; 
v_val_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_val_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v___y_2230_ = v___y_2304_;
v___y_2231_ = v_h_2303_;
goto v___jp_2229_;
}
else
{
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v___y_2230_ = v___y_2304_;
v___y_2231_ = v_h_2303_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
lean_dec(v_lakeOpts_2047_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l_Lake_importConfigFile___lam__0(v___x_2071_, v___x_2068_, v_h_2303_);
lean_dec(v_h_2303_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v_h_2075_ = v_a_2328_;
v_lakeOpts_2076_ = v_a_2326_;
v___y_2077_ = v___y_2304_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec(v_a_2326_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2329_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2330_ = lean_io_error_to_string(v_a_2329_);
v___x_2331_ = 3;
v___x_2332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*1, v___x_2331_);
v___x_2333_ = lean_array_get_size(v___y_2304_);
v___x_2334_ = lean_array_push(v___y_2304_, v___x_2332_);
v___x_2335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
return v___x_2335_;
}
}
}
}
}
}
else
{
lean_object* v_a_2336_; uint8_t v___x_2337_; lean_object* v_idx_2338_; lean_object* v_name_2339_; lean_object* v_platform_2340_; lean_object* v_leanHash_2341_; uint64_t v_configHash_2342_; lean_object* v_options_2343_; uint8_t v___x_2344_; uint8_t v___x_2345_; uint64_t v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
lean_dec(v_a_2318_);
lean_dec(v_lakeOpts_2047_);
v_a_2336_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2337_ = l_System_FilePath_pathExists(v___x_2065_);
v_idx_2338_ = lean_ctor_get(v_a_2336_, 0);
lean_inc(v_idx_2338_);
v_name_2339_ = lean_ctor_get(v_a_2336_, 1);
lean_inc(v_name_2339_);
v_platform_2340_ = lean_ctor_get(v_a_2336_, 2);
lean_inc_ref(v_platform_2340_);
v_leanHash_2341_ = lean_ctor_get(v_a_2336_, 3);
lean_inc_ref(v_leanHash_2341_);
v_configHash_2342_ = lean_ctor_get_uint64(v_a_2336_, sizeof(void*)*5);
v_options_2343_ = lean_ctor_get(v_a_2336_, 4);
lean_inc(v_options_2343_);
lean_dec(v_a_2336_);
v___x_2344_ = lean_nat_dec_eq(v_idx_2338_, v_pkgIdx_2043_);
lean_dec(v_idx_2338_);
v___x_2345_ = lean_name_eq(v_name_2339_, v_pkgName_2044_);
lean_dec(v_name_2339_);
v___x_2346_ = lean_unbox_uint64(v_a_2073_);
v___x_2347_ = lean_uint64_dec_eq(v_configHash_2342_, v___x_2346_);
v___x_2348_ = l_System_Platform_target;
v___x_2349_ = lean_string_dec_eq(v_platform_2340_, v___x_2348_);
lean_dec_ref(v_platform_2340_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v_leanHash_2341_);
v___y_2294_ = v___x_2347_;
v___y_2295_ = v___x_2344_;
v___y_2296_ = v___y_2304_;
v___y_2297_ = v___x_2345_;
v___y_2298_ = v___x_2337_;
v___y_2299_ = v_options_2343_;
v___y_2300_ = v_h_2303_;
v___y_2301_ = v___x_2349_;
goto v___jp_2293_;
}
else
{
lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = l_Lake_Env_leanGithash(v_lakeEnv_2041_);
v___x_2351_ = lean_string_dec_eq(v_leanHash_2341_, v___x_2350_);
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_leanHash_2341_);
v___y_2294_ = v___x_2347_;
v___y_2295_ = v___x_2344_;
v___y_2296_ = v___y_2304_;
v___y_2297_ = v___x_2345_;
v___y_2298_ = v___x_2337_;
v___y_2299_ = v_options_2343_;
v___y_2300_ = v_h_2303_;
v___y_2301_ = v___x_2351_;
goto v___jp_2293_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_h_2303_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2352_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2353_ = lean_io_error_to_string(v_a_2352_);
v___x_2354_ = 3;
v___x_2355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set_uint8(v___x_2355_, sizeof(void*)*1, v___x_2354_);
v___x_2356_ = lean_array_get_size(v___y_2304_);
v___x_2357_ = lean_array_push(v___y_2304_, v___x_2355_);
v___x_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
return v___x_2358_;
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec(v_h_2303_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2359_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2360_ = lean_io_error_to_string(v_a_2359_);
v___x_2361_ = 3;
v___x_2362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2361_);
v___x_2363_ = lean_array_get_size(v___y_2304_);
v___x_2364_ = lean_array_push(v___y_2304_, v___x_2362_);
v___x_2365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
return v___x_2365_;
}
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lake_importConfigFile___lam__0(v___x_2071_, v___x_2068_, v_h_2303_);
lean_dec(v_h_2303_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v_h_2075_ = v_a_2367_;
v_lakeOpts_2076_ = v_lakeOpts_2047_;
v___y_2077_ = v___y_2304_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2368_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2369_ = lean_io_error_to_string(v_a_2368_);
v___x_2370_ = 3;
v___x_2371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*1, v___x_2370_);
v___x_2372_ = lean_array_get_size(v___y_2304_);
v___x_2373_ = lean_array_push(v___y_2304_, v___x_2371_);
v___x_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec_ref(v___x_2071_);
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_leanOpts_2048_);
lean_dec(v_lakeOpts_2047_);
lean_dec_ref(v_configFile_2046_);
lean_dec_ref(v_pkgDir_2045_);
lean_dec(v_pkgName_2044_);
lean_dec(v_pkgIdx_2043_);
lean_dec_ref(v_lakeEnv_2041_);
v_a_2424_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2072_, 1);
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
