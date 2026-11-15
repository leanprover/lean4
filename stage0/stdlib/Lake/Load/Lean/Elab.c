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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cacheServiceAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__10_value),LEAN_SCALAR_PTR_LITERAL(13, 178, 58, 239, 111, 131, 38, 45)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__13_value),LEAN_SCALAR_PTR_LITERAL(26, 29, 82, 124, 109, 105, 242, 204)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "defaultScriptAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__16_value),LEAN_SCALAR_PTR_LITERAL(102, 220, 227, 87, 142, 243, 134, 10)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanLibAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__19_value),LEAN_SCALAR_PTR_LITERAL(32, 216, 106, 32, 231, 39, 130, 108)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanExeAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__22_value),LEAN_SCALAR_PTR_LITERAL(188, 182, 7, 15, 47, 104, 138, 158)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "externLibAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__25_value),LEAN_SCALAR_PTR_LITERAL(101, 0, 33, 72, 82, 211, 54, 104)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "targetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__28_value),LEAN_SCALAR_PTR_LITERAL(230, 170, 78, 40, 161, 217, 169, 127)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "defaultTargetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__31_value),LEAN_SCALAR_PTR_LITERAL(136, 50, 195, 92, 10, 179, 138, 115)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "testDriverAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__34_value),LEAN_SCALAR_PTR_LITERAL(145, 171, 145, 31, 167, 29, 89, 20)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lintDriverAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__37_value),LEAN_SCALAR_PTR_LITERAL(162, 200, 112, 121, 111, 252, 78, 167)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "moduleFacetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__40_value),LEAN_SCALAR_PTR_LITERAL(184, 177, 55, 179, 152, 236, 7, 155)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageFacetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__43_value),LEAN_SCALAR_PTR_LITERAL(30, 214, 121, 146, 170, 223, 202, 251)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libraryFacetAttr"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__46_value),LEAN_SCALAR_PTR_LITERAL(68, 159, 200, 109, 254, 124, 216, 54)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__50_value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value;
static const lean_string_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54_value;
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55_value_aux_0),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_value),LEAN_SCALAR_PTR_LITERAL(225, 220, 115, 150, 240, 139, 111, 12)}};
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55_value_aux_1),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__54_value),LEAN_SCALAR_PTR_LITERAL(176, 236, 150, 45, 29, 146, 124, 106)}};
static const lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55 = (const lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55_value;
static lean_once_cell_t l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__56;
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
static const lean_ctor_object l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__4_value),((lean_object*)&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_value),LEAN_SCALAR_PTR_LITERAL(253, 154, 30, 39, 33, 163, 227, 110)}};
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
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__0_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_, &l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2__once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_initFn___closed__1_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_);
v___x_9_ = lean_st_mk_ref(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2____boxed(lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_();
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1(lean_object* v___x_427_, lean_object* v_x_428_){
_start:
{
lean_inc(v___x_427_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1___boxed(lean_object* v___x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1(v___x_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec(v___x_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2(lean_object* v___x_432_, lean_object* v_x_433_){
_start:
{
lean_inc(v___x_432_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2___boxed(lean_object* v___x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2(v___x_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec(v___x_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3(lean_object* v___x_437_, lean_object* v_x_438_){
_start:
{
lean_inc_ref(v___x_437_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3___boxed(lean_object* v___x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3(v___x_439_, v_x_440_);
lean_dec_ref(v_x_440_);
lean_dec_ref(v___x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(lean_object* v_f_442_, lean_object* v_as_443_, size_t v_i_444_, size_t v_stop_445_, lean_object* v_b_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_eq(v_i_444_, v_stop_445_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_array_uget_borrowed(v_as_443_, v_i_444_);
lean_inc_ref(v_f_442_);
lean_inc(v___x_450_);
v___x_451_ = lean_apply_3(v_f_442_, v___x_450_, v___y_447_, lean_box(0));
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v_a_453_; size_t v___x_454_; size_t v___x_455_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
v_a_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_451_, 2);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_444_, v___x_454_);
v_i_444_ = v___x_455_;
v_b_446_ = v_a_452_;
v___y_447_ = v_a_453_;
goto _start;
}
else
{
lean_dec_ref(v_f_442_);
return v___x_451_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec_ref(v_f_442_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_b_446_);
lean_ctor_set(v___x_457_, 1, v___y_447_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2___boxed(lean_object* v_f_458_, lean_object* v_as_459_, lean_object* v_i_460_, lean_object* v_stop_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
size_t v_i_boxed_465_; size_t v_stop_boxed_466_; lean_object* v_res_467_; 
v_i_boxed_465_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_stop_boxed_466_ = lean_unbox_usize(v_stop_461_);
lean_dec(v_stop_461_);
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_458_, v_as_459_, v_i_boxed_465_, v_stop_boxed_466_, v_b_462_, v___y_463_);
lean_dec_ref(v_as_459_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_f_468_, lean_object* v_x_469_, lean_object* v___y_470_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v_cs_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_cs_472_ = lean_ctor_get(v_x_469_, 0);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_array_get_size(v_cs_472_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_nat_dec_lt(v___x_473_, v___x_474_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec_ref(v_f_468_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___y_470_);
return v___x_477_;
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_474_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_468_, v_cs_472_, v___x_478_, v___x_479_, v___x_475_, v___y_470_);
return v___x_480_;
}
}
else
{
lean_object* v_vs_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_vs_481_ = lean_ctor_get(v_x_469_, 0);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_array_get_size(v_vs_481_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_f_468_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___y_470_);
return v___x_486_;
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_483_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_468_, v_vs_481_, v___x_487_, v___x_488_, v___x_484_, v___y_470_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_f_490_, lean_object* v_as_491_, size_t v_i_492_, size_t v_stop_493_, lean_object* v_b_494_, lean_object* v___y_495_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_eq(v_i_492_, v_stop_493_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_array_uget_borrowed(v_as_491_, v_i_492_);
lean_inc_ref(v_f_490_);
v___x_499_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_490_, v___x_498_, v___y_495_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v_a_501_; size_t v___x_502_; size_t v___x_503_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
v_a_501_ = lean_ctor_get(v___x_499_, 1);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_499_, 2);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_492_, v___x_502_);
v_i_492_ = v___x_503_;
v_b_494_ = v_a_500_;
v___y_495_ = v_a_501_;
goto _start;
}
else
{
lean_dec_ref(v_f_490_);
return v___x_499_;
}
}
else
{
lean_object* v___x_505_; 
lean_dec_ref(v_f_490_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_b_494_);
lean_ctor_set(v___x_505_, 1, v___y_495_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_f_506_, lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_stop_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
size_t v_i_boxed_513_; size_t v_stop_boxed_514_; lean_object* v_res_515_; 
v_i_boxed_513_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_stop_boxed_514_ = lean_unbox_usize(v_stop_509_);
lean_dec(v_stop_509_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_506_, v_as_507_, v_i_boxed_513_, v_stop_boxed_514_, v_b_510_, v___y_511_);
lean_dec_ref(v_as_507_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_f_516_, lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_516_, v_x_517_, v___y_518_);
lean_dec_ref(v_x_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(lean_object* v_f_521_, lean_object* v_t_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_root_525_; lean_object* v_tail_526_; lean_object* v___x_527_; 
v_root_525_ = lean_ctor_get(v_t_522_, 0);
v_tail_526_ = lean_ctor_get(v_t_522_, 1);
lean_inc_ref(v_f_521_);
v___x_527_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__2(v_f_521_, v_root_525_, v___y_523_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_542_; 
v_a_528_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v___x_527_, 0);
lean_dec(v_unused_543_);
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_542_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_542_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_array_get_size(v_tail_526_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_nat_dec_lt(v___x_532_, v___x_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_537_; 
lean_dec_ref(v_f_521_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_534_);
v___x_537_ = v___x_530_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_528_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
lean_del_object(v___x_530_);
v___x_539_ = ((size_t)0ULL);
v___x_540_ = lean_usize_of_nat(v___x_533_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_521_, v_tail_526_, v___x_539_, v___x_540_, v___x_534_, v_a_528_);
return v___x_541_;
}
}
}
else
{
lean_dec_ref(v_f_521_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3___boxed(lean_object* v_f_544_, lean_object* v_t_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_544_, v_t_545_, v___y_546_);
lean_dec_ref(v_t_545_);
return v_res_548_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(lean_object* v_f_550_, lean_object* v_x_551_, size_t v_x_552_, size_t v_x_553_, lean_object* v___y_554_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_cs_556_; lean_object* v___x_557_; size_t v___x_558_; lean_object* v_j_559_; lean_object* v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v_cs_556_ = lean_ctor_get(v_x_551_, 0);
v___x_557_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___closed__0);
v___x_558_ = lean_usize_shift_right(v_x_552_, v_x_553_);
v_j_559_ = lean_usize_to_nat(v___x_558_);
v___x_560_ = lean_array_get_borrowed(v___x_557_, v_cs_556_, v_j_559_);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_shift_left(v___x_561_, v_x_553_);
v___x_563_ = lean_usize_sub(v___x_562_, v___x_561_);
v___x_564_ = lean_usize_land(v_x_552_, v___x_563_);
v___x_565_ = ((size_t)5ULL);
v___x_566_ = lean_usize_sub(v_x_553_, v___x_565_);
lean_inc_ref(v_f_550_);
v___x_567_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_550_, v___x_560_, v___x_564_, v___x_566_, v___y_554_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_583_; 
v_a_568_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v___x_567_, 0);
lean_dec(v_unused_584_);
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_j_559_, v___x_572_);
lean_dec(v_j_559_);
v___x_574_ = lean_array_get_size(v_cs_556_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_nat_dec_lt(v___x_573_, v___x_574_);
if (v___x_576_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___x_573_);
lean_dec_ref(v_f_550_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_575_);
v___x_578_ = v___x_570_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_a_568_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
lean_del_object(v___x_570_);
v___x_580_ = lean_usize_of_nat(v___x_573_);
lean_dec(v___x_573_);
v___x_581_ = lean_usize_of_nat(v___x_574_);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1_spec__3(v_f_550_, v_cs_556_, v___x_580_, v___x_581_, v___x_575_, v_a_568_);
return v___x_582_;
}
}
}
else
{
lean_dec(v_j_559_);
lean_dec_ref(v_f_550_);
return v___x_567_;
}
}
else
{
lean_object* v_vs_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_vs_585_ = lean_ctor_get(v_x_551_, 0);
v___x_586_ = lean_usize_to_nat(v_x_552_);
v___x_587_ = lean_array_get_size(v_vs_585_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v___x_586_);
lean_dec_ref(v_f_550_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___y_554_);
return v___x_590_;
}
else
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_usize_of_nat(v___x_586_);
lean_dec(v___x_586_);
v___x_592_ = lean_usize_of_nat(v___x_587_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_550_, v_vs_585_, v___x_591_, v___x_592_, v___x_588_, v___y_554_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1___boxed(lean_object* v_f_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
size_t v_x_13138__boxed_600_; size_t v_x_13139__boxed_601_; lean_object* v_res_602_; 
v_x_13138__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_x_13139__boxed_601_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_602_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_594_, v_x_595_, v_x_13138__boxed_600_, v_x_13139__boxed_601_, v___y_598_);
lean_dec_ref(v_x_595_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(lean_object* v_f_603_, lean_object* v_t_604_, lean_object* v_start_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_nat_dec_eq(v_start_605_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v_root_610_; lean_object* v_tail_611_; size_t v_shift_612_; lean_object* v_tailOff_613_; uint8_t v___x_614_; 
v_root_610_ = lean_ctor_get(v_t_604_, 0);
v_tail_611_ = lean_ctor_get(v_t_604_, 1);
v_shift_612_ = lean_ctor_get_usize(v_t_604_, 4);
v_tailOff_613_ = lean_ctor_get(v_t_604_, 3);
v___x_614_ = lean_nat_dec_le(v_tailOff_613_, v_start_605_);
if (v___x_614_ == 0)
{
size_t v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_usize_of_nat(v_start_605_);
lean_inc_ref(v_f_603_);
v___x_616_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__1(v_f_603_, v_root_610_, v___x_615_, v_shift_612_, v___y_606_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_630_; 
v_a_617_ = lean_ctor_get(v___x_616_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_616_, 0);
lean_dec(v_unused_631_);
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_array_get_size(v_tail_611_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_nat_dec_lt(v___x_608_, v___x_621_);
if (v___x_623_ == 0)
{
lean_object* v___x_625_; 
lean_dec_ref(v_f_603_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_622_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_a_617_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_619_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_621_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_603_, v_tail_611_, v___x_627_, v___x_628_, v___x_622_, v_a_617_);
return v___x_629_;
}
}
}
else
{
lean_dec_ref(v_f_603_);
return v___x_616_;
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_632_ = lean_nat_sub(v_start_605_, v_tailOff_613_);
v___x_633_ = lean_array_get_size(v_tail_611_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec(v___x_632_);
lean_dec_ref(v_f_603_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___y_606_);
return v___x_636_;
}
else
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_usize_of_nat(v___x_632_);
lean_dec(v___x_632_);
v___x_638_ = lean_usize_of_nat(v___x_633_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__2(v_f_603_, v_tail_611_, v___x_637_, v___x_638_, v___x_634_, v___y_606_);
return v___x_639_;
}
}
}
else
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0_spec__3(v_f_603_, v_t_604_, v___y_606_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* v_f_641_, lean_object* v_t_642_, lean_object* v_start_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_641_, v_t_642_, v_start_643_, v___y_644_);
lean_dec(v_start_643_);
lean_dec_ref(v_t_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(lean_object* v_log_647_, lean_object* v_f_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_unreported_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_unreported_651_ = lean_ctor_get(v_log_647_, 1);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0_spec__0(v_f_648_, v_unreported_651_, v___x_652_, v___y_649_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0___boxed(lean_object* v_log_654_, lean_object* v_f_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_log_654_, v_f_655_, v___y_656_);
lean_dec_ref(v_log_654_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(lean_object* v_pkgIdx_661_, lean_object* v_pkgName_662_, lean_object* v_pkgDir_663_, lean_object* v_lakeOpts_664_, lean_object* v_leanOpts_665_, lean_object* v_configFile_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___f_669_; lean_object* v___x_670_; 
v___f_669_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___closed__0));
v___x_670_ = l_IO_FS_readFile(v_configFile_666_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = 1;
v___x_673_ = lean_string_utf8_byte_size(v_a_671_);
lean_inc_ref(v_configFile_666_);
v___x_674_ = l_Lean_Parser_mkInputContext___redArg(v_a_671_, v_configFile_666_, v___x_672_, v___x_673_);
lean_inc_ref(v___x_674_);
v___x_675_ = l_Lean_Parser_parseHeader(v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_794_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_794_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_794_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_794_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_snd_680_; lean_object* v_fst_681_; lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_793_; 
v_snd_680_ = lean_ctor_get(v_a_676_, 1);
lean_inc(v_snd_680_);
v_fst_681_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_fst_681_);
lean_dec(v_a_676_);
v_fst_682_ = lean_ctor_get(v_snd_680_, 0);
v_snd_683_ = lean_ctor_get(v_snd_680_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_snd_680_);
if (v_isSharedCheck_793_ == 0)
{
v___x_685_ = v_snd_680_;
v_isShared_686_ = v_isSharedCheck_793_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_inc(v_fst_682_);
lean_dec(v_snd_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_793_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; 
lean_inc_ref(v___x_674_);
lean_inc_ref(v_leanOpts_665_);
v___x_687_ = l___private_Lake_Load_Lean_Elab_0__Lake_processHeader(v_fst_681_, v_leanOpts_665_, v___x_674_, v_snd_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_783_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_783_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_783_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_783_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_782_; 
v_fst_692_ = lean_ctor_get(v_a_688_, 0);
v_snd_693_ = lean_ctor_get(v_a_688_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_a_688_);
if (v_isSharedCheck_782_ == 0)
{
v___x_695_ = v_a_688_;
v_isShared_696_ = v_isSharedCheck_782_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
lean_dec(v_a_688_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_782_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___y_698_; lean_object* v___y_744_; lean_object* v___y_757_; lean_object* v___x_769_; lean_object* v_asyncMode_770_; uint8_t v_logWrites_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_769_ = l_Lake_nameExt;
v_asyncMode_770_ = lean_ctor_get(v___x_769_, 2);
v_logWrites_771_ = lean_ctor_get_uint8(v___x_769_, sizeof(void*)*6);
v___x_772_ = ((lean_object*)(l_Lake_configModuleName));
v___x_773_ = l_Lean_Environment_setMainModule(v_fst_692_, v___x_772_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_pkgName_662_);
lean_ctor_set(v___x_695_, 0, v_pkgIdx_661_);
v___x_775_ = v___x_695_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_pkgIdx_661_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_pkgName_662_);
v___x_775_ = v_reuseFailAlloc_781_;
goto v_reusejp_774_;
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = l_Lean_Elab_Command_mkState(v___y_698_, v_snd_693_, v_leanOpts_665_);
v___x_700_ = l_Lean_Elab_IO_processCommands(v___x_674_, v_fst_682_, v___x_699_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v_commandState_702_; lean_object* v_env_703_; lean_object* v_messages_704_; lean_object* v___x_705_; 
lean_del_object(v___x_685_);
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
v___x_705_ = l_Lean_MessageLog_forM___at___00__private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile_spec__0(v_messages_704_, v___f_669_, v_a_667_);
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
lean_dec_ref(v_configFile_666_);
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
v___x_715_ = lean_string_append(v_configFile_666_, v___x_714_);
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
lean_dec_ref(v_configFile_666_);
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
lean_dec_ref(v_configFile_666_);
v_a_734_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_700_, 1);
v___x_735_ = lean_io_error_to_string(v_a_734_);
v___x_736_ = 3;
v___x_737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*1, v___x_736_);
v___x_738_ = lean_array_get_size(v_a_667_);
v___x_739_ = lean_array_push(v_a_667_, v___x_737_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 1, v___x_739_);
lean_ctor_set(v___x_685_, 0, v___x_738_);
v___x_741_ = v___x_685_;
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
v___jp_743_:
{
lean_object* v___x_745_; lean_object* v_asyncMode_746_; uint8_t v_logWrites_747_; lean_object* v___x_749_; 
v___x_745_ = l_Lake_optsExt;
v_asyncMode_746_ = lean_ctor_get(v___x_745_, 2);
v_logWrites_747_ = lean_ctor_get_uint8(v___x_745_, sizeof(void*)*6);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 1);
lean_ctor_set(v___x_690_, 0, v_lakeOpts_664_);
v___x_749_ = v___x_690_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_lakeOpts_664_);
v___x_749_ = v_reuseFailAlloc_755_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___f_750_; lean_object* v___x_751_; 
v___f_750_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__1___boxed), 2, 1);
lean_closure_set(v___f_750_, 0, v___x_749_);
v___x_751_ = lean_box(0);
if (v_logWrites_747_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_745_, v___y_744_, v___f_750_, v_asyncMode_746_, v___x_751_, v___x_672_);
v___y_698_ = v___x_752_;
goto v___jp_697_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_745_, v___y_744_);
lean_dec_ref(v___y_744_);
v___x_754_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_745_, v___x_753_, v___f_750_, v_asyncMode_746_, v___x_751_, v___x_672_);
v___y_698_ = v___x_754_;
goto v___jp_697_;
}
}
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v_asyncMode_759_; uint8_t v_logWrites_760_; lean_object* v___x_762_; 
v___x_758_ = l_Lake_dirExt;
v_asyncMode_759_ = lean_ctor_get(v___x_758_, 2);
v_logWrites_760_ = lean_ctor_get_uint8(v___x_758_, sizeof(void*)*6);
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 1);
lean_ctor_set(v___x_678_, 0, v_pkgDir_663_);
v___x_762_ = v___x_678_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_pkgDir_663_);
v___x_762_ = v_reuseFailAlloc_768_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___f_763_; lean_object* v___x_764_; 
v___f_763_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__2___boxed), 2, 1);
lean_closure_set(v___f_763_, 0, v___x_762_);
v___x_764_ = lean_box(0);
if (v_logWrites_760_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_758_, v___y_757_, v___f_763_, v_asyncMode_759_, v___x_764_, v___x_672_);
v___y_744_ = v___x_765_;
goto v___jp_743_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_758_, v___y_757_);
lean_dec_ref(v___y_757_);
v___x_767_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_758_, v___x_766_, v___f_763_, v_asyncMode_759_, v___x_764_, v___x_672_);
v___y_744_ = v___x_767_;
goto v___jp_743_;
}
}
}
v_reusejp_774_:
{
lean_object* v___f_776_; lean_object* v___x_777_; 
v___f_776_ = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___lam__3___boxed), 2, 1);
lean_closure_set(v___f_776_, 0, v___x_775_);
v___x_777_ = lean_box(0);
if (v_logWrites_771_ == 0)
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_769_, v___x_773_, v___f_776_, v_asyncMode_770_, v___x_777_, v___x_672_);
v___y_757_ = v___x_778_;
goto v___jp_756_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_769_, v___x_773_);
lean_dec_ref(v___x_773_);
v___x_780_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_769_, v___x_779_, v___f_776_, v_asyncMode_770_, v___x_777_, v___x_672_);
v___y_757_ = v___x_780_;
goto v___jp_756_;
}
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
lean_dec(v_fst_682_);
lean_del_object(v___x_678_);
lean_dec_ref(v___x_674_);
lean_dec_ref(v_configFile_666_);
lean_dec_ref(v_leanOpts_665_);
lean_dec(v_lakeOpts_664_);
lean_dec_ref(v_pkgDir_663_);
lean_dec(v_pkgName_662_);
lean_dec(v_pkgIdx_661_);
v_a_784_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_687_, 1);
v___x_785_ = lean_io_error_to_string(v_a_784_);
v___x_786_ = 3;
v___x_787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*1, v___x_786_);
v___x_788_ = lean_array_get_size(v_a_667_);
v___x_789_ = lean_array_push(v_a_667_, v___x_787_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 1, v___x_789_);
lean_ctor_set(v___x_685_, 0, v___x_788_);
v___x_791_ = v___x_685_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
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
}
else
{
lean_object* v_a_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v___x_674_);
lean_dec_ref(v_configFile_666_);
lean_dec_ref(v_leanOpts_665_);
lean_dec(v_lakeOpts_664_);
lean_dec_ref(v_pkgDir_663_);
lean_dec(v_pkgName_662_);
lean_dec(v_pkgIdx_661_);
v_a_795_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_675_, 1);
v___x_796_ = lean_io_error_to_string(v_a_795_);
v___x_797_ = 3;
v___x_798_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1, v___x_797_);
v___x_799_ = lean_array_get_size(v_a_667_);
v___x_800_ = lean_array_push(v_a_667_, v___x_798_);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
return v___x_801_;
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_configFile_666_);
lean_dec_ref(v_leanOpts_665_);
lean_dec(v_lakeOpts_664_);
lean_dec_ref(v_pkgDir_663_);
lean_dec(v_pkgName_662_);
lean_dec(v_pkgIdx_661_);
v_a_802_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_670_, 1);
v___x_803_ = lean_io_error_to_string(v_a_802_);
v___x_804_ = 3;
v___x_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_804_);
v___x_806_ = lean_array_get_size(v_a_667_);
v___x_807_ = lean_array_push(v_a_667_, v___x_805_);
v___x_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile___boxed(lean_object* v_pkgIdx_809_, lean_object* v_pkgName_810_, lean_object* v_pkgDir_811_, lean_object* v_lakeOpts_812_, lean_object* v_leanOpts_813_, lean_object* v_configFile_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_809_, v_pkgName_810_, v_pkgDir_811_, v_lakeOpts_812_, v_leanOpts_813_, v_configFile_814_, v_a_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* v_env_820_, lean_object* v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = lake_environment_add(v_env_820_, v_x_00___x40_Lake_Load_Lean_Elab_1076801777____hygCtx___hyg_821_);
return v_res_822_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__2));
v___x_829_ = l_Lean_NameSet_empty;
v___x_830_ = l_Lean_NameSet_insert(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__5));
v___x_836_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__3);
v___x_837_ = l_Lean_NameSet_insert(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__8));
v___x_843_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__6);
v___x_844_ = l_Lean_NameSet_insert(v___x_843_, v___x_842_);
return v___x_844_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__11));
v___x_850_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__9);
v___x_851_ = l_Lean_NameSet_insert(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__14));
v___x_857_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__12);
v___x_858_ = l_Lean_NameSet_insert(v___x_857_, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__17));
v___x_864_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__15);
v___x_865_ = l_Lean_NameSet_insert(v___x_864_, v___x_863_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__20));
v___x_871_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__18);
v___x_872_ = l_Lean_NameSet_insert(v___x_871_, v___x_870_);
return v___x_872_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__23));
v___x_878_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__21);
v___x_879_ = l_Lean_NameSet_insert(v___x_878_, v___x_877_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__26));
v___x_885_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__24);
v___x_886_ = l_Lean_NameSet_insert(v___x_885_, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__29));
v___x_892_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__27);
v___x_893_ = l_Lean_NameSet_insert(v___x_892_, v___x_891_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__32));
v___x_899_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__30);
v___x_900_ = l_Lean_NameSet_insert(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__35));
v___x_906_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__33);
v___x_907_ = l_Lean_NameSet_insert(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__38));
v___x_913_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__36);
v___x_914_ = l_Lean_NameSet_insert(v___x_913_, v___x_912_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__41));
v___x_920_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__39);
v___x_921_ = l_Lean_NameSet_insert(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__44));
v___x_927_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__42);
v___x_928_ = l_Lean_NameSet_insert(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__47));
v___x_934_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_935_ = l_Lean_NameSet_insert(v___x_934_, v___x_933_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__51));
v___x_942_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48);
v___x_943_ = l_Lean_NameSet_insert(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__56(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__55));
v___x_951_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52);
v___x_952_ = l_Lean_NameSet_insert(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__56, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__56_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__56);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0(lean_object* v_addEntryFn_954_, lean_object* v___x_955_, lean_object* v_s_956_){
_start:
{
lean_object* v_importedEntries_957_; lean_object* v_state_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_importedEntries_957_ = lean_ctor_get(v_s_956_, 0);
v_state_958_ = lean_ctor_get(v_s_956_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_s_956_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v_s_956_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_state_958_);
lean_inc(v_importedEntries_957_);
lean_dec(v_s_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_state_962_; lean_object* v___x_964_; 
v_state_962_ = lean_apply_2(v_addEntryFn_954_, v_state_958_, v___x_955_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_state_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_importedEntries_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_state_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_instInhabitedPersistentEnvExtension___redArg();
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_968_, lean_object* v_val_969_, uint8_t v___x_970_, lean_object* v_as_971_, size_t v_i_972_, size_t v_stop_973_, lean_object* v_b_974_){
_start:
{
lean_object* v___y_976_; uint8_t v___x_980_; 
v___x_980_ = lean_usize_dec_eq(v_i_972_, v_stop_973_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_toEnvExtension_983_; lean_object* v_addEntryFn_984_; uint8_t v_logWrites_985_; lean_object* v___x_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_981_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_982_ = lean_array_get_borrowed(v___x_981_, v_val_968_, v_val_969_);
v_toEnvExtension_983_ = lean_ctor_get(v___x_982_, 0);
v_addEntryFn_984_ = lean_ctor_get(v___x_982_, 3);
v_logWrites_985_ = lean_ctor_get_uint8(v_toEnvExtension_983_, sizeof(void*)*6);
v___x_986_ = lean_array_uget_borrowed(v_as_971_, v_i_972_);
lean_inc(v___x_986_);
lean_inc(v_addEntryFn_984_);
v___f_987_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_987_, 0, v_addEntryFn_984_);
lean_closure_set(v___f_987_, 1, v___x_986_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_box(0);
if (v_logWrites_985_ == 0)
{
lean_object* v___x_990_; 
lean_inc_ref(v_toEnvExtension_983_);
v___x_990_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_983_, v_b_974_, v___f_987_, v___x_988_, v___x_989_, v___x_970_);
v___y_976_ = v___x_990_;
goto v___jp_975_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_inc_ref_n(v_toEnvExtension_983_, 2);
v___x_991_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_983_, v_b_974_);
lean_dec_ref(v_b_974_);
v___x_992_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_983_, v___x_991_, v___f_987_, v___x_988_, v___x_989_, v___x_970_);
v___y_976_ = v___x_992_;
goto v___jp_975_;
}
}
else
{
return v_b_974_;
}
v___jp_975_:
{
size_t v___x_977_; size_t v___x_978_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_972_, v___x_977_);
v_i_972_ = v___x_978_;
v_b_974_ = v___y_976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_993_, lean_object* v_val_994_, lean_object* v___x_995_, lean_object* v_as_996_, lean_object* v_i_997_, lean_object* v_stop_998_, lean_object* v_b_999_){
_start:
{
uint8_t v___x_1499__boxed_1000_; size_t v_i_boxed_1001_; size_t v_stop_boxed_1002_; lean_object* v_res_1003_; 
v___x_1499__boxed_1000_ = lean_unbox(v___x_995_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_stop_boxed_1002_ = lean_unbox_usize(v_stop_998_);
lean_dec(v_stop_998_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_993_, v_val_994_, v___x_1499__boxed_1000_, v_as_996_, v_i_boxed_1001_, v_stop_boxed_1002_, v_b_999_);
lean_dec_ref(v_as_996_);
lean_dec(v_val_994_);
lean_dec_ref(v_val_993_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_box(0);
return v___x_1006_;
}
else
{
lean_object* v_key_1007_; lean_object* v_value_1008_; lean_object* v_tail_1009_; uint8_t v___x_1010_; 
v_key_1007_ = lean_ctor_get(v_x_1005_, 0);
v_value_1008_ = lean_ctor_get(v_x_1005_, 1);
v_tail_1009_ = lean_ctor_get(v_x_1005_, 2);
v___x_1010_ = lean_name_eq(v_key_1007_, v_a_1004_);
if (v___x_1010_ == 0)
{
v_x_1005_ = v_tail_1009_;
goto _start;
}
else
{
lean_object* v___x_1012_; 
lean_inc(v_value_1008_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_value_1008_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1013_, v_x_1014_);
lean_dec(v_x_1014_);
lean_dec(v_a_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_buckets_1018_; lean_object* v___x_1019_; uint64_t v___y_1021_; 
v_buckets_1018_ = lean_ctor_get(v_m_1016_, 1);
v___x_1019_ = lean_array_get_size(v_buckets_1018_);
if (lean_obj_tag(v_a_1017_) == 0)
{
uint64_t v___x_1035_; 
v___x_1035_ = 1723ULL;
v___y_1021_ = v___x_1035_;
goto v___jp_1020_;
}
else
{
uint64_t v_hash_1036_; 
v_hash_1036_ = lean_ctor_get_uint64(v_a_1017_, sizeof(void*)*2);
v___y_1021_ = v_hash_1036_;
goto v___jp_1020_;
}
v___jp_1020_:
{
uint64_t v___x_1022_; uint64_t v___x_1023_; uint64_t v_fold_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1022_ = 32ULL;
v___x_1023_ = lean_uint64_shift_right(v___y_1021_, v___x_1022_);
v_fold_1024_ = lean_uint64_xor(v___y_1021_, v___x_1023_);
v___x_1025_ = 16ULL;
v___x_1026_ = lean_uint64_shift_right(v_fold_1024_, v___x_1025_);
v___x_1027_ = lean_uint64_xor(v_fold_1024_, v___x_1026_);
v___x_1028_ = lean_uint64_to_usize(v___x_1027_);
v___x_1029_ = lean_usize_of_nat(v___x_1019_);
v___x_1030_ = ((size_t)1ULL);
v___x_1031_ = lean_usize_sub(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_usize_land(v___x_1028_, v___x_1031_);
v___x_1033_ = lean_array_uget_borrowed(v_buckets_1018_, v___x_1032_);
v___x_1034_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1017_, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_m_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_1040_, lean_object* v_val_1041_, lean_object* v_as_1042_, size_t v_i_1043_, size_t v_stop_1044_, lean_object* v_b_1045_){
_start:
{
lean_object* v___y_1047_; uint8_t v___x_1051_; 
v___x_1051_ = lean_usize_dec_eq(v_i_1043_, v_stop_1044_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1052_ = lean_array_uget_borrowed(v_as_1042_, v_i_1043_);
v_fst_1053_ = lean_ctor_get(v___x_1052_, 0);
v_snd_1054_ = lean_ctor_get(v___x_1052_, 1);
v___x_1055_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_1056_ = l_Lean_NameSet_contains(v___x_1055_, v_fst_1053_);
if (v___x_1056_ == 0)
{
v___y_1047_ = v_b_1045_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_1040_, v_fst_1053_);
if (lean_obj_tag(v___x_1057_) == 0)
{
v___y_1047_ = v_b_1045_;
goto v___jp_1046_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_array_get_size(v_snd_1054_);
v___x_1061_ = lean_nat_dec_lt(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v_val_1058_);
v___y_1047_ = v_b_1045_;
goto v___jp_1046_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1060_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1041_, v_val_1058_, v___x_1056_, v_snd_1054_, v___x_1062_, v___x_1063_, v_b_1045_);
lean_dec(v_val_1058_);
v___y_1047_ = v___x_1064_;
goto v___jp_1046_;
}
}
}
}
else
{
return v_b_1045_;
}
v___jp_1046_:
{
size_t v___x_1048_; size_t v___x_1049_; 
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1043_, v___x_1048_);
v_i_1043_ = v___x_1049_;
v_b_1045_ = v___y_1047_;
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
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_size(v_constants_1098_);
v___x_1134_ = lean_nat_dec_lt(v___x_1103_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v_constants_1098_);
v___y_1105_ = v_a_1102_;
goto v___jp_1104_;
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1133_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1098_, v___x_1135_, v___x_1136_, v_a_1102_);
lean_dec_ref(v_constants_1098_);
v___y_1105_ = v___x_1137_;
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_persistentEnvExtensionsRef;
v___x_1107_ = lean_st_ref_get(v___x_1106_);
v___x_1108_ = l_Lean_mkExtNameMap(v___x_1103_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1124_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1124_;
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
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = lean_usize_of_nat(v___x_1113_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1109_, v___x_1107_, v_entries_1099_, v___x_1118_, v___x_1119_, v___y_1105_);
lean_dec_ref(v_entries_1099_);
lean_dec(v___x_1107_);
lean_dec(v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v___x_1107_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_entries_1099_);
v_a_1125_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1108_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1108_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
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
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_leanOpts_1092_);
v_a_1138_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1094_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1094_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1146_, lean_object* v_leanOpts_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1146_, v_leanOpts_1147_);
lean_dec_ref(v_olean_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1151_, v_a_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_m_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1154_, v_m_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_m_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1158_, lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1159_, v_x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1162_, lean_object* v_a_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1162_, v_a_1163_, v_x_1164_);
lean_dec(v_x_1164_);
lean_dec(v_a_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(1);
v___x_1168_ = lean_panic_fn_borrowed(v___x_1167_, v_msg_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1172_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1173_ = lean_unsigned_to_nat(35u);
v___x_1174_ = lean_unsigned_to_nat(182u);
v___x_1175_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1176_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1177_ = l_mkPanicMessageWithDecl(v___x_1176_, v___x_1175_, v___x_1174_, v___x_1173_, v___x_1172_);
return v___x_1177_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1179_ = lean_unsigned_to_nat(21u);
v___x_1180_ = lean_unsigned_to_nat(183u);
v___x_1181_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1183_ = l_mkPanicMessageWithDecl(v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_);
return v___x_1183_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1187_ = lean_unsigned_to_nat(35u);
v___x_1188_ = lean_unsigned_to_nat(276u);
v___x_1189_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1190_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1191_ = l_mkPanicMessageWithDecl(v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_);
return v___x_1191_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1192_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1193_ = lean_unsigned_to_nat(21u);
v___x_1194_ = lean_unsigned_to_nat(277u);
v___x_1195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1197_ = l_mkPanicMessageWithDecl(v___x_1196_, v___x_1195_, v___x_1194_, v___x_1193_, v___x_1192_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1198_, lean_object* v_v_1199_, lean_object* v_t_1200_){
_start:
{
if (lean_obj_tag(v_t_1200_) == 0)
{
lean_object* v_size_1201_; lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v_l_1204_; lean_object* v_r_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1561_; 
v_size_1201_ = lean_ctor_get(v_t_1200_, 0);
v_k_1202_ = lean_ctor_get(v_t_1200_, 1);
v_v_1203_ = lean_ctor_get(v_t_1200_, 2);
v_l_1204_ = lean_ctor_get(v_t_1200_, 3);
v_r_1205_ = lean_ctor_get(v_t_1200_, 4);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_t_1200_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1207_ = v_t_1200_;
v_isShared_1208_ = v_isSharedCheck_1561_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_r_1205_);
lean_inc(v_l_1204_);
lean_inc(v_v_1203_);
lean_inc(v_k_1202_);
lean_inc(v_size_1201_);
lean_dec(v_t_1200_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1561_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_string_compare(v_k_1198_, v_k_1202_);
switch(v___x_1209_)
{
case 0:
{
lean_object* v___x_1210_; 
lean_dec(v_size_1201_);
v___x_1210_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1198_, v_v_1199_, v_l_1204_);
if (lean_obj_tag(v_r_1205_) == 0)
{
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_size_1211_; lean_object* v_size_1212_; lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v_l_1215_; lean_object* v_r_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_size_1211_ = lean_ctor_get(v_r_1205_, 0);
v_size_1212_ = lean_ctor_get(v___x_1210_, 0);
v_k_1213_ = lean_ctor_get(v___x_1210_, 1);
v_v_1214_ = lean_ctor_get(v___x_1210_, 2);
v_l_1215_ = lean_ctor_get(v___x_1210_, 3);
v_r_1216_ = lean_ctor_get(v___x_1210_, 4);
lean_inc(v_r_1216_);
v___x_1217_ = lean_unsigned_to_nat(3u);
v___x_1218_ = lean_nat_mul(v___x_1217_, v_size_1211_);
v___x_1219_ = lean_nat_dec_lt(v___x_1218_, v_size_1212_);
lean_dec(v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec(v_r_1216_);
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v___x_1220_, v_size_1212_);
v___x_1222_ = lean_nat_add(v___x_1221_, v_size_1211_);
lean_dec(v___x_1221_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 3, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1222_);
v___x_1224_ = v___x_1207_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_r_1205_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
else
{
lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1297_; 
lean_inc(v_l_1215_);
lean_inc(v_v_1214_);
lean_inc(v_k_1213_);
lean_inc(v_size_1212_);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; lean_object* v_unused_1299_; lean_object* v_unused_1300_; lean_object* v_unused_1301_; lean_object* v_unused_1302_; 
v_unused_1298_ = lean_ctor_get(v___x_1210_, 4);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v___x_1210_, 3);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v___x_1210_, 2);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v___x_1210_, 1);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1302_);
v___x_1227_ = v___x_1210_;
v_isShared_1228_ = v_isSharedCheck_1297_;
goto v_resetjp_1226_;
}
else
{
lean_dec(v___x_1210_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1297_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
if (lean_obj_tag(v_l_1215_) == 0)
{
if (lean_obj_tag(v_r_1216_) == 0)
{
lean_object* v_size_1229_; lean_object* v_size_1230_; lean_object* v_k_1231_; lean_object* v_v_1232_; lean_object* v_l_1233_; lean_object* v_r_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_size_1229_ = lean_ctor_get(v_l_1215_, 0);
v_size_1230_ = lean_ctor_get(v_r_1216_, 0);
v_k_1231_ = lean_ctor_get(v_r_1216_, 1);
v_v_1232_ = lean_ctor_get(v_r_1216_, 2);
v_l_1233_ = lean_ctor_get(v_r_1216_, 3);
v_r_1234_ = lean_ctor_get(v_r_1216_, 4);
v___x_1235_ = lean_unsigned_to_nat(2u);
v___x_1236_ = lean_nat_mul(v___x_1235_, v_size_1229_);
v___x_1237_ = lean_nat_dec_lt(v_size_1230_, v___x_1236_);
lean_dec(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1267_; 
lean_inc(v_r_1234_);
lean_inc(v_l_1233_);
lean_inc(v_v_1232_);
lean_inc(v_k_1231_);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_r_1216_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; lean_object* v_unused_1269_; lean_object* v_unused_1270_; lean_object* v_unused_1271_; lean_object* v_unused_1272_; 
v_unused_1268_ = lean_ctor_get(v_r_1216_, 4);
lean_dec(v_unused_1268_);
v_unused_1269_ = lean_ctor_get(v_r_1216_, 3);
lean_dec(v_unused_1269_);
v_unused_1270_ = lean_ctor_get(v_r_1216_, 2);
lean_dec(v_unused_1270_);
v_unused_1271_ = lean_ctor_get(v_r_1216_, 1);
lean_dec(v_unused_1271_);
v_unused_1272_ = lean_ctor_get(v_r_1216_, 0);
lean_dec(v_unused_1272_);
v___x_1239_ = v_r_1216_;
v_isShared_1240_ = v_isSharedCheck_1267_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v_r_1216_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1267_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___x_1255_; lean_object* v___y_1257_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_add(v___x_1241_, v_size_1212_);
lean_dec(v_size_1212_);
v___x_1243_ = lean_nat_add(v___x_1242_, v_size_1211_);
lean_dec(v___x_1242_);
v___x_1255_ = lean_nat_add(v___x_1241_, v_size_1229_);
if (lean_obj_tag(v_l_1233_) == 0)
{
lean_object* v_size_1265_; 
v_size_1265_ = lean_ctor_get(v_l_1233_, 0);
lean_inc(v_size_1265_);
v___y_1257_ = v_size_1265_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_unsigned_to_nat(0u);
v___y_1257_ = v___x_1266_;
goto v___jp_1256_;
}
v___jp_1244_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_nat_add(v___y_1245_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec(v___y_1245_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 4, v_r_1205_);
lean_ctor_set(v___x_1239_, 3, v_r_1234_);
lean_ctor_set(v___x_1239_, 2, v_v_1203_);
lean_ctor_set(v___x_1239_, 1, v_k_1202_);
lean_ctor_set(v___x_1239_, 0, v___x_1248_);
v___x_1250_ = v___x_1239_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_r_1234_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_r_1205_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 4, v___x_1250_);
lean_ctor_set(v___x_1227_, 3, v___y_1246_);
lean_ctor_set(v___x_1227_, 2, v_v_1232_);
lean_ctor_set(v___x_1227_, 1, v_k_1231_);
lean_ctor_set(v___x_1227_, 0, v___x_1243_);
v___x_1252_ = v___x_1227_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_k_1231_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_v_1232_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v___y_1246_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_nat_add(v___x_1255_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec(v___x_1255_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_l_1233_);
lean_ctor_set(v___x_1207_, 3, v_l_1215_);
lean_ctor_set(v___x_1207_, 2, v_v_1214_);
lean_ctor_set(v___x_1207_, 1, v_k_1213_);
lean_ctor_set(v___x_1207_, 0, v___x_1258_);
v___x_1260_ = v___x_1207_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_k_1213_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_v_1214_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_l_1215_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_l_1233_);
v___x_1260_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_nat_add(v___x_1241_, v_size_1211_);
if (lean_obj_tag(v_r_1234_) == 0)
{
lean_object* v_size_1262_; 
v_size_1262_ = lean_ctor_get(v_r_1234_, 0);
lean_inc(v_size_1262_);
v___y_1245_ = v___x_1261_;
v___y_1246_ = v___x_1260_;
v___y_1247_ = v_size_1262_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___y_1245_ = v___x_1261_;
v___y_1246_ = v___x_1260_;
v___y_1247_ = v___x_1263_;
goto v___jp_1244_;
}
}
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_del_object(v___x_1207_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_add(v___x_1273_, v_size_1212_);
lean_dec(v_size_1212_);
v___x_1275_ = lean_nat_add(v___x_1274_, v_size_1211_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_nat_add(v___x_1273_, v_size_1211_);
v___x_1277_ = lean_nat_add(v___x_1276_, v_size_1230_);
lean_dec(v___x_1276_);
lean_inc_ref(v_r_1205_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 4, v_r_1205_);
lean_ctor_set(v___x_1227_, 3, v_r_1216_);
lean_ctor_set(v___x_1227_, 2, v_v_1203_);
lean_ctor_set(v___x_1227_, 1, v_k_1202_);
lean_ctor_set(v___x_1227_, 0, v___x_1277_);
v___x_1279_ = v___x_1227_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_r_1216_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_r_1205_);
v___x_1279_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v_r_1205_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; lean_object* v_unused_1288_; lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; 
v_unused_1287_ = lean_ctor_get(v_r_1205_, 4);
lean_dec(v_unused_1287_);
v_unused_1288_ = lean_ctor_get(v_r_1205_, 3);
lean_dec(v_unused_1288_);
v_unused_1289_ = lean_ctor_get(v_r_1205_, 2);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v_r_1205_, 1);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_r_1205_, 0);
lean_dec(v_unused_1291_);
v___x_1281_ = v_r_1205_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_dec(v_r_1205_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v___x_1279_);
lean_ctor_set(v___x_1281_, 3, v_l_1215_);
lean_ctor_set(v___x_1281_, 2, v_v_1214_);
lean_ctor_set(v___x_1281_, 1, v_k_1213_);
lean_ctor_set(v___x_1281_, 0, v___x_1275_);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_k_1213_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_v_1214_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_l_1215_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v___x_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref_known(v_l_1215_, 5);
lean_del_object(v___x_1227_);
lean_dec(v_v_1214_);
lean_dec(v_k_1213_);
lean_dec(v_size_1212_);
lean_dec_ref_known(v_r_1205_, 5);
lean_del_object(v___x_1207_);
lean_dec(v_v_1203_);
lean_dec(v_k_1202_);
v___x_1293_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1294_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1293_);
return v___x_1294_;
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1227_);
lean_dec(v_r_1216_);
lean_dec(v_v_1214_);
lean_dec(v_k_1213_);
lean_dec(v_size_1212_);
lean_dec_ref_known(v_r_1205_, 5);
lean_del_object(v___x_1207_);
lean_dec(v_v_1203_);
lean_dec(v_k_1202_);
v___x_1295_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1296_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1295_);
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_size_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v_size_1303_ = lean_ctor_get(v_r_1205_, 0);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_add(v___x_1304_, v_size_1303_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 3, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1305_);
v___x_1307_ = v___x_1207_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_r_1205_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_l_1309_; 
v_l_1309_ = lean_ctor_get(v___x_1210_, 3);
if (lean_obj_tag(v_l_1309_) == 0)
{
lean_object* v_r_1310_; 
lean_inc_ref(v_l_1309_);
v_r_1310_ = lean_ctor_get(v___x_1210_, 4);
lean_inc(v_r_1310_);
if (lean_obj_tag(v_r_1310_) == 0)
{
lean_object* v_size_1311_; lean_object* v_k_1312_; lean_object* v_v_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1327_; 
v_size_1311_ = lean_ctor_get(v___x_1210_, 0);
v_k_1312_ = lean_ctor_get(v___x_1210_, 1);
v_v_1313_ = lean_ctor_get(v___x_1210_, 2);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; lean_object* v_unused_1329_; 
v_unused_1328_ = lean_ctor_get(v___x_1210_, 4);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v___x_1210_, 3);
lean_dec(v_unused_1329_);
v___x_1315_ = v___x_1210_;
v_isShared_1316_ = v_isSharedCheck_1327_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_v_1313_);
lean_inc(v_k_1312_);
lean_inc(v_size_1311_);
lean_dec(v___x_1210_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1327_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_size_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v_size_1317_ = lean_ctor_get(v_r_1310_, 0);
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_add(v___x_1318_, v_size_1311_);
lean_dec(v_size_1311_);
v___x_1320_ = lean_nat_add(v___x_1318_, v_size_1317_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 4, v_r_1205_);
lean_ctor_set(v___x_1315_, 3, v_r_1310_);
lean_ctor_set(v___x_1315_, 2, v_v_1203_);
lean_ctor_set(v___x_1315_, 1, v_k_1202_);
lean_ctor_set(v___x_1315_, 0, v___x_1320_);
v___x_1322_ = v___x_1315_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_r_1310_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_r_1205_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1322_);
lean_ctor_set(v___x_1207_, 3, v_l_1309_);
lean_ctor_set(v___x_1207_, 2, v_v_1313_);
lean_ctor_set(v___x_1207_, 1, v_k_1312_);
lean_ctor_set(v___x_1207_, 0, v___x_1319_);
v___x_1324_ = v___x_1207_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1325_, 3, v_l_1309_);
lean_ctor_set(v_reuseFailAlloc_1325_, 4, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_k_1330_; lean_object* v_v_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1343_; 
v_k_1330_ = lean_ctor_get(v___x_1210_, 1);
v_v_1331_ = lean_ctor_get(v___x_1210_, 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; lean_object* v_unused_1345_; lean_object* v_unused_1346_; 
v_unused_1344_ = lean_ctor_get(v___x_1210_, 4);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v___x_1210_, 3);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1346_);
v___x_1333_ = v___x_1210_;
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_v_1331_);
lean_inc(v_k_1330_);
lean_dec(v___x_1210_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1335_ = lean_unsigned_to_nat(3u);
v___x_1336_ = lean_unsigned_to_nat(1u);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 3, v_r_1310_);
lean_ctor_set(v___x_1333_, 2, v_v_1203_);
lean_ctor_set(v___x_1333_, 1, v_k_1202_);
lean_ctor_set(v___x_1333_, 0, v___x_1336_);
v___x_1338_ = v___x_1333_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_r_1310_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1310_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1338_);
lean_ctor_set(v___x_1207_, 3, v_l_1309_);
lean_ctor_set(v___x_1207_, 2, v_v_1331_);
lean_ctor_set(v___x_1207_, 1, v_k_1330_);
lean_ctor_set(v___x_1207_, 0, v___x_1335_);
v___x_1340_ = v___x_1207_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_k_1330_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_v_1331_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_l_1309_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
else
{
lean_object* v_r_1347_; 
v_r_1347_ = lean_ctor_get(v___x_1210_, 4);
lean_inc(v_r_1347_);
if (lean_obj_tag(v_r_1347_) == 0)
{
lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1373_; 
lean_inc(v_l_1309_);
v_k_1348_ = lean_ctor_get(v___x_1210_, 1);
v_v_1349_ = lean_ctor_get(v___x_1210_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1374_ = lean_ctor_get(v___x_1210_, 4);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v___x_1210_, 3);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1376_);
v___x_1351_ = v___x_1210_;
v_isShared_1352_ = v_isSharedCheck_1373_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_v_1349_);
lean_inc(v_k_1348_);
lean_dec(v___x_1210_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1373_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_k_1353_; lean_object* v_v_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1369_; 
v_k_1353_ = lean_ctor_get(v_r_1347_, 1);
v_v_1354_ = lean_ctor_get(v_r_1347_, 2);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_r_1347_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1370_ = lean_ctor_get(v_r_1347_, 4);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_r_1347_, 3);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_r_1347_, 0);
lean_dec(v_unused_1372_);
v___x_1356_ = v_r_1347_;
v_isShared_1357_ = v_isSharedCheck_1369_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_v_1354_);
lean_inc(v_k_1353_);
lean_dec(v_r_1347_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1369_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1358_ = lean_unsigned_to_nat(3u);
v___x_1359_ = lean_unsigned_to_nat(1u);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 4, v_l_1309_);
lean_ctor_set(v___x_1356_, 3, v_l_1309_);
lean_ctor_set(v___x_1356_, 2, v_v_1349_);
lean_ctor_set(v___x_1356_, 1, v_k_1348_);
lean_ctor_set(v___x_1356_, 0, v___x_1359_);
v___x_1361_ = v___x_1356_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_l_1309_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_l_1309_);
v___x_1361_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 4, v_l_1309_);
lean_ctor_set(v___x_1351_, 2, v_v_1203_);
lean_ctor_set(v___x_1351_, 1, v_k_1202_);
lean_ctor_set(v___x_1351_, 0, v___x_1359_);
v___x_1363_ = v___x_1351_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_l_1309_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_l_1309_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1363_);
lean_ctor_set(v___x_1207_, 3, v___x_1361_);
lean_ctor_set(v___x_1207_, 2, v_v_1354_);
lean_ctor_set(v___x_1207_, 1, v_k_1353_);
lean_ctor_set(v___x_1207_, 0, v___x_1358_);
v___x_1365_ = v___x_1207_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1353_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1354_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_unsigned_to_nat(2u);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_r_1347_);
lean_ctor_set(v___x_1207_, 3, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1377_);
v___x_1379_ = v___x_1207_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_r_1347_);
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
else
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1210_);
lean_ctor_set(v___x_1207_, 3, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1381_);
v___x_1383_ = v___x_1207_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v___x_1210_);
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
case 1:
{
lean_object* v___x_1386_; 
lean_dec(v_v_1203_);
lean_dec(v_k_1202_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 2, v_v_1199_);
lean_ctor_set(v___x_1207_, 1, v_k_1198_);
v___x_1386_ = v___x_1207_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_size_1201_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_k_1198_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_v_1199_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_r_1205_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
default: 
{
lean_object* v___x_1388_; 
lean_dec(v_size_1201_);
v___x_1388_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1198_, v_v_1199_, v_r_1205_);
if (lean_obj_tag(v_l_1204_) == 0)
{
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_size_1389_; lean_object* v_size_1390_; lean_object* v_k_1391_; lean_object* v_v_1392_; lean_object* v_l_1393_; lean_object* v_r_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_size_1389_ = lean_ctor_get(v_l_1204_, 0);
v_size_1390_ = lean_ctor_get(v___x_1388_, 0);
v_k_1391_ = lean_ctor_get(v___x_1388_, 1);
v_v_1392_ = lean_ctor_get(v___x_1388_, 2);
v_l_1393_ = lean_ctor_get(v___x_1388_, 3);
lean_inc(v_l_1393_);
v_r_1394_ = lean_ctor_get(v___x_1388_, 4);
v___x_1395_ = lean_unsigned_to_nat(3u);
v___x_1396_ = lean_nat_mul(v___x_1395_, v_size_1389_);
v___x_1397_ = lean_nat_dec_lt(v___x_1396_, v_size_1390_);
lean_dec(v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_dec(v_l_1393_);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v___x_1398_, v_size_1389_);
v___x_1400_ = lean_nat_add(v___x_1399_, v_size_1390_);
lean_dec(v___x_1399_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1388_);
lean_ctor_set(v___x_1207_, 0, v___x_1400_);
v___x_1402_ = v___x_1207_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v___x_1388_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1473_; 
lean_inc(v_r_1394_);
lean_inc(v_v_1392_);
lean_inc(v_k_1391_);
lean_inc(v_size_1390_);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1474_ = lean_ctor_get(v___x_1388_, 4);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v___x_1388_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v___x_1388_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v___x_1388_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1478_);
v___x_1405_ = v___x_1388_;
v_isShared_1406_ = v_isSharedCheck_1473_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v___x_1388_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1473_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
if (lean_obj_tag(v_l_1393_) == 0)
{
if (lean_obj_tag(v_r_1394_) == 0)
{
lean_object* v_size_1407_; lean_object* v_k_1408_; lean_object* v_v_1409_; lean_object* v_l_1410_; lean_object* v_r_1411_; lean_object* v_size_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_size_1407_ = lean_ctor_get(v_l_1393_, 0);
v_k_1408_ = lean_ctor_get(v_l_1393_, 1);
v_v_1409_ = lean_ctor_get(v_l_1393_, 2);
v_l_1410_ = lean_ctor_get(v_l_1393_, 3);
v_r_1411_ = lean_ctor_get(v_l_1393_, 4);
v_size_1412_ = lean_ctor_get(v_r_1394_, 0);
v___x_1413_ = lean_unsigned_to_nat(2u);
v___x_1414_ = lean_nat_mul(v___x_1413_, v_size_1412_);
v___x_1415_ = lean_nat_dec_lt(v_size_1407_, v___x_1414_);
lean_dec(v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_r_1411_);
lean_inc(v_l_1410_);
lean_inc(v_v_1409_);
lean_inc(v_k_1408_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_l_1393_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1445_ = lean_ctor_get(v_l_1393_, 4);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_l_1393_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_l_1393_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_l_1393_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1393_, 0);
lean_dec(v_unused_1449_);
v___x_1417_ = v_l_1393_;
v_isShared_1418_ = v_isSharedCheck_1444_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v_l_1393_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1444_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1434_; 
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v___x_1419_, v_size_1389_);
v___x_1421_ = lean_nat_add(v___x_1420_, v_size_1390_);
lean_dec(v_size_1390_);
if (lean_obj_tag(v_l_1410_) == 0)
{
lean_object* v_size_1442_; 
v_size_1442_ = lean_ctor_get(v_l_1410_, 0);
lean_inc(v_size_1442_);
v___y_1434_ = v_size_1442_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___y_1434_ = v___x_1443_;
goto v___jp_1433_;
}
v___jp_1422_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_nat_add(v___y_1423_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec(v___y_1423_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 4, v_r_1394_);
lean_ctor_set(v___x_1417_, 3, v_r_1411_);
lean_ctor_set(v___x_1417_, 2, v_v_1392_);
lean_ctor_set(v___x_1417_, 1, v_k_1391_);
lean_ctor_set(v___x_1417_, 0, v___x_1426_);
v___x_1428_ = v___x_1417_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_r_1411_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_r_1394_);
v___x_1428_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1430_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 4, v___x_1428_);
lean_ctor_set(v___x_1405_, 3, v___y_1424_);
lean_ctor_set(v___x_1405_, 2, v_v_1409_);
lean_ctor_set(v___x_1405_, 1, v_k_1408_);
lean_ctor_set(v___x_1405_, 0, v___x_1421_);
v___x_1430_ = v___x_1405_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1408_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1409_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v___y_1424_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
v___jp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_nat_add(v___x_1420_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec(v___x_1420_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_l_1410_);
lean_ctor_set(v___x_1207_, 0, v___x_1435_);
v___x_1437_ = v___x_1207_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_l_1410_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_nat_add(v___x_1419_, v_size_1412_);
if (lean_obj_tag(v_r_1411_) == 0)
{
lean_object* v_size_1439_; 
v_size_1439_ = lean_ctor_get(v_r_1411_, 0);
lean_inc(v_size_1439_);
v___y_1423_ = v___x_1438_;
v___y_1424_ = v___x_1437_;
v___y_1425_ = v_size_1439_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___y_1423_ = v___x_1438_;
v___y_1424_ = v___x_1437_;
v___y_1425_ = v___x_1440_;
goto v___jp_1422_;
}
}
}
}
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
lean_del_object(v___x_1207_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v___x_1450_, v_size_1389_);
v___x_1452_ = lean_nat_add(v___x_1451_, v_size_1390_);
lean_dec(v_size_1390_);
v___x_1453_ = lean_nat_add(v___x_1451_, v_size_1407_);
lean_dec(v___x_1451_);
lean_inc_ref(v_l_1204_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 4, v_l_1393_);
lean_ctor_set(v___x_1405_, 3, v_l_1204_);
lean_ctor_set(v___x_1405_, 2, v_v_1203_);
lean_ctor_set(v___x_1405_, 1, v_k_1202_);
lean_ctor_set(v___x_1405_, 0, v___x_1453_);
v___x_1455_ = v___x_1405_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_l_1393_);
v___x_1455_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v_l_1204_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; lean_object* v_unused_1464_; lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; 
v_unused_1463_ = lean_ctor_get(v_l_1204_, 4);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_l_1204_, 3);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_l_1204_, 2);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_l_1204_, 1);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_l_1204_, 0);
lean_dec(v_unused_1467_);
v___x_1457_ = v_l_1204_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_l_1204_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_r_1394_);
lean_ctor_set(v___x_1457_, 3, v___x_1455_);
lean_ctor_set(v___x_1457_, 2, v_v_1392_);
lean_ctor_set(v___x_1457_, 1, v_k_1391_);
lean_ctor_set(v___x_1457_, 0, v___x_1452_);
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1394_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref_known(v_l_1393_, 5);
lean_del_object(v___x_1405_);
lean_dec(v_v_1392_);
lean_dec(v_k_1391_);
lean_dec(v_size_1390_);
lean_dec_ref_known(v_l_1204_, 5);
lean_del_object(v___x_1207_);
lean_dec(v_v_1203_);
lean_dec(v_k_1202_);
v___x_1469_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1470_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1469_);
return v___x_1470_;
}
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_del_object(v___x_1405_);
lean_dec(v_r_1394_);
lean_dec(v_v_1392_);
lean_dec(v_k_1391_);
lean_dec(v_size_1390_);
lean_dec_ref_known(v_l_1204_, 5);
lean_del_object(v___x_1207_);
lean_dec(v_v_1203_);
lean_dec(v_k_1202_);
v___x_1471_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1472_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1471_);
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_size_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v_size_1479_ = lean_ctor_get(v_l_1204_, 0);
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_add(v___x_1480_, v_size_1479_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1388_);
lean_ctor_set(v___x_1207_, 0, v___x_1481_);
v___x_1483_ = v___x_1207_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___x_1388_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_l_1485_; 
v_l_1485_ = lean_ctor_get(v___x_1388_, 3);
lean_inc(v_l_1485_);
if (lean_obj_tag(v_l_1485_) == 0)
{
lean_object* v_r_1486_; 
v_r_1486_ = lean_ctor_get(v___x_1388_, 4);
lean_inc(v_r_1486_);
if (lean_obj_tag(v_r_1486_) == 0)
{
lean_object* v_size_1487_; lean_object* v_k_1488_; lean_object* v_v_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1503_; 
v_size_1487_ = lean_ctor_get(v___x_1388_, 0);
v_k_1488_ = lean_ctor_get(v___x_1388_, 1);
v_v_1489_ = lean_ctor_get(v___x_1388_, 2);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1504_ = lean_ctor_get(v___x_1388_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v___x_1388_, 3);
lean_dec(v_unused_1505_);
v___x_1491_ = v___x_1388_;
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_v_1489_);
lean_inc(v_k_1488_);
lean_inc(v_size_1487_);
lean_dec(v___x_1388_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_size_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v_size_1493_ = lean_ctor_get(v_l_1485_, 0);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1487_);
lean_dec(v_size_1487_);
v___x_1496_ = lean_nat_add(v___x_1494_, v_size_1493_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v_l_1485_);
lean_ctor_set(v___x_1491_, 3, v_l_1204_);
lean_ctor_set(v___x_1491_, 2, v_v_1203_);
lean_ctor_set(v___x_1491_, 1, v_k_1202_);
lean_ctor_set(v___x_1491_, 0, v___x_1496_);
v___x_1498_ = v___x_1491_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_l_1204_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1485_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_r_1486_);
lean_ctor_set(v___x_1207_, 3, v___x_1498_);
lean_ctor_set(v___x_1207_, 2, v_v_1489_);
lean_ctor_set(v___x_1207_, 1, v_k_1488_);
lean_ctor_set(v___x_1207_, 0, v___x_1495_);
v___x_1500_ = v___x_1207_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1488_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1489_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_r_1486_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_k_1506_; lean_object* v_v_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1531_; 
v_k_1506_ = lean_ctor_get(v___x_1388_, 1);
v_v_1507_ = lean_ctor_get(v___x_1388_, 2);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1532_ = lean_ctor_get(v___x_1388_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v___x_1388_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1534_);
v___x_1509_ = v___x_1388_;
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_v_1507_);
lean_inc(v_k_1506_);
lean_dec(v___x_1388_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1527_; 
v_k_1511_ = lean_ctor_get(v_l_1485_, 1);
v_v_1512_ = lean_ctor_get(v_l_1485_, 2);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_l_1485_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; lean_object* v_unused_1529_; lean_object* v_unused_1530_; 
v_unused_1528_ = lean_ctor_get(v_l_1485_, 4);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_l_1485_, 3);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_l_1485_, 0);
lean_dec(v_unused_1530_);
v___x_1514_ = v_l_1485_;
v_isShared_1515_ = v_isSharedCheck_1527_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_v_1512_);
lean_inc(v_k_1511_);
lean_dec(v_l_1485_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1527_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1516_ = lean_unsigned_to_nat(3u);
v___x_1517_ = lean_unsigned_to_nat(1u);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_r_1486_);
lean_ctor_set(v___x_1514_, 3, v_r_1486_);
lean_ctor_set(v___x_1514_, 2, v_v_1203_);
lean_ctor_set(v___x_1514_, 1, v_k_1202_);
lean_ctor_set(v___x_1514_, 0, v___x_1517_);
v___x_1519_ = v___x_1514_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_r_1486_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_r_1486_);
v___x_1519_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 3, v_r_1486_);
lean_ctor_set(v___x_1509_, 0, v___x_1517_);
v___x_1521_ = v___x_1509_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1506_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1507_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_r_1486_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_r_1486_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1521_);
lean_ctor_set(v___x_1207_, 3, v___x_1519_);
lean_ctor_set(v___x_1207_, 2, v_v_1512_);
lean_ctor_set(v___x_1207_, 1, v_k_1511_);
lean_ctor_set(v___x_1207_, 0, v___x_1516_);
v___x_1523_ = v___x_1207_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1535_; 
v_r_1535_ = lean_ctor_get(v___x_1388_, 4);
lean_inc(v_r_1535_);
if (lean_obj_tag(v_r_1535_) == 0)
{
lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1549_; 
v_k_1536_ = lean_ctor_get(v___x_1388_, 1);
v_v_1537_ = lean_ctor_get(v___x_1388_, 2);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1550_ = lean_ctor_get(v___x_1388_, 4);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v___x_1388_, 3);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1552_);
v___x_1539_ = v___x_1388_;
v_isShared_1540_ = v_isSharedCheck_1549_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
lean_dec(v___x_1388_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1549_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1541_ = lean_unsigned_to_nat(3u);
v___x_1542_ = lean_unsigned_to_nat(1u);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 4, v_l_1485_);
lean_ctor_set(v___x_1539_, 2, v_v_1203_);
lean_ctor_set(v___x_1539_, 1, v_k_1202_);
lean_ctor_set(v___x_1539_, 0, v___x_1542_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_l_1485_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_l_1485_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_r_1535_);
lean_ctor_set(v___x_1207_, 3, v___x_1544_);
lean_ctor_set(v___x_1207_, 2, v_v_1537_);
lean_ctor_set(v___x_1207_, 1, v_k_1536_);
lean_ctor_set(v___x_1207_, 0, v___x_1541_);
v___x_1546_ = v___x_1207_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1535_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = lean_unsigned_to_nat(2u);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1388_);
lean_ctor_set(v___x_1207_, 3, v_r_1535_);
lean_ctor_set(v___x_1207_, 0, v___x_1553_);
v___x_1555_ = v___x_1207_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_r_1535_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v___x_1388_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_unsigned_to_nat(1u);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1388_);
lean_ctor_set(v___x_1207_, 3, v___x_1388_);
lean_ctor_set(v___x_1207_, 0, v___x_1557_);
v___x_1559_ = v___x_1207_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v___x_1388_);
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
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_k_1198_);
lean_ctor_set(v___x_1563_, 2, v_v_1199_);
lean_ctor_set(v___x_1563_, 3, v_t_1200_);
lean_ctor_set(v___x_1563_, 4, v_t_1200_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1564_, lean_object* v_x_1565_){
_start:
{
if (lean_obj_tag(v_x_1565_) == 0)
{
lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v_l_1568_; lean_object* v_r_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_k_1566_ = lean_ctor_get(v_x_1565_, 1);
lean_inc(v_k_1566_);
v_v_1567_ = lean_ctor_get(v_x_1565_, 2);
lean_inc(v_v_1567_);
v_l_1568_ = lean_ctor_get(v_x_1565_, 3);
lean_inc(v_l_1568_);
v_r_1569_ = lean_ctor_get(v_x_1565_, 4);
lean_inc(v_r_1569_);
lean_dec_ref_known(v_x_1565_, 5);
v___x_1570_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1564_, v_l_1568_);
v___x_1571_ = 1;
v___x_1572_ = l_Lean_Name_toString(v_k_1566_, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_v_1567_);
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1572_, v___x_1573_, v___x_1570_);
v_init_1564_ = v___x_1574_;
v_x_1565_ = v_r_1569_;
goto _start;
}
else
{
return v_init_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(1);
v___x_1578_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1577_, v_m_1576_);
v___x_1579_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
if (lean_obj_tag(v_a_1580_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_array_to_list(v_a_1581_);
return v___x_1582_;
}
else
{
lean_object* v_head_1583_; lean_object* v_tail_1584_; lean_object* v___x_1585_; 
v_head_1583_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_head_1583_);
v_tail_1584_ = lean_ctor_get(v_a_1580_, 1);
lean_inc(v_tail_1584_);
lean_dec_ref_known(v_a_1580_, 2);
v___x_1585_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1581_, v_head_1583_);
v_a_1580_ = v_tail_1584_;
v_a_1581_ = v___x_1585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1595_){
_start:
{
lean_object* v_idx_1596_; lean_object* v_name_1597_; lean_object* v_platform_1598_; lean_object* v_leanHash_1599_; uint64_t v_configHash_1600_; lean_object* v_options_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_idx_1596_ = lean_ctor_get(v_x_1595_, 0);
lean_inc(v_idx_1596_);
v_name_1597_ = lean_ctor_get(v_x_1595_, 1);
lean_inc(v_name_1597_);
v_platform_1598_ = lean_ctor_get(v_x_1595_, 2);
lean_inc_ref(v_platform_1598_);
v_leanHash_1599_ = lean_ctor_get(v_x_1595_, 3);
lean_inc_ref(v_leanHash_1599_);
v_configHash_1600_ = lean_ctor_get_uint64(v_x_1595_, sizeof(void*)*5);
v_options_1601_ = lean_ctor_get(v_x_1595_, 4);
lean_inc(v_options_1601_);
lean_dec_ref(v_x_1595_);
v___x_1602_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1603_ = l_Lean_JsonNumber_fromNat(v_idx_1596_);
v___x_1604_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1602_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1609_ = 1;
v___x_1610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1597_, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1608_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1606_);
v___x_1614_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_platform_1598_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1606_);
v___x_1618_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_leanHash_1599_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___x_1606_);
v___x_1622_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1623_ = l_Lake_lowerHexUInt64(v_configHash_1600_);
v___x_1624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v___x_1606_);
v___x_1627_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1628_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1601_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1606_);
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___x_1606_);
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1626_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1621_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1617_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1613_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1607_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1638_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1636_, v___x_1637_);
v___x_1639_ = l_Lean_Json_mkObj(v___x_1638_);
lean_dec(v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1640_, lean_object* v_msg_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1643_, lean_object* v_k_1644_, lean_object* v_v_1645_, lean_object* v_t_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1644_, v_v_1645_, v_t_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1648_, lean_object* v_t_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1648_, v_t_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1653_, lean_object* v_k_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = l_Lean_Json_getObjValD(v_j_1653_, v_k_1654_);
v___x_1656_ = l_Lean_Json_getNat_x3f(v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1657_, lean_object* v_k_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1657_, v_k_1658_);
lean_dec_ref(v_k_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1660_, lean_object* v_k_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = l_Lean_Json_getObjValD(v_j_1660_, v_k_1661_);
v___x_1663_ = l_Lean_Name_fromJson_x3f(v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1664_, v_k_1665_);
lean_dec_ref(v_k_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1667_, lean_object* v_k_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = l_Lean_Json_getObjValD(v_j_1667_, v_k_1668_);
v___x_1670_ = l_Lean_Json_getStr_x3f(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1671_, v_k_1672_);
lean_dec_ref(v_k_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1674_, lean_object* v_k_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = l_Lean_Json_getObjValD(v_j_1674_, v_k_1675_);
v___x_1677_ = l_Lake_Hash_fromJson_x3f(v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1678_, lean_object* v_k_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1678_, v_k_1679_);
lean_dec_ref(v_k_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1684_, lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v_k_1686_; lean_object* v_v_1687_; lean_object* v_l_1688_; lean_object* v_r_1689_; lean_object* v___x_1690_; 
v_k_1686_ = lean_ctor_get(v_x_1685_, 1);
lean_inc(v_k_1686_);
v_v_1687_ = lean_ctor_get(v_x_1685_, 2);
lean_inc(v_v_1687_);
v_l_1688_ = lean_ctor_get(v_x_1685_, 3);
lean_inc(v_l_1688_);
v_r_1689_ = lean_ctor_get(v_x_1685_, 4);
lean_inc(v_r_1689_);
lean_dec_ref_known(v_x_1685_, 5);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1684_, v_l_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_dec(v_r_1689_);
lean_dec(v_v_1687_);
lean_dec(v_k_1686_);
return v___x_1690_;
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1731_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1731_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1731_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1696_ = lean_string_dec_eq(v_k_1686_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v_n_1697_; uint8_t v___x_1698_; 
lean_inc(v_k_1686_);
v_n_1697_ = l_String_toName(v_k_1686_);
v___x_1698_ = l_Lean_Name_isAnonymous(v_n_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
lean_del_object(v___x_1693_);
lean_dec(v_k_1686_);
v___x_1699_ = l_Lean_Json_getStr_x3f(v_v_1687_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_n_1697_);
lean_dec(v_a_1691_);
lean_dec(v_r_1689_);
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1697_, v_a_1708_, v_a_1691_);
v_init_1684_ = v___x_1709_;
v_x_1685_ = v_r_1689_;
goto _start;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_n_1697_);
lean_dec(v_a_1691_);
lean_dec(v_r_1689_);
lean_dec(v_v_1687_);
v___x_1711_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1712_ = lean_string_append(v___x_1711_, v_k_1686_);
lean_dec(v_k_1686_);
v___x_1713_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1714_);
v___x_1716_ = v___x_1693_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v___x_1718_; 
lean_del_object(v___x_1693_);
lean_dec(v_k_1686_);
v___x_1718_ = l_Lean_Json_getStr_x3f(v_v_1687_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1691_);
lean_dec(v_r_1689_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1728_, v_a_1727_, v_a_1691_);
v_init_1684_ = v___x_1729_;
v_x_1685_ = v_r_1689_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_init_1684_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1734_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 5)
{
lean_object* v_kvPairs_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_kvPairs_1735_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_kvPairs_1735_);
lean_dec_ref_known(v_x_1734_, 1);
v___x_1736_ = lean_box(1);
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1736_, v_kvPairs_1735_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1738_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1739_ = lean_unsigned_to_nat(80u);
v___x_1740_ = l_Lean_Json_pretty(v_x_1734_, v___x_1739_);
v___x_1741_ = lean_string_append(v___x_1738_, v___x_1740_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1743_ = lean_string_append(v___x_1741_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1745_, lean_object* v_k_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = l_Lean_Json_getObjValD(v_j_1745_, v_k_1746_);
v___x_1748_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1749_, lean_object* v_k_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1749_, v_k_1750_);
lean_dec_ref(v_k_1750_);
return v_res_1751_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = 1;
v___x_1781_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1781_, v___x_1780_);
return v___x_1782_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1785_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1786_ = lean_string_append(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = 1;
v___x_1790_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1793_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1794_ = lean_string_append(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1797_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1798_ = lean_string_append(v___x_1797_, v___x_1796_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = 1;
v___x_1802_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1805_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1806_ = lean_string_append(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1808_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1809_ = lean_string_append(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = 1;
v___x_1813_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1814_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1813_, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1816_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1817_ = lean_string_append(v___x_1816_, v___x_1815_);
return v___x_1817_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1819_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1820_ = lean_string_append(v___x_1819_, v___x_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = 1;
v___x_1824_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1825_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1827_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1828_ = lean_string_append(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1830_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = 1;
v___x_1835_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1836_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1835_, v___x_1834_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1838_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1839_ = lean_string_append(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1841_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1842_ = lean_string_append(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = 1;
v___x_1846_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1847_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1846_, v___x_1845_);
return v___x_1847_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1849_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1850_ = lean_string_append(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1852_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1853_ = lean_string_append(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1854_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1854_);
v___x_1856_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1854_, v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_json_1854_);
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
v___x_1862_ = lean_string_append(v___x_1861_, v_a_1857_);
lean_dec(v_a_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
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
lean_object* v_a_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_a_1867_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1868_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1854_);
v___x_1869_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1854_, v___x_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_a_1867_);
lean_dec(v_json_1854_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1874_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
v___x_1875_ = lean_string_append(v___x_1874_, v_a_1870_);
lean_dec(v_a_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1875_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_a_1880_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1881_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1854_);
v___x_1882_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1854_, v___x_1881_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1880_);
lean_dec(v_a_1867_);
lean_dec(v_json_1854_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1888_ = lean_string_append(v___x_1887_, v_a_1883_);
lean_dec(v_a_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1894_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1854_);
v___x_1895_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1854_, v___x_1894_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1893_);
lean_dec(v_a_1880_);
lean_dec(v_a_1867_);
lean_dec(v_json_1854_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1905_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1905_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1900_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
v___x_1901_ = lean_string_append(v___x_1900_, v_a_1896_);
lean_dec(v_a_1896_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1901_);
v___x_1903_ = v___x_1898_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_a_1906_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1907_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1854_);
v___x_1908_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1854_, v___x_1907_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1906_);
lean_dec(v_a_1893_);
lean_dec(v_a_1880_);
lean_dec(v_a_1867_);
lean_dec(v_json_1854_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1918_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1918_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1913_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
v___x_1914_ = lean_string_append(v___x_1913_, v_a_1909_);
lean_dec(v_a_1909_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1914_);
v___x_1916_ = v___x_1911_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_a_1919_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1920_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1921_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1854_, v___x_1920_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_a_1919_);
lean_dec(v_a_1906_);
lean_dec(v_a_1893_);
lean_dec(v_a_1880_);
lean_dec(v_a_1867_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1926_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_1927_ = lean_string_append(v___x_1926_, v_a_1922_);
lean_dec(v_a_1922_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1927_);
v___x_1929_ = v___x_1924_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
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
v_a_1932_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1934_ = v___x_1921_;
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1921_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; uint64_t v___x_1937_; lean_object* v___x_1939_; 
v___x_1936_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1936_, 0, v_a_1867_);
lean_ctor_set(v___x_1936_, 1, v_a_1880_);
lean_ctor_set(v___x_1936_, 2, v_a_1893_);
lean_ctor_set(v___x_1936_, 3, v_a_1906_);
lean_ctor_set(v___x_1936_, 4, v_a_1932_);
v___x_1937_ = lean_unbox_uint64(v_a_1919_);
lean_dec(v_a_1919_);
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
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref_known(v___x_2063_, 1);
v___x_2064_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2056_, 2);
v___x_2065_ = l_System_FilePath_withExtension(v_val_2056_, v___x_2064_);
lean_inc_ref_n(v_configDir_2062_, 2);
v___x_2066_ = l_Lake_joinRelative(v_configDir_2062_, v___x_2065_);
v___x_2067_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2068_ = l_System_FilePath_withExtension(v_val_2056_, v___x_2067_);
v___x_2069_ = l_Lake_joinRelative(v_configDir_2062_, v___x_2068_);
v___x_2070_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2071_ = l_System_FilePath_withExtension(v_val_2056_, v___x_2070_);
v___x_2072_ = l_Lake_joinRelative(v_configDir_2062_, v___x_2071_);
v___x_2073_ = l_Lake_computeTextFileHash(v_configFile_2047_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v_h_2076_; lean_object* v_lakeOpts_2077_; lean_object* v___y_2078_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v_h_2257_; lean_object* v___y_2258_; uint8_t v___x_2346_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2346_ = l_System_FilePath_pathExists(v___x_2069_);
if (v___x_2346_ == 0)
{
uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = 1;
lean_inc_ref(v_pkgDir_2046_);
v___x_2348_ = l_Lake_joinRelative(v_pkgDir_2046_, v___x_2057_);
v___x_2349_ = l_IO_FS_createDirAll(v___x_2348_);
if (lean_obj_tag(v___x_2349_) == 0)
{
uint8_t v___x_2350_; lean_object* v___x_2351_; 
lean_dec_ref_known(v___x_2349_, 1);
v___x_2350_ = 2;
v___x_2351_ = lean_io_prim_handle_mk(v___x_2069_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2353_; 
lean_dec_ref(v___x_2072_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = lean_io_prim_handle_lock(v_a_2352_, v___x_2347_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_dec_ref_known(v___x_2353_, 1);
v_h_2076_ = v_a_2352_;
v_lakeOpts_2077_ = v_lakeOpts_2048_;
v___y_2078_ = v_a_2036_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec(v_a_2352_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = lean_io_error_to_string(v_a_2354_);
v___x_2356_ = 3;
v___x_2357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*1, v___x_2356_);
v___x_2358_ = lean_array_get_size(v_a_2036_);
v___x_2359_ = lean_array_push(v_a_2036_, v___x_2357_);
v___x_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
return v___x_2360_;
}
}
else
{
lean_object* v_a_2361_; 
v_a_2361_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2351_, 1);
if (lean_obj_tag(v_a_2361_) == 0)
{
uint8_t v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref_known(v_a_2361_, 2);
v___x_2362_ = 0;
v___x_2363_ = lean_io_prim_handle_mk(v___x_2069_, v___x_2362_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_h_2257_ = v_a_2364_;
v___y_2258_ = v_a_2036_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2365_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2366_ = lean_io_error_to_string(v_a_2365_);
v___x_2367_ = 3;
v___x_2368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*1, v___x_2367_);
v___x_2369_ = lean_array_get_size(v_a_2036_);
v___x_2370_ = lean_array_push(v_a_2036_, v___x_2368_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
return v___x_2371_;
}
}
else
{
lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2372_ = lean_io_error_to_string(v_a_2361_);
v___x_2373_ = 3;
v___x_2374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1, v___x_2373_);
v___x_2375_ = lean_array_get_size(v_a_2036_);
v___x_2376_ = lean_array_push(v_a_2036_, v___x_2374_);
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
return v___x_2377_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2378_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2379_ = lean_io_error_to_string(v_a_2378_);
v___x_2380_ = 3;
v___x_2381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2380_);
v___x_2382_ = lean_array_get_size(v_a_2036_);
v___x_2383_ = lean_array_push(v_a_2036_, v___x_2381_);
v___x_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
return v___x_2384_;
}
}
else
{
uint8_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = 0;
v___x_2386_ = lean_io_prim_handle_mk(v___x_2069_, v___x_2385_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v_h_2257_ = v_a_2387_;
v___y_2258_ = v_a_2036_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2388_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2389_ = lean_io_error_to_string(v_a_2388_);
v___x_2390_ = 3;
v___x_2391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*1, v___x_2390_);
v___x_2392_ = lean_array_get_size(v_a_2036_);
v___x_2393_ = lean_array_push(v_a_2036_, v___x_2391_);
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
return v___x_2394_;
}
}
v___jp_2075_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_io_remove_file(v___x_2066_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint64_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2079_, 1);
lean_dec_ref(v___x_2069_);
v___x_2080_ = l_System_Platform_target;
v___x_2081_ = l_Lake_Env_leanGithash(v_lakeEnv_2042_);
lean_dec_ref(v_lakeEnv_2042_);
lean_inc(v_lakeOpts_2077_);
lean_inc(v_pkgName_2045_);
lean_inc(v_pkgIdx_2044_);
v___x_2082_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2082_, 0, v_pkgIdx_2044_);
lean_ctor_set(v___x_2082_, 1, v_pkgName_2045_);
lean_ctor_set(v___x_2082_, 2, v___x_2080_);
lean_ctor_set(v___x_2082_, 3, v___x_2081_);
lean_ctor_set(v___x_2082_, 4, v_lakeOpts_2077_);
v___x_2083_ = lean_unbox_uint64(v_a_2074_);
lean_dec(v_a_2074_);
lean_ctor_set_uint64(v___x_2082_, sizeof(void*)*5, v___x_2083_);
v___x_2084_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2082_);
v___x_2085_ = lean_unsigned_to_nat(80u);
v___x_2086_ = l_Lean_Json_pretty(v___x_2084_, v___x_2085_);
v___x_2087_ = l_IO_FS_Handle_putStrLn(v_h_2076_, v___x_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2088_ = lean_io_prim_handle_flush(v_h_2076_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2089_ = lean_io_prim_handle_truncate(v_h_2076_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v___x_2090_; 
lean_dec_ref_known(v___x_2089_, 1);
v___x_2090_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2044_, v_pkgName_2045_, v_pkgDir_2046_, v_lakeOpts_2077_, v_leanOpts_2049_, v_configFile_2047_, v___y_2078_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v_a_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_a_2092_ = lean_ctor_get(v___x_2090_, 1);
v___x_2093_ = 1;
lean_inc(v_a_2091_);
v___x_2094_ = l_Lean_writeModule(v_a_2091_, v___x_2066_, v___x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; 
lean_dec_ref_known(v___x_2094_, 1);
v___x_2095_ = lean_io_prim_handle_unlock(v_h_2076_);
lean_dec(v_h_2076_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
return v___x_2090_;
}
else
{
lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2108_; 
lean_inc(v_a_2092_);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; lean_object* v_unused_2110_; 
v_unused_2109_ = lean_ctor_get(v___x_2090_, 1);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v___x_2090_, 0);
lean_dec(v_unused_2110_);
v___x_2097_ = v___x_2090_;
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
else
{
lean_dec(v___x_2090_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_a_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2100_ = lean_io_error_to_string(v_a_2099_);
v___x_2101_ = 3;
v___x_2102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*1, v___x_2101_);
v___x_2103_ = lean_array_get_size(v_a_2092_);
v___x_2104_ = lean_array_push(v_a_2092_, v___x_2102_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 1);
lean_ctor_set(v___x_2097_, 1, v___x_2104_);
lean_ctor_set(v___x_2097_, 0, v___x_2103_);
v___x_2106_ = v___x_2097_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2123_; 
lean_inc(v_a_2092_);
lean_dec(v_h_2076_);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; lean_object* v_unused_2125_; 
v_unused_2124_ = lean_ctor_get(v___x_2090_, 1);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v___x_2090_, 0);
lean_dec(v_unused_2125_);
v___x_2112_ = v___x_2090_;
v_isShared_2113_ = v_isSharedCheck_2123_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2090_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2123_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_a_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2115_ = lean_io_error_to_string(v_a_2114_);
v___x_2116_ = 3;
v___x_2117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1, v___x_2116_);
v___x_2118_ = lean_array_get_size(v_a_2092_);
v___x_2119_ = lean_array_push(v_a_2092_, v___x_2117_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 1);
lean_ctor_set(v___x_2112_, 1, v___x_2119_);
lean_ctor_set(v___x_2112_, 0, v___x_2118_);
v___x_2121_ = v___x_2112_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
return v___x_2090_;
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2126_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2127_ = lean_io_error_to_string(v_a_2126_);
v___x_2128_ = 3;
v___x_2129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*1, v___x_2128_);
v___x_2130_ = lean_array_get_size(v___y_2078_);
v___x_2131_ = lean_array_push(v___y_2078_, v___x_2129_);
v___x_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2133_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2134_ = lean_io_error_to_string(v_a_2133_);
v___x_2135_ = 3;
v___x_2136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*1, v___x_2135_);
v___x_2137_ = lean_array_get_size(v___y_2078_);
v___x_2138_ = lean_array_push(v___y_2078_, v___x_2136_);
v___x_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
return v___x_2139_;
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2140_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2141_ = lean_io_error_to_string(v_a_2140_);
v___x_2142_ = 3;
v___x_2143_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*1, v___x_2142_);
v___x_2144_ = lean_array_get_size(v___y_2078_);
v___x_2145_ = lean_array_push(v___y_2078_, v___x_2143_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2144_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
return v___x_2146_;
}
}
else
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2079_, 1);
if (lean_obj_tag(v_a_2147_) == 11)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint64_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref_known(v_a_2147_, 2);
lean_dec_ref(v___x_2069_);
v___x_2148_ = l_System_Platform_target;
v___x_2149_ = l_Lake_Env_leanGithash(v_lakeEnv_2042_);
lean_dec_ref(v_lakeEnv_2042_);
lean_inc(v_lakeOpts_2077_);
lean_inc(v_pkgName_2045_);
lean_inc(v_pkgIdx_2044_);
v___x_2150_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2150_, 0, v_pkgIdx_2044_);
lean_ctor_set(v___x_2150_, 1, v_pkgName_2045_);
lean_ctor_set(v___x_2150_, 2, v___x_2148_);
lean_ctor_set(v___x_2150_, 3, v___x_2149_);
lean_ctor_set(v___x_2150_, 4, v_lakeOpts_2077_);
v___x_2151_ = lean_unbox_uint64(v_a_2074_);
lean_dec(v_a_2074_);
lean_ctor_set_uint64(v___x_2150_, sizeof(void*)*5, v___x_2151_);
v___x_2152_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2150_);
v___x_2153_ = lean_unsigned_to_nat(80u);
v___x_2154_ = l_Lean_Json_pretty(v___x_2152_, v___x_2153_);
v___x_2155_ = l_IO_FS_Handle_putStrLn(v_h_2076_, v___x_2154_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref_known(v___x_2155_, 1);
v___x_2156_ = lean_io_prim_handle_flush(v_h_2076_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v___x_2157_; 
lean_dec_ref_known(v___x_2156_, 1);
v___x_2157_ = lean_io_prim_handle_truncate(v_h_2076_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2044_, v_pkgName_2045_, v_pkgDir_2046_, v_lakeOpts_2077_, v_leanOpts_2049_, v_configFile_2047_, v___y_2078_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_a_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_a_2160_ = lean_ctor_get(v___x_2158_, 1);
v___x_2161_ = 1;
lean_inc(v_a_2159_);
v___x_2162_ = l_Lean_writeModule(v_a_2159_, v___x_2066_, v___x_2161_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2163_; 
lean_dec_ref_known(v___x_2162_, 1);
v___x_2163_ = lean_io_prim_handle_unlock(v_h_2076_);
lean_dec(v_h_2076_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref_known(v___x_2163_, 1);
return v___x_2158_;
}
else
{
lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2176_; 
lean_inc(v_a_2160_);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; lean_object* v_unused_2178_; 
v_unused_2177_ = lean_ctor_get(v___x_2158_, 1);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v___x_2158_, 0);
lean_dec(v_unused_2178_);
v___x_2165_ = v___x_2158_;
v_isShared_2166_ = v_isSharedCheck_2176_;
goto v_resetjp_2164_;
}
else
{
lean_dec(v___x_2158_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2176_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_a_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2168_ = lean_io_error_to_string(v_a_2167_);
v___x_2169_ = 3;
v___x_2170_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*1, v___x_2169_);
v___x_2171_ = lean_array_get_size(v_a_2160_);
v___x_2172_ = lean_array_push(v_a_2160_, v___x_2170_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set_tag(v___x_2165_, 1);
lean_ctor_set(v___x_2165_, 1, v___x_2172_);
lean_ctor_set(v___x_2165_, 0, v___x_2171_);
v___x_2174_ = v___x_2165_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2191_; 
lean_inc(v_a_2160_);
lean_dec(v_h_2076_);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2192_ = lean_ctor_get(v___x_2158_, 1);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v___x_2158_, 0);
lean_dec(v_unused_2193_);
v___x_2180_ = v___x_2158_;
v_isShared_2181_ = v_isSharedCheck_2191_;
goto v_resetjp_2179_;
}
else
{
lean_dec(v___x_2158_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2191_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v_a_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v_a_2182_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2183_ = lean_io_error_to_string(v_a_2182_);
v___x_2184_ = 3;
v___x_2185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*1, v___x_2184_);
v___x_2186_ = lean_array_get_size(v_a_2160_);
v___x_2187_ = lean_array_push(v_a_2160_, v___x_2185_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set_tag(v___x_2180_, 1);
lean_ctor_set(v___x_2180_, 1, v___x_2187_);
lean_ctor_set(v___x_2180_, 0, v___x_2186_);
v___x_2189_ = v___x_2180_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
return v___x_2158_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2194_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2195_ = lean_io_error_to_string(v_a_2194_);
v___x_2196_ = 3;
v___x_2197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*1, v___x_2196_);
v___x_2198_ = lean_array_get_size(v___y_2078_);
v___x_2199_ = lean_array_push(v___y_2078_, v___x_2197_);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
return v___x_2200_;
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2201_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2202_ = lean_io_error_to_string(v_a_2201_);
v___x_2203_ = 3;
v___x_2204_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2203_);
v___x_2205_ = lean_array_get_size(v___y_2078_);
v___x_2206_ = lean_array_push(v___y_2078_, v___x_2204_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
return v___x_2207_;
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_h_2076_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
v_a_2208_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2209_ = lean_io_error_to_string(v_a_2208_);
v___x_2210_ = 3;
v___x_2211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*1, v___x_2210_);
v___x_2212_ = lean_array_get_size(v___y_2078_);
v___x_2213_ = lean_array_push(v___y_2078_, v___x_2211_);
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
return v___x_2214_;
}
}
else
{
lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec(v_lakeOpts_2077_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2215_ = lean_io_error_to_string(v_a_2147_);
v___x_2216_ = 3;
v___x_2217_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*1, v___x_2216_);
v___x_2218_ = lean_array_get_size(v___y_2078_);
v___x_2219_ = lean_array_push(v___y_2078_, v___x_2217_);
v___x_2220_ = lean_io_prim_handle_unlock(v_h_2076_);
lean_dec(v_h_2076_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref_known(v___x_2220_, 1);
v___x_2221_ = lean_io_remove_file(v___x_2069_);
lean_dec_ref(v___x_2069_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_dec_ref_known(v___x_2221_, 1);
v___y_2039_ = v___x_2218_;
v_a_2040_ = v___x_2219_;
goto v___jp_2038_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = lean_io_error_to_string(v_a_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*1, v___x_2216_);
v___x_2225_ = lean_array_push(v___x_2219_, v___x_2224_);
v___y_2039_ = v___x_2218_;
v_a_2040_ = v___x_2225_;
goto v___jp_2038_;
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v___x_2069_);
v_a_2226_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2227_ = lean_io_error_to_string(v_a_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set_uint8(v___x_2228_, sizeof(void*)*1, v___x_2216_);
v___x_2229_ = lean_array_push(v___x_2219_, v___x_2228_);
v___y_2039_ = v___x_2218_;
v_a_2040_ = v___x_2229_;
goto v___jp_2038_;
}
}
}
}
v___jp_2230_:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lake_importConfigFile___lam__0(v___x_2072_, v___x_2069_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___x_2072_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v_h_2076_ = v_a_2234_;
v_lakeOpts_2077_ = v_lakeOpts_2048_;
v___y_2078_ = v___y_2232_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2235_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2236_ = lean_io_error_to_string(v_a_2235_);
v___x_2237_ = 3;
v___x_2238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1, v___x_2237_);
v___x_2239_ = lean_array_get_size(v___y_2232_);
v___x_2240_ = lean_array_push(v___y_2232_, v___x_2238_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
return v___x_2241_;
}
}
v___jp_2242_:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lake_importConfigFile___lam__0(v___x_2072_, v___x_2069_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___x_2072_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v_options_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v_options_2248_ = lean_ctor_get(v___y_2244_, 4);
lean_inc(v_options_2248_);
lean_dec_ref(v___y_2244_);
v_h_2076_ = v_a_2247_;
v_lakeOpts_2077_ = v_options_2248_;
v___y_2078_ = v___y_2245_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref(v___y_2244_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2249_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2250_ = lean_io_error_to_string(v_a_2249_);
v___x_2251_ = 3;
v___x_2252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*1, v___x_2251_);
v___x_2253_ = lean_array_get_size(v___y_2245_);
v___x_2254_ = lean_array_push(v___y_2245_, v___x_2252_);
v___x_2255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
return v___x_2255_;
}
}
v___jp_2256_:
{
if (v_reconfigure_2050_ == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_io_prim_handle_lock(v_h_2257_, v_reconfigure_2050_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2260_; 
lean_dec_ref_known(v___x_2259_, 1);
v___x_2260_ = l_IO_FS_Handle_readToEnd(v_h_2257_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = l_Lean_Json_parse(v_a_2261_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___x_2263_; 
lean_dec_ref_known(v___x_2262_, 1);
v___x_2263_ = l_Lake_importConfigFile___lam__0(v___x_2072_, v___x_2069_, v_h_2257_);
lean_dec(v_h_2257_);
lean_dec_ref(v___x_2072_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2263_, 1);
v_h_2076_ = v_a_2264_;
v_lakeOpts_2077_ = v_lakeOpts_2048_;
v___y_2078_ = v___y_2258_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2265_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2263_, 1);
v___x_2266_ = lean_io_error_to_string(v_a_2265_);
v___x_2267_ = 3;
v___x_2268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set_uint8(v___x_2268_, sizeof(void*)*1, v___x_2267_);
v___x_2269_ = lean_array_get_size(v___y_2258_);
v___x_2270_ = lean_array_push(v___y_2258_, v___x_2268_);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
return v___x_2271_;
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_n(v_a_2272_, 2);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2273_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2272_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2274_; 
lean_dec_ref_known(v___x_2273_, 1);
v___x_2274_ = l_Lean_Json_getObj_x3f(v_a_2272_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_dec_ref_known(v___x_2274_, 1);
v___y_2231_ = v_h_2257_;
v___y_2232_ = v___y_2258_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2277_ = l_Lake_JsonObject_getJson_x3f(v_a_2275_, v___x_2276_);
lean_dec(v_a_2275_);
if (lean_obj_tag(v___x_2277_) == 0)
{
v___y_2231_ = v_h_2257_;
v___y_2232_ = v___y_2258_;
goto v___jp_2230_;
}
else
{
lean_object* v_val_2278_; lean_object* v___x_2279_; 
v_val_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2279_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref_known(v___x_2279_, 1);
v___y_2231_ = v_h_2257_;
v___y_2232_ = v___y_2258_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2281_; 
lean_dec(v_lakeOpts_2048_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = l_Lake_importConfigFile___lam__0(v___x_2072_, v___x_2069_, v_h_2257_);
lean_dec(v_h_2257_);
lean_dec_ref(v___x_2072_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v_h_2076_ = v_a_2282_;
v_lakeOpts_2077_ = v_a_2280_;
v___y_2078_ = v___y_2258_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec(v_a_2280_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2283_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2284_ = lean_io_error_to_string(v_a_2283_);
v___x_2285_ = 3;
v___x_2286_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*1, v___x_2285_);
v___x_2287_ = lean_array_get_size(v___y_2258_);
v___x_2288_ = lean_array_push(v___y_2258_, v___x_2286_);
v___x_2289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
return v___x_2289_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; uint8_t v___x_2291_; 
lean_dec(v_a_2272_);
lean_dec(v_lakeOpts_2048_);
v_a_2290_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2291_ = l_System_FilePath_pathExists(v___x_2066_);
if (v___x_2291_ == 0)
{
v___y_2243_ = v_h_2257_;
v___y_2244_ = v_a_2290_;
v___y_2245_ = v___y_2258_;
goto v___jp_2242_;
}
else
{
lean_object* v_idx_2292_; lean_object* v_name_2293_; lean_object* v_platform_2294_; lean_object* v_leanHash_2295_; uint64_t v_configHash_2296_; uint8_t v___x_2297_; 
v_idx_2292_ = lean_ctor_get(v_a_2290_, 0);
v_name_2293_ = lean_ctor_get(v_a_2290_, 1);
v_platform_2294_ = lean_ctor_get(v_a_2290_, 2);
v_leanHash_2295_ = lean_ctor_get(v_a_2290_, 3);
v_configHash_2296_ = lean_ctor_get_uint64(v_a_2290_, sizeof(void*)*5);
v___x_2297_ = lean_nat_dec_eq(v_idx_2292_, v_pkgIdx_2044_);
if (v___x_2297_ == 0)
{
v___y_2243_ = v_h_2257_;
v___y_2244_ = v_a_2290_;
v___y_2245_ = v___y_2258_;
goto v___jp_2242_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_name_eq(v_name_2293_, v_pkgName_2045_);
if (v___x_2298_ == 0)
{
v___y_2243_ = v_h_2257_;
v___y_2244_ = v_a_2290_;
v___y_2245_ = v___y_2258_;
goto v___jp_2242_;
}
else
{
uint64_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_unbox_uint64(v_a_2074_);
v___x_2300_ = lean_uint64_dec_eq(v_configHash_2296_, v___x_2299_);
if (v___x_2300_ == 0)
{
v___y_2243_ = v_h_2257_;
v___y_2244_ = v_a_2290_;
v___y_2245_ = v___y_2258_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = l_System_Platform_target;
v___x_2302_ = lean_string_dec_eq(v_platform_2294_, v___x_2301_);
if (v___x_2302_ == 0)
{
v___y_2243_ = v_h_2257_;
v___y_2244_ = v_a_2290_;
v___y_2245_ = v___y_2258_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = l_Lake_Env_leanGithash(v_lakeEnv_2042_);
v___x_2304_ = lean_string_dec_eq(v_leanHash_2295_, v___x_2303_);
lean_dec_ref(v___x_2303_);
if (v___x_2304_ == 0)
{
v___y_2243_ = v_h_2257_;
v___y_2244_ = v_a_2290_;
v___y_2245_ = v___y_2258_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2305_; 
lean_dec(v_a_2290_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v___x_2305_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2066_, v_leanOpts_2049_);
lean_dec_ref(v___x_2066_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = lean_io_prim_handle_unlock(v_h_2257_);
lean_dec(v_h_2257_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2308_; 
lean_dec_ref_known(v___x_2307_, 1);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v_a_2306_);
lean_ctor_set(v___x_2308_, 1, v___y_2258_);
return v___x_2308_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec(v_a_2306_);
v_a_2309_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2310_ = lean_io_error_to_string(v_a_2309_);
v___x_2311_ = 3;
v___x_2312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*1, v___x_2311_);
v___x_2313_ = lean_array_get_size(v___y_2258_);
v___x_2314_ = lean_array_push(v___y_2258_, v___x_2312_);
v___x_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
return v___x_2315_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec(v_h_2257_);
v_a_2316_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2317_ = lean_io_error_to_string(v_a_2316_);
v___x_2318_ = 3;
v___x_2319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*1, v___x_2318_);
v___x_2320_ = lean_array_get_size(v___y_2258_);
v___x_2321_ = lean_array_push(v___y_2258_, v___x_2319_);
v___x_2322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
return v___x_2322_;
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
lean_object* v_a_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_h_2257_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2323_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2324_ = lean_io_error_to_string(v_a_2323_);
v___x_2325_ = 3;
v___x_2326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*1, v___x_2325_);
v___x_2327_ = lean_array_get_size(v___y_2258_);
v___x_2328_ = lean_array_push(v___y_2258_, v___x_2326_);
v___x_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
return v___x_2329_;
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_h_2257_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2330_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2331_ = lean_io_error_to_string(v_a_2330_);
v___x_2332_ = 3;
v___x_2333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*1, v___x_2332_);
v___x_2334_ = lean_array_get_size(v___y_2258_);
v___x_2335_ = lean_array_push(v___y_2258_, v___x_2333_);
v___x_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
return v___x_2336_;
}
}
else
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lake_importConfigFile___lam__0(v___x_2072_, v___x_2069_, v_h_2257_);
lean_dec(v_h_2257_);
lean_dec_ref(v___x_2072_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_h_2076_ = v_a_2338_;
v_lakeOpts_2077_ = v_lakeOpts_2048_;
v___y_2078_ = v___y_2258_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2339_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2340_ = lean_io_error_to_string(v_a_2339_);
v___x_2341_ = 3;
v___x_2342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*1, v___x_2341_);
v___x_2343_ = lean_array_get_size(v___y_2258_);
v___x_2344_ = lean_array_push(v___y_2258_, v___x_2342_);
v___x_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
return v___x_2345_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2395_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2073_, 1);
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
lean_object* v_a_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_configDir_2062_);
lean_dec(v_val_2056_);
lean_dec_ref(v_leanOpts_2049_);
lean_dec(v_lakeOpts_2048_);
lean_dec_ref(v_configFile_2047_);
lean_dec_ref(v_pkgDir_2046_);
lean_dec(v_pkgName_2045_);
lean_dec(v_pkgIdx_2044_);
lean_dec_ref(v_lakeEnv_2042_);
v_a_2402_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2403_ = lean_io_error_to_string(v_a_2402_);
v___x_2404_ = 3;
v___x_2405_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set_uint8(v___x_2405_, sizeof(void*)*1, v___x_2404_);
v___x_2406_ = lean_array_get_size(v_a_2036_);
v___x_2407_ = lean_array_push(v_a_2036_, v___x_2405_);
v___x_2408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
return v___x_2408_;
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
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lake_importConfigFile(v_cfg_2409_, v_a_2410_);
return v_res_2412_;
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
res = l___private_Lake_Load_Lean_Elab_0__Lake_initFn_00___x40_Lake_Load_Lean_Elab_851604885____hygCtx___hyg_2_();
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
