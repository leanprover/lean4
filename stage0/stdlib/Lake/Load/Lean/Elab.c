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
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__48));
v___x_935_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__45);
v___x_936_ = l_Lean_NameSet_insert(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__52));
v___x_944_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__49);
v___x_945_ = l_Lean_NameSet_insert(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts(void){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53, &l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts___closed__53);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0(lean_object* v_addEntryFn_947_, lean_object* v___x_948_, lean_object* v_s_949_){
_start:
{
lean_object* v_importedEntries_950_; lean_object* v_state_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
v_importedEntries_950_ = lean_ctor_get(v_s_949_, 0);
v_state_951_ = lean_ctor_get(v_s_949_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_s_949_);
if (v_isSharedCheck_959_ == 0)
{
v___x_953_ = v_s_949_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_state_951_);
lean_inc(v_importedEntries_950_);
lean_dec(v_s_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_state_955_; lean_object* v___x_957_; 
v_state_955_ = lean_apply_2(v_addEntryFn_947_, v_state_951_, v___x_948_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_state_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_importedEntries_950_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_state_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_instInhabitedPersistentEnvExtension___redArg();
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(lean_object* v_val_961_, lean_object* v_val_962_, uint8_t v___x_963_, lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_){
_start:
{
lean_object* v___y_969_; uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_toEnvExtension_976_; lean_object* v_addEntryFn_977_; uint8_t v_logWrites_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_974_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___closed__0);
v___x_975_ = lean_array_get_borrowed(v___x_974_, v_val_961_, v_val_962_);
v_toEnvExtension_976_ = lean_ctor_get(v___x_975_, 0);
v_addEntryFn_977_ = lean_ctor_get(v___x_975_, 3);
v_logWrites_978_ = lean_ctor_get_uint8(v_toEnvExtension_976_, sizeof(void*)*6);
v___x_979_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
lean_inc(v___x_979_);
lean_inc(v_addEntryFn_977_);
v___f_980_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_980_, 0, v_addEntryFn_977_);
lean_closure_set(v___f_980_, 1, v___x_979_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_box(0);
if (v_logWrites_978_ == 0)
{
lean_object* v___x_983_; 
lean_inc_ref(v_toEnvExtension_976_);
v___x_983_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_976_, v_b_967_, v___f_980_, v___x_981_, v___x_982_, v___x_963_);
v___y_969_ = v___x_983_;
goto v___jp_968_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_inc_ref_n(v_toEnvExtension_976_, 2);
v___x_984_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_976_, v_b_967_);
lean_dec_ref(v_b_967_);
v___x_985_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_976_, v___x_984_, v___f_980_, v___x_981_, v___x_982_, v___x_963_);
v___y_969_ = v___x_985_;
goto v___jp_968_;
}
}
else
{
return v_b_967_;
}
v___jp_968_:
{
size_t v___x_970_; size_t v___x_971_; 
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_965_, v___x_970_);
v_i_965_ = v___x_971_;
v_b_967_ = v___y_969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1___boxed(lean_object* v_val_986_, lean_object* v_val_987_, lean_object* v___x_988_, lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_, lean_object* v_b_992_){
_start:
{
uint8_t v___x_1499__boxed_993_; size_t v_i_boxed_994_; size_t v_stop_boxed_995_; lean_object* v_res_996_; 
v___x_1499__boxed_993_ = lean_unbox(v___x_988_);
v_i_boxed_994_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_995_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_986_, v_val_987_, v___x_1499__boxed_993_, v_as_989_, v_i_boxed_994_, v_stop_boxed_995_, v_b_992_);
lean_dec_ref(v_as_989_);
lean_dec(v_val_987_);
lean_dec_ref(v_val_986_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(lean_object* v_a_997_, lean_object* v_x_998_){
_start:
{
if (lean_obj_tag(v_x_998_) == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
else
{
lean_object* v_key_1000_; lean_object* v_value_1001_; lean_object* v_tail_1002_; uint8_t v___x_1003_; 
v_key_1000_ = lean_ctor_get(v_x_998_, 0);
v_value_1001_ = lean_ctor_get(v_x_998_, 1);
v_tail_1002_ = lean_ctor_get(v_x_998_, 2);
v___x_1003_ = lean_name_eq(v_key_1000_, v_a_997_);
if (v___x_1003_ == 0)
{
v_x_998_ = v_tail_1002_;
goto _start;
}
else
{
lean_object* v___x_1005_; 
lean_inc(v_value_1001_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_value_1001_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1006_, v_x_1007_);
lean_dec(v_x_1007_);
lean_dec(v_a_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(lean_object* v_m_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_buckets_1011_; lean_object* v___x_1012_; uint64_t v___y_1014_; 
v_buckets_1011_ = lean_ctor_get(v_m_1009_, 1);
v___x_1012_ = lean_array_get_size(v_buckets_1011_);
if (lean_obj_tag(v_a_1010_) == 0)
{
uint64_t v___x_1028_; 
v___x_1028_ = 1723ULL;
v___y_1014_ = v___x_1028_;
goto v___jp_1013_;
}
else
{
uint64_t v_hash_1029_; 
v_hash_1029_ = lean_ctor_get_uint64(v_a_1010_, sizeof(void*)*2);
v___y_1014_ = v_hash_1029_;
goto v___jp_1013_;
}
v___jp_1013_:
{
uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v_fold_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; uint64_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1015_ = 32ULL;
v___x_1016_ = lean_uint64_shift_right(v___y_1014_, v___x_1015_);
v_fold_1017_ = lean_uint64_xor(v___y_1014_, v___x_1016_);
v___x_1018_ = 16ULL;
v___x_1019_ = lean_uint64_shift_right(v_fold_1017_, v___x_1018_);
v___x_1020_ = lean_uint64_xor(v_fold_1017_, v___x_1019_);
v___x_1021_ = lean_uint64_to_usize(v___x_1020_);
v___x_1022_ = lean_usize_of_nat(v___x_1012_);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_sub(v___x_1022_, v___x_1023_);
v___x_1025_ = lean_usize_land(v___x_1021_, v___x_1024_);
v___x_1026_ = lean_array_uget_borrowed(v_buckets_1011_, v___x_1025_);
v___x_1027_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1010_, v___x_1026_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg___boxed(lean_object* v_m_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_m_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(lean_object* v_a_1033_, lean_object* v_val_1034_, lean_object* v_as_1035_, size_t v_i_1036_, size_t v_stop_1037_, lean_object* v_b_1038_){
_start:
{
lean_object* v___y_1040_; uint8_t v___x_1044_; 
v___x_1044_ = lean_usize_dec_eq(v_i_1036_, v_stop_1037_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1045_ = lean_array_uget_borrowed(v_as_1035_, v_i_1036_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
v_snd_1047_ = lean_ctor_get(v___x_1045_, 1);
v___x_1048_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_lakeExts;
v___x_1049_ = l_Lean_NameSet_contains(v___x_1048_, v_fst_1046_);
if (v___x_1049_ == 0)
{
v___y_1040_ = v_b_1038_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_a_1033_, v_fst_1046_);
if (lean_obj_tag(v___x_1050_) == 0)
{
v___y_1040_ = v_b_1038_;
goto v___jp_1039_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_array_get_size(v_snd_1047_);
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v_val_1051_);
v___y_1040_ = v_b_1038_;
goto v___jp_1039_;
}
else
{
size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = lean_usize_of_nat(v___x_1053_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__1(v_val_1034_, v_val_1051_, v___x_1049_, v_snd_1047_, v___x_1055_, v___x_1056_, v_b_1038_);
lean_dec(v_val_1051_);
v___y_1040_ = v___x_1057_;
goto v___jp_1039_;
}
}
}
}
else
{
return v_b_1038_;
}
v___jp_1039_:
{
size_t v___x_1041_; size_t v___x_1042_; 
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1036_, v___x_1041_);
v_i_1036_ = v___x_1042_;
v_b_1038_ = v___y_1040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2___boxed(lean_object* v_a_1058_, lean_object* v_val_1059_, lean_object* v_as_1060_, lean_object* v_i_1061_, lean_object* v_stop_1062_, lean_object* v_b_1063_){
_start:
{
size_t v_i_boxed_1064_; size_t v_stop_boxed_1065_; lean_object* v_res_1066_; 
v_i_boxed_1064_ = lean_unbox_usize(v_i_1061_);
lean_dec(v_i_1061_);
v_stop_boxed_1065_ = lean_unbox_usize(v_stop_1062_);
lean_dec(v_stop_1062_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1058_, v_val_1059_, v_as_1060_, v_i_boxed_1064_, v_stop_boxed_1065_, v_b_1063_);
lean_dec_ref(v_as_1060_);
lean_dec_ref(v_val_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(lean_object* v_as_1067_, size_t v_i_1068_, size_t v_stop_1069_, lean_object* v_b_1070_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_eq(v_i_1068_, v_stop_1069_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; 
v___x_1072_ = lean_array_uget_borrowed(v_as_1067_, v_i_1068_);
lean_inc(v___x_1072_);
v___x_1073_ = lake_environment_add(v_b_1070_, v___x_1072_);
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_add(v_i_1068_, v___x_1074_);
v_i_1068_ = v___x_1075_;
v_b_1070_ = v___x_1073_;
goto _start;
}
else
{
return v_b_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3___boxed(lean_object* v_as_1077_, lean_object* v_i_1078_, lean_object* v_stop_1079_, lean_object* v_b_1080_){
_start:
{
size_t v_i_boxed_1081_; size_t v_stop_boxed_1082_; lean_object* v_res_1083_; 
v_i_boxed_1081_ = lean_unbox_usize(v_i_1078_);
lean_dec(v_i_1078_);
v_stop_boxed_1082_ = lean_unbox_usize(v_stop_1079_);
lean_dec(v_stop_1079_);
v_res_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_as_1077_, v_i_boxed_1081_, v_stop_boxed_1082_, v_b_1080_);
lean_dec_ref(v_as_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(lean_object* v_olean_1084_, lean_object* v_leanOpts_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_readModuleData(v_olean_1084_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v_fst_1089_; lean_object* v_imports_1090_; lean_object* v_constants_1091_; lean_object* v_entries_1092_; uint32_t v___x_1093_; lean_object* v___x_1094_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v_fst_1089_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_fst_1089_);
lean_dec(v_a_1088_);
v_imports_1090_ = lean_ctor_get(v_fst_1089_, 0);
lean_inc_ref(v_imports_1090_);
v_constants_1091_ = lean_ctor_get(v_fst_1089_, 2);
lean_inc_ref(v_constants_1091_);
v_entries_1092_ = lean_ctor_get(v_fst_1089_, 4);
lean_inc_ref(v_entries_1092_);
lean_dec(v_fst_1089_);
v___x_1093_ = 1024;
v___x_1094_ = l_Lake_importModulesUsingCache(v_imports_1090_, v_leanOpts_1085_, v___x_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___y_1098_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_array_get_size(v_constants_1091_);
v___x_1127_ = lean_nat_dec_lt(v___x_1096_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_dec_ref(v_constants_1091_);
v___y_1098_ = v_a_1095_;
goto v___jp_1097_;
}
else
{
size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = lean_usize_of_nat(v___x_1126_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__3(v_constants_1091_, v___x_1128_, v___x_1129_, v_a_1095_);
lean_dec_ref(v_constants_1091_);
v___y_1098_ = v___x_1130_;
goto v___jp_1097_;
}
v___jp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = l_Lean_persistentEnvExtensionsRef;
v___x_1100_ = lean_st_ref_get(v___x_1099_);
v___x_1101_ = l_Lean_mkExtNameMap(v___x_1096_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1117_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1117_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1117_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_array_get_size(v_entries_1092_);
v___x_1107_ = lean_nat_dec_lt(v___x_1096_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1109_; 
lean_dec(v_a_1102_);
lean_dec(v___x_1100_);
lean_dec_ref(v_entries_1092_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___y_1098_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___y_1098_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
else
{
size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = lean_usize_of_nat(v___x_1106_);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__2(v_a_1102_, v___x_1100_, v_entries_1092_, v___x_1111_, v___x_1112_, v___y_1098_);
lean_dec_ref(v_entries_1092_);
lean_dec(v___x_1100_);
lean_dec(v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1113_);
v___x_1115_ = v___x_1104_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v___x_1100_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_entries_1092_);
v_a_1118_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1101_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1101_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
else
{
lean_dec_ref(v_entries_1092_);
lean_dec_ref(v_constants_1091_);
return v___x_1094_;
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_leanOpts_1085_);
v_a_1131_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1087_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1087_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore___boxed(lean_object* v_olean_1139_, lean_object* v_leanOpts_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v_olean_1139_, v_leanOpts_1140_);
lean_dec_ref(v_olean_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___redArg(v_m_1144_, v_a_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_m_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0(v_00_u03b2_1147_, v_m_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_m_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(lean_object* v_00_u03b2_1151_, lean_object* v_a_1152_, lean_object* v_x_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___redArg(v_a_1152_, v_x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore_spec__0_spec__0(v_00_u03b2_1155_, v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec(v_a_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(1);
v___x_1161_ = lean_panic_fn_borrowed(v___x_1160_, v_msg_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1166_ = lean_unsigned_to_nat(35u);
v___x_1167_ = lean_unsigned_to_nat(182u);
v___x_1168_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1169_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1170_ = l_mkPanicMessageWithDecl(v___x_1169_, v___x_1168_, v___x_1167_, v___x_1166_, v___x_1165_);
return v___x_1170_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1171_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__2));
v___x_1172_ = lean_unsigned_to_nat(21u);
v___x_1173_ = lean_unsigned_to_nat(183u);
v___x_1174_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__1));
v___x_1175_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1176_ = l_mkPanicMessageWithDecl(v___x_1175_, v___x_1174_, v___x_1173_, v___x_1172_, v___x_1171_);
return v___x_1176_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1179_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1180_ = lean_unsigned_to_nat(35u);
v___x_1181_ = lean_unsigned_to_nat(276u);
v___x_1182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1183_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1184_ = l_mkPanicMessageWithDecl(v___x_1183_, v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_);
return v___x_1184_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1185_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__6));
v___x_1186_ = lean_unsigned_to_nat(21u);
v___x_1187_ = lean_unsigned_to_nat(277u);
v___x_1188_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__5));
v___x_1189_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__0));
v___x_1190_ = l_mkPanicMessageWithDecl(v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_, v___x_1185_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(lean_object* v_k_1191_, lean_object* v_v_1192_, lean_object* v_t_1193_){
_start:
{
if (lean_obj_tag(v_t_1193_) == 0)
{
lean_object* v_size_1194_; lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v_l_1197_; lean_object* v_r_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1554_; 
v_size_1194_ = lean_ctor_get(v_t_1193_, 0);
v_k_1195_ = lean_ctor_get(v_t_1193_, 1);
v_v_1196_ = lean_ctor_get(v_t_1193_, 2);
v_l_1197_ = lean_ctor_get(v_t_1193_, 3);
v_r_1198_ = lean_ctor_get(v_t_1193_, 4);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_t_1193_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1200_ = v_t_1193_;
v_isShared_1201_ = v_isSharedCheck_1554_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_r_1198_);
lean_inc(v_l_1197_);
lean_inc(v_v_1196_);
lean_inc(v_k_1195_);
lean_inc(v_size_1194_);
lean_dec(v_t_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1554_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_string_compare(v_k_1191_, v_k_1195_);
switch(v___x_1202_)
{
case 0:
{
lean_object* v___x_1203_; 
lean_dec(v_size_1194_);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1191_, v_v_1192_, v_l_1197_);
if (lean_obj_tag(v_r_1198_) == 0)
{
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_size_1204_; lean_object* v_size_1205_; lean_object* v_k_1206_; lean_object* v_v_1207_; lean_object* v_l_1208_; lean_object* v_r_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_size_1204_ = lean_ctor_get(v_r_1198_, 0);
v_size_1205_ = lean_ctor_get(v___x_1203_, 0);
v_k_1206_ = lean_ctor_get(v___x_1203_, 1);
v_v_1207_ = lean_ctor_get(v___x_1203_, 2);
v_l_1208_ = lean_ctor_get(v___x_1203_, 3);
v_r_1209_ = lean_ctor_get(v___x_1203_, 4);
lean_inc(v_r_1209_);
v___x_1210_ = lean_unsigned_to_nat(3u);
v___x_1211_ = lean_nat_mul(v___x_1210_, v_size_1204_);
v___x_1212_ = lean_nat_dec_lt(v___x_1211_, v_size_1205_);
lean_dec(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec(v_r_1209_);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_nat_add(v___x_1213_, v_size_1205_);
v___x_1215_ = lean_nat_add(v___x_1214_, v_size_1204_);
lean_dec(v___x_1214_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 3, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1215_);
v___x_1217_ = v___x_1200_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_r_1198_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
else
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1290_; 
lean_inc(v_l_1208_);
lean_inc(v_v_1207_);
lean_inc(v_k_1206_);
lean_inc(v_size_1205_);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; 
v_unused_1291_ = lean_ctor_get(v___x_1203_, 4);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v___x_1203_, 3);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v___x_1203_, 2);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v___x_1203_, 1);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1295_);
v___x_1220_ = v___x_1203_;
v_isShared_1221_ = v_isSharedCheck_1290_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1203_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1290_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
if (lean_obj_tag(v_l_1208_) == 0)
{
if (lean_obj_tag(v_r_1209_) == 0)
{
lean_object* v_size_1222_; lean_object* v_size_1223_; lean_object* v_k_1224_; lean_object* v_v_1225_; lean_object* v_l_1226_; lean_object* v_r_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_size_1222_ = lean_ctor_get(v_l_1208_, 0);
v_size_1223_ = lean_ctor_get(v_r_1209_, 0);
v_k_1224_ = lean_ctor_get(v_r_1209_, 1);
v_v_1225_ = lean_ctor_get(v_r_1209_, 2);
v_l_1226_ = lean_ctor_get(v_r_1209_, 3);
v_r_1227_ = lean_ctor_get(v_r_1209_, 4);
v___x_1228_ = lean_unsigned_to_nat(2u);
v___x_1229_ = lean_nat_mul(v___x_1228_, v_size_1222_);
v___x_1230_ = lean_nat_dec_lt(v_size_1223_, v___x_1229_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1260_; 
lean_inc(v_r_1227_);
lean_inc(v_l_1226_);
lean_inc(v_v_1225_);
lean_inc(v_k_1224_);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_r_1209_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; lean_object* v_unused_1262_; lean_object* v_unused_1263_; lean_object* v_unused_1264_; lean_object* v_unused_1265_; 
v_unused_1261_ = lean_ctor_get(v_r_1209_, 4);
lean_dec(v_unused_1261_);
v_unused_1262_ = lean_ctor_get(v_r_1209_, 3);
lean_dec(v_unused_1262_);
v_unused_1263_ = lean_ctor_get(v_r_1209_, 2);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v_r_1209_, 1);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_r_1209_, 0);
lean_dec(v_unused_1265_);
v___x_1232_ = v_r_1209_;
v_isShared_1233_ = v_isSharedCheck_1260_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v_r_1209_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1260_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___x_1248_; lean_object* v___y_1250_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v___x_1234_, v_size_1205_);
lean_dec(v_size_1205_);
v___x_1236_ = lean_nat_add(v___x_1235_, v_size_1204_);
lean_dec(v___x_1235_);
v___x_1248_ = lean_nat_add(v___x_1234_, v_size_1222_);
if (lean_obj_tag(v_l_1226_) == 0)
{
lean_object* v_size_1258_; 
v_size_1258_ = lean_ctor_get(v_l_1226_, 0);
lean_inc(v_size_1258_);
v___y_1250_ = v_size_1258_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___y_1250_ = v___x_1259_;
goto v___jp_1249_;
}
v___jp_1237_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_nat_add(v___y_1238_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec(v___y_1238_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 4, v_r_1198_);
lean_ctor_set(v___x_1232_, 3, v_r_1227_);
lean_ctor_set(v___x_1232_, 2, v_v_1196_);
lean_ctor_set(v___x_1232_, 1, v_k_1195_);
lean_ctor_set(v___x_1232_, 0, v___x_1241_);
v___x_1243_ = v___x_1232_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_r_1227_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_r_1198_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 4, v___x_1243_);
lean_ctor_set(v___x_1220_, 3, v___y_1239_);
lean_ctor_set(v___x_1220_, 2, v_v_1225_);
lean_ctor_set(v___x_1220_, 1, v_k_1224_);
lean_ctor_set(v___x_1220_, 0, v___x_1236_);
v___x_1245_ = v___x_1220_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1224_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1225_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v___y_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_nat_add(v___x_1248_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec(v___x_1248_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_l_1226_);
lean_ctor_set(v___x_1200_, 3, v_l_1208_);
lean_ctor_set(v___x_1200_, 2, v_v_1207_);
lean_ctor_set(v___x_1200_, 1, v_k_1206_);
lean_ctor_set(v___x_1200_, 0, v___x_1251_);
v___x_1253_ = v___x_1200_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_k_1206_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_v_1207_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_l_1208_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_l_1226_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_nat_add(v___x_1234_, v_size_1204_);
if (lean_obj_tag(v_r_1227_) == 0)
{
lean_object* v_size_1255_; 
v_size_1255_ = lean_ctor_get(v_r_1227_, 0);
lean_inc(v_size_1255_);
v___y_1238_ = v___x_1254_;
v___y_1239_ = v___x_1253_;
v___y_1240_ = v_size_1255_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___y_1238_ = v___x_1254_;
v___y_1239_ = v___x_1253_;
v___y_1240_ = v___x_1256_;
goto v___jp_1237_;
}
}
}
}
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
lean_del_object(v___x_1200_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v___x_1266_, v_size_1205_);
lean_dec(v_size_1205_);
v___x_1268_ = lean_nat_add(v___x_1267_, v_size_1204_);
lean_dec(v___x_1267_);
v___x_1269_ = lean_nat_add(v___x_1266_, v_size_1204_);
v___x_1270_ = lean_nat_add(v___x_1269_, v_size_1223_);
lean_dec(v___x_1269_);
lean_inc_ref(v_r_1198_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 4, v_r_1198_);
lean_ctor_set(v___x_1220_, 3, v_r_1209_);
lean_ctor_set(v___x_1220_, 2, v_v_1196_);
lean_ctor_set(v___x_1220_, 1, v_k_1195_);
lean_ctor_set(v___x_1220_, 0, v___x_1270_);
v___x_1272_ = v___x_1220_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_r_1209_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_r_1198_);
v___x_1272_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_isSharedCheck_1279_ = !lean_is_exclusive(v_r_1198_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; lean_object* v_unused_1281_; lean_object* v_unused_1282_; lean_object* v_unused_1283_; lean_object* v_unused_1284_; 
v_unused_1280_ = lean_ctor_get(v_r_1198_, 4);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v_r_1198_, 3);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_r_1198_, 2);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_r_1198_, 1);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v_r_1198_, 0);
lean_dec(v_unused_1284_);
v___x_1274_ = v_r_1198_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v_r_1198_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 4, v___x_1272_);
lean_ctor_set(v___x_1274_, 3, v_l_1208_);
lean_ctor_set(v___x_1274_, 2, v_v_1207_);
lean_ctor_set(v___x_1274_, 1, v_k_1206_);
lean_ctor_set(v___x_1274_, 0, v___x_1268_);
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1206_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1207_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_l_1208_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v___x_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref_known(v_l_1208_, 5);
lean_del_object(v___x_1220_);
lean_dec(v_v_1207_);
lean_dec(v_k_1206_);
lean_dec(v_size_1205_);
lean_dec_ref_known(v_r_1198_, 5);
lean_del_object(v___x_1200_);
lean_dec(v_v_1196_);
lean_dec(v_k_1195_);
v___x_1286_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__3);
v___x_1287_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1286_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_del_object(v___x_1220_);
lean_dec(v_r_1209_);
lean_dec(v_v_1207_);
lean_dec(v_k_1206_);
lean_dec(v_size_1205_);
lean_dec_ref_known(v_r_1198_, 5);
lean_del_object(v___x_1200_);
lean_dec(v_v_1196_);
lean_dec(v_k_1195_);
v___x_1288_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__4);
v___x_1289_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1288_);
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_size_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_size_1296_ = lean_ctor_get(v_r_1198_, 0);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v___x_1297_, v_size_1296_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 3, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1298_);
v___x_1300_ = v___x_1200_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v_r_1198_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_l_1302_; 
v_l_1302_ = lean_ctor_get(v___x_1203_, 3);
if (lean_obj_tag(v_l_1302_) == 0)
{
lean_object* v_r_1303_; 
lean_inc_ref(v_l_1302_);
v_r_1303_ = lean_ctor_get(v___x_1203_, 4);
lean_inc(v_r_1303_);
if (lean_obj_tag(v_r_1303_) == 0)
{
lean_object* v_size_1304_; lean_object* v_k_1305_; lean_object* v_v_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1320_; 
v_size_1304_ = lean_ctor_get(v___x_1203_, 0);
v_k_1305_ = lean_ctor_get(v___x_1203_, 1);
v_v_1306_ = lean_ctor_get(v___x_1203_, 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; lean_object* v_unused_1322_; 
v_unused_1321_ = lean_ctor_get(v___x_1203_, 4);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v___x_1203_, 3);
lean_dec(v_unused_1322_);
v___x_1308_ = v___x_1203_;
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_v_1306_);
lean_inc(v_k_1305_);
lean_inc(v_size_1304_);
lean_dec(v___x_1203_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_size_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v_size_1310_ = lean_ctor_get(v_r_1303_, 0);
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = lean_nat_add(v___x_1311_, v_size_1304_);
lean_dec(v_size_1304_);
v___x_1313_ = lean_nat_add(v___x_1311_, v_size_1310_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 4, v_r_1198_);
lean_ctor_set(v___x_1308_, 3, v_r_1303_);
lean_ctor_set(v___x_1308_, 2, v_v_1196_);
lean_ctor_set(v___x_1308_, 1, v_k_1195_);
lean_ctor_set(v___x_1308_, 0, v___x_1313_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_r_1303_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_r_1198_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1315_);
lean_ctor_set(v___x_1200_, 3, v_l_1302_);
lean_ctor_set(v___x_1200_, 2, v_v_1306_);
lean_ctor_set(v___x_1200_, 1, v_k_1305_);
lean_ctor_set(v___x_1200_, 0, v___x_1312_);
v___x_1317_ = v___x_1200_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_k_1305_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_v_1306_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_l_1302_);
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
else
{
lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1336_; 
v_k_1323_ = lean_ctor_get(v___x_1203_, 1);
v_v_1324_ = lean_ctor_get(v___x_1203_, 2);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1337_ = lean_ctor_get(v___x_1203_, 4);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v___x_1203_, 3);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1339_);
v___x_1326_ = v___x_1203_;
v_isShared_1327_ = v_isSharedCheck_1336_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_v_1324_);
lean_inc(v_k_1323_);
lean_dec(v___x_1203_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1336_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_unsigned_to_nat(3u);
v___x_1329_ = lean_unsigned_to_nat(1u);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 3, v_r_1303_);
lean_ctor_set(v___x_1326_, 2, v_v_1196_);
lean_ctor_set(v___x_1326_, 1, v_k_1195_);
lean_ctor_set(v___x_1326_, 0, v___x_1329_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_r_1303_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_r_1303_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1331_);
lean_ctor_set(v___x_1200_, 3, v_l_1302_);
lean_ctor_set(v___x_1200_, 2, v_v_1324_);
lean_ctor_set(v___x_1200_, 1, v_k_1323_);
lean_ctor_set(v___x_1200_, 0, v___x_1328_);
v___x_1333_ = v___x_1200_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_l_1302_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v_r_1340_; 
v_r_1340_ = lean_ctor_get(v___x_1203_, 4);
lean_inc(v_r_1340_);
if (lean_obj_tag(v_r_1340_) == 0)
{
lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1366_; 
lean_inc(v_l_1302_);
v_k_1341_ = lean_ctor_get(v___x_1203_, 1);
v_v_1342_ = lean_ctor_get(v___x_1203_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1367_ = lean_ctor_get(v___x_1203_, 4);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v___x_1203_, 3);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1369_);
v___x_1344_ = v___x_1203_;
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_v_1342_);
lean_inc(v_k_1341_);
lean_dec(v___x_1203_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1362_; 
v_k_1346_ = lean_ctor_get(v_r_1340_, 1);
v_v_1347_ = lean_ctor_get(v_r_1340_, 2);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_r_1340_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1363_ = lean_ctor_get(v_r_1340_, 4);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_r_1340_, 3);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_r_1340_, 0);
lean_dec(v_unused_1365_);
v___x_1349_ = v_r_1340_;
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_v_1347_);
lean_inc(v_k_1346_);
lean_dec(v_r_1340_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(3u);
v___x_1352_ = lean_unsigned_to_nat(1u);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v_l_1302_);
lean_ctor_set(v___x_1349_, 3, v_l_1302_);
lean_ctor_set(v___x_1349_, 2, v_v_1342_);
lean_ctor_set(v___x_1349_, 1, v_k_1341_);
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_l_1302_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_l_1302_);
v___x_1354_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 4, v_l_1302_);
lean_ctor_set(v___x_1344_, 2, v_v_1196_);
lean_ctor_set(v___x_1344_, 1, v_k_1195_);
lean_ctor_set(v___x_1344_, 0, v___x_1352_);
v___x_1356_ = v___x_1344_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_l_1302_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_l_1302_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1356_);
lean_ctor_set(v___x_1200_, 3, v___x_1354_);
lean_ctor_set(v___x_1200_, 2, v_v_1347_);
lean_ctor_set(v___x_1200_, 1, v_k_1346_);
lean_ctor_set(v___x_1200_, 0, v___x_1351_);
v___x_1358_ = v___x_1200_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_k_1346_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_v_1347_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_unsigned_to_nat(2u);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_r_1340_);
lean_ctor_set(v___x_1200_, 3, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1370_);
v___x_1372_ = v___x_1200_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1340_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1203_);
lean_ctor_set(v___x_1200_, 3, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1374_);
v___x_1376_ = v___x_1200_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v___x_1203_);
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
case 1:
{
lean_object* v___x_1379_; 
lean_dec(v_v_1196_);
lean_dec(v_k_1195_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 2, v_v_1192_);
lean_ctor_set(v___x_1200_, 1, v_k_1191_);
v___x_1379_ = v___x_1200_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_size_1194_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_k_1191_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_v_1192_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_r_1198_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
default: 
{
lean_object* v___x_1381_; 
lean_dec(v_size_1194_);
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1191_, v_v_1192_, v_r_1198_);
if (lean_obj_tag(v_l_1197_) == 0)
{
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_size_1382_; lean_object* v_size_1383_; lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_l_1386_; lean_object* v_r_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_size_1382_ = lean_ctor_get(v_l_1197_, 0);
v_size_1383_ = lean_ctor_get(v___x_1381_, 0);
v_k_1384_ = lean_ctor_get(v___x_1381_, 1);
v_v_1385_ = lean_ctor_get(v___x_1381_, 2);
v_l_1386_ = lean_ctor_get(v___x_1381_, 3);
lean_inc(v_l_1386_);
v_r_1387_ = lean_ctor_get(v___x_1381_, 4);
v___x_1388_ = lean_unsigned_to_nat(3u);
v___x_1389_ = lean_nat_mul(v___x_1388_, v_size_1382_);
v___x_1390_ = lean_nat_dec_lt(v___x_1389_, v_size_1383_);
lean_dec(v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_dec(v_l_1386_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v___x_1391_, v_size_1382_);
v___x_1393_ = lean_nat_add(v___x_1392_, v_size_1383_);
lean_dec(v___x_1392_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1381_);
lean_ctor_set(v___x_1200_, 0, v___x_1393_);
v___x_1395_ = v___x_1200_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v___x_1381_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1466_; 
lean_inc(v_r_1387_);
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_inc(v_size_1383_);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; 
v_unused_1467_ = lean_ctor_get(v___x_1381_, 4);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v___x_1381_, 3);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v___x_1381_, 2);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v___x_1381_, 1);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1471_);
v___x_1398_ = v___x_1381_;
v_isShared_1399_ = v_isSharedCheck_1466_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v___x_1381_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1466_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_l_1386_) == 0)
{
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_size_1400_; lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v_l_1403_; lean_object* v_r_1404_; lean_object* v_size_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_size_1400_ = lean_ctor_get(v_l_1386_, 0);
v_k_1401_ = lean_ctor_get(v_l_1386_, 1);
v_v_1402_ = lean_ctor_get(v_l_1386_, 2);
v_l_1403_ = lean_ctor_get(v_l_1386_, 3);
v_r_1404_ = lean_ctor_get(v_l_1386_, 4);
v_size_1405_ = lean_ctor_get(v_r_1387_, 0);
v___x_1406_ = lean_unsigned_to_nat(2u);
v___x_1407_ = lean_nat_mul(v___x_1406_, v_size_1405_);
v___x_1408_ = lean_nat_dec_lt(v_size_1400_, v___x_1407_);
lean_dec(v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1437_; 
lean_inc(v_r_1404_);
lean_inc(v_l_1403_);
lean_inc(v_v_1402_);
lean_inc(v_k_1401_);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; 
v_unused_1438_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_l_1386_, 2);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_l_1386_, 1);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1442_);
v___x_1410_ = v_l_1386_;
v_isShared_1411_ = v_isSharedCheck_1437_;
goto v_resetjp_1409_;
}
else
{
lean_dec(v_l_1386_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1437_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1427_; 
v___x_1412_ = lean_unsigned_to_nat(1u);
v___x_1413_ = lean_nat_add(v___x_1412_, v_size_1382_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_size_1383_);
lean_dec(v_size_1383_);
if (lean_obj_tag(v_l_1403_) == 0)
{
lean_object* v_size_1435_; 
v_size_1435_ = lean_ctor_get(v_l_1403_, 0);
lean_inc(v_size_1435_);
v___y_1427_ = v_size_1435_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___y_1427_ = v___x_1436_;
goto v___jp_1426_;
}
v___jp_1415_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_nat_add(v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v_r_1387_);
lean_ctor_set(v___x_1410_, 3, v_r_1404_);
lean_ctor_set(v___x_1410_, 2, v_v_1385_);
lean_ctor_set(v___x_1410_, 1, v_k_1384_);
lean_ctor_set(v___x_1410_, 0, v___x_1419_);
v___x_1421_ = v___x_1410_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_r_1404_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_r_1387_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v___x_1421_);
lean_ctor_set(v___x_1398_, 3, v___y_1416_);
lean_ctor_set(v___x_1398_, 2, v_v_1402_);
lean_ctor_set(v___x_1398_, 1, v_k_1401_);
lean_ctor_set(v___x_1398_, 0, v___x_1414_);
v___x_1423_ = v___x_1398_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1401_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1402_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v___y_1416_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
v___jp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_nat_add(v___x_1413_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec(v___x_1413_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_l_1403_);
lean_ctor_set(v___x_1200_, 0, v___x_1428_);
v___x_1430_ = v___x_1200_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_l_1403_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_nat_add(v___x_1412_, v_size_1405_);
if (lean_obj_tag(v_r_1404_) == 0)
{
lean_object* v_size_1432_; 
v_size_1432_ = lean_ctor_get(v_r_1404_, 0);
lean_inc(v_size_1432_);
v___y_1416_ = v___x_1430_;
v___y_1417_ = v___x_1431_;
v___y_1418_ = v_size_1432_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___y_1416_ = v___x_1430_;
v___y_1417_ = v___x_1431_;
v___y_1418_ = v___x_1433_;
goto v___jp_1415_;
}
}
}
}
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
lean_del_object(v___x_1200_);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1382_);
v___x_1445_ = lean_nat_add(v___x_1444_, v_size_1383_);
lean_dec(v_size_1383_);
v___x_1446_ = lean_nat_add(v___x_1444_, v_size_1400_);
lean_dec(v___x_1444_);
lean_inc_ref(v_l_1197_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v_l_1386_);
lean_ctor_set(v___x_1398_, 3, v_l_1197_);
lean_ctor_set(v___x_1398_, 2, v_v_1196_);
lean_ctor_set(v___x_1398_, 1, v_k_1195_);
lean_ctor_set(v___x_1398_, 0, v___x_1446_);
v___x_1448_ = v___x_1398_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_l_1386_);
v___x_1448_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
v_isSharedCheck_1455_ = !lean_is_exclusive(v_l_1197_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1456_ = lean_ctor_get(v_l_1197_, 4);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_l_1197_, 3);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_l_1197_, 2);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_l_1197_, 1);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_l_1197_, 0);
lean_dec(v_unused_1460_);
v___x_1450_ = v_l_1197_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v_l_1197_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 4, v_r_1387_);
lean_ctor_set(v___x_1450_, 3, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v_v_1385_);
lean_ctor_set(v___x_1450_, 1, v_k_1384_);
lean_ctor_set(v___x_1450_, 0, v___x_1445_);
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_r_1387_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref_known(v_l_1386_, 5);
lean_del_object(v___x_1398_);
lean_dec(v_v_1385_);
lean_dec(v_k_1384_);
lean_dec(v_size_1383_);
lean_dec_ref_known(v_l_1197_, 5);
lean_del_object(v___x_1200_);
lean_dec(v_v_1196_);
lean_dec(v_k_1195_);
v___x_1462_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__7);
v___x_1463_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1462_);
return v___x_1463_;
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_del_object(v___x_1398_);
lean_dec(v_r_1387_);
lean_dec(v_v_1385_);
lean_dec(v_k_1384_);
lean_dec(v_size_1383_);
lean_dec_ref_known(v_l_1197_, 5);
lean_del_object(v___x_1200_);
lean_dec(v_v_1196_);
lean_dec(v_k_1195_);
v___x_1464_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg___closed__8);
v___x_1465_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v___x_1464_);
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_size_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v_size_1472_ = lean_ctor_get(v_l_1197_, 0);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1472_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1381_);
lean_ctor_set(v___x_1200_, 0, v___x_1474_);
v___x_1476_ = v___x_1200_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v___x_1381_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_l_1478_; 
v_l_1478_ = lean_ctor_get(v___x_1381_, 3);
lean_inc(v_l_1478_);
if (lean_obj_tag(v_l_1478_) == 0)
{
lean_object* v_r_1479_; 
v_r_1479_ = lean_ctor_get(v___x_1381_, 4);
lean_inc(v_r_1479_);
if (lean_obj_tag(v_r_1479_) == 0)
{
lean_object* v_size_1480_; lean_object* v_k_1481_; lean_object* v_v_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1496_; 
v_size_1480_ = lean_ctor_get(v___x_1381_, 0);
v_k_1481_ = lean_ctor_get(v___x_1381_, 1);
v_v_1482_ = lean_ctor_get(v___x_1381_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1497_ = lean_ctor_get(v___x_1381_, 4);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v___x_1381_, 3);
lean_dec(v_unused_1498_);
v___x_1484_ = v___x_1381_;
v_isShared_1485_ = v_isSharedCheck_1496_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_v_1482_);
lean_inc(v_k_1481_);
lean_inc(v_size_1480_);
lean_dec(v___x_1381_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1496_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_size_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v_size_1486_ = lean_ctor_get(v_l_1478_, 0);
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_add(v___x_1487_, v_size_1480_);
lean_dec(v_size_1480_);
v___x_1489_ = lean_nat_add(v___x_1487_, v_size_1486_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_l_1478_);
lean_ctor_set(v___x_1484_, 3, v_l_1197_);
lean_ctor_set(v___x_1484_, 2, v_v_1196_);
lean_ctor_set(v___x_1484_, 1, v_k_1195_);
lean_ctor_set(v___x_1484_, 0, v___x_1489_);
v___x_1491_ = v___x_1484_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_l_1197_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_l_1478_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_r_1479_);
lean_ctor_set(v___x_1200_, 3, v___x_1491_);
lean_ctor_set(v___x_1200_, 2, v_v_1482_);
lean_ctor_set(v___x_1200_, 1, v_k_1481_);
lean_ctor_set(v___x_1200_, 0, v___x_1488_);
v___x_1493_ = v___x_1200_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_r_1479_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_k_1499_; lean_object* v_v_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1524_; 
v_k_1499_ = lean_ctor_get(v___x_1381_, 1);
v_v_1500_ = lean_ctor_get(v___x_1381_, 2);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1525_ = lean_ctor_get(v___x_1381_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v___x_1381_, 3);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1527_);
v___x_1502_ = v___x_1381_;
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_v_1500_);
lean_inc(v_k_1499_);
lean_dec(v___x_1381_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_k_1504_; lean_object* v_v_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1520_; 
v_k_1504_ = lean_ctor_get(v_l_1478_, 1);
v_v_1505_ = lean_ctor_get(v_l_1478_, 2);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_l_1478_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1521_ = lean_ctor_get(v_l_1478_, 4);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_l_1478_, 3);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_l_1478_, 0);
lean_dec(v_unused_1523_);
v___x_1507_ = v_l_1478_;
v_isShared_1508_ = v_isSharedCheck_1520_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_v_1505_);
lean_inc(v_k_1504_);
lean_dec(v_l_1478_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1520_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1509_ = lean_unsigned_to_nat(3u);
v___x_1510_ = lean_unsigned_to_nat(1u);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 4, v_r_1479_);
lean_ctor_set(v___x_1507_, 3, v_r_1479_);
lean_ctor_set(v___x_1507_, 2, v_v_1196_);
lean_ctor_set(v___x_1507_, 1, v_k_1195_);
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_r_1479_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_r_1479_);
v___x_1512_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 3, v_r_1479_);
lean_ctor_set(v___x_1502_, 0, v___x_1510_);
v___x_1514_ = v___x_1502_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1499_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1500_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_r_1479_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_r_1479_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1514_);
lean_ctor_set(v___x_1200_, 3, v___x_1512_);
lean_ctor_set(v___x_1200_, 2, v_v_1505_);
lean_ctor_set(v___x_1200_, 1, v_k_1504_);
lean_ctor_set(v___x_1200_, 0, v___x_1509_);
v___x_1516_ = v___x_1200_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1504_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1505_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1528_; 
v_r_1528_ = lean_ctor_get(v___x_1381_, 4);
lean_inc(v_r_1528_);
if (lean_obj_tag(v_r_1528_) == 0)
{
lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1542_; 
v_k_1529_ = lean_ctor_get(v___x_1381_, 1);
v_v_1530_ = lean_ctor_get(v___x_1381_, 2);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1543_ = lean_ctor_get(v___x_1381_, 4);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v___x_1381_, 3);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1545_);
v___x_1532_ = v___x_1381_;
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_v_1530_);
lean_inc(v_k_1529_);
lean_dec(v___x_1381_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1534_ = lean_unsigned_to_nat(3u);
v___x_1535_ = lean_unsigned_to_nat(1u);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v_l_1478_);
lean_ctor_set(v___x_1532_, 2, v_v_1196_);
lean_ctor_set(v___x_1532_, 1, v_k_1195_);
lean_ctor_set(v___x_1532_, 0, v___x_1535_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_l_1478_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_l_1478_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_r_1528_);
lean_ctor_set(v___x_1200_, 3, v___x_1537_);
lean_ctor_set(v___x_1200_, 2, v_v_1530_);
lean_ctor_set(v___x_1200_, 1, v_k_1529_);
lean_ctor_set(v___x_1200_, 0, v___x_1534_);
v___x_1539_ = v___x_1200_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_k_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_v_1530_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_r_1528_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1546_ = lean_unsigned_to_nat(2u);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1381_);
lean_ctor_set(v___x_1200_, 3, v_r_1528_);
lean_ctor_set(v___x_1200_, 0, v___x_1546_);
v___x_1548_ = v___x_1200_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v___x_1381_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v___x_1381_);
lean_ctor_set(v___x_1200_, 3, v___x_1381_);
lean_ctor_set(v___x_1200_, 0, v___x_1550_);
v___x_1552_ = v___x_1200_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v___x_1381_);
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
}
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_k_1191_);
lean_ctor_set(v___x_1556_, 2, v_v_1192_);
lean_ctor_set(v___x_1556_, 3, v_t_1193_);
lean_ctor_set(v___x_1556_, 4, v_t_1193_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(lean_object* v_init_1557_, lean_object* v_x_1558_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_l_1561_; lean_object* v_r_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_k_1559_ = lean_ctor_get(v_x_1558_, 1);
lean_inc(v_k_1559_);
v_v_1560_ = lean_ctor_get(v_x_1558_, 2);
lean_inc(v_v_1560_);
v_l_1561_ = lean_ctor_get(v_x_1558_, 3);
lean_inc(v_l_1561_);
v_r_1562_ = lean_ctor_get(v_x_1558_, 4);
lean_inc(v_r_1562_);
lean_dec_ref_known(v_x_1558_, 5);
v___x_1563_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1557_, v_l_1561_);
v___x_1564_ = 1;
v___x_1565_ = l_Lean_Name_toString(v_k_1559_, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_v_1560_);
v___x_1567_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v___x_1565_, v___x_1566_, v___x_1563_);
v_init_1557_ = v___x_1567_;
v_x_1558_ = v_r_1562_;
goto _start;
}
else
{
return v_init_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(lean_object* v_m_1569_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_box(1);
v___x_1571_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v___x_1570_, v_m_1569_);
v___x_1572_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
if (lean_obj_tag(v_a_1573_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_array_to_list(v_a_1574_);
return v___x_1575_;
}
else
{
lean_object* v_head_1576_; lean_object* v_tail_1577_; lean_object* v___x_1578_; 
v_head_1576_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_head_1576_);
v_tail_1577_ = lean_ctor_get(v_a_1573_, 1);
lean_inc(v_tail_1577_);
lean_dec_ref_known(v_a_1573_, 2);
v___x_1578_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1574_, v_head_1576_);
v_a_1573_ = v_tail_1577_;
v_a_1574_ = v___x_1578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(lean_object* v_x_1588_){
_start:
{
lean_object* v_idx_1589_; lean_object* v_name_1590_; lean_object* v_platform_1591_; lean_object* v_leanHash_1592_; uint64_t v_configHash_1593_; lean_object* v_options_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_idx_1589_ = lean_ctor_get(v_x_1588_, 0);
lean_inc(v_idx_1589_);
v_name_1590_ = lean_ctor_get(v_x_1588_, 1);
lean_inc(v_name_1590_);
v_platform_1591_ = lean_ctor_get(v_x_1588_, 2);
lean_inc_ref(v_platform_1591_);
v_leanHash_1592_ = lean_ctor_get(v_x_1588_, 3);
lean_inc_ref(v_leanHash_1592_);
v_configHash_1593_ = lean_ctor_get_uint64(v_x_1588_, sizeof(void*)*5);
v_options_1594_ = lean_ctor_get(v_x_1588_, 4);
lean_inc(v_options_1594_);
lean_dec_ref(v_x_1588_);
v___x_1595_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
v___x_1596_ = l_Lean_JsonNumber_fromNat(v_idx_1589_);
v___x_1597_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1595_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
v___x_1602_ = 1;
v___x_1603_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1590_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1601_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1599_);
v___x_1607_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
v___x_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_platform_1591_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1599_);
v___x_1611_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
v___x_1612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_leanHash_1592_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1599_);
v___x_1615_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
v___x_1616_ = l_Lake_lowerHexUInt64(v_configHash_1593_);
v___x_1617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1615_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___x_1599_);
v___x_1620_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1621_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0(v_options_1594_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___x_1599_);
v___x_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1599_);
v___x_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1619_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1614_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1610_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1606_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1600_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__6));
v___x_1631_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__1(v___x_1629_, v___x_1630_);
v___x_1632_ = l_Lean_Json_mkObj(v___x_1631_);
lean_dec(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1633_, lean_object* v_msg_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0_spec__1___redArg(v_msg_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0(lean_object* v_00_u03b2_1636_, lean_object* v_k_1637_, lean_object* v_v_1638_, lean_object* v_t_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__0___redArg(v_k_1637_, v_v_1638_, v_t_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1(lean_object* v_init_1641_, lean_object* v_t_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson_spec__0_spec__1_spec__3(v_init_1641_, v_t_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(lean_object* v_j_1646_, lean_object* v_k_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = l_Lean_Json_getObjValD(v_j_1646_, v_k_1647_);
v___x_1649_ = l_Lean_Json_getNat_x3f(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0___boxed(lean_object* v_j_1650_, lean_object* v_k_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_j_1650_, v_k_1651_);
lean_dec_ref(v_k_1651_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(lean_object* v_j_1653_, lean_object* v_k_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = l_Lean_Json_getObjValD(v_j_1653_, v_k_1654_);
v___x_1656_ = l_Lean_Name_fromJson_x3f(v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1___boxed(lean_object* v_j_1657_, lean_object* v_k_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_j_1657_, v_k_1658_);
lean_dec_ref(v_k_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(lean_object* v_j_1660_, lean_object* v_k_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = l_Lean_Json_getObjValD(v_j_1660_, v_k_1661_);
v___x_1663_ = l_Lean_Json_getStr_x3f(v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2___boxed(lean_object* v_j_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_j_1664_, v_k_1665_);
lean_dec_ref(v_k_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(lean_object* v_j_1667_, lean_object* v_k_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = l_Lean_Json_getObjValD(v_j_1667_, v_k_1668_);
v___x_1670_ = l_Lake_Hash_fromJson_x3f(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3___boxed(lean_object* v_j_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_j_1671_, v_k_1672_);
lean_dec_ref(v_k_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(lean_object* v_init_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v_k_1679_; lean_object* v_v_1680_; lean_object* v_l_1681_; lean_object* v_r_1682_; lean_object* v___x_1683_; 
v_k_1679_ = lean_ctor_get(v_x_1678_, 1);
lean_inc(v_k_1679_);
v_v_1680_ = lean_ctor_get(v_x_1678_, 2);
lean_inc(v_v_1680_);
v_l_1681_ = lean_ctor_get(v_x_1678_, 3);
lean_inc(v_l_1681_);
v_r_1682_ = lean_ctor_get(v_x_1678_, 4);
lean_inc(v_r_1682_);
lean_dec_ref_known(v_x_1678_, 5);
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v_init_1677_, v_l_1681_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_dec(v_r_1682_);
lean_dec(v_v_1680_);
lean_dec(v_k_1679_);
return v___x_1683_;
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1724_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1724_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1724_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__0));
v___x_1689_ = lean_string_dec_eq(v_k_1679_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v_n_1690_; uint8_t v___x_1691_; 
lean_inc(v_k_1679_);
v_n_1690_ = l_String_toName(v_k_1679_);
v___x_1691_ = l_Lean_Name_isAnonymous(v_n_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_del_object(v___x_1686_);
lean_dec(v_k_1679_);
v___x_1692_ = l_Lean_Json_getStr_x3f(v_v_1680_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_n_1690_);
lean_dec(v_a_1684_);
lean_dec(v_r_1682_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1702_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1690_, v_a_1701_, v_a_1684_);
v_init_1677_ = v___x_1702_;
v_x_1678_ = v_r_1682_;
goto _start;
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
lean_dec(v_n_1690_);
lean_dec(v_a_1684_);
lean_dec(v_r_1682_);
lean_dec(v_v_1680_);
v___x_1704_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__1));
v___x_1705_ = lean_string_append(v___x_1704_, v_k_1679_);
lean_dec(v_k_1679_);
v___x_1706_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1707_ = lean_string_append(v___x_1705_, v___x_1706_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1707_);
v___x_1709_ = v___x_1686_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v___x_1711_; 
lean_del_object(v___x_1686_);
lean_dec(v_k_1679_);
v___x_1711_ = l_Lean_Json_getStr_x3f(v_v_1680_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_a_1684_);
lean_dec(v_r_1682_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1721_ = lean_box(0);
v___x_1722_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1721_, v_a_1720_, v_a_1684_);
v_init_1677_ = v___x_1722_;
v_x_1678_ = v_r_1682_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_init_1677_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(lean_object* v_x_1727_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 5)
{
lean_object* v_kvPairs_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_kvPairs_1728_ = lean_ctor_get(v_x_1727_, 0);
lean_inc(v_kvPairs_1728_);
lean_dec_ref_known(v_x_1727_, 1);
v___x_1729_ = lean_box(1);
v___x_1730_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5(v___x_1729_, v_kvPairs_1728_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1731_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4___closed__0));
v___x_1732_ = lean_unsigned_to_nat(80u);
v___x_1733_ = l_Lean_Json_pretty(v_x_1727_, v___x_1732_);
v___x_1734_ = lean_string_append(v___x_1731_, v___x_1733_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4_spec__5___closed__2));
v___x_1736_ = lean_string_append(v___x_1734_, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(lean_object* v_j_1738_, lean_object* v_k_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = l_Lean_Json_getObjValD(v_j_1738_, v_k_1739_);
v___x_1741_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v___x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4___boxed(lean_object* v_j_1742_, lean_object* v_k_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_j_1742_, v_k_1743_);
lean_dec_ref(v_k_1743_);
return v_res_1744_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12(void){
_start:
{
uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = 1;
v___x_1774_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__11));
v___x_1775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1774_, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__13));
v___x_1778_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__12);
v___x_1779_ = lean_string_append(v___x_1778_, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = 1;
v___x_1783_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__15));
v___x_1784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1783_, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__16);
v___x_1786_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1787_ = lean_string_append(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1790_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__17);
v___x_1791_ = lean_string_append(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = 1;
v___x_1795_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__20));
v___x_1796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__21);
v___x_1798_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1799_ = lean_string_append(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1801_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__22);
v___x_1802_ = lean_string_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = 1;
v___x_1806_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__24));
v___x_1807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1806_, v___x_1805_);
return v___x_1807_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__25);
v___x_1809_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1810_ = lean_string_append(v___x_1809_, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1812_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__26);
v___x_1813_ = lean_string_append(v___x_1812_, v___x_1811_);
return v___x_1813_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = 1;
v___x_1817_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__28));
v___x_1818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__29);
v___x_1820_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1821_ = lean_string_append(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1823_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__30);
v___x_1824_ = lean_string_append(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = 1;
v___x_1828_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__32));
v___x_1829_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1828_, v___x_1827_);
return v___x_1829_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__33);
v___x_1831_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1832_ = lean_string_append(v___x_1831_, v___x_1830_);
return v___x_1832_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1834_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__34);
v___x_1835_ = lean_string_append(v___x_1834_, v___x_1833_);
return v___x_1835_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = 1;
v___x_1839_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__36));
v___x_1840_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__37);
v___x_1842_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__14);
v___x_1843_ = lean_string_append(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__18));
v___x_1845_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__38);
v___x_1846_ = lean_string_append(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(lean_object* v_json_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__0));
lean_inc(v_json_1847_);
v___x_1849_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__0(v_json_1847_, v___x_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_json_1847_);
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
v___x_1854_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__19);
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
lean_object* v_a_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_a_1860_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1861_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__1));
lean_inc(v_json_1847_);
v___x_1862_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__1(v_json_1847_, v___x_1861_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_a_1860_);
lean_dec(v_json_1847_);
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
v___x_1867_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__23);
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
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_a_1873_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1874_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__2));
lean_inc(v_json_1847_);
v___x_1875_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1847_, v___x_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1860_);
lean_dec(v_json_1847_);
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__27);
v___x_1881_ = lean_string_append(v___x_1880_, v_a_1876_);
lean_dec(v_a_1876_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
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
v_a_1886_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1887_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__3));
lean_inc(v_json_1847_);
v___x_1888_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__2(v_json_1847_, v___x_1887_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1886_);
lean_dec(v_a_1873_);
lean_dec(v_a_1860_);
lean_dec(v_json_1847_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1893_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__31);
v___x_1894_ = lean_string_append(v___x_1893_, v_a_1889_);
lean_dec(v_a_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_a_1899_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1900_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__4));
lean_inc(v_json_1847_);
v___x_1901_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__3(v_json_1847_, v___x_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1899_);
lean_dec(v_a_1886_);
lean_dec(v_a_1873_);
lean_dec(v_a_1860_);
lean_dec(v_json_1847_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1906_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__35);
v___x_1907_ = lean_string_append(v___x_1906_, v_a_1902_);
lean_dec(v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1907_);
v___x_1909_ = v___x_1904_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1913_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_1914_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4(v_json_1847_, v___x_1913_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1912_);
lean_dec(v_a_1899_);
lean_dec(v_a_1886_);
lean_dec(v_a_1873_);
lean_dec(v_a_1860_);
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1924_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1924_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1919_ = lean_obj_once(&l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39, &l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39_once, _init_l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson___closed__39);
v___x_1920_ = lean_string_append(v___x_1919_, v_a_1915_);
lean_dec(v_a_1915_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1920_);
v___x_1922_ = v___x_1917_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1934_; 
v_a_1925_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1927_ = v___x_1914_;
v_isShared_1928_ = v_isSharedCheck_1934_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1914_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1934_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; uint64_t v___x_1930_; lean_object* v___x_1932_; 
v___x_1929_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_1929_, 0, v_a_1860_);
lean_ctor_set(v___x_1929_, 1, v_a_1873_);
lean_ctor_set(v___x_1929_, 2, v_a_1886_);
lean_ctor_set(v___x_1929_, 3, v_a_1899_);
lean_ctor_set(v___x_1929_, 4, v_a_1925_);
v___x_1930_ = lean_unbox_uint64(v_a_1912_);
lean_dec(v_a_1912_);
lean_ctor_set_uint64(v___x_1929_, sizeof(void*)*5, v___x_1930_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1932_ = v___x_1927_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1929_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
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
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lake_importConfigFile___lam__0___closed__0));
v___x_1939_ = lean_mk_io_user_error(v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* v___x_1940_, lean_object* v___x_1941_, lean_object* v_h_1942_){
_start:
{
uint8_t v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = 1;
v___x_1945_ = lean_io_prim_handle_mk(v___x_1940_, v___x_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
v___x_1947_ = 1;
v___x_1948_ = lean_io_prim_handle_try_lock(v_a_1946_, v___x_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = lean_unbox(v_a_1949_);
lean_dec(v_a_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_a_1946_);
v___x_1951_ = lean_io_prim_handle_unlock(v_h_1942_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1951_, 0);
lean_dec(v_unused_1960_);
v___x_1953_ = v___x_1951_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_dec(v___x_1951_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_obj_once(&l_Lake_importConfigFile___lam__0___closed__1, &l_Lake_importConfigFile___lam__0___closed__1_once, _init_l_Lake_importConfigFile___lam__0___closed__1);
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1961_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1951_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1951_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_io_prim_handle_unlock(v_h_1942_);
if (lean_obj_tag(v___x_1969_) == 0)
{
uint8_t v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1969_, 1);
v___x_1970_ = 3;
v___x_1971_ = lean_io_prim_handle_mk(v___x_1941_, v___x_1970_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = lean_io_prim_handle_lock(v_a_1972_, v___x_1947_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1973_, 1);
v___x_1974_ = lean_io_prim_handle_unlock(v_a_1946_);
lean_dec(v_a_1946_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1974_, 0);
lean_dec(v_unused_1982_);
v___x_1976_ = v___x_1974_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_dec(v___x_1974_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_a_1972_);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1972_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_a_1972_);
v_a_1983_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_a_1972_);
lean_dec(v_a_1946_);
v_a_1991_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1973_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1973_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_dec(v_a_1946_);
return v___x_1971_;
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_a_1946_);
v_a_1999_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1969_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1969_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_a_1946_);
v_a_2007_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1948_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1948_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* v___x_2015_, lean_object* v___x_2016_, lean_object* v_h_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lake_importConfigFile___lam__0(v___x_2015_, v___x_2016_, v_h_2017_);
lean_dec(v_h_2017_);
lean_dec_ref(v___x_2016_);
lean_dec_ref(v___x_2015_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* v_cfg_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___y_2032_; lean_object* v_a_2033_; lean_object* v_lakeEnv_2035_; lean_object* v_wsDir_2036_; lean_object* v_pkgIdx_2037_; lean_object* v_pkgName_2038_; lean_object* v_pkgDir_2039_; lean_object* v_configFile_2040_; lean_object* v_lakeOpts_2041_; lean_object* v_leanOpts_2042_; uint8_t v_reconfigure_2043_; lean_object* v___x_2044_; 
v_lakeEnv_2035_ = lean_ctor_get(v_cfg_2028_, 0);
lean_inc_ref(v_lakeEnv_2035_);
v_wsDir_2036_ = lean_ctor_get(v_cfg_2028_, 2);
lean_inc_ref(v_wsDir_2036_);
v_pkgIdx_2037_ = lean_ctor_get(v_cfg_2028_, 3);
lean_inc(v_pkgIdx_2037_);
v_pkgName_2038_ = lean_ctor_get(v_cfg_2028_, 4);
lean_inc(v_pkgName_2038_);
v_pkgDir_2039_ = lean_ctor_get(v_cfg_2028_, 6);
lean_inc_ref(v_pkgDir_2039_);
v_configFile_2040_ = lean_ctor_get(v_cfg_2028_, 8);
lean_inc_ref_n(v_configFile_2040_, 2);
v_lakeOpts_2041_ = lean_ctor_get(v_cfg_2028_, 12);
lean_inc(v_lakeOpts_2041_);
v_leanOpts_2042_ = lean_ctor_get(v_cfg_2028_, 13);
lean_inc_ref(v_leanOpts_2042_);
v_reconfigure_2043_ = lean_ctor_get_uint8(v_cfg_2028_, sizeof(void*)*16);
lean_dec_ref(v_cfg_2028_);
v___x_2044_ = l_System_FilePath_fileName(v_configFile_2040_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_wsDir_2036_);
lean_dec_ref(v_lakeEnv_2035_);
v___x_2045_ = ((lean_object*)(l_Lake_importConfigFile___closed__1));
v___x_2046_ = lean_array_get_size(v_a_2029_);
v___x_2047_ = lean_array_push(v_a_2029_, v___x_2045_);
v___x_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
return v___x_2048_;
}
else
{
lean_object* v_val_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_configDir_2055_; lean_object* v___x_2056_; 
v_val_2049_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2050_ = l_Lake_defaultLakeDir;
v___x_2051_ = l_Lake_joinRelative(v_wsDir_2036_, v___x_2050_);
v___x_2052_ = ((lean_object*)(l_Lake_importConfigFile___closed__2));
v___x_2053_ = l_Lake_joinRelative(v___x_2051_, v___x_2052_);
lean_inc(v_pkgIdx_2037_);
v___x_2054_ = l_Nat_reprFast(v_pkgIdx_2037_);
v_configDir_2055_ = l_Lake_joinRelative(v___x_2053_, v___x_2054_);
lean_inc_ref(v_configDir_2055_);
v___x_2056_ = l_IO_FS_createDirAll(v_configDir_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref_known(v___x_2056_, 1);
v___x_2057_ = ((lean_object*)(l_Lake_importConfigFile___closed__3));
lean_inc_n(v_val_2049_, 2);
v___x_2058_ = l_System_FilePath_withExtension(v_val_2049_, v___x_2057_);
lean_inc_ref_n(v_configDir_2055_, 2);
v___x_2059_ = l_Lake_joinRelative(v_configDir_2055_, v___x_2058_);
v___x_2060_ = ((lean_object*)(l_Lake_importConfigFile___closed__4));
v___x_2061_ = l_System_FilePath_withExtension(v_val_2049_, v___x_2060_);
v___x_2062_ = l_Lake_joinRelative(v_configDir_2055_, v___x_2061_);
v___x_2063_ = ((lean_object*)(l_Lake_importConfigFile___closed__5));
v___x_2064_ = l_System_FilePath_withExtension(v_val_2049_, v___x_2063_);
v___x_2065_ = l_Lake_joinRelative(v_configDir_2055_, v___x_2064_);
v___x_2066_ = l_Lake_computeTextFileHash(v_configFile_2040_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v_h_2069_; lean_object* v_lakeOpts_2070_; lean_object* v___y_2071_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v_h_2250_; lean_object* v___y_2251_; uint8_t v___x_2339_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2339_ = l_System_FilePath_pathExists(v___x_2062_);
if (v___x_2339_ == 0)
{
uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = 1;
lean_inc_ref(v_pkgDir_2039_);
v___x_2341_ = l_Lake_joinRelative(v_pkgDir_2039_, v___x_2050_);
v___x_2342_ = l_IO_FS_createDirAll(v___x_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
uint8_t v___x_2343_; lean_object* v___x_2344_; 
lean_dec_ref_known(v___x_2342_, 1);
v___x_2343_ = 2;
v___x_2344_ = lean_io_prim_handle_mk(v___x_2062_, v___x_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; 
lean_dec_ref(v___x_2065_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = lean_io_prim_handle_lock(v_a_2345_, v___x_2340_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_dec_ref_known(v___x_2346_, 1);
v_h_2069_ = v_a_2345_;
v_lakeOpts_2070_ = v_lakeOpts_2041_;
v___y_2071_ = v_a_2029_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_a_2345_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = lean_io_error_to_string(v_a_2347_);
v___x_2349_ = 3;
v___x_2350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*1, v___x_2349_);
v___x_2351_ = lean_array_get_size(v_a_2029_);
v___x_2352_ = lean_array_push(v_a_2029_, v___x_2350_);
v___x_2353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
return v___x_2353_;
}
}
else
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2344_, 1);
if (lean_obj_tag(v_a_2354_) == 0)
{
uint8_t v___x_2355_; lean_object* v___x_2356_; 
lean_dec_ref_known(v_a_2354_, 2);
v___x_2355_ = 0;
v___x_2356_ = lean_io_prim_handle_mk(v___x_2062_, v___x_2355_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v_h_2250_ = v_a_2357_;
v___y_2251_ = v_a_2029_;
goto v___jp_2249_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2358_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2359_ = lean_io_error_to_string(v_a_2358_);
v___x_2360_ = 3;
v___x_2361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*1, v___x_2360_);
v___x_2362_ = lean_array_get_size(v_a_2029_);
v___x_2363_ = lean_array_push(v_a_2029_, v___x_2361_);
v___x_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
return v___x_2364_;
}
}
else
{
lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v___x_2365_ = lean_io_error_to_string(v_a_2354_);
v___x_2366_ = 3;
v___x_2367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2366_);
v___x_2368_ = lean_array_get_size(v_a_2029_);
v___x_2369_ = lean_array_push(v_a_2029_, v___x_2367_);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
return v___x_2370_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2371_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2372_ = lean_io_error_to_string(v_a_2371_);
v___x_2373_ = 3;
v___x_2374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*1, v___x_2373_);
v___x_2375_ = lean_array_get_size(v_a_2029_);
v___x_2376_ = lean_array_push(v_a_2029_, v___x_2374_);
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
return v___x_2377_;
}
}
else
{
uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = 0;
v___x_2379_ = lean_io_prim_handle_mk(v___x_2062_, v___x_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v_h_2250_ = v_a_2380_;
v___y_2251_ = v_a_2029_;
goto v___jp_2249_;
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2381_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2382_ = lean_io_error_to_string(v_a_2381_);
v___x_2383_ = 3;
v___x_2384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*1, v___x_2383_);
v___x_2385_ = lean_array_get_size(v_a_2029_);
v___x_2386_ = lean_array_push(v_a_2029_, v___x_2384_);
v___x_2387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
return v___x_2387_;
}
}
v___jp_2068_:
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_io_remove_file(v___x_2059_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint64_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref_known(v___x_2072_, 1);
lean_dec_ref(v___x_2062_);
v___x_2073_ = l_System_Platform_target;
v___x_2074_ = l_Lake_Env_leanGithash(v_lakeEnv_2035_);
lean_dec_ref(v_lakeEnv_2035_);
lean_inc(v_lakeOpts_2070_);
lean_inc(v_pkgName_2038_);
lean_inc(v_pkgIdx_2037_);
v___x_2075_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2075_, 0, v_pkgIdx_2037_);
lean_ctor_set(v___x_2075_, 1, v_pkgName_2038_);
lean_ctor_set(v___x_2075_, 2, v___x_2073_);
lean_ctor_set(v___x_2075_, 3, v___x_2074_);
lean_ctor_set(v___x_2075_, 4, v_lakeOpts_2070_);
v___x_2076_ = lean_unbox_uint64(v_a_2067_);
lean_dec(v_a_2067_);
lean_ctor_set_uint64(v___x_2075_, sizeof(void*)*5, v___x_2076_);
v___x_2077_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2075_);
v___x_2078_ = lean_unsigned_to_nat(80u);
v___x_2079_ = l_Lean_Json_pretty(v___x_2077_, v___x_2078_);
v___x_2080_ = l_IO_FS_Handle_putStrLn(v_h_2069_, v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2081_; 
lean_dec_ref_known(v___x_2080_, 1);
v___x_2081_ = lean_io_prim_handle_flush(v_h_2069_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v___x_2082_; 
lean_dec_ref_known(v___x_2081_, 1);
v___x_2082_ = lean_io_prim_handle_truncate(v_h_2069_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v___x_2083_; 
lean_dec_ref_known(v___x_2082_, 1);
v___x_2083_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2037_, v_pkgName_2038_, v_pkgDir_2039_, v_lakeOpts_2070_, v_leanOpts_2042_, v_configFile_2040_, v___y_2071_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v_a_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_a_2085_ = lean_ctor_get(v___x_2083_, 1);
v___x_2086_ = 1;
lean_inc(v_a_2084_);
v___x_2087_ = l_Lean_writeModule(v_a_2084_, v___x_2059_, v___x_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2088_ = lean_io_prim_handle_unlock(v_h_2069_);
lean_dec(v_h_2069_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_dec_ref_known(v___x_2088_, 1);
return v___x_2083_;
}
else
{
lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2101_; 
lean_inc(v_a_2085_);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; lean_object* v_unused_2103_; 
v_unused_2102_ = lean_ctor_get(v___x_2083_, 1);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v___x_2083_, 0);
lean_dec(v_unused_2103_);
v___x_2090_ = v___x_2083_;
v_isShared_2091_ = v_isSharedCheck_2101_;
goto v_resetjp_2089_;
}
else
{
lean_dec(v___x_2083_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2101_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_a_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_a_2092_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2093_ = lean_io_error_to_string(v_a_2092_);
v___x_2094_ = 3;
v___x_2095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*1, v___x_2094_);
v___x_2096_ = lean_array_get_size(v_a_2085_);
v___x_2097_ = lean_array_push(v_a_2085_, v___x_2095_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 1);
lean_ctor_set(v___x_2090_, 1, v___x_2097_);
lean_ctor_set(v___x_2090_, 0, v___x_2096_);
v___x_2099_ = v___x_2090_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2116_; 
lean_inc(v_a_2085_);
lean_dec(v_h_2069_);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; lean_object* v_unused_2118_; 
v_unused_2117_ = lean_ctor_get(v___x_2083_, 1);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v___x_2083_, 0);
lean_dec(v_unused_2118_);
v___x_2105_ = v___x_2083_;
v_isShared_2106_ = v_isSharedCheck_2116_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v___x_2083_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2116_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_a_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2108_ = lean_io_error_to_string(v_a_2107_);
v___x_2109_ = 3;
v___x_2110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*1, v___x_2109_);
v___x_2111_ = lean_array_get_size(v_a_2085_);
v___x_2112_ = lean_array_push(v_a_2085_, v___x_2110_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 1);
lean_ctor_set(v___x_2105_, 1, v___x_2112_);
lean_ctor_set(v___x_2105_, 0, v___x_2111_);
v___x_2114_ = v___x_2105_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
return v___x_2083_;
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
v_a_2119_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2120_ = lean_io_error_to_string(v_a_2119_);
v___x_2121_ = 3;
v___x_2122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1, v___x_2121_);
v___x_2123_ = lean_array_get_size(v___y_2071_);
v___x_2124_ = lean_array_push(v___y_2071_, v___x_2122_);
v___x_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
return v___x_2125_;
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
v_a_2126_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2127_ = lean_io_error_to_string(v_a_2126_);
v___x_2128_ = 3;
v___x_2129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*1, v___x_2128_);
v___x_2130_ = lean_array_get_size(v___y_2071_);
v___x_2131_ = lean_array_push(v___y_2071_, v___x_2129_);
v___x_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
v_a_2133_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2080_, 1);
v___x_2134_ = lean_io_error_to_string(v_a_2133_);
v___x_2135_ = 3;
v___x_2136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*1, v___x_2135_);
v___x_2137_ = lean_array_get_size(v___y_2071_);
v___x_2138_ = lean_array_push(v___y_2071_, v___x_2136_);
v___x_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
return v___x_2139_;
}
}
else
{
lean_object* v_a_2140_; 
v_a_2140_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2072_, 1);
if (lean_obj_tag(v_a_2140_) == 11)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint64_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref_known(v_a_2140_, 2);
lean_dec_ref(v___x_2062_);
v___x_2141_ = l_System_Platform_target;
v___x_2142_ = l_Lake_Env_leanGithash(v_lakeEnv_2035_);
lean_dec_ref(v_lakeEnv_2035_);
lean_inc(v_lakeOpts_2070_);
lean_inc(v_pkgName_2038_);
lean_inc(v_pkgIdx_2037_);
v___x_2143_ = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(v___x_2143_, 0, v_pkgIdx_2037_);
lean_ctor_set(v___x_2143_, 1, v_pkgName_2038_);
lean_ctor_set(v___x_2143_, 2, v___x_2141_);
lean_ctor_set(v___x_2143_, 3, v___x_2142_);
lean_ctor_set(v___x_2143_, 4, v_lakeOpts_2070_);
v___x_2144_ = lean_unbox_uint64(v_a_2067_);
lean_dec(v_a_2067_);
lean_ctor_set_uint64(v___x_2143_, sizeof(void*)*5, v___x_2144_);
v___x_2145_ = l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson(v___x_2143_);
v___x_2146_ = lean_unsigned_to_nat(80u);
v___x_2147_ = l_Lean_Json_pretty(v___x_2145_, v___x_2146_);
v___x_2148_ = l_IO_FS_Handle_putStrLn(v_h_2069_, v___x_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2149_ = lean_io_prim_handle_flush(v_h_2069_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; 
lean_dec_ref_known(v___x_2149_, 1);
v___x_2150_ = lean_io_prim_handle_truncate(v_h_2069_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v___x_2151_; 
lean_dec_ref_known(v___x_2150_, 1);
v___x_2151_ = l___private_Lake_Load_Lean_Elab_0__Lake_elabConfigFile(v_pkgIdx_2037_, v_pkgName_2038_, v_pkgDir_2039_, v_lakeOpts_2070_, v_leanOpts_2042_, v_configFile_2040_, v___y_2071_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v_a_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_a_2153_ = lean_ctor_get(v___x_2151_, 1);
v___x_2154_ = 1;
lean_inc(v_a_2152_);
v___x_2155_ = l_Lean_writeModule(v_a_2152_, v___x_2059_, v___x_2154_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref_known(v___x_2155_, 1);
v___x_2156_ = lean_io_prim_handle_unlock(v_h_2069_);
lean_dec(v_h_2069_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_dec_ref_known(v___x_2156_, 1);
return v___x_2151_;
}
else
{
lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2169_; 
lean_inc(v_a_2153_);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; lean_object* v_unused_2171_; 
v_unused_2170_ = lean_ctor_get(v___x_2151_, 1);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2171_);
v___x_2158_ = v___x_2151_;
v_isShared_2159_ = v_isSharedCheck_2169_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v___x_2151_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2169_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_a_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v_a_2160_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2161_ = lean_io_error_to_string(v_a_2160_);
v___x_2162_ = 3;
v___x_2163_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set_uint8(v___x_2163_, sizeof(void*)*1, v___x_2162_);
v___x_2164_ = lean_array_get_size(v_a_2153_);
v___x_2165_ = lean_array_push(v_a_2153_, v___x_2163_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 1);
lean_ctor_set(v___x_2158_, 1, v___x_2165_);
lean_ctor_set(v___x_2158_, 0, v___x_2164_);
v___x_2167_ = v___x_2158_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2184_; 
lean_inc(v_a_2153_);
lean_dec(v_h_2069_);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2185_ = lean_ctor_get(v___x_2151_, 1);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2186_);
v___x_2173_ = v___x_2151_;
v_isShared_2174_ = v_isSharedCheck_2184_;
goto v_resetjp_2172_;
}
else
{
lean_dec(v___x_2151_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2184_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_a_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v_a_2175_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2176_ = lean_io_error_to_string(v_a_2175_);
v___x_2177_ = 3;
v___x_2178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*1, v___x_2177_);
v___x_2179_ = lean_array_get_size(v_a_2153_);
v___x_2180_ = lean_array_push(v_a_2153_, v___x_2178_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 1);
lean_ctor_set(v___x_2173_, 1, v___x_2180_);
lean_ctor_set(v___x_2173_, 0, v___x_2179_);
v___x_2182_ = v___x_2173_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
return v___x_2151_;
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
v_a_2187_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2188_ = lean_io_error_to_string(v_a_2187_);
v___x_2189_ = 3;
v___x_2190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v___x_2189_);
v___x_2191_ = lean_array_get_size(v___y_2071_);
v___x_2192_ = lean_array_push(v___y_2071_, v___x_2190_);
v___x_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
return v___x_2193_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
v_a_2194_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2195_ = lean_io_error_to_string(v_a_2194_);
v___x_2196_ = 3;
v___x_2197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*1, v___x_2196_);
v___x_2198_ = lean_array_get_size(v___y_2071_);
v___x_2199_ = lean_array_push(v___y_2071_, v___x_2197_);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
return v___x_2200_;
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_h_2069_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
v_a_2201_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2202_ = lean_io_error_to_string(v_a_2201_);
v___x_2203_ = 3;
v___x_2204_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2203_);
v___x_2205_ = lean_array_get_size(v___y_2071_);
v___x_2206_ = lean_array_push(v___y_2071_, v___x_2204_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
return v___x_2207_;
}
}
else
{
lean_object* v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v_lakeOpts_2070_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v___x_2208_ = lean_io_error_to_string(v_a_2140_);
v___x_2209_ = 3;
v___x_2210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*1, v___x_2209_);
v___x_2211_ = lean_array_get_size(v___y_2071_);
v___x_2212_ = lean_array_push(v___y_2071_, v___x_2210_);
v___x_2213_ = lean_io_prim_handle_unlock(v_h_2069_);
lean_dec(v_h_2069_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; 
lean_dec_ref_known(v___x_2213_, 1);
v___x_2214_ = lean_io_remove_file(v___x_2062_);
lean_dec_ref(v___x_2062_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_dec_ref_known(v___x_2214_, 1);
v___y_2032_ = v___x_2211_;
v_a_2033_ = v___x_2212_;
goto v___jp_2031_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_io_error_to_string(v_a_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*1, v___x_2209_);
v___x_2218_ = lean_array_push(v___x_2212_, v___x_2217_);
v___y_2032_ = v___x_2211_;
v_a_2033_ = v___x_2218_;
goto v___jp_2031_;
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v___x_2062_);
v_a_2219_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2220_ = lean_io_error_to_string(v_a_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*1, v___x_2209_);
v___x_2222_ = lean_array_push(v___x_2212_, v___x_2221_);
v___y_2032_ = v___x_2211_;
v_a_2033_ = v___x_2222_;
goto v___jp_2031_;
}
}
}
}
v___jp_2223_:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lake_importConfigFile___lam__0(v___x_2065_, v___x_2062_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v_h_2069_ = v_a_2227_;
v_lakeOpts_2070_ = v_lakeOpts_2041_;
v___y_2071_ = v___y_2224_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2228_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2229_ = lean_io_error_to_string(v_a_2228_);
v___x_2230_ = 3;
v___x_2231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*1, v___x_2230_);
v___x_2232_ = lean_array_get_size(v___y_2224_);
v___x_2233_ = lean_array_push(v___y_2224_, v___x_2231_);
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
return v___x_2234_;
}
}
v___jp_2235_:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lake_importConfigFile___lam__0(v___x_2065_, v___x_2062_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_options_2241_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v_options_2241_ = lean_ctor_get(v___y_2236_, 4);
lean_inc(v_options_2241_);
lean_dec_ref(v___y_2236_);
v_h_2069_ = v_a_2240_;
v_lakeOpts_2070_ = v_options_2241_;
v___y_2071_ = v___y_2237_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v___y_2236_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2242_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2243_ = lean_io_error_to_string(v_a_2242_);
v___x_2244_ = 3;
v___x_2245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*1, v___x_2244_);
v___x_2246_ = lean_array_get_size(v___y_2237_);
v___x_2247_ = lean_array_push(v___y_2237_, v___x_2245_);
v___x_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
return v___x_2248_;
}
}
v___jp_2249_:
{
if (v_reconfigure_2043_ == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_io_prim_handle_lock(v_h_2250_, v_reconfigure_2043_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref_known(v___x_2252_, 1);
v___x_2253_ = l_IO_FS_Handle_readToEnd(v_h_2250_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v___x_2255_ = l_Lean_Json_parse(v_a_2254_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v___x_2256_; 
lean_dec_ref_known(v___x_2255_, 1);
v___x_2256_ = l_Lake_importConfigFile___lam__0(v___x_2065_, v___x_2062_, v_h_2250_);
lean_dec(v_h_2250_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v_h_2069_ = v_a_2257_;
v_lakeOpts_2070_ = v_lakeOpts_2041_;
v___y_2071_ = v___y_2251_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2258_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2259_ = lean_io_error_to_string(v_a_2258_);
v___x_2260_ = 3;
v___x_2261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*1, v___x_2260_);
v___x_2262_ = lean_array_get_size(v___y_2251_);
v___x_2263_ = lean_array_push(v___y_2251_, v___x_2261_);
v___x_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
return v___x_2264_;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_n(v_a_2265_, 2);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2266_ = l___private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson(v_a_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2267_; 
lean_dec_ref_known(v___x_2266_, 1);
v___x_2267_ = l_Lean_Json_getObj_x3f(v_a_2265_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_dec_ref_known(v___x_2267_, 1);
v___y_2224_ = v___y_2251_;
v___y_2225_ = v_h_2250_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = ((lean_object*)(l___private_Lake_Load_Lean_Elab_0__Lake_instToJsonConfigTrace_toJson___closed__5));
v___x_2270_ = l_Lake_JsonObject_getJson_x3f(v_a_2268_, v___x_2269_);
lean_dec(v_a_2268_);
if (lean_obj_tag(v___x_2270_) == 0)
{
v___y_2224_ = v___y_2251_;
v___y_2225_ = v_h_2250_;
goto v___jp_2223_;
}
else
{
lean_object* v_val_2271_; lean_object* v___x_2272_; 
v_val_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_Load_Lean_Elab_0__Lake_instFromJsonConfigTrace_fromJson_spec__4_spec__4(v_val_2271_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec_ref_known(v___x_2272_, 1);
v___y_2224_ = v___y_2251_;
v___y_2225_ = v_h_2250_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
lean_dec(v_lakeOpts_2041_);
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = l_Lake_importConfigFile___lam__0(v___x_2065_, v___x_2062_, v_h_2250_);
lean_dec(v_h_2250_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v_h_2069_ = v_a_2275_;
v_lakeOpts_2070_ = v_a_2273_;
v___y_2071_ = v___y_2251_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v_a_2273_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2276_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2277_ = lean_io_error_to_string(v_a_2276_);
v___x_2278_ = 3;
v___x_2279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*1, v___x_2278_);
v___x_2280_ = lean_array_get_size(v___y_2251_);
v___x_2281_ = lean_array_push(v___y_2251_, v___x_2279_);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
return v___x_2282_;
}
}
}
}
}
else
{
lean_object* v_a_2283_; uint8_t v___x_2284_; 
lean_dec(v_a_2265_);
lean_dec(v_lakeOpts_2041_);
v_a_2283_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2284_ = l_System_FilePath_pathExists(v___x_2059_);
if (v___x_2284_ == 0)
{
v___y_2236_ = v_a_2283_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v_h_2250_;
goto v___jp_2235_;
}
else
{
lean_object* v_idx_2285_; lean_object* v_name_2286_; lean_object* v_platform_2287_; lean_object* v_leanHash_2288_; uint64_t v_configHash_2289_; uint8_t v___x_2290_; 
v_idx_2285_ = lean_ctor_get(v_a_2283_, 0);
v_name_2286_ = lean_ctor_get(v_a_2283_, 1);
v_platform_2287_ = lean_ctor_get(v_a_2283_, 2);
v_leanHash_2288_ = lean_ctor_get(v_a_2283_, 3);
v_configHash_2289_ = lean_ctor_get_uint64(v_a_2283_, sizeof(void*)*5);
v___x_2290_ = lean_nat_dec_eq(v_idx_2285_, v_pkgIdx_2037_);
if (v___x_2290_ == 0)
{
v___y_2236_ = v_a_2283_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v_h_2250_;
goto v___jp_2235_;
}
else
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_name_eq(v_name_2286_, v_pkgName_2038_);
if (v___x_2291_ == 0)
{
v___y_2236_ = v_a_2283_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v_h_2250_;
goto v___jp_2235_;
}
else
{
uint64_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = lean_unbox_uint64(v_a_2067_);
v___x_2293_ = lean_uint64_dec_eq(v_configHash_2289_, v___x_2292_);
if (v___x_2293_ == 0)
{
v___y_2236_ = v_a_2283_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v_h_2250_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = l_System_Platform_target;
v___x_2295_ = lean_string_dec_eq(v_platform_2287_, v___x_2294_);
if (v___x_2295_ == 0)
{
v___y_2236_ = v_a_2283_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v_h_2250_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = l_Lake_Env_leanGithash(v_lakeEnv_2035_);
v___x_2297_ = lean_string_dec_eq(v_leanHash_2288_, v___x_2296_);
lean_dec_ref(v___x_2296_);
if (v___x_2297_ == 0)
{
v___y_2236_ = v_a_2283_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v_h_2250_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2298_; 
lean_dec(v_a_2283_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v___x_2298_ = l___private_Lake_Load_Lean_Elab_0__Lake_importConfigFileCore(v___x_2059_, v_leanOpts_2042_);
lean_dec_ref(v___x_2059_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = lean_io_prim_handle_unlock(v_h_2250_);
lean_dec(v_h_2250_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; 
lean_dec_ref_known(v___x_2300_, 1);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2299_);
lean_ctor_set(v___x_2301_, 1, v___y_2251_);
return v___x_2301_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_a_2299_);
v_a_2302_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2303_ = lean_io_error_to_string(v_a_2302_);
v___x_2304_ = 3;
v___x_2305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*1, v___x_2304_);
v___x_2306_ = lean_array_get_size(v___y_2251_);
v___x_2307_ = lean_array_push(v___y_2251_, v___x_2305_);
v___x_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
return v___x_2308_;
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec(v_h_2250_);
v_a_2309_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2310_ = lean_io_error_to_string(v_a_2309_);
v___x_2311_ = 3;
v___x_2312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*1, v___x_2311_);
v___x_2313_ = lean_array_get_size(v___y_2251_);
v___x_2314_ = lean_array_push(v___y_2251_, v___x_2312_);
v___x_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
return v___x_2315_;
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
lean_object* v_a_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec(v_h_2250_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2316_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2253_, 1);
v___x_2317_ = lean_io_error_to_string(v_a_2316_);
v___x_2318_ = 3;
v___x_2319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*1, v___x_2318_);
v___x_2320_ = lean_array_get_size(v___y_2251_);
v___x_2321_ = lean_array_push(v___y_2251_, v___x_2319_);
v___x_2322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
return v___x_2322_;
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_h_2250_);
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2323_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2324_ = lean_io_error_to_string(v_a_2323_);
v___x_2325_ = 3;
v___x_2326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*1, v___x_2325_);
v___x_2327_ = lean_array_get_size(v___y_2251_);
v___x_2328_ = lean_array_push(v___y_2251_, v___x_2326_);
v___x_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
return v___x_2329_;
}
}
else
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lake_importConfigFile___lam__0(v___x_2065_, v___x_2062_, v_h_2250_);
lean_dec(v_h_2250_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v_h_2069_ = v_a_2331_;
v_lakeOpts_2070_ = v_lakeOpts_2041_;
v___y_2071_ = v___y_2251_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_a_2067_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2332_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2333_ = lean_io_error_to_string(v_a_2332_);
v___x_2334_ = 3;
v___x_2335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*1, v___x_2334_);
v___x_2336_ = lean_array_get_size(v___y_2251_);
v___x_2337_ = lean_array_push(v___y_2251_, v___x_2335_);
v___x_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2062_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2388_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2389_ = lean_io_error_to_string(v_a_2388_);
v___x_2390_ = 3;
v___x_2391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*1, v___x_2390_);
v___x_2392_ = lean_array_get_size(v_a_2029_);
v___x_2393_ = lean_array_push(v_a_2029_, v___x_2391_);
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
return v___x_2394_;
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v_configDir_2055_);
lean_dec(v_val_2049_);
lean_dec_ref(v_leanOpts_2042_);
lean_dec(v_lakeOpts_2041_);
lean_dec_ref(v_configFile_2040_);
lean_dec_ref(v_pkgDir_2039_);
lean_dec(v_pkgName_2038_);
lean_dec(v_pkgIdx_2037_);
lean_dec_ref(v_lakeEnv_2035_);
v_a_2395_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2396_ = lean_io_error_to_string(v_a_2395_);
v___x_2397_ = 3;
v___x_2398_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*1, v___x_2397_);
v___x_2399_ = lean_array_get_size(v_a_2029_);
v___x_2400_ = lean_array_push(v_a_2029_, v___x_2398_);
v___x_2401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
return v___x_2401_;
}
}
v___jp_2031_:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___y_2032_);
lean_ctor_set(v___x_2034_, 1, v_a_2033_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___boxed(lean_object* v_cfg_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lake_importConfigFile(v_cfg_2402_, v_a_2403_);
return v_res_2405_;
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
