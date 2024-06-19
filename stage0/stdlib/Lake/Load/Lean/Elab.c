// Lean compiler output
// Module: Lake.Load.Lean.Elab
// Imports: Init Lean.Elab.Frontend Lake.DSL.Extensions Lake.DSL.Attributes Lake.Load.Config Lake.Build.Trace Lake.Util.Log
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
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__40;
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_dirExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_instHashableImport__lake___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lake_importModulesUsingCache___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__21;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126____spec__1___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqImport__lake;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__49;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lake_importModulesUsingCache___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__3;
static lean_object* l_Lake_importConfigFile___closed__10;
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__7;
static lean_object* l_Lake_importConfigFile___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__39;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkExtNameMap(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__9;
lean_object* l___private_Init_GetElem_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lake_instToJsonConfigTrace___closed__1;
static lean_object* l_Lake_configModuleName___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__52;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__12;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__14;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lake_elabConfigFile___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__6;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_headerToImports(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__22;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__29;
lean_object* l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1315____spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__4;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__17;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__19;
extern lean_object* l_Lake_optsExt;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__19;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__21;
static lean_object* l_Lake_importConfigFileCore___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126____spec__1(lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__15;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__13;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__10;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__24;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__51;
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__13;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9;
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__2;
static lean_object* l_Lake_instBEqImport__lake___closed__1;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__43;
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14;
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__20;
lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__32;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84____boxed(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__34;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__23;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__18;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7___at_Lake_importModulesUsingCache___spec__8(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__5;
static lean_object* l_Lake_processHeader___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__38;
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonConfigTrace___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__27;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3;
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__16;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__31;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__2;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__12;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonConfigTrace;
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__8;
static lean_object* l_Lake_configModuleName___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__35;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__41;
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__53;
LEAN_EXPORT lean_object* l_Lake_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__50;
LEAN_EXPORT lean_object* l_Lake_instToJsonConfigTrace;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__47;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__25;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__1;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importModulesUsingCache___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__37;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__45;
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__3;
static lean_object* l_Lake_importConfigFile___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__33;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importEnvCache;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126_(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__44;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__20;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__7;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__30;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(lean_object*, size_t, size_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__4;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__15;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__48;
lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__42;
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lake_importModulesUsingCache___spec__4(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__46;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__9;
static lean_object* l_Lake_elabConfigFile___closed__3;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore_lakeExts;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__2;
LEAN_EXPORT lean_object* l_Lake_instHashableImport__lake;
static lean_object* l_Lake_importConfigFile___closed__2;
lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__11;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__16;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__26;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__36;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__54;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__6;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__28;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__17;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5;
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1;
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
if (x_4 == 0)
{
if (x_6 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instBEqImport__lake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instBEqImport__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instBEqImport__lake___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = 0;
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
if (x_3 == 0)
{
uint64_t x_7; uint64_t x_8; 
x_7 = 13;
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
else
{
uint64_t x_9; uint64_t x_10; 
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_6, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHashableImport__lake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instHashableImport__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instHashableImport__lake___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_Lean_mkHashMapImp___rarg(x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126____spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126____spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_4);
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3(x_1, x_4, lean_box(0), x_4, x_1, x_10);
if (x_11 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_84_(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7___at_Lake_importModulesUsingCache___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 7;
x_8 = lean_array_get_size(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_11 = lean_hashmap_mk_idx(x_6, x_7);
x_12 = lean_array_uget(x_1, x_11);
lean_ctor_set(x_2, 2, x_12);
x_13 = lean_array_uset(x_1, x_11, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_8, x_8);
if (x_15 == 0)
{
size_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_16 = lean_hashmap_mk_idx(x_6, x_7);
x_17 = lean_array_uget(x_1, x_16);
lean_ctor_set(x_2, 2, x_17);
x_18 = lean_array_uset(x_1, x_16, x_2);
x_1 = x_18;
x_2 = x_5;
goto _start;
}
else
{
size_t x_20; size_t x_21; uint64_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_22 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(x_4, x_20, x_21, x_7);
x_23 = lean_hashmap_mk_idx(x_6, x_22);
x_24 = lean_array_uget(x_1, x_23);
lean_ctor_set(x_2, 2, x_24);
x_25 = lean_array_uset(x_1, x_23, x_2);
x_1 = x_25;
x_2 = x_5;
goto _start;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_30 = lean_array_get_size(x_1);
x_31 = 7;
x_32 = lean_array_get_size(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
x_35 = lean_hashmap_mk_idx(x_30, x_31);
x_36 = lean_array_uget(x_1, x_35);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_array_uset(x_1, x_35, x_37);
x_1 = x_38;
x_2 = x_29;
goto _start;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_32, x_32);
if (x_40 == 0)
{
size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_32);
x_41 = lean_hashmap_mk_idx(x_30, x_31);
x_42 = lean_array_uget(x_1, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_uset(x_1, x_41, x_43);
x_1 = x_44;
x_2 = x_29;
goto _start;
}
else
{
size_t x_46; size_t x_47; uint64_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(x_27, x_46, x_47, x_31);
x_49 = lean_hashmap_mk_idx(x_30, x_48);
x_50 = lean_array_uget(x_1, x_49);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_28);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_array_uset(x_1, x_49, x_51);
x_1 = x_52;
x_2 = x_29;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lake_importModulesUsingCache___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7___at_Lake_importModulesUsingCache___spec__8(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lake_importModulesUsingCache___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lake_importModulesUsingCache___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_array_get_size(x_6);
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10(x_1, x_6, lean_box(0), x_6, x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_15);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_19 = lean_array_get_size(x_16);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(x_1, x_2, x_18);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10(x_1, x_16, lean_box(0), x_16, x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(x_1, x_2, x_18);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_18);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lake_importModulesUsingCache___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_7 = lean_array_get_size(x_5);
x_26 = 7;
x_27 = lean_array_get_size(x_2);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
x_8 = x_26;
goto block_25;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_dec(x_27);
x_8 = x_26;
goto block_25;
}
else
{
size_t x_31; size_t x_32; uint64_t x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(x_2, x_31, x_32, x_26);
x_8 = x_33;
goto block_25;
}
}
block_25:
{
size_t x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_5, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_6);
x_18 = l_Lean_HashMapImp_expand___at_Lake_importModulesUsingCache___spec__4(x_13, x_15);
return x_18;
}
else
{
lean_object* x_19; 
if (lean_is_scalar(x_6)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_6;
}
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_5, x_9, x_20);
x_22 = l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(x_2, x_3, x_10);
x_23 = lean_array_uset(x_21, x_9, x_22);
if (lean_is_scalar(x_6)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_6;
}
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_array_get_size(x_4);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13(x_1, x_4, lean_box(0), x_4, x_1, x_11);
if (x_12 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_14; 
lean_inc(x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = 7;
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = lean_hashmap_mk_idx(x_4, x_5);
x_10 = lean_array_uget(x_3, x_9);
x_11 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_2, x_10);
lean_dec(x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = lean_hashmap_mk_idx(x_4, x_5);
x_14 = lean_array_uget(x_3, x_13);
x_15 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_2, x_14);
lean_dec(x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(x_2, x_16, x_17, x_5);
x_19 = lean_hashmap_mk_idx(x_4, x_18);
x_20 = lean_array_uget(x_3, x_19);
x_21 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_2, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lake_importModulesUsingCache___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_importEnvCache;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
lean_inc(x_1);
x_7 = lean_import_modules(x_1, x_2, x_3, x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lake_importModulesUsingCache___lambda__1___closed__1;
x_11 = lean_st_ref_take(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
x_14 = l_Lean_HashMap_insert___at_Lake_importModulesUsingCache___spec__1(x_12, x_1, x_8);
x_15 = lean_st_ref_set(x_10, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_8);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lake_importModulesUsingCache___lambda__1___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(x_8, x_1);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_box(0);
x_12 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(x_14, x_1);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_17, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_7 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_Lake_importModulesUsingCache(x_1, x_2, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_processHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_6 = l_Lean_Elab_headerToImports(x_1);
x_7 = 1024;
x_8 = l_Lake_importModulesUsingCache(x_6, x_2, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = 0;
x_20 = l_Lean_Syntax_getPos_x3f(x_1, x_19);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_io_error_to_string(x_16);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = 0;
x_27 = lean_mk_empty_environment(x_26, x_17);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_FileMap_toPosition(x_18, x_30);
x_32 = 2;
x_33 = l_Lake_processHeader___closed__1;
x_34 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 1, x_32);
x_35 = l_Lean_MessageLog_add(x_34, x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_FileMap_toPosition(x_18, x_39);
x_41 = 2;
x_42 = l_Lake_processHeader___closed__1;
x_43 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_22);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_25);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_41);
x_44 = l_Lean_MessageLog_add(x_43, x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_20, 0);
lean_inc(x_51);
lean_dec(x_20);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = l_Lean_FileMap_toPosition(x_18, x_51);
lean_dec(x_51);
x_55 = 2;
x_56 = l_Lake_processHeader___closed__1;
x_57 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_22);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_25);
lean_ctor_set_uint8(x_57, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_57, sizeof(void*)*5 + 1, x_55);
x_58 = l_Lean_MessageLog_add(x_57, x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_27, 0, x_59);
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
x_62 = l_Lean_FileMap_toPosition(x_18, x_51);
lean_dec(x_51);
x_63 = 2;
x_64 = l_Lake_processHeader___closed__1;
x_65 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_22);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 4, x_25);
lean_ctor_set_uint8(x_65, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_65, sizeof(void*)*5 + 1, x_63);
x_66 = l_Lean_MessageLog_add(x_65, x_4);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_27);
if (x_69 == 0)
{
return x_27;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_27, 0);
x_71 = lean_ctor_get(x_27, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_27);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_processHeader(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_configModuleName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lakefile", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_configModuleName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_configModuleName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_configModuleName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_configModuleName___closed__2;
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lake_elabConfigFile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_31; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_9 = x_1;
} else {
 lean_dec_ref(x_1);
 x_9 = lean_box(0);
}
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*5 + 1);
switch (x_31) {
case 0:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
x_33 = l_Lean_Message_toString(x_7, x_32, x_4);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_3, x_38);
x_40 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
lean_ctor_set(x_33, 1, x_39);
lean_ctor_set(x_33, 0, x_40);
x_10 = x_33;
x_11 = x_36;
goto block_30;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = 1;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_push(x_3, x_44);
x_46 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_10 = x_47;
x_11 = x_42;
goto block_30;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
x_51 = lean_io_error_to_string(x_49);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_3);
x_55 = lean_array_push(x_3, x_53);
lean_ctor_set(x_33, 1, x_55);
lean_ctor_set(x_33, 0, x_54);
x_10 = x_33;
x_11 = x_50;
goto block_30;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_33, 0);
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_33);
x_58 = lean_io_error_to_string(x_56);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_get_size(x_3);
x_62 = lean_array_push(x_3, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_10 = x_63;
x_11 = x_57;
goto block_30;
}
}
}
case 1:
{
uint8_t x_64; lean_object* x_65; 
x_64 = 0;
x_65 = l_Lean_Message_toString(x_7, x_64, x_4);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = 2;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_array_push(x_3, x_70);
x_72 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
lean_ctor_set(x_65, 1, x_71);
lean_ctor_set(x_65, 0, x_72);
x_10 = x_65;
x_11 = x_68;
goto block_30;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_65, 0);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_65);
x_75 = 2;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_push(x_3, x_76);
x_78 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_10 = x_79;
x_11 = x_74;
goto block_30;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
x_83 = lean_io_error_to_string(x_81);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_get_size(x_3);
x_87 = lean_array_push(x_3, x_85);
lean_ctor_set(x_65, 1, x_87);
lean_ctor_set(x_65, 0, x_86);
x_10 = x_65;
x_11 = x_82;
goto block_30;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_65, 0);
x_89 = lean_ctor_get(x_65, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_65);
x_90 = lean_io_error_to_string(x_88);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_array_get_size(x_3);
x_94 = lean_array_push(x_3, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_10 = x_95;
x_11 = x_89;
goto block_30;
}
}
}
default: 
{
uint8_t x_96; lean_object* x_97; 
x_96 = 0;
x_97 = l_Lean_Message_toString(x_7, x_96, x_4);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = 3;
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
x_103 = lean_array_push(x_3, x_102);
x_104 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
lean_ctor_set(x_97, 1, x_103);
lean_ctor_set(x_97, 0, x_104);
x_10 = x_97;
x_11 = x_100;
goto block_30;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_97, 0);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_97);
x_107 = 3;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_push(x_3, x_108);
x_110 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_10 = x_111;
x_11 = x_106;
goto block_30;
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_97);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_97, 0);
x_114 = lean_ctor_get(x_97, 1);
x_115 = lean_io_error_to_string(x_113);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_get_size(x_3);
x_119 = lean_array_push(x_3, x_117);
lean_ctor_set(x_97, 1, x_119);
lean_ctor_set(x_97, 0, x_118);
x_10 = x_97;
x_11 = x_114;
goto block_30;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_97, 0);
x_121 = lean_ctor_get(x_97, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_97);
x_122 = lean_io_error_to_string(x_120);
x_123 = 3;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_array_get_size(x_3);
x_126 = lean_array_push(x_3, x_124);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_10 = x_127;
x_11 = x_121;
goto block_30;
}
}
}
}
block_30:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_15);
if (lean_is_scalar(x_9)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_9;
 lean_ctor_set_tag(x_16, 0);
}
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
if (lean_is_scalar(x_9)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_9;
 lean_ctor_set_tag(x_20, 0);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_1 = x_8;
x_2 = x_22;
x_3 = x_21;
x_4 = x_11;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; 
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_9;
 lean_ctor_set_tag(x_25, 0);
}
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_9)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_9;
 lean_ctor_set_tag(x_29, 0);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
return x_29;
}
}
}
}
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": package configuration has errors", 34);
return x_1;
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_dirExt;
return x_1;
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_optsExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_79; lean_object* x_80; lean_object* x_318; 
x_318 = l_IO_FS_readFile(x_4, x_6);
if (lean_obj_tag(x_318) == 0)
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_318, 1);
lean_ctor_set(x_318, 1, x_5);
x_79 = x_318;
x_80 = x_320;
goto block_317;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_318, 0);
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_318);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_5);
x_79 = x_323;
x_80 = x_322;
goto block_317;
}
}
else
{
uint8_t x_324; 
x_324 = !lean_is_exclusive(x_318);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_325 = lean_ctor_get(x_318, 0);
x_326 = lean_ctor_get(x_318, 1);
x_327 = lean_io_error_to_string(x_325);
x_328 = 3;
x_329 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*1, x_328);
x_330 = lean_array_get_size(x_5);
x_331 = lean_array_push(x_5, x_329);
lean_ctor_set(x_318, 1, x_331);
lean_ctor_set(x_318, 0, x_330);
x_79 = x_318;
x_80 = x_326;
goto block_317;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_332 = lean_ctor_get(x_318, 0);
x_333 = lean_ctor_get(x_318, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_318);
x_334 = lean_io_error_to_string(x_332);
x_335 = 3;
x_336 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set_uint8(x_336, sizeof(void*)*1, x_335);
x_337 = lean_array_get_size(x_5);
x_338 = lean_array_push(x_5, x_336);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_79 = x_339;
x_80 = x_333;
goto block_317;
}
}
block_78:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_MessageLog_toList(x_13);
x_15 = lean_box(0);
x_16 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1(x_14, x_15, x_11, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = l_Lean_MessageLog_hasErrors(x_13);
lean_dec(x_13);
if (x_23 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_17, 0, x_12);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_24 = l_Lake_processHeader___closed__1;
x_25 = lean_string_append(x_24, x_4);
lean_dec(x_4);
x_26 = l_Lake_elabConfigFile___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_21);
x_31 = lean_array_push(x_21, x_29);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_31);
lean_ctor_set(x_17, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = l_Lean_MessageLog_hasErrors(x_13);
lean_dec(x_13);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_4);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_16, 0, x_34);
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_12);
x_35 = l_Lake_processHeader___closed__1;
x_36 = lean_string_append(x_35, x_4);
lean_dec(x_4);
x_37 = l_Lake_elabConfigFile___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_32);
x_42 = lean_array_push(x_32, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_16, 0, x_43);
return x_16;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_46 = x_17;
} else {
 lean_dec_ref(x_17);
 x_46 = lean_box(0);
}
x_47 = l_Lean_MessageLog_hasErrors(x_13);
lean_dec(x_13);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_4);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
x_50 = l_Lake_processHeader___closed__1;
x_51 = lean_string_append(x_50, x_4);
lean_dec(x_4);
x_52 = l_Lake_elabConfigFile___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_45);
x_57 = lean_array_push(x_45, x_55);
if (lean_is_scalar(x_46)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_46;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_44);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_16, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_17);
if (x_62 == 0)
{
return x_16;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_17, 0);
x_64 = lean_ctor_get(x_17, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_17);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_16, 0, x_65);
return x_16;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_dec(x_16);
x_67 = lean_ctor_get(x_17, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_17, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_69 = x_17;
} else {
 lean_dec_ref(x_17);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_7);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_7);
lean_ctor_set(x_73, 1, x_8);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_7, 0);
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_7);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_8);
return x_77;
}
}
}
block_317:
{
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_223; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
x_84 = 1;
lean_inc(x_4);
x_85 = l_Lean_Parser_mkInputContext(x_82, x_4, x_84);
lean_inc(x_85);
x_223 = l_Lean_Parser_parseHeader(x_85, x_80);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
lean_ctor_set(x_79, 0, x_224);
x_86 = x_79;
x_87 = x_225;
goto block_222;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
x_228 = lean_io_error_to_string(x_226);
x_229 = 3;
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_229);
x_231 = lean_array_get_size(x_83);
x_232 = lean_array_push(x_83, x_230);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 1, x_232);
lean_ctor_set(x_79, 0, x_231);
x_86 = x_79;
x_87 = x_227;
goto block_222;
}
block_222:
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_90 = !lean_is_exclusive(x_86);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_155; 
x_91 = lean_ctor_get(x_86, 1);
x_92 = lean_ctor_get(x_86, 0);
lean_dec(x_92);
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
lean_inc(x_85);
lean_inc(x_3);
x_155 = l_Lake_processHeader(x_93, x_3, x_85, x_95, x_87);
lean_dec(x_93);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_ctor_set(x_86, 0, x_156);
x_97 = x_86;
x_98 = x_157;
goto block_154;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
x_160 = lean_io_error_to_string(x_158);
x_161 = 3;
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
x_163 = lean_array_get_size(x_91);
x_164 = lean_array_push(x_91, x_162);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 1, x_164);
lean_ctor_set(x_86, 0, x_163);
x_97 = x_86;
x_98 = x_159;
goto block_154;
}
block_154:
{
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_99; 
lean_dec(x_96);
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_ctor_get(x_97, 1);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = l_Lake_configModuleName;
x_105 = lean_environment_set_main_module(x_102, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_1);
x_107 = l_Lake_elabConfigFile___closed__2;
x_108 = l_Lean_EnvExtension_setState___rarg(x_107, x_105, x_106);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_2);
x_110 = l_Lake_elabConfigFile___closed__3;
x_111 = l_Lean_EnvExtension_setState___rarg(x_110, x_108, x_109);
x_112 = l_Lean_Elab_Command_mkState(x_111, x_103, x_3);
x_113 = l_Lean_Elab_IO_processCommands(x_85, x_94, x_112, x_98);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_ctor_set(x_97, 0, x_114);
x_7 = x_97;
x_8 = x_115;
goto block_78;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_io_error_to_string(x_116);
x_119 = 3;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_array_get_size(x_101);
x_122 = lean_array_push(x_101, x_120);
lean_ctor_set_tag(x_97, 1);
lean_ctor_set(x_97, 1, x_122);
lean_ctor_set(x_97, 0, x_121);
x_7 = x_97;
x_8 = x_117;
goto block_78;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_123 = lean_ctor_get(x_97, 0);
x_124 = lean_ctor_get(x_97, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_97);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = l_Lake_configModuleName;
x_128 = lean_environment_set_main_module(x_125, x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_1);
x_130 = l_Lake_elabConfigFile___closed__2;
x_131 = l_Lean_EnvExtension_setState___rarg(x_130, x_128, x_129);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_2);
x_133 = l_Lake_elabConfigFile___closed__3;
x_134 = l_Lean_EnvExtension_setState___rarg(x_133, x_131, x_132);
x_135 = l_Lean_Elab_Command_mkState(x_134, x_126, x_3);
x_136 = l_Lean_Elab_IO_processCommands(x_85, x_94, x_135, x_98);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_124);
x_7 = x_139;
x_8 = x_138;
goto block_78;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_io_error_to_string(x_140);
x_143 = 3;
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = lean_array_get_size(x_124);
x_146 = lean_array_push(x_124, x_144);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_7 = x_147;
x_8 = x_141;
goto block_78;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_94);
lean_dec(x_85);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_97);
if (x_148 == 0)
{
lean_object* x_149; 
if (lean_is_scalar(x_96)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_96;
}
lean_ctor_set(x_149, 0, x_97);
lean_ctor_set(x_149, 1, x_98);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_97, 0);
x_151 = lean_ctor_get(x_97, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_97);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
if (lean_is_scalar(x_96)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_96;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_98);
return x_153;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_204; 
x_165 = lean_ctor_get(x_86, 1);
lean_inc(x_165);
lean_dec(x_86);
x_166 = lean_ctor_get(x_88, 0);
lean_inc(x_166);
lean_dec(x_88);
x_167 = lean_ctor_get(x_89, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_89, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_169 = x_89;
} else {
 lean_dec_ref(x_89);
 x_169 = lean_box(0);
}
lean_inc(x_85);
lean_inc(x_3);
x_204 = l_Lake_processHeader(x_166, x_3, x_85, x_168, x_87);
lean_dec(x_166);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_165);
x_170 = x_207;
x_171 = x_206;
goto block_203;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_204, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_dec(x_204);
x_210 = lean_io_error_to_string(x_208);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_array_get_size(x_165);
x_214 = lean_array_push(x_165, x_212);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_170 = x_215;
x_171 = x_209;
goto block_203;
}
block_203:
{
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_174 = x_170;
} else {
 lean_dec_ref(x_170);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = l_Lake_configModuleName;
x_178 = lean_environment_set_main_module(x_175, x_177);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_1);
x_180 = l_Lake_elabConfigFile___closed__2;
x_181 = l_Lean_EnvExtension_setState___rarg(x_180, x_178, x_179);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_2);
x_183 = l_Lake_elabConfigFile___closed__3;
x_184 = l_Lean_EnvExtension_setState___rarg(x_183, x_181, x_182);
x_185 = l_Lean_Elab_Command_mkState(x_184, x_176, x_3);
x_186 = l_Lean_Elab_IO_processCommands(x_85, x_167, x_185, x_171);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
if (lean_is_scalar(x_174)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_174;
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_173);
x_7 = x_189;
x_8 = x_188;
goto block_78;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_dec(x_186);
x_192 = lean_io_error_to_string(x_190);
x_193 = 3;
x_194 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_193);
x_195 = lean_array_get_size(x_173);
x_196 = lean_array_push(x_173, x_194);
if (lean_is_scalar(x_174)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_174;
 lean_ctor_set_tag(x_197, 1);
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_7 = x_197;
x_8 = x_191;
goto block_78;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_167);
lean_dec(x_85);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_170, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_170, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_200 = x_170;
} else {
 lean_dec_ref(x_170);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
if (lean_is_scalar(x_169)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_169;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_171);
return x_202;
}
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_85);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_86);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_86);
lean_ctor_set(x_217, 1, x_87);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_86, 0);
x_219 = lean_ctor_get(x_86, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_86);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_87);
return x_221;
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_299; 
x_233 = lean_ctor_get(x_79, 0);
x_234 = lean_ctor_get(x_79, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_79);
x_235 = 1;
lean_inc(x_4);
x_236 = l_Lean_Parser_mkInputContext(x_233, x_4, x_235);
lean_inc(x_236);
x_299 = l_Lean_Parser_parseHeader(x_236, x_80);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_234);
x_237 = x_302;
x_238 = x_301;
goto block_298;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_303 = lean_ctor_get(x_299, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_299, 1);
lean_inc(x_304);
lean_dec(x_299);
x_305 = lean_io_error_to_string(x_303);
x_306 = 3;
x_307 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_306);
x_308 = lean_array_get_size(x_234);
x_309 = lean_array_push(x_234, x_307);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_237 = x_310;
x_238 = x_304;
goto block_298;
}
block_298:
{
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_281; 
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_242 = x_237;
} else {
 lean_dec_ref(x_237);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_ctor_get(x_240, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_246 = x_240;
} else {
 lean_dec_ref(x_240);
 x_246 = lean_box(0);
}
lean_inc(x_236);
lean_inc(x_3);
x_281 = l_Lake_processHeader(x_243, x_3, x_236, x_245, x_238);
lean_dec(x_243);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
if (lean_is_scalar(x_242)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_242;
}
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_241);
x_247 = x_284;
x_248 = x_283;
goto block_280;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_281, 1);
lean_inc(x_286);
lean_dec(x_281);
x_287 = lean_io_error_to_string(x_285);
x_288 = 3;
x_289 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*1, x_288);
x_290 = lean_array_get_size(x_241);
x_291 = lean_array_push(x_241, x_289);
if (lean_is_scalar(x_242)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_242;
 lean_ctor_set_tag(x_292, 1);
}
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_247 = x_292;
x_248 = x_286;
goto block_280;
}
block_280:
{
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_246);
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_251 = x_247;
} else {
 lean_dec_ref(x_247);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_249, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_249, 1);
lean_inc(x_253);
lean_dec(x_249);
x_254 = l_Lake_configModuleName;
x_255 = lean_environment_set_main_module(x_252, x_254);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_1);
x_257 = l_Lake_elabConfigFile___closed__2;
x_258 = l_Lean_EnvExtension_setState___rarg(x_257, x_255, x_256);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_2);
x_260 = l_Lake_elabConfigFile___closed__3;
x_261 = l_Lean_EnvExtension_setState___rarg(x_260, x_258, x_259);
x_262 = l_Lean_Elab_Command_mkState(x_261, x_253, x_3);
x_263 = l_Lean_Elab_IO_processCommands(x_236, x_244, x_262, x_248);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
if (lean_is_scalar(x_251)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_251;
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_250);
x_7 = x_266;
x_8 = x_265;
goto block_78;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
lean_dec(x_263);
x_269 = lean_io_error_to_string(x_267);
x_270 = 3;
x_271 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_270);
x_272 = lean_array_get_size(x_250);
x_273 = lean_array_push(x_250, x_271);
if (lean_is_scalar(x_251)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_251;
 lean_ctor_set_tag(x_274, 1);
}
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_7 = x_274;
x_8 = x_268;
goto block_78;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_244);
lean_dec(x_236);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = lean_ctor_get(x_247, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_247, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_277 = x_247;
} else {
 lean_dec_ref(x_247);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
if (lean_is_scalar(x_246)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_246;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_248);
return x_279;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_236);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = lean_ctor_get(x_237, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_237, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_295 = x_237;
} else {
 lean_dec_ref(x_237);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_238);
return x_297;
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_79);
if (x_311 == 0)
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_79);
lean_ctor_set(x_312, 1, x_80);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_ctor_get(x_79, 0);
x_314 = lean_ctor_get(x_79, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_79);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_80);
return x_316;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("packageAttr", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__3;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("packageDepAttr", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__4;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__6;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("postUpdateAttr", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__7;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__9;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("scriptAttr", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__10;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__12;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("defaultScriptAttr", 17);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__13;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__15;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("leanLibAttr", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__16;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__18;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("leanExeAttr", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__20;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__19;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__21;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("externLibAttr", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__23;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__22;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__24;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("targetAttr", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__26;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__25;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__27;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("defaultTargetAttr", 17);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__29;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__28;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__30;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("testDriverAttr", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__32;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__31;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__33;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lintDriverAttr", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__35;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__34;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__36;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("moduleFacetAttr", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__38;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__37;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__39;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("packageFacetAttr", 16);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__41;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__40;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__42;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("libraryFacetAttr", 16);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__44;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__43;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__45;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docStringExt", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__47;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__48;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__46;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__49;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IR", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declMapExt", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__47;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__51;
x_3 = l_Lake_importConfigFileCore_lakeExts___closed__52;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__50;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__53;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__54;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedEnvExtensionState;
x_2 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lake_importConfigFileCore_lakeExts;
x_14 = l_Lean_NameSet_contains(x_13, x_11);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_2, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_1);
x_20 = lean_nat_dec_lt(x_18, x_19);
lean_dec(x_19);
x_21 = lean_array_get_size(x_12);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_20 == 0)
{
lean_dec(x_18);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1;
x_26 = l___private_Init_GetElem_0__outOfBounds___rarg(x_25);
x_27 = lean_nat_dec_le(x_21, x_21);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(x_26, x_12, x_29, x_30, x_6);
lean_dec(x_12);
x_4 = x_10;
x_6 = x_31;
goto _start;
}
}
}
else
{
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_array_fget(x_1, x_18);
lean_dec(x_18);
x_35 = lean_nat_dec_le(x_21, x_21);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_21);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(x_34, x_12, x_37, x_38, x_6);
lean_dec(x_12);
x_4 = x_10;
x_6 = x_39;
goto _start;
}
}
}
}
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_environment_add(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lake_importConfigFileCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_persistentEnvExtensionsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_read_module_data(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 1024;
x_10 = l_Lake_importModulesUsingCache(x_8, x_2, x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
x_17 = l_Lake_importConfigFileCore___closed__1;
x_18 = lean_st_ref_get(x_17, x_12);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
x_19 = x_11;
goto block_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_14, x_14);
if (x_45 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
x_19 = x_11;
goto block_44;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4(x_13, x_46, x_47, x_11);
lean_dec(x_13);
x_19 = x_48;
goto block_44;
}
}
block_44:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_mkExtNameMap(x_15, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_7, 4);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_15, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(x_20, x_24, x_25, x_29, x_30, x_19);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_ctor_get(x_7, 4);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_15, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_35, x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(x_20, x_32, x_34, x_40, x_41, x_19);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_20);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
return x_4;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_importConfigFileCore(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("platform", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("leanHash", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("configHash", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("options", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_16 = lean_uint64_to_nat(x_15);
x_17 = l_Lean_bignumToJson(x_16);
x_18 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_box(0);
x_22 = l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(x_21, x_5);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__4;
x_32 = l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1315____spec__1(x_30, x_31);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
static lean_object* _init_l_Lake_instToJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonConfigTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonConfigTrace___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint64_of_nat(x_1);
x_4 = lean_box_uint64(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value '{j}' is too large for `UInt64`", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_bignumFromJson_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__1;
x_10 = lean_nat_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___lambda__1(x_8, x_11);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__3;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getObj_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(x_9, x_8);
return x_10;
}
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ConfigTrace", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__2;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__3;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__6;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__8;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__11;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__12;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__13;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__15;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__17;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__19;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__20;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__21;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2;
lean_inc(x_1);
x_14 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3;
lean_inc(x_1);
x_25 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5;
x_36 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__2(x_1, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_23);
lean_ctor_set(x_47, 2, x_34);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_36, 0, x_47);
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_23);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonConfigTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonConfigTrace___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid configuration file name", 31);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_importConfigFile___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("olean", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("olean.trace", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("olean.lock", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiled configuration is invalid; run with '-R' to reconfigure", 63);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_importConfigFile___closed__6;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not acquire an exclusive configuration lock; ", 51);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("another process may already be reconfiguring the package", 56);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFile___closed__8;
x_2 = l_Lake_importConfigFile___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_importConfigFile___closed__10;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = l_System_FilePath_join(x_4, x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
x_8 = l_System_FilePath_join(x_6, x_7);
lean_inc(x_8);
x_9 = l_System_FilePath_fileName(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lake_importConfigFile___closed__2;
x_12 = lean_array_push(x_2, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_2088; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_16 = x_9;
} else {
 lean_dec_ref(x_9);
 x_16 = lean_box(0);
}
x_17 = l_Lake_defaultLakeDir;
lean_inc(x_6);
x_18 = l_System_FilePath_join(x_6, x_17);
x_19 = l_Lake_importConfigFile___closed__3;
lean_inc(x_15);
x_20 = l_System_FilePath_withExtension(x_15, x_19);
lean_inc(x_18);
x_21 = l_System_FilePath_join(x_18, x_20);
x_22 = l_Lake_importConfigFile___closed__4;
lean_inc(x_15);
x_23 = l_System_FilePath_withExtension(x_15, x_22);
lean_inc(x_18);
x_24 = l_System_FilePath_join(x_18, x_23);
x_25 = l_Lake_importConfigFile___closed__5;
x_26 = l_System_FilePath_withExtension(x_15, x_25);
lean_inc(x_18);
x_27 = l_System_FilePath_join(x_18, x_26);
x_2088 = l_Lake_computeTextFileHash(x_8, x_3);
if (lean_obj_tag(x_2088) == 0)
{
uint8_t x_2089; 
x_2089 = !lean_is_exclusive(x_2088);
if (x_2089 == 0)
{
lean_object* x_2090; 
x_2090 = lean_ctor_get(x_2088, 1);
lean_ctor_set(x_2088, 1, x_2);
x_28 = x_2088;
x_29 = x_2090;
goto block_2087;
}
else
{
lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; 
x_2091 = lean_ctor_get(x_2088, 0);
x_2092 = lean_ctor_get(x_2088, 1);
lean_inc(x_2092);
lean_inc(x_2091);
lean_dec(x_2088);
x_2093 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2093, 0, x_2091);
lean_ctor_set(x_2093, 1, x_2);
x_28 = x_2093;
x_29 = x_2092;
goto block_2087;
}
}
else
{
uint8_t x_2094; 
x_2094 = !lean_is_exclusive(x_2088);
if (x_2094 == 0)
{
lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; uint8_t x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; 
x_2095 = lean_ctor_get(x_2088, 0);
x_2096 = lean_ctor_get(x_2088, 1);
x_2097 = lean_io_error_to_string(x_2095);
x_2098 = 3;
x_2099 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2099, 0, x_2097);
lean_ctor_set_uint8(x_2099, sizeof(void*)*1, x_2098);
x_2100 = lean_array_get_size(x_2);
x_2101 = lean_array_push(x_2, x_2099);
lean_ctor_set(x_2088, 1, x_2101);
lean_ctor_set(x_2088, 0, x_2100);
x_28 = x_2088;
x_29 = x_2096;
goto block_2087;
}
else
{
lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; uint8_t x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; 
x_2102 = lean_ctor_get(x_2088, 0);
x_2103 = lean_ctor_get(x_2088, 1);
lean_inc(x_2103);
lean_inc(x_2102);
lean_dec(x_2088);
x_2104 = lean_io_error_to_string(x_2102);
x_2105 = 3;
x_2106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2106, 0, x_2104);
lean_ctor_set_uint8(x_2106, sizeof(void*)*1, x_2105);
x_2107 = lean_array_get_size(x_2);
x_2108 = lean_array_push(x_2, x_2106);
x_2109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2109, 0, x_2107);
lean_ctor_set(x_2109, 1, x_2108);
x_28 = x_2109;
x_29 = x_2103;
goto block_2087;
}
}
block_2087:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_519; lean_object* x_520; lean_object* x_1253; lean_object* x_1254; lean_object* x_1991; lean_object* x_1992; uint8_t x_1993; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_1991 = l_System_FilePath_pathExists(x_24, x_29);
x_1992 = lean_ctor_get(x_1991, 0);
lean_inc(x_1992);
x_1993 = lean_unbox(x_1992);
lean_dec(x_1992);
if (x_1993 == 0)
{
uint8_t x_1994; 
x_1994 = !lean_is_exclusive(x_1991);
if (x_1994 == 0)
{
lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; 
x_1995 = lean_ctor_get(x_1991, 1);
x_1996 = lean_ctor_get(x_1991, 0);
lean_dec(x_1996);
x_1997 = l_IO_FS_createDirAll(x_18, x_1995);
if (lean_obj_tag(x_1997) == 0)
{
lean_object* x_1998; uint8_t x_1999; lean_object* x_2000; 
lean_free_object(x_1991);
x_1998 = lean_ctor_get(x_1997, 1);
lean_inc(x_1998);
lean_dec(x_1997);
x_1999 = 2;
x_2000 = lean_io_prim_handle_mk(x_24, x_1999, x_1998);
if (lean_obj_tag(x_2000) == 0)
{
uint8_t x_2001; 
x_2001 = !lean_is_exclusive(x_2000);
if (x_2001 == 0)
{
lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; 
x_2002 = lean_ctor_get(x_2000, 0);
x_2003 = lean_ctor_get(x_2000, 1);
x_2004 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2004, 0, x_2002);
lean_ctor_set(x_2000, 1, x_31);
lean_ctor_set(x_2000, 0, x_2004);
x_1253 = x_2000;
x_1254 = x_2003;
goto block_1990;
}
else
{
lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; 
x_2005 = lean_ctor_get(x_2000, 0);
x_2006 = lean_ctor_get(x_2000, 1);
lean_inc(x_2006);
lean_inc(x_2005);
lean_dec(x_2000);
x_2007 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2007, 0, x_2005);
x_2008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2008, 0, x_2007);
lean_ctor_set(x_2008, 1, x_31);
x_1253 = x_2008;
x_1254 = x_2006;
goto block_1990;
}
}
else
{
uint8_t x_2009; 
x_2009 = !lean_is_exclusive(x_2000);
if (x_2009 == 0)
{
lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; 
x_2010 = lean_ctor_get(x_2000, 0);
x_2011 = lean_ctor_get(x_2000, 1);
x_2012 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2012, 0, x_2010);
lean_ctor_set_tag(x_2000, 0);
lean_ctor_set(x_2000, 1, x_31);
lean_ctor_set(x_2000, 0, x_2012);
x_1253 = x_2000;
x_1254 = x_2011;
goto block_1990;
}
else
{
lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; 
x_2013 = lean_ctor_get(x_2000, 0);
x_2014 = lean_ctor_get(x_2000, 1);
lean_inc(x_2014);
lean_inc(x_2013);
lean_dec(x_2000);
x_2015 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2015, 0, x_2013);
x_2016 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2016, 0, x_2015);
lean_ctor_set(x_2016, 1, x_31);
x_1253 = x_2016;
x_1254 = x_2014;
goto block_1990;
}
}
}
else
{
uint8_t x_2017; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2017 = !lean_is_exclusive(x_1997);
if (x_2017 == 0)
{
lean_object* x_2018; lean_object* x_2019; uint8_t x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; 
x_2018 = lean_ctor_get(x_1997, 0);
x_2019 = lean_io_error_to_string(x_2018);
x_2020 = 3;
x_2021 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2021, 0, x_2019);
lean_ctor_set_uint8(x_2021, sizeof(void*)*1, x_2020);
x_2022 = lean_array_get_size(x_31);
x_2023 = lean_array_push(x_31, x_2021);
lean_ctor_set_tag(x_1991, 1);
lean_ctor_set(x_1991, 1, x_2023);
lean_ctor_set(x_1991, 0, x_2022);
lean_ctor_set_tag(x_1997, 0);
lean_ctor_set(x_1997, 0, x_1991);
return x_1997;
}
else
{
lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; uint8_t x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; 
x_2024 = lean_ctor_get(x_1997, 0);
x_2025 = lean_ctor_get(x_1997, 1);
lean_inc(x_2025);
lean_inc(x_2024);
lean_dec(x_1997);
x_2026 = lean_io_error_to_string(x_2024);
x_2027 = 3;
x_2028 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2028, 0, x_2026);
lean_ctor_set_uint8(x_2028, sizeof(void*)*1, x_2027);
x_2029 = lean_array_get_size(x_31);
x_2030 = lean_array_push(x_31, x_2028);
lean_ctor_set_tag(x_1991, 1);
lean_ctor_set(x_1991, 1, x_2030);
lean_ctor_set(x_1991, 0, x_2029);
x_2031 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2031, 0, x_1991);
lean_ctor_set(x_2031, 1, x_2025);
return x_2031;
}
}
}
else
{
lean_object* x_2032; lean_object* x_2033; 
x_2032 = lean_ctor_get(x_1991, 1);
lean_inc(x_2032);
lean_dec(x_1991);
x_2033 = l_IO_FS_createDirAll(x_18, x_2032);
if (lean_obj_tag(x_2033) == 0)
{
lean_object* x_2034; uint8_t x_2035; lean_object* x_2036; 
x_2034 = lean_ctor_get(x_2033, 1);
lean_inc(x_2034);
lean_dec(x_2033);
x_2035 = 2;
x_2036 = lean_io_prim_handle_mk(x_24, x_2035, x_2034);
if (lean_obj_tag(x_2036) == 0)
{
lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; 
x_2037 = lean_ctor_get(x_2036, 0);
lean_inc(x_2037);
x_2038 = lean_ctor_get(x_2036, 1);
lean_inc(x_2038);
if (lean_is_exclusive(x_2036)) {
 lean_ctor_release(x_2036, 0);
 lean_ctor_release(x_2036, 1);
 x_2039 = x_2036;
} else {
 lean_dec_ref(x_2036);
 x_2039 = lean_box(0);
}
x_2040 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2040, 0, x_2037);
if (lean_is_scalar(x_2039)) {
 x_2041 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2041 = x_2039;
}
lean_ctor_set(x_2041, 0, x_2040);
lean_ctor_set(x_2041, 1, x_31);
x_1253 = x_2041;
x_1254 = x_2038;
goto block_1990;
}
else
{
lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; 
x_2042 = lean_ctor_get(x_2036, 0);
lean_inc(x_2042);
x_2043 = lean_ctor_get(x_2036, 1);
lean_inc(x_2043);
if (lean_is_exclusive(x_2036)) {
 lean_ctor_release(x_2036, 0);
 lean_ctor_release(x_2036, 1);
 x_2044 = x_2036;
} else {
 lean_dec_ref(x_2036);
 x_2044 = lean_box(0);
}
x_2045 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2045, 0, x_2042);
if (lean_is_scalar(x_2044)) {
 x_2046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2046 = x_2044;
 lean_ctor_set_tag(x_2046, 0);
}
lean_ctor_set(x_2046, 0, x_2045);
lean_ctor_set(x_2046, 1, x_31);
x_1253 = x_2046;
x_1254 = x_2043;
goto block_1990;
}
}
else
{
lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; uint8_t x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2047 = lean_ctor_get(x_2033, 0);
lean_inc(x_2047);
x_2048 = lean_ctor_get(x_2033, 1);
lean_inc(x_2048);
if (lean_is_exclusive(x_2033)) {
 lean_ctor_release(x_2033, 0);
 lean_ctor_release(x_2033, 1);
 x_2049 = x_2033;
} else {
 lean_dec_ref(x_2033);
 x_2049 = lean_box(0);
}
x_2050 = lean_io_error_to_string(x_2047);
x_2051 = 3;
x_2052 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2052, 0, x_2050);
lean_ctor_set_uint8(x_2052, sizeof(void*)*1, x_2051);
x_2053 = lean_array_get_size(x_31);
x_2054 = lean_array_push(x_31, x_2052);
x_2055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2055, 0, x_2053);
lean_ctor_set(x_2055, 1, x_2054);
if (lean_is_scalar(x_2049)) {
 x_2056 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2056 = x_2049;
 lean_ctor_set_tag(x_2056, 0);
}
lean_ctor_set(x_2056, 0, x_2055);
lean_ctor_set(x_2056, 1, x_2048);
return x_2056;
}
}
}
else
{
lean_object* x_2057; uint8_t x_2058; lean_object* x_2059; 
lean_dec(x_18);
x_2057 = lean_ctor_get(x_1991, 1);
lean_inc(x_2057);
lean_dec(x_1991);
x_2058 = 0;
x_2059 = lean_io_prim_handle_mk(x_24, x_2058, x_2057);
if (lean_obj_tag(x_2059) == 0)
{
uint8_t x_2060; 
x_2060 = !lean_is_exclusive(x_2059);
if (x_2060 == 0)
{
lean_object* x_2061; 
x_2061 = lean_ctor_get(x_2059, 1);
lean_ctor_set(x_2059, 1, x_31);
x_519 = x_2059;
x_520 = x_2061;
goto block_1252;
}
else
{
lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; 
x_2062 = lean_ctor_get(x_2059, 0);
x_2063 = lean_ctor_get(x_2059, 1);
lean_inc(x_2063);
lean_inc(x_2062);
lean_dec(x_2059);
x_2064 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2064, 0, x_2062);
lean_ctor_set(x_2064, 1, x_31);
x_519 = x_2064;
x_520 = x_2063;
goto block_1252;
}
}
else
{
uint8_t x_2065; 
x_2065 = !lean_is_exclusive(x_2059);
if (x_2065 == 0)
{
lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; uint8_t x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; 
x_2066 = lean_ctor_get(x_2059, 0);
x_2067 = lean_ctor_get(x_2059, 1);
x_2068 = lean_io_error_to_string(x_2066);
x_2069 = 3;
x_2070 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2070, 0, x_2068);
lean_ctor_set_uint8(x_2070, sizeof(void*)*1, x_2069);
x_2071 = lean_array_get_size(x_31);
x_2072 = lean_array_push(x_31, x_2070);
lean_ctor_set(x_2059, 1, x_2072);
lean_ctor_set(x_2059, 0, x_2071);
x_519 = x_2059;
x_520 = x_2067;
goto block_1252;
}
else
{
lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; uint8_t x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; 
x_2073 = lean_ctor_get(x_2059, 0);
x_2074 = lean_ctor_get(x_2059, 1);
lean_inc(x_2074);
lean_inc(x_2073);
lean_dec(x_2059);
x_2075 = lean_io_error_to_string(x_2073);
x_2076 = 3;
x_2077 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2077, 0, x_2075);
lean_ctor_set_uint8(x_2077, sizeof(void*)*1, x_2076);
x_2078 = lean_array_get_size(x_31);
x_2079 = lean_array_push(x_31, x_2077);
x_2080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2080, 0, x_2078);
lean_ctor_set(x_2080, 1, x_2079);
x_519 = x_2080;
x_520 = x_2074;
goto block_1252;
}
}
}
block_518:
{
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_133; lean_object* x_134; lean_object* x_342; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_1, 4);
lean_inc(x_37);
x_342 = lean_io_remove_file(x_21, x_34);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
if (lean_is_scalar(x_16)) {
 x_345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_345 = x_16;
}
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_33, 0, x_345);
x_133 = x_33;
x_134 = x_344;
goto block_341;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_342, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 1);
lean_inc(x_347);
lean_dec(x_342);
if (lean_is_scalar(x_16)) {
 x_348 = lean_alloc_ctor(0, 1, 0);
} else {
 x_348 = x_16;
 lean_ctor_set_tag(x_348, 0);
}
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_33, 0, x_348);
x_133 = x_33;
x_134 = x_347;
goto block_341;
}
block_132:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_1, 5);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lake_elabConfigFile(x_6, x_37, x_41, x_8, x_40, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_48 = lean_write_module(x_46, x_21, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_io_prim_handle_unlock(x_36, x_49);
lean_dec(x_36);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_43);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_46);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_io_error_to_string(x_56);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_get_size(x_47);
x_61 = lean_array_push(x_47, x_59);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_61);
lean_ctor_set(x_43, 0, x_60);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_43);
return x_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_io_error_to_string(x_62);
x_65 = 3;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = lean_array_get_size(x_47);
x_68 = lean_array_push(x_47, x_66);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_68);
lean_ctor_set(x_43, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_43);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_46);
lean_dec(x_36);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_47);
x_76 = lean_array_push(x_47, x_74);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_76);
lean_ctor_set(x_43, 0, x_75);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_43);
return x_48;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_48, 0);
x_78 = lean_ctor_get(x_48, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_48);
x_79 = lean_io_error_to_string(x_77);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_array_get_size(x_47);
x_83 = lean_array_push(x_47, x_81);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_83);
lean_ctor_set(x_43, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_43);
lean_ctor_set(x_84, 1, x_78);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_43, 0);
x_86 = lean_ctor_get(x_43, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_43);
lean_inc(x_85);
x_87 = lean_write_module(x_85, x_21, x_44);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_io_prim_handle_unlock(x_36, x_88);
lean_dec(x_36);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_86);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_85);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
x_97 = lean_io_error_to_string(x_94);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_86);
x_101 = lean_array_push(x_86, x_99);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_96;
 lean_ctor_set_tag(x_103, 0);
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_85);
lean_dec(x_36);
x_104 = lean_ctor_get(x_87, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_106 = x_87;
} else {
 lean_dec_ref(x_87);
 x_106 = lean_box(0);
}
x_107 = lean_io_error_to_string(x_104);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_array_get_size(x_86);
x_111 = lean_array_push(x_86, x_109);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_106)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_106;
 lean_ctor_set_tag(x_113, 0);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_36);
lean_dec(x_21);
x_114 = !lean_is_exclusive(x_42);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_42, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_43);
if (x_116 == 0)
{
return x_42;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_43, 0);
x_118 = lean_ctor_get(x_43, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_43);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_42, 0, x_119);
return x_42;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_42, 1);
lean_inc(x_120);
lean_dec(x_42);
x_121 = lean_ctor_get(x_43, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_43, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_123 = x_43;
} else {
 lean_dec_ref(x_43);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_120);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_38);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_38);
lean_ctor_set(x_127, 1, x_39);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_38, 0);
x_129 = lean_ctor_get(x_38, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_38);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_39);
return x_131;
}
}
}
block_341:
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 11)
{
uint8_t x_137; 
lean_dec(x_136);
lean_dec(x_24);
x_137 = !lean_is_exclusive(x_133);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_133, 1);
x_139 = lean_ctor_get(x_133, 0);
lean_dec(x_139);
x_140 = lean_ctor_get(x_1, 0);
lean_inc(x_140);
x_141 = l_Lake_Env_leanGithash(x_140);
lean_dec(x_140);
x_142 = l_System_Platform_target;
lean_inc(x_37);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_30);
lean_ctor_set(x_143, 3, x_37);
x_144 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_143);
x_145 = lean_unsigned_to_nat(80u);
x_146 = l_Lean_Json_pretty(x_144, x_145);
x_147 = l_IO_FS_Handle_putStrLn(x_36, x_146, x_134);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_io_prim_handle_truncate(x_36, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_ctor_set(x_133, 0, x_150);
x_38 = x_133;
x_39 = x_151;
goto block_132;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_io_error_to_string(x_152);
x_155 = 3;
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_array_get_size(x_138);
x_158 = lean_array_push(x_138, x_156);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_158);
lean_ctor_set(x_133, 0, x_157);
x_38 = x_133;
x_39 = x_153;
goto block_132;
}
}
else
{
uint8_t x_159; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_147);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_147, 0);
x_161 = lean_io_error_to_string(x_160);
x_162 = 3;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_array_get_size(x_138);
x_165 = lean_array_push(x_138, x_163);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_165);
lean_ctor_set(x_133, 0, x_164);
lean_ctor_set_tag(x_147, 0);
lean_ctor_set(x_147, 0, x_133);
return x_147;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_147, 0);
x_167 = lean_ctor_get(x_147, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_147);
x_168 = lean_io_error_to_string(x_166);
x_169 = 3;
x_170 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_169);
x_171 = lean_array_get_size(x_138);
x_172 = lean_array_push(x_138, x_170);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_172);
lean_ctor_set(x_133, 0, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_133);
lean_ctor_set(x_173, 1, x_167);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_133, 1);
lean_inc(x_174);
lean_dec(x_133);
x_175 = lean_ctor_get(x_1, 0);
lean_inc(x_175);
x_176 = l_Lake_Env_leanGithash(x_175);
lean_dec(x_175);
x_177 = l_System_Platform_target;
lean_inc(x_37);
x_178 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_178, 2, x_30);
lean_ctor_set(x_178, 3, x_37);
x_179 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_178);
x_180 = lean_unsigned_to_nat(80u);
x_181 = l_Lean_Json_pretty(x_179, x_180);
x_182 = l_IO_FS_Handle_putStrLn(x_36, x_181, x_134);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_io_prim_handle_truncate(x_36, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_174);
x_38 = x_187;
x_39 = x_186;
goto block_132;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_dec(x_184);
x_190 = lean_io_error_to_string(x_188);
x_191 = 3;
x_192 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_191);
x_193 = lean_array_get_size(x_174);
x_194 = lean_array_push(x_174, x_192);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_38 = x_195;
x_39 = x_189;
goto block_132;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_196 = lean_ctor_get(x_182, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_182, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_198 = x_182;
} else {
 lean_dec_ref(x_182);
 x_198 = lean_box(0);
}
x_199 = lean_io_error_to_string(x_196);
x_200 = 3;
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_array_get_size(x_174);
x_203 = lean_array_push(x_174, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
if (lean_is_scalar(x_198)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_198;
 lean_ctor_set_tag(x_205, 0);
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_197);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_133);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_207 = lean_ctor_get(x_133, 1);
x_208 = lean_ctor_get(x_133, 0);
lean_dec(x_208);
x_209 = lean_io_error_to_string(x_136);
x_210 = 3;
x_211 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_210);
x_212 = lean_array_get_size(x_207);
x_213 = lean_array_push(x_207, x_211);
x_214 = lean_io_prim_handle_unlock(x_36, x_134);
lean_dec(x_36);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_io_remove_file(x_24, x_215);
lean_dec(x_24);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_216, 0);
lean_dec(x_218);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_213);
lean_ctor_set(x_133, 0, x_212);
lean_ctor_set(x_216, 0, x_133);
return x_216;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_213);
lean_ctor_set(x_133, 0, x_212);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_133);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
else
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_216);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_216, 0);
x_223 = lean_io_error_to_string(x_222);
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_210);
x_225 = lean_array_push(x_213, x_224);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_225);
lean_ctor_set(x_133, 0, x_212);
lean_ctor_set_tag(x_216, 0);
lean_ctor_set(x_216, 0, x_133);
return x_216;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_216, 0);
x_227 = lean_ctor_get(x_216, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_216);
x_228 = lean_io_error_to_string(x_226);
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_210);
x_230 = lean_array_push(x_213, x_229);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_230);
lean_ctor_set(x_133, 0, x_212);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_133);
lean_ctor_set(x_231, 1, x_227);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_24);
x_232 = !lean_is_exclusive(x_214);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_214, 0);
x_234 = lean_io_error_to_string(x_233);
x_235 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set_uint8(x_235, sizeof(void*)*1, x_210);
x_236 = lean_array_push(x_213, x_235);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_236);
lean_ctor_set(x_133, 0, x_212);
lean_ctor_set_tag(x_214, 0);
lean_ctor_set(x_214, 0, x_133);
return x_214;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_ctor_get(x_214, 0);
x_238 = lean_ctor_get(x_214, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_214);
x_239 = lean_io_error_to_string(x_237);
x_240 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set_uint8(x_240, sizeof(void*)*1, x_210);
x_241 = lean_array_push(x_213, x_240);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_241);
lean_ctor_set(x_133, 0, x_212);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_133);
lean_ctor_set(x_242, 1, x_238);
return x_242;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_243 = lean_ctor_get(x_133, 1);
lean_inc(x_243);
lean_dec(x_133);
x_244 = lean_io_error_to_string(x_136);
x_245 = 3;
x_246 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set_uint8(x_246, sizeof(void*)*1, x_245);
x_247 = lean_array_get_size(x_243);
x_248 = lean_array_push(x_243, x_246);
x_249 = lean_io_prim_handle_unlock(x_36, x_134);
lean_dec(x_36);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_io_remove_file(x_24, x_250);
lean_dec(x_24);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_247);
lean_ctor_set(x_254, 1, x_248);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_256 = lean_ctor_get(x_251, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_251, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_258 = x_251;
} else {
 lean_dec_ref(x_251);
 x_258 = lean_box(0);
}
x_259 = lean_io_error_to_string(x_256);
x_260 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_245);
x_261 = lean_array_push(x_248, x_260);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_247);
lean_ctor_set(x_262, 1, x_261);
if (lean_is_scalar(x_258)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_258;
 lean_ctor_set_tag(x_263, 0);
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_257);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_24);
x_264 = lean_ctor_get(x_249, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_249, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_266 = x_249;
} else {
 lean_dec_ref(x_249);
 x_266 = lean_box(0);
}
x_267 = lean_io_error_to_string(x_264);
x_268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_245);
x_269 = lean_array_push(x_248, x_268);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_247);
lean_ctor_set(x_270, 1, x_269);
if (lean_is_scalar(x_266)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_266;
 lean_ctor_set_tag(x_271, 0);
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_265);
return x_271;
}
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_135);
lean_dec(x_24);
x_272 = !lean_is_exclusive(x_133);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_273 = lean_ctor_get(x_133, 1);
x_274 = lean_ctor_get(x_133, 0);
lean_dec(x_274);
x_275 = lean_ctor_get(x_1, 0);
lean_inc(x_275);
x_276 = l_Lake_Env_leanGithash(x_275);
lean_dec(x_275);
x_277 = l_System_Platform_target;
lean_inc(x_37);
x_278 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
lean_ctor_set(x_278, 2, x_30);
lean_ctor_set(x_278, 3, x_37);
x_279 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_278);
x_280 = lean_unsigned_to_nat(80u);
x_281 = l_Lean_Json_pretty(x_279, x_280);
x_282 = l_IO_FS_Handle_putStrLn(x_36, x_281, x_134);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = lean_io_prim_handle_truncate(x_36, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_ctor_set(x_133, 0, x_285);
x_38 = x_133;
x_39 = x_286;
goto block_132;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_284, 1);
lean_inc(x_288);
lean_dec(x_284);
x_289 = lean_io_error_to_string(x_287);
x_290 = 3;
x_291 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*1, x_290);
x_292 = lean_array_get_size(x_273);
x_293 = lean_array_push(x_273, x_291);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_293);
lean_ctor_set(x_133, 0, x_292);
x_38 = x_133;
x_39 = x_288;
goto block_132;
}
}
else
{
uint8_t x_294; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_282);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_295 = lean_ctor_get(x_282, 0);
x_296 = lean_io_error_to_string(x_295);
x_297 = 3;
x_298 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*1, x_297);
x_299 = lean_array_get_size(x_273);
x_300 = lean_array_push(x_273, x_298);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_300);
lean_ctor_set(x_133, 0, x_299);
lean_ctor_set_tag(x_282, 0);
lean_ctor_set(x_282, 0, x_133);
return x_282;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_301 = lean_ctor_get(x_282, 0);
x_302 = lean_ctor_get(x_282, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_282);
x_303 = lean_io_error_to_string(x_301);
x_304 = 3;
x_305 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set_uint8(x_305, sizeof(void*)*1, x_304);
x_306 = lean_array_get_size(x_273);
x_307 = lean_array_push(x_273, x_305);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 1, x_307);
lean_ctor_set(x_133, 0, x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_133);
lean_ctor_set(x_308, 1, x_302);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_309 = lean_ctor_get(x_133, 1);
lean_inc(x_309);
lean_dec(x_133);
x_310 = lean_ctor_get(x_1, 0);
lean_inc(x_310);
x_311 = l_Lake_Env_leanGithash(x_310);
lean_dec(x_310);
x_312 = l_System_Platform_target;
lean_inc(x_37);
x_313 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
lean_ctor_set(x_313, 2, x_30);
lean_ctor_set(x_313, 3, x_37);
x_314 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_313);
x_315 = lean_unsigned_to_nat(80u);
x_316 = l_Lean_Json_pretty(x_314, x_315);
x_317 = l_IO_FS_Handle_putStrLn(x_36, x_316, x_134);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_io_prim_handle_truncate(x_36, x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_309);
x_38 = x_322;
x_39 = x_321;
goto block_132;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_323 = lean_ctor_get(x_319, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 1);
lean_inc(x_324);
lean_dec(x_319);
x_325 = lean_io_error_to_string(x_323);
x_326 = 3;
x_327 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set_uint8(x_327, sizeof(void*)*1, x_326);
x_328 = lean_array_get_size(x_309);
x_329 = lean_array_push(x_309, x_327);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
x_38 = x_330;
x_39 = x_324;
goto block_132;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_331 = lean_ctor_get(x_317, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_317, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_333 = x_317;
} else {
 lean_dec_ref(x_317);
 x_333 = lean_box(0);
}
x_334 = lean_io_error_to_string(x_331);
x_335 = 3;
x_336 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set_uint8(x_336, sizeof(void*)*1, x_335);
x_337 = lean_array_get_size(x_309);
x_338 = lean_array_push(x_309, x_336);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
if (lean_is_scalar(x_333)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_333;
 lean_ctor_set_tag(x_340, 0);
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
return x_340;
}
}
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_402; lean_object* x_403; lean_object* x_503; 
x_349 = lean_ctor_get(x_33, 0);
x_350 = lean_ctor_get(x_33, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_33);
x_351 = lean_ctor_get(x_1, 4);
lean_inc(x_351);
x_503 = lean_io_remove_file(x_21, x_34);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
if (lean_is_scalar(x_16)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_16;
}
lean_ctor_set(x_506, 0, x_504);
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_350);
x_402 = x_507;
x_403 = x_505;
goto block_502;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_508 = lean_ctor_get(x_503, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_503, 1);
lean_inc(x_509);
lean_dec(x_503);
if (lean_is_scalar(x_16)) {
 x_510 = lean_alloc_ctor(0, 1, 0);
} else {
 x_510 = x_16;
 lean_ctor_set_tag(x_510, 0);
}
lean_ctor_set(x_510, 0, x_508);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_350);
x_402 = x_511;
x_403 = x_509;
goto block_502;
}
block_401:
{
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_1, 5);
lean_inc(x_355);
lean_dec(x_1);
x_356 = l_Lake_elabConfigFile(x_6, x_351, x_355, x_8, x_354, x_353);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_361 = x_357;
} else {
 lean_dec_ref(x_357);
 x_361 = lean_box(0);
}
lean_inc(x_359);
x_362 = lean_write_module(x_359, x_21, x_358);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
x_364 = lean_io_prim_handle_unlock(x_349, x_363);
lean_dec(x_349);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_361;
}
lean_ctor_set(x_367, 0, x_359);
lean_ctor_set(x_367, 1, x_360);
if (lean_is_scalar(x_366)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_366;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_365);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_359);
x_369 = lean_ctor_get(x_364, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_371 = x_364;
} else {
 lean_dec_ref(x_364);
 x_371 = lean_box(0);
}
x_372 = lean_io_error_to_string(x_369);
x_373 = 3;
x_374 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_373);
x_375 = lean_array_get_size(x_360);
x_376 = lean_array_push(x_360, x_374);
if (lean_is_scalar(x_361)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_361;
 lean_ctor_set_tag(x_377, 1);
}
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
if (lean_is_scalar(x_371)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_371;
 lean_ctor_set_tag(x_378, 0);
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_370);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_359);
lean_dec(x_349);
x_379 = lean_ctor_get(x_362, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_362, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_381 = x_362;
} else {
 lean_dec_ref(x_362);
 x_381 = lean_box(0);
}
x_382 = lean_io_error_to_string(x_379);
x_383 = 3;
x_384 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*1, x_383);
x_385 = lean_array_get_size(x_360);
x_386 = lean_array_push(x_360, x_384);
if (lean_is_scalar(x_361)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_361;
 lean_ctor_set_tag(x_387, 1);
}
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
if (lean_is_scalar(x_381)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_381;
 lean_ctor_set_tag(x_388, 0);
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_380);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_349);
lean_dec(x_21);
x_389 = lean_ctor_get(x_356, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_390 = x_356;
} else {
 lean_dec_ref(x_356);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_357, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_357, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_393 = x_357;
} else {
 lean_dec_ref(x_357);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
if (lean_is_scalar(x_390)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_390;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_389);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_396 = lean_ctor_get(x_352, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_352, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_398 = x_352;
} else {
 lean_dec_ref(x_352);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_353);
return x_400;
}
}
block_502:
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec(x_404);
if (lean_obj_tag(x_405) == 11)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_405);
lean_dec(x_24);
x_406 = lean_ctor_get(x_402, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_407 = x_402;
} else {
 lean_dec_ref(x_402);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_1, 0);
lean_inc(x_408);
x_409 = l_Lake_Env_leanGithash(x_408);
lean_dec(x_408);
x_410 = l_System_Platform_target;
lean_inc(x_351);
x_411 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set(x_411, 2, x_30);
lean_ctor_set(x_411, 3, x_351);
x_412 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_411);
x_413 = lean_unsigned_to_nat(80u);
x_414 = l_Lean_Json_pretty(x_412, x_413);
x_415 = l_IO_FS_Handle_putStrLn(x_349, x_414, x_403);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
lean_dec(x_415);
x_417 = lean_io_prim_handle_truncate(x_349, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
if (lean_is_scalar(x_407)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_407;
}
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_406);
x_352 = x_420;
x_353 = x_419;
goto block_401;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_421 = lean_ctor_get(x_417, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_417, 1);
lean_inc(x_422);
lean_dec(x_417);
x_423 = lean_io_error_to_string(x_421);
x_424 = 3;
x_425 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set_uint8(x_425, sizeof(void*)*1, x_424);
x_426 = lean_array_get_size(x_406);
x_427 = lean_array_push(x_406, x_425);
if (lean_is_scalar(x_407)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_407;
 lean_ctor_set_tag(x_428, 1);
}
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
x_352 = x_428;
x_353 = x_422;
goto block_401;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_429 = lean_ctor_get(x_415, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_415, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_431 = x_415;
} else {
 lean_dec_ref(x_415);
 x_431 = lean_box(0);
}
x_432 = lean_io_error_to_string(x_429);
x_433 = 3;
x_434 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*1, x_433);
x_435 = lean_array_get_size(x_406);
x_436 = lean_array_push(x_406, x_434);
if (lean_is_scalar(x_407)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_407;
 lean_ctor_set_tag(x_437, 1);
}
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
if (lean_is_scalar(x_431)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_431;
 lean_ctor_set_tag(x_438, 0);
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_430);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_351);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_439 = lean_ctor_get(x_402, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_440 = x_402;
} else {
 lean_dec_ref(x_402);
 x_440 = lean_box(0);
}
x_441 = lean_io_error_to_string(x_405);
x_442 = 3;
x_443 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set_uint8(x_443, sizeof(void*)*1, x_442);
x_444 = lean_array_get_size(x_439);
x_445 = lean_array_push(x_439, x_443);
x_446 = lean_io_prim_handle_unlock(x_349, x_403);
lean_dec(x_349);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_io_remove_file(x_24, x_447);
lean_dec(x_24);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_440;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_444);
lean_ctor_set(x_451, 1, x_445);
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_449);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_453 = lean_ctor_get(x_448, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_448, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_455 = x_448;
} else {
 lean_dec_ref(x_448);
 x_455 = lean_box(0);
}
x_456 = lean_io_error_to_string(x_453);
x_457 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set_uint8(x_457, sizeof(void*)*1, x_442);
x_458 = lean_array_push(x_445, x_457);
if (lean_is_scalar(x_440)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_440;
 lean_ctor_set_tag(x_459, 1);
}
lean_ctor_set(x_459, 0, x_444);
lean_ctor_set(x_459, 1, x_458);
if (lean_is_scalar(x_455)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_455;
 lean_ctor_set_tag(x_460, 0);
}
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_454);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_24);
x_461 = lean_ctor_get(x_446, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_446, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_463 = x_446;
} else {
 lean_dec_ref(x_446);
 x_463 = lean_box(0);
}
x_464 = lean_io_error_to_string(x_461);
x_465 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*1, x_442);
x_466 = lean_array_push(x_445, x_465);
if (lean_is_scalar(x_440)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_440;
 lean_ctor_set_tag(x_467, 1);
}
lean_ctor_set(x_467, 0, x_444);
lean_ctor_set(x_467, 1, x_466);
if (lean_is_scalar(x_463)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_463;
 lean_ctor_set_tag(x_468, 0);
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_462);
return x_468;
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_404);
lean_dec(x_24);
x_469 = lean_ctor_get(x_402, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_470 = x_402;
} else {
 lean_dec_ref(x_402);
 x_470 = lean_box(0);
}
x_471 = lean_ctor_get(x_1, 0);
lean_inc(x_471);
x_472 = l_Lake_Env_leanGithash(x_471);
lean_dec(x_471);
x_473 = l_System_Platform_target;
lean_inc(x_351);
x_474 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_472);
lean_ctor_set(x_474, 2, x_30);
lean_ctor_set(x_474, 3, x_351);
x_475 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_474);
x_476 = lean_unsigned_to_nat(80u);
x_477 = l_Lean_Json_pretty(x_475, x_476);
x_478 = l_IO_FS_Handle_putStrLn(x_349, x_477, x_403);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
x_480 = lean_io_prim_handle_truncate(x_349, x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
if (lean_is_scalar(x_470)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_470;
}
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_469);
x_352 = x_483;
x_353 = x_482;
goto block_401;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_484 = lean_ctor_get(x_480, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_480, 1);
lean_inc(x_485);
lean_dec(x_480);
x_486 = lean_io_error_to_string(x_484);
x_487 = 3;
x_488 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set_uint8(x_488, sizeof(void*)*1, x_487);
x_489 = lean_array_get_size(x_469);
x_490 = lean_array_push(x_469, x_488);
if (lean_is_scalar(x_470)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_470;
 lean_ctor_set_tag(x_491, 1);
}
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_352 = x_491;
x_353 = x_485;
goto block_401;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_492 = lean_ctor_get(x_478, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_478, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_494 = x_478;
} else {
 lean_dec_ref(x_478);
 x_494 = lean_box(0);
}
x_495 = lean_io_error_to_string(x_492);
x_496 = 3;
x_497 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*1, x_496);
x_498 = lean_array_get_size(x_469);
x_499 = lean_array_push(x_469, x_497);
if (lean_is_scalar(x_470)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_470;
 lean_ctor_set_tag(x_500, 1);
}
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
if (lean_is_scalar(x_494)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_494;
 lean_ctor_set_tag(x_501, 0);
}
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_493);
return x_501;
}
}
}
}
}
else
{
uint8_t x_512; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_512 = !lean_is_exclusive(x_33);
if (x_512 == 0)
{
lean_object* x_513; 
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_33);
lean_ctor_set(x_513, 1, x_34);
return x_513;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_33, 0);
x_515 = lean_ctor_get(x_33, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_33);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_34);
return x_517;
}
}
}
block_1252:
{
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_1152; 
x_521 = lean_ctor_get(x_519, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_523 = x_519;
} else {
 lean_dec_ref(x_519);
 x_523 = lean_box(0);
}
x_1152 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_1152 == 0)
{
uint8_t x_1153; lean_object* x_1154; 
lean_dec(x_16);
x_1153 = 0;
x_1154 = lean_io_prim_handle_lock(x_521, x_1153, x_520);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1155 = lean_ctor_get(x_1154, 1);
lean_inc(x_1155);
lean_dec(x_1154);
x_1156 = l_Lake_processHeader___closed__1;
x_1157 = l_IO_FS_Handle_readToEnd_loop(x_521, x_1156, x_1155);
if (lean_obj_tag(x_1157) == 0)
{
uint8_t x_1158; 
x_1158 = !lean_is_exclusive(x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; 
x_1159 = lean_ctor_get(x_1157, 1);
lean_ctor_set(x_1157, 1, x_522);
x_524 = x_1157;
x_525 = x_1159;
goto block_1151;
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1160 = lean_ctor_get(x_1157, 0);
x_1161 = lean_ctor_get(x_1157, 1);
lean_inc(x_1161);
lean_inc(x_1160);
lean_dec(x_1157);
x_1162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1162, 0, x_1160);
lean_ctor_set(x_1162, 1, x_522);
x_524 = x_1162;
x_525 = x_1161;
goto block_1151;
}
}
else
{
uint8_t x_1163; 
x_1163 = !lean_is_exclusive(x_1157);
if (x_1163 == 0)
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; uint8_t x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1164 = lean_ctor_get(x_1157, 0);
x_1165 = lean_ctor_get(x_1157, 1);
x_1166 = lean_io_error_to_string(x_1164);
x_1167 = 3;
x_1168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set_uint8(x_1168, sizeof(void*)*1, x_1167);
x_1169 = lean_array_get_size(x_522);
x_1170 = lean_array_push(x_522, x_1168);
lean_ctor_set(x_1157, 1, x_1170);
lean_ctor_set(x_1157, 0, x_1169);
x_524 = x_1157;
x_525 = x_1165;
goto block_1151;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; uint8_t x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1171 = lean_ctor_get(x_1157, 0);
x_1172 = lean_ctor_get(x_1157, 1);
lean_inc(x_1172);
lean_inc(x_1171);
lean_dec(x_1157);
x_1173 = lean_io_error_to_string(x_1171);
x_1174 = 3;
x_1175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1175, 0, x_1173);
lean_ctor_set_uint8(x_1175, sizeof(void*)*1, x_1174);
x_1176 = lean_array_get_size(x_522);
x_1177 = lean_array_push(x_522, x_1175);
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
x_524 = x_1178;
x_525 = x_1172;
goto block_1151;
}
}
}
else
{
uint8_t x_1179; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1179 = !lean_is_exclusive(x_1154);
if (x_1179 == 0)
{
lean_object* x_1180; lean_object* x_1181; uint8_t x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1180 = lean_ctor_get(x_1154, 0);
x_1181 = lean_io_error_to_string(x_1180);
x_1182 = 3;
x_1183 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set_uint8(x_1183, sizeof(void*)*1, x_1182);
x_1184 = lean_array_get_size(x_522);
x_1185 = lean_array_push(x_522, x_1183);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
lean_ctor_set_tag(x_1154, 0);
lean_ctor_set(x_1154, 0, x_1186);
return x_1154;
}
else
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; uint8_t x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1187 = lean_ctor_get(x_1154, 0);
x_1188 = lean_ctor_get(x_1154, 1);
lean_inc(x_1188);
lean_inc(x_1187);
lean_dec(x_1154);
x_1189 = lean_io_error_to_string(x_1187);
x_1190 = 3;
x_1191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set_uint8(x_1191, sizeof(void*)*1, x_1190);
x_1192 = lean_array_get_size(x_522);
x_1193 = lean_array_push(x_522, x_1191);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
x_1195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1195, 0, x_1194);
lean_ctor_set(x_1195, 1, x_1188);
return x_1195;
}
}
}
else
{
lean_object* x_1196; lean_object* x_1197; uint8_t x_1205; lean_object* x_1206; 
lean_dec(x_523);
lean_dec(x_32);
x_1205 = 1;
x_1206 = lean_io_prim_handle_mk(x_27, x_1205, x_520);
lean_dec(x_27);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; uint8_t x_1209; lean_object* x_1210; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = 1;
x_1210 = lean_io_prim_handle_try_lock(x_1207, x_1209, x_1208);
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1211; uint8_t x_1212; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
x_1212 = lean_unbox(x_1211);
lean_dec(x_1211);
if (x_1212 == 0)
{
lean_object* x_1213; lean_object* x_1214; 
lean_dec(x_1207);
x_1213 = lean_ctor_get(x_1210, 1);
lean_inc(x_1213);
lean_dec(x_1210);
x_1214 = lean_io_prim_handle_unlock(x_521, x_1213);
lean_dec(x_521);
if (lean_obj_tag(x_1214) == 0)
{
lean_object* x_1215; lean_object* x_1216; 
x_1215 = lean_ctor_get(x_1214, 1);
lean_inc(x_1215);
lean_dec(x_1214);
x_1216 = l_Lake_importConfigFile___closed__11;
x_1196 = x_1216;
x_1197 = x_1215;
goto block_1204;
}
else
{
lean_object* x_1217; lean_object* x_1218; 
x_1217 = lean_ctor_get(x_1214, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1214, 1);
lean_inc(x_1218);
lean_dec(x_1214);
x_1196 = x_1217;
x_1197 = x_1218;
goto block_1204;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; 
x_1219 = lean_ctor_get(x_1210, 1);
lean_inc(x_1219);
lean_dec(x_1210);
x_1220 = lean_io_prim_handle_unlock(x_521, x_1219);
lean_dec(x_521);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; uint8_t x_1222; lean_object* x_1223; 
x_1221 = lean_ctor_get(x_1220, 1);
lean_inc(x_1221);
lean_dec(x_1220);
x_1222 = 3;
x_1223 = lean_io_prim_handle_mk(x_24, x_1222, x_1221);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1223, 1);
lean_inc(x_1225);
lean_dec(x_1223);
x_1226 = lean_io_prim_handle_lock(x_1224, x_1209, x_1225);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; lean_object* x_1228; 
x_1227 = lean_ctor_get(x_1226, 1);
lean_inc(x_1227);
lean_dec(x_1226);
x_1228 = lean_io_prim_handle_unlock(x_1207, x_1227);
lean_dec(x_1207);
if (lean_obj_tag(x_1228) == 0)
{
uint8_t x_1229; 
x_1229 = !lean_is_exclusive(x_1228);
if (x_1229 == 0)
{
lean_object* x_1230; lean_object* x_1231; 
x_1230 = lean_ctor_get(x_1228, 1);
x_1231 = lean_ctor_get(x_1228, 0);
lean_dec(x_1231);
lean_ctor_set(x_1228, 1, x_522);
lean_ctor_set(x_1228, 0, x_1224);
x_33 = x_1228;
x_34 = x_1230;
goto block_518;
}
else
{
lean_object* x_1232; lean_object* x_1233; 
x_1232 = lean_ctor_get(x_1228, 1);
lean_inc(x_1232);
lean_dec(x_1228);
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1224);
lean_ctor_set(x_1233, 1, x_522);
x_33 = x_1233;
x_34 = x_1232;
goto block_518;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1224);
x_1234 = lean_ctor_get(x_1228, 0);
lean_inc(x_1234);
x_1235 = lean_ctor_get(x_1228, 1);
lean_inc(x_1235);
lean_dec(x_1228);
x_1196 = x_1234;
x_1197 = x_1235;
goto block_1204;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; 
lean_dec(x_1224);
lean_dec(x_1207);
x_1236 = lean_ctor_get(x_1226, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1226, 1);
lean_inc(x_1237);
lean_dec(x_1226);
x_1196 = x_1236;
x_1197 = x_1237;
goto block_1204;
}
}
else
{
lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1207);
x_1238 = lean_ctor_get(x_1223, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1223, 1);
lean_inc(x_1239);
lean_dec(x_1223);
x_1196 = x_1238;
x_1197 = x_1239;
goto block_1204;
}
}
else
{
lean_object* x_1240; lean_object* x_1241; 
lean_dec(x_1207);
x_1240 = lean_ctor_get(x_1220, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1220, 1);
lean_inc(x_1241);
lean_dec(x_1220);
x_1196 = x_1240;
x_1197 = x_1241;
goto block_1204;
}
}
}
else
{
lean_object* x_1242; lean_object* x_1243; 
lean_dec(x_1207);
lean_dec(x_521);
x_1242 = lean_ctor_get(x_1210, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1210, 1);
lean_inc(x_1243);
lean_dec(x_1210);
x_1196 = x_1242;
x_1197 = x_1243;
goto block_1204;
}
}
else
{
lean_object* x_1244; lean_object* x_1245; 
lean_dec(x_521);
x_1244 = lean_ctor_get(x_1206, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1206, 1);
lean_inc(x_1245);
lean_dec(x_1206);
x_1196 = x_1244;
x_1197 = x_1245;
goto block_1204;
}
block_1204:
{
lean_object* x_1198; uint8_t x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1198 = lean_io_error_to_string(x_1196);
x_1199 = 3;
x_1200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1200, 0, x_1198);
lean_ctor_set_uint8(x_1200, sizeof(void*)*1, x_1199);
x_1201 = lean_array_get_size(x_522);
x_1202 = lean_array_push(x_522, x_1200);
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1201);
lean_ctor_set(x_1203, 1, x_1202);
x_33 = x_1203;
x_34 = x_1197;
goto block_518;
}
}
block_1151:
{
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_524, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_528 = x_524;
} else {
 lean_dec_ref(x_524);
 x_528 = lean_box(0);
}
x_529 = l_Lean_Json_parse(x_526);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_529);
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_530 = lean_array_get_size(x_527);
x_531 = l_Lake_importConfigFile___closed__7;
x_532 = lean_array_push(x_527, x_531);
if (lean_is_scalar(x_528)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_528;
 lean_ctor_set_tag(x_533, 1);
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_532);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_525);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_529, 0);
lean_inc(x_535);
lean_dec(x_529);
x_536 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108_(x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_537 = lean_array_get_size(x_527);
x_538 = l_Lake_importConfigFile___closed__7;
x_539 = lean_array_push(x_527, x_538);
if (lean_is_scalar(x_528)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_528;
 lean_ctor_set_tag(x_540, 1);
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_539);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_525);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; uint8_t x_1084; 
x_542 = lean_ctor_get(x_536, 0);
lean_inc(x_542);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_543 = x_536;
} else {
 lean_dec_ref(x_536);
 x_543 = lean_box(0);
}
x_1032 = l_System_FilePath_pathExists(x_21, x_525);
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1084 = lean_unbox(x_1033);
lean_dec(x_1033);
if (x_1084 == 0)
{
lean_object* x_1085; 
lean_dec(x_32);
x_1085 = lean_box(0);
x_1035 = x_1085;
goto block_1083;
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; 
x_1086 = lean_ctor_get(x_542, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_542, 1);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_542, 2);
lean_inc(x_1088);
x_1089 = l_System_Platform_target;
x_1090 = lean_string_dec_eq(x_1086, x_1089);
lean_dec(x_1086);
if (x_1090 == 0)
{
lean_object* x_1091; 
lean_dec(x_1088);
lean_dec(x_1087);
lean_dec(x_32);
x_1091 = lean_box(0);
x_1035 = x_1091;
goto block_1083;
}
else
{
lean_object* x_1092; lean_object* x_1093; uint8_t x_1094; 
x_1092 = lean_ctor_get(x_1, 0);
lean_inc(x_1092);
x_1093 = l_Lake_Env_leanGithash(x_1092);
lean_dec(x_1092);
x_1094 = lean_string_dec_eq(x_1087, x_1093);
lean_dec(x_1093);
lean_dec(x_1087);
if (x_1094 == 0)
{
lean_object* x_1095; 
lean_dec(x_1088);
lean_dec(x_32);
x_1095 = lean_box(0);
x_1035 = x_1095;
goto block_1083;
}
else
{
uint64_t x_1096; uint64_t x_1097; uint8_t x_1098; 
x_1096 = lean_unbox_uint64(x_1088);
lean_dec(x_1088);
x_1097 = lean_unbox_uint64(x_30);
x_1098 = lean_uint64_dec_eq(x_1096, x_1097);
if (x_1098 == 0)
{
lean_object* x_1099; 
lean_dec(x_32);
x_1099 = lean_box(0);
x_1035 = x_1099;
goto block_1083;
}
else
{
lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_528);
lean_dec(x_523);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
x_1100 = lean_ctor_get(x_1, 5);
lean_inc(x_1100);
lean_dec(x_1);
x_1101 = l_Lake_importConfigFileCore(x_21, x_1100, x_1034);
lean_dec(x_21);
if (lean_obj_tag(x_1101) == 0)
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1102 = lean_ctor_get(x_1101, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1101, 1);
lean_inc(x_1103);
lean_dec(x_1101);
x_1104 = lean_io_prim_handle_unlock(x_521, x_1103);
lean_dec(x_521);
if (lean_obj_tag(x_1104) == 0)
{
uint8_t x_1105; 
x_1105 = !lean_is_exclusive(x_1104);
if (x_1105 == 0)
{
lean_object* x_1106; lean_object* x_1107; 
x_1106 = lean_ctor_get(x_1104, 0);
lean_dec(x_1106);
if (lean_is_scalar(x_32)) {
 x_1107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1107 = x_32;
}
lean_ctor_set(x_1107, 0, x_1102);
lean_ctor_set(x_1107, 1, x_527);
lean_ctor_set(x_1104, 0, x_1107);
return x_1104;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1108 = lean_ctor_get(x_1104, 1);
lean_inc(x_1108);
lean_dec(x_1104);
if (lean_is_scalar(x_32)) {
 x_1109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1109 = x_32;
}
lean_ctor_set(x_1109, 0, x_1102);
lean_ctor_set(x_1109, 1, x_527);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_1109);
lean_ctor_set(x_1110, 1, x_1108);
return x_1110;
}
}
else
{
uint8_t x_1111; 
lean_dec(x_1102);
x_1111 = !lean_is_exclusive(x_1104);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; uint8_t x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1112 = lean_ctor_get(x_1104, 0);
x_1113 = lean_io_error_to_string(x_1112);
x_1114 = 3;
x_1115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1115, 0, x_1113);
lean_ctor_set_uint8(x_1115, sizeof(void*)*1, x_1114);
x_1116 = lean_array_get_size(x_527);
x_1117 = lean_array_push(x_527, x_1115);
if (lean_is_scalar(x_32)) {
 x_1118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1118 = x_32;
 lean_ctor_set_tag(x_1118, 1);
}
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1117);
lean_ctor_set_tag(x_1104, 0);
lean_ctor_set(x_1104, 0, x_1118);
return x_1104;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1119 = lean_ctor_get(x_1104, 0);
x_1120 = lean_ctor_get(x_1104, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_1104);
x_1121 = lean_io_error_to_string(x_1119);
x_1122 = 3;
x_1123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1123, 0, x_1121);
lean_ctor_set_uint8(x_1123, sizeof(void*)*1, x_1122);
x_1124 = lean_array_get_size(x_527);
x_1125 = lean_array_push(x_527, x_1123);
if (lean_is_scalar(x_32)) {
 x_1126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1126 = x_32;
 lean_ctor_set_tag(x_1126, 1);
}
lean_ctor_set(x_1126, 0, x_1124);
lean_ctor_set(x_1126, 1, x_1125);
x_1127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1127, 0, x_1126);
lean_ctor_set(x_1127, 1, x_1120);
return x_1127;
}
}
}
else
{
uint8_t x_1128; 
lean_dec(x_521);
x_1128 = !lean_is_exclusive(x_1101);
if (x_1128 == 0)
{
lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1129 = lean_ctor_get(x_1101, 0);
x_1130 = lean_io_error_to_string(x_1129);
x_1131 = 3;
x_1132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set_uint8(x_1132, sizeof(void*)*1, x_1131);
x_1133 = lean_array_get_size(x_527);
x_1134 = lean_array_push(x_527, x_1132);
if (lean_is_scalar(x_32)) {
 x_1135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1135 = x_32;
 lean_ctor_set_tag(x_1135, 1);
}
lean_ctor_set(x_1135, 0, x_1133);
lean_ctor_set(x_1135, 1, x_1134);
lean_ctor_set_tag(x_1101, 0);
lean_ctor_set(x_1101, 0, x_1135);
return x_1101;
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1136 = lean_ctor_get(x_1101, 0);
x_1137 = lean_ctor_get(x_1101, 1);
lean_inc(x_1137);
lean_inc(x_1136);
lean_dec(x_1101);
x_1138 = lean_io_error_to_string(x_1136);
x_1139 = 3;
x_1140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set_uint8(x_1140, sizeof(void*)*1, x_1139);
x_1141 = lean_array_get_size(x_527);
x_1142 = lean_array_push(x_527, x_1140);
if (lean_is_scalar(x_32)) {
 x_1143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1143 = x_32;
 lean_ctor_set_tag(x_1143, 1);
}
lean_ctor_set(x_1143, 0, x_1141);
lean_ctor_set(x_1143, 1, x_1142);
x_1144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1144, 0, x_1143);
lean_ctor_set(x_1144, 1, x_1137);
return x_1144;
}
}
}
}
}
}
block_1031:
{
if (lean_obj_tag(x_544) == 0)
{
uint8_t x_546; 
x_546 = !lean_is_exclusive(x_544);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_645; lean_object* x_646; lean_object* x_854; 
x_547 = lean_ctor_get(x_544, 0);
x_548 = lean_ctor_get(x_542, 3);
lean_inc(x_548);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 lean_ctor_release(x_542, 2);
 lean_ctor_release(x_542, 3);
 x_549 = x_542;
} else {
 lean_dec_ref(x_542);
 x_549 = lean_box(0);
}
x_854 = lean_io_remove_file(x_21, x_545);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
if (lean_is_scalar(x_543)) {
 x_857 = lean_alloc_ctor(1, 1, 0);
} else {
 x_857 = x_543;
}
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_544, 0, x_857);
x_645 = x_544;
x_646 = x_856;
goto block_853;
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_858 = lean_ctor_get(x_854, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_854, 1);
lean_inc(x_859);
lean_dec(x_854);
if (lean_is_scalar(x_543)) {
 x_860 = lean_alloc_ctor(0, 1, 0);
} else {
 x_860 = x_543;
 lean_ctor_set_tag(x_860, 0);
}
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_544, 0, x_860);
x_645 = x_544;
x_646 = x_859;
goto block_853;
}
block_644:
{
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = lean_ctor_get(x_1, 5);
lean_inc(x_553);
lean_dec(x_1);
x_554 = l_Lake_elabConfigFile(x_6, x_548, x_553, x_8, x_552, x_551);
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; uint8_t x_557; 
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = !lean_is_exclusive(x_555);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_555, 0);
x_559 = lean_ctor_get(x_555, 1);
lean_inc(x_558);
x_560 = lean_write_module(x_558, x_21, x_556);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
lean_dec(x_560);
x_562 = lean_io_prim_handle_unlock(x_547, x_561);
lean_dec(x_547);
if (lean_obj_tag(x_562) == 0)
{
uint8_t x_563; 
x_563 = !lean_is_exclusive(x_562);
if (x_563 == 0)
{
lean_object* x_564; 
x_564 = lean_ctor_get(x_562, 0);
lean_dec(x_564);
lean_ctor_set(x_562, 0, x_555);
return x_562;
}
else
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_562, 1);
lean_inc(x_565);
lean_dec(x_562);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_555);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
else
{
uint8_t x_567; 
lean_dec(x_558);
x_567 = !lean_is_exclusive(x_562);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_568 = lean_ctor_get(x_562, 0);
x_569 = lean_io_error_to_string(x_568);
x_570 = 3;
x_571 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set_uint8(x_571, sizeof(void*)*1, x_570);
x_572 = lean_array_get_size(x_559);
x_573 = lean_array_push(x_559, x_571);
lean_ctor_set_tag(x_555, 1);
lean_ctor_set(x_555, 1, x_573);
lean_ctor_set(x_555, 0, x_572);
lean_ctor_set_tag(x_562, 0);
lean_ctor_set(x_562, 0, x_555);
return x_562;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_574 = lean_ctor_get(x_562, 0);
x_575 = lean_ctor_get(x_562, 1);
lean_inc(x_575);
lean_inc(x_574);
lean_dec(x_562);
x_576 = lean_io_error_to_string(x_574);
x_577 = 3;
x_578 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*1, x_577);
x_579 = lean_array_get_size(x_559);
x_580 = lean_array_push(x_559, x_578);
lean_ctor_set_tag(x_555, 1);
lean_ctor_set(x_555, 1, x_580);
lean_ctor_set(x_555, 0, x_579);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_555);
lean_ctor_set(x_581, 1, x_575);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_dec(x_558);
lean_dec(x_547);
x_582 = !lean_is_exclusive(x_560);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; uint8_t x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_583 = lean_ctor_get(x_560, 0);
x_584 = lean_io_error_to_string(x_583);
x_585 = 3;
x_586 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set_uint8(x_586, sizeof(void*)*1, x_585);
x_587 = lean_array_get_size(x_559);
x_588 = lean_array_push(x_559, x_586);
lean_ctor_set_tag(x_555, 1);
lean_ctor_set(x_555, 1, x_588);
lean_ctor_set(x_555, 0, x_587);
lean_ctor_set_tag(x_560, 0);
lean_ctor_set(x_560, 0, x_555);
return x_560;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_589 = lean_ctor_get(x_560, 0);
x_590 = lean_ctor_get(x_560, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_560);
x_591 = lean_io_error_to_string(x_589);
x_592 = 3;
x_593 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set_uint8(x_593, sizeof(void*)*1, x_592);
x_594 = lean_array_get_size(x_559);
x_595 = lean_array_push(x_559, x_593);
lean_ctor_set_tag(x_555, 1);
lean_ctor_set(x_555, 1, x_595);
lean_ctor_set(x_555, 0, x_594);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_555);
lean_ctor_set(x_596, 1, x_590);
return x_596;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_555, 0);
x_598 = lean_ctor_get(x_555, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_555);
lean_inc(x_597);
x_599 = lean_write_module(x_597, x_21, x_556);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
lean_dec(x_599);
x_601 = lean_io_prim_handle_unlock(x_547, x_600);
lean_dec(x_547);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = lean_ctor_get(x_601, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_603 = x_601;
} else {
 lean_dec_ref(x_601);
 x_603 = lean_box(0);
}
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_597);
lean_ctor_set(x_604, 1, x_598);
if (lean_is_scalar(x_603)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_603;
}
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_602);
return x_605;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_597);
x_606 = lean_ctor_get(x_601, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_601, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_608 = x_601;
} else {
 lean_dec_ref(x_601);
 x_608 = lean_box(0);
}
x_609 = lean_io_error_to_string(x_606);
x_610 = 3;
x_611 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set_uint8(x_611, sizeof(void*)*1, x_610);
x_612 = lean_array_get_size(x_598);
x_613 = lean_array_push(x_598, x_611);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
if (lean_is_scalar(x_608)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_608;
 lean_ctor_set_tag(x_615, 0);
}
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_607);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_597);
lean_dec(x_547);
x_616 = lean_ctor_get(x_599, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_599, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_618 = x_599;
} else {
 lean_dec_ref(x_599);
 x_618 = lean_box(0);
}
x_619 = lean_io_error_to_string(x_616);
x_620 = 3;
x_621 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set_uint8(x_621, sizeof(void*)*1, x_620);
x_622 = lean_array_get_size(x_598);
x_623 = lean_array_push(x_598, x_621);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
if (lean_is_scalar(x_618)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_618;
 lean_ctor_set_tag(x_625, 0);
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_617);
return x_625;
}
}
}
else
{
uint8_t x_626; 
lean_dec(x_547);
lean_dec(x_21);
x_626 = !lean_is_exclusive(x_554);
if (x_626 == 0)
{
lean_object* x_627; uint8_t x_628; 
x_627 = lean_ctor_get(x_554, 0);
lean_dec(x_627);
x_628 = !lean_is_exclusive(x_555);
if (x_628 == 0)
{
return x_554;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_555, 0);
x_630 = lean_ctor_get(x_555, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_555);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
lean_ctor_set(x_554, 0, x_631);
return x_554;
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_632 = lean_ctor_get(x_554, 1);
lean_inc(x_632);
lean_dec(x_554);
x_633 = lean_ctor_get(x_555, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_555, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_635 = x_555;
} else {
 lean_dec_ref(x_555);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_632);
return x_637;
}
}
}
else
{
uint8_t x_638; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_638 = !lean_is_exclusive(x_550);
if (x_638 == 0)
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_550);
lean_ctor_set(x_639, 1, x_551);
return x_639;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_640 = lean_ctor_get(x_550, 0);
x_641 = lean_ctor_get(x_550, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_550);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_551);
return x_643;
}
}
}
block_853:
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_645, 0);
lean_inc(x_647);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
lean_dec(x_647);
if (lean_obj_tag(x_648) == 11)
{
uint8_t x_649; 
lean_dec(x_648);
lean_dec(x_24);
x_649 = !lean_is_exclusive(x_645);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_650 = lean_ctor_get(x_645, 1);
x_651 = lean_ctor_get(x_645, 0);
lean_dec(x_651);
x_652 = lean_ctor_get(x_1, 0);
lean_inc(x_652);
x_653 = l_Lake_Env_leanGithash(x_652);
lean_dec(x_652);
x_654 = l_System_Platform_target;
lean_inc(x_548);
if (lean_is_scalar(x_549)) {
 x_655 = lean_alloc_ctor(0, 4, 0);
} else {
 x_655 = x_549;
}
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_653);
lean_ctor_set(x_655, 2, x_30);
lean_ctor_set(x_655, 3, x_548);
x_656 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_655);
x_657 = lean_unsigned_to_nat(80u);
x_658 = l_Lean_Json_pretty(x_656, x_657);
x_659 = l_IO_FS_Handle_putStrLn(x_547, x_658, x_646);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; 
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_661 = lean_io_prim_handle_truncate(x_547, x_660);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
lean_ctor_set(x_645, 0, x_662);
x_550 = x_645;
x_551 = x_663;
goto block_644;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_664 = lean_ctor_get(x_661, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_661, 1);
lean_inc(x_665);
lean_dec(x_661);
x_666 = lean_io_error_to_string(x_664);
x_667 = 3;
x_668 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set_uint8(x_668, sizeof(void*)*1, x_667);
x_669 = lean_array_get_size(x_650);
x_670 = lean_array_push(x_650, x_668);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_670);
lean_ctor_set(x_645, 0, x_669);
x_550 = x_645;
x_551 = x_665;
goto block_644;
}
}
else
{
uint8_t x_671; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_671 = !lean_is_exclusive(x_659);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_672 = lean_ctor_get(x_659, 0);
x_673 = lean_io_error_to_string(x_672);
x_674 = 3;
x_675 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set_uint8(x_675, sizeof(void*)*1, x_674);
x_676 = lean_array_get_size(x_650);
x_677 = lean_array_push(x_650, x_675);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_677);
lean_ctor_set(x_645, 0, x_676);
lean_ctor_set_tag(x_659, 0);
lean_ctor_set(x_659, 0, x_645);
return x_659;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_678 = lean_ctor_get(x_659, 0);
x_679 = lean_ctor_get(x_659, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_659);
x_680 = lean_io_error_to_string(x_678);
x_681 = 3;
x_682 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_682, 0, x_680);
lean_ctor_set_uint8(x_682, sizeof(void*)*1, x_681);
x_683 = lean_array_get_size(x_650);
x_684 = lean_array_push(x_650, x_682);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_684);
lean_ctor_set(x_645, 0, x_683);
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_645);
lean_ctor_set(x_685, 1, x_679);
return x_685;
}
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_686 = lean_ctor_get(x_645, 1);
lean_inc(x_686);
lean_dec(x_645);
x_687 = lean_ctor_get(x_1, 0);
lean_inc(x_687);
x_688 = l_Lake_Env_leanGithash(x_687);
lean_dec(x_687);
x_689 = l_System_Platform_target;
lean_inc(x_548);
if (lean_is_scalar(x_549)) {
 x_690 = lean_alloc_ctor(0, 4, 0);
} else {
 x_690 = x_549;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_688);
lean_ctor_set(x_690, 2, x_30);
lean_ctor_set(x_690, 3, x_548);
x_691 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_690);
x_692 = lean_unsigned_to_nat(80u);
x_693 = l_Lean_Json_pretty(x_691, x_692);
x_694 = l_IO_FS_Handle_putStrLn(x_547, x_693, x_646);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; 
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
lean_dec(x_694);
x_696 = lean_io_prim_handle_truncate(x_547, x_695);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_686);
x_550 = x_699;
x_551 = x_698;
goto block_644;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_700 = lean_ctor_get(x_696, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_696, 1);
lean_inc(x_701);
lean_dec(x_696);
x_702 = lean_io_error_to_string(x_700);
x_703 = 3;
x_704 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set_uint8(x_704, sizeof(void*)*1, x_703);
x_705 = lean_array_get_size(x_686);
x_706 = lean_array_push(x_686, x_704);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
x_550 = x_707;
x_551 = x_701;
goto block_644;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; uint8_t x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_708 = lean_ctor_get(x_694, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_694, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_710 = x_694;
} else {
 lean_dec_ref(x_694);
 x_710 = lean_box(0);
}
x_711 = lean_io_error_to_string(x_708);
x_712 = 3;
x_713 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set_uint8(x_713, sizeof(void*)*1, x_712);
x_714 = lean_array_get_size(x_686);
x_715 = lean_array_push(x_686, x_713);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
if (lean_is_scalar(x_710)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_710;
 lean_ctor_set_tag(x_717, 0);
}
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_709);
return x_717;
}
}
}
else
{
uint8_t x_718; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_718 = !lean_is_exclusive(x_645);
if (x_718 == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_719 = lean_ctor_get(x_645, 1);
x_720 = lean_ctor_get(x_645, 0);
lean_dec(x_720);
x_721 = lean_io_error_to_string(x_648);
x_722 = 3;
x_723 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*1, x_722);
x_724 = lean_array_get_size(x_719);
x_725 = lean_array_push(x_719, x_723);
x_726 = lean_io_prim_handle_unlock(x_547, x_646);
lean_dec(x_547);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
lean_dec(x_726);
x_728 = lean_io_remove_file(x_24, x_727);
lean_dec(x_24);
if (lean_obj_tag(x_728) == 0)
{
uint8_t x_729; 
x_729 = !lean_is_exclusive(x_728);
if (x_729 == 0)
{
lean_object* x_730; 
x_730 = lean_ctor_get(x_728, 0);
lean_dec(x_730);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_725);
lean_ctor_set(x_645, 0, x_724);
lean_ctor_set(x_728, 0, x_645);
return x_728;
}
else
{
lean_object* x_731; lean_object* x_732; 
x_731 = lean_ctor_get(x_728, 1);
lean_inc(x_731);
lean_dec(x_728);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_725);
lean_ctor_set(x_645, 0, x_724);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_645);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
else
{
uint8_t x_733; 
x_733 = !lean_is_exclusive(x_728);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_734 = lean_ctor_get(x_728, 0);
x_735 = lean_io_error_to_string(x_734);
x_736 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set_uint8(x_736, sizeof(void*)*1, x_722);
x_737 = lean_array_push(x_725, x_736);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_737);
lean_ctor_set(x_645, 0, x_724);
lean_ctor_set_tag(x_728, 0);
lean_ctor_set(x_728, 0, x_645);
return x_728;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_738 = lean_ctor_get(x_728, 0);
x_739 = lean_ctor_get(x_728, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_728);
x_740 = lean_io_error_to_string(x_738);
x_741 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set_uint8(x_741, sizeof(void*)*1, x_722);
x_742 = lean_array_push(x_725, x_741);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_742);
lean_ctor_set(x_645, 0, x_724);
x_743 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_743, 0, x_645);
lean_ctor_set(x_743, 1, x_739);
return x_743;
}
}
}
else
{
uint8_t x_744; 
lean_dec(x_24);
x_744 = !lean_is_exclusive(x_726);
if (x_744 == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_745 = lean_ctor_get(x_726, 0);
x_746 = lean_io_error_to_string(x_745);
x_747 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set_uint8(x_747, sizeof(void*)*1, x_722);
x_748 = lean_array_push(x_725, x_747);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_748);
lean_ctor_set(x_645, 0, x_724);
lean_ctor_set_tag(x_726, 0);
lean_ctor_set(x_726, 0, x_645);
return x_726;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_749 = lean_ctor_get(x_726, 0);
x_750 = lean_ctor_get(x_726, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_726);
x_751 = lean_io_error_to_string(x_749);
x_752 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set_uint8(x_752, sizeof(void*)*1, x_722);
x_753 = lean_array_push(x_725, x_752);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_753);
lean_ctor_set(x_645, 0, x_724);
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_645);
lean_ctor_set(x_754, 1, x_750);
return x_754;
}
}
}
else
{
lean_object* x_755; lean_object* x_756; uint8_t x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_755 = lean_ctor_get(x_645, 1);
lean_inc(x_755);
lean_dec(x_645);
x_756 = lean_io_error_to_string(x_648);
x_757 = 3;
x_758 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_758, 0, x_756);
lean_ctor_set_uint8(x_758, sizeof(void*)*1, x_757);
x_759 = lean_array_get_size(x_755);
x_760 = lean_array_push(x_755, x_758);
x_761 = lean_io_prim_handle_unlock(x_547, x_646);
lean_dec(x_547);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; 
x_762 = lean_ctor_get(x_761, 1);
lean_inc(x_762);
lean_dec(x_761);
x_763 = lean_io_remove_file(x_24, x_762);
lean_dec(x_24);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_764 = lean_ctor_get(x_763, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 lean_ctor_release(x_763, 1);
 x_765 = x_763;
} else {
 lean_dec_ref(x_763);
 x_765 = lean_box(0);
}
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_759);
lean_ctor_set(x_766, 1, x_760);
if (lean_is_scalar(x_765)) {
 x_767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_767 = x_765;
}
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_764);
return x_767;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_768 = lean_ctor_get(x_763, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_763, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 lean_ctor_release(x_763, 1);
 x_770 = x_763;
} else {
 lean_dec_ref(x_763);
 x_770 = lean_box(0);
}
x_771 = lean_io_error_to_string(x_768);
x_772 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_772, 0, x_771);
lean_ctor_set_uint8(x_772, sizeof(void*)*1, x_757);
x_773 = lean_array_push(x_760, x_772);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_759);
lean_ctor_set(x_774, 1, x_773);
if (lean_is_scalar(x_770)) {
 x_775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_775 = x_770;
 lean_ctor_set_tag(x_775, 0);
}
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_769);
return x_775;
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_24);
x_776 = lean_ctor_get(x_761, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_761, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_778 = x_761;
} else {
 lean_dec_ref(x_761);
 x_778 = lean_box(0);
}
x_779 = lean_io_error_to_string(x_776);
x_780 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set_uint8(x_780, sizeof(void*)*1, x_757);
x_781 = lean_array_push(x_760, x_780);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_759);
lean_ctor_set(x_782, 1, x_781);
if (lean_is_scalar(x_778)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_778;
 lean_ctor_set_tag(x_783, 0);
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_777);
return x_783;
}
}
}
}
else
{
uint8_t x_784; 
lean_dec(x_647);
lean_dec(x_24);
x_784 = !lean_is_exclusive(x_645);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_785 = lean_ctor_get(x_645, 1);
x_786 = lean_ctor_get(x_645, 0);
lean_dec(x_786);
x_787 = lean_ctor_get(x_1, 0);
lean_inc(x_787);
x_788 = l_Lake_Env_leanGithash(x_787);
lean_dec(x_787);
x_789 = l_System_Platform_target;
lean_inc(x_548);
if (lean_is_scalar(x_549)) {
 x_790 = lean_alloc_ctor(0, 4, 0);
} else {
 x_790 = x_549;
}
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_788);
lean_ctor_set(x_790, 2, x_30);
lean_ctor_set(x_790, 3, x_548);
x_791 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_790);
x_792 = lean_unsigned_to_nat(80u);
x_793 = l_Lean_Json_pretty(x_791, x_792);
x_794 = l_IO_FS_Handle_putStrLn(x_547, x_793, x_646);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; 
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
lean_dec(x_794);
x_796 = lean_io_prim_handle_truncate(x_547, x_795);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; 
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
lean_ctor_set(x_645, 0, x_797);
x_550 = x_645;
x_551 = x_798;
goto block_644;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_799 = lean_ctor_get(x_796, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_796, 1);
lean_inc(x_800);
lean_dec(x_796);
x_801 = lean_io_error_to_string(x_799);
x_802 = 3;
x_803 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_803, 0, x_801);
lean_ctor_set_uint8(x_803, sizeof(void*)*1, x_802);
x_804 = lean_array_get_size(x_785);
x_805 = lean_array_push(x_785, x_803);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_805);
lean_ctor_set(x_645, 0, x_804);
x_550 = x_645;
x_551 = x_800;
goto block_644;
}
}
else
{
uint8_t x_806; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_806 = !lean_is_exclusive(x_794);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; uint8_t x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_807 = lean_ctor_get(x_794, 0);
x_808 = lean_io_error_to_string(x_807);
x_809 = 3;
x_810 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_810, 0, x_808);
lean_ctor_set_uint8(x_810, sizeof(void*)*1, x_809);
x_811 = lean_array_get_size(x_785);
x_812 = lean_array_push(x_785, x_810);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_812);
lean_ctor_set(x_645, 0, x_811);
lean_ctor_set_tag(x_794, 0);
lean_ctor_set(x_794, 0, x_645);
return x_794;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; uint8_t x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_813 = lean_ctor_get(x_794, 0);
x_814 = lean_ctor_get(x_794, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_794);
x_815 = lean_io_error_to_string(x_813);
x_816 = 3;
x_817 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set_uint8(x_817, sizeof(void*)*1, x_816);
x_818 = lean_array_get_size(x_785);
x_819 = lean_array_push(x_785, x_817);
lean_ctor_set_tag(x_645, 1);
lean_ctor_set(x_645, 1, x_819);
lean_ctor_set(x_645, 0, x_818);
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_645);
lean_ctor_set(x_820, 1, x_814);
return x_820;
}
}
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_821 = lean_ctor_get(x_645, 1);
lean_inc(x_821);
lean_dec(x_645);
x_822 = lean_ctor_get(x_1, 0);
lean_inc(x_822);
x_823 = l_Lake_Env_leanGithash(x_822);
lean_dec(x_822);
x_824 = l_System_Platform_target;
lean_inc(x_548);
if (lean_is_scalar(x_549)) {
 x_825 = lean_alloc_ctor(0, 4, 0);
} else {
 x_825 = x_549;
}
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
lean_ctor_set(x_825, 2, x_30);
lean_ctor_set(x_825, 3, x_548);
x_826 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_825);
x_827 = lean_unsigned_to_nat(80u);
x_828 = l_Lean_Json_pretty(x_826, x_827);
x_829 = l_IO_FS_Handle_putStrLn(x_547, x_828, x_646);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; 
x_830 = lean_ctor_get(x_829, 1);
lean_inc(x_830);
lean_dec(x_829);
x_831 = lean_io_prim_handle_truncate(x_547, x_830);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_834 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_821);
x_550 = x_834;
x_551 = x_833;
goto block_644;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_835 = lean_ctor_get(x_831, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_831, 1);
lean_inc(x_836);
lean_dec(x_831);
x_837 = lean_io_error_to_string(x_835);
x_838 = 3;
x_839 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set_uint8(x_839, sizeof(void*)*1, x_838);
x_840 = lean_array_get_size(x_821);
x_841 = lean_array_push(x_821, x_839);
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_840);
lean_ctor_set(x_842, 1, x_841);
x_550 = x_842;
x_551 = x_836;
goto block_644;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; uint8_t x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_843 = lean_ctor_get(x_829, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_829, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_845 = x_829;
} else {
 lean_dec_ref(x_829);
 x_845 = lean_box(0);
}
x_846 = lean_io_error_to_string(x_843);
x_847 = 3;
x_848 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_848, 0, x_846);
lean_ctor_set_uint8(x_848, sizeof(void*)*1, x_847);
x_849 = lean_array_get_size(x_821);
x_850 = lean_array_push(x_821, x_848);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
if (lean_is_scalar(x_845)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_845;
 lean_ctor_set_tag(x_852, 0);
}
lean_ctor_set(x_852, 0, x_851);
lean_ctor_set(x_852, 1, x_844);
return x_852;
}
}
}
}
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_915; lean_object* x_916; lean_object* x_1016; 
x_861 = lean_ctor_get(x_544, 0);
x_862 = lean_ctor_get(x_544, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_544);
x_863 = lean_ctor_get(x_542, 3);
lean_inc(x_863);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 lean_ctor_release(x_542, 2);
 lean_ctor_release(x_542, 3);
 x_864 = x_542;
} else {
 lean_dec_ref(x_542);
 x_864 = lean_box(0);
}
x_1016 = lean_io_remove_file(x_21, x_545);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec(x_1016);
if (lean_is_scalar(x_543)) {
 x_1019 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1019 = x_543;
}
lean_ctor_set(x_1019, 0, x_1017);
x_1020 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_862);
x_915 = x_1020;
x_916 = x_1018;
goto block_1015;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1021 = lean_ctor_get(x_1016, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1016, 1);
lean_inc(x_1022);
lean_dec(x_1016);
if (lean_is_scalar(x_543)) {
 x_1023 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1023 = x_543;
 lean_ctor_set_tag(x_1023, 0);
}
lean_ctor_set(x_1023, 0, x_1021);
x_1024 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_862);
x_915 = x_1024;
x_916 = x_1022;
goto block_1015;
}
block_914:
{
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_868 = lean_ctor_get(x_1, 5);
lean_inc(x_868);
lean_dec(x_1);
x_869 = l_Lake_elabConfigFile(x_6, x_863, x_868, x_8, x_867, x_866);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_ctor_get(x_870, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_870, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_874 = x_870;
} else {
 lean_dec_ref(x_870);
 x_874 = lean_box(0);
}
lean_inc(x_872);
x_875 = lean_write_module(x_872, x_21, x_871);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; 
x_876 = lean_ctor_get(x_875, 1);
lean_inc(x_876);
lean_dec(x_875);
x_877 = lean_io_prim_handle_unlock(x_861, x_876);
lean_dec(x_861);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_878 = lean_ctor_get(x_877, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 lean_ctor_release(x_877, 1);
 x_879 = x_877;
} else {
 lean_dec_ref(x_877);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_874;
}
lean_ctor_set(x_880, 0, x_872);
lean_ctor_set(x_880, 1, x_873);
if (lean_is_scalar(x_879)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_879;
}
lean_ctor_set(x_881, 0, x_880);
lean_ctor_set(x_881, 1, x_878);
return x_881;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
lean_dec(x_872);
x_882 = lean_ctor_get(x_877, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_877, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_877)) {
 lean_ctor_release(x_877, 0);
 lean_ctor_release(x_877, 1);
 x_884 = x_877;
} else {
 lean_dec_ref(x_877);
 x_884 = lean_box(0);
}
x_885 = lean_io_error_to_string(x_882);
x_886 = 3;
x_887 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_887, 0, x_885);
lean_ctor_set_uint8(x_887, sizeof(void*)*1, x_886);
x_888 = lean_array_get_size(x_873);
x_889 = lean_array_push(x_873, x_887);
if (lean_is_scalar(x_874)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_874;
 lean_ctor_set_tag(x_890, 1);
}
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
if (lean_is_scalar(x_884)) {
 x_891 = lean_alloc_ctor(0, 2, 0);
} else {
 x_891 = x_884;
 lean_ctor_set_tag(x_891, 0);
}
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_883);
return x_891;
}
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; uint8_t x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_872);
lean_dec(x_861);
x_892 = lean_ctor_get(x_875, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_875, 1);
lean_inc(x_893);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_894 = x_875;
} else {
 lean_dec_ref(x_875);
 x_894 = lean_box(0);
}
x_895 = lean_io_error_to_string(x_892);
x_896 = 3;
x_897 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set_uint8(x_897, sizeof(void*)*1, x_896);
x_898 = lean_array_get_size(x_873);
x_899 = lean_array_push(x_873, x_897);
if (lean_is_scalar(x_874)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_874;
 lean_ctor_set_tag(x_900, 1);
}
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
if (lean_is_scalar(x_894)) {
 x_901 = lean_alloc_ctor(0, 2, 0);
} else {
 x_901 = x_894;
 lean_ctor_set_tag(x_901, 0);
}
lean_ctor_set(x_901, 0, x_900);
lean_ctor_set(x_901, 1, x_893);
return x_901;
}
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_861);
lean_dec(x_21);
x_902 = lean_ctor_get(x_869, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_903 = x_869;
} else {
 lean_dec_ref(x_869);
 x_903 = lean_box(0);
}
x_904 = lean_ctor_get(x_870, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_870, 1);
lean_inc(x_905);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_906 = x_870;
} else {
 lean_dec_ref(x_870);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(1, 2, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_904);
lean_ctor_set(x_907, 1, x_905);
if (lean_is_scalar(x_903)) {
 x_908 = lean_alloc_ctor(0, 2, 0);
} else {
 x_908 = x_903;
}
lean_ctor_set(x_908, 0, x_907);
lean_ctor_set(x_908, 1, x_902);
return x_908;
}
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_909 = lean_ctor_get(x_865, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_865, 1);
lean_inc(x_910);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 x_911 = x_865;
} else {
 lean_dec_ref(x_865);
 x_911 = lean_box(0);
}
if (lean_is_scalar(x_911)) {
 x_912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_912 = x_911;
}
lean_ctor_set(x_912, 0, x_909);
lean_ctor_set(x_912, 1, x_910);
x_913 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_866);
return x_913;
}
}
block_1015:
{
lean_object* x_917; 
x_917 = lean_ctor_get(x_915, 0);
lean_inc(x_917);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; 
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
lean_dec(x_917);
if (lean_obj_tag(x_918) == 11)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_918);
lean_dec(x_24);
x_919 = lean_ctor_get(x_915, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_920 = x_915;
} else {
 lean_dec_ref(x_915);
 x_920 = lean_box(0);
}
x_921 = lean_ctor_get(x_1, 0);
lean_inc(x_921);
x_922 = l_Lake_Env_leanGithash(x_921);
lean_dec(x_921);
x_923 = l_System_Platform_target;
lean_inc(x_863);
if (lean_is_scalar(x_864)) {
 x_924 = lean_alloc_ctor(0, 4, 0);
} else {
 x_924 = x_864;
}
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_922);
lean_ctor_set(x_924, 2, x_30);
lean_ctor_set(x_924, 3, x_863);
x_925 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_924);
x_926 = lean_unsigned_to_nat(80u);
x_927 = l_Lean_Json_pretty(x_925, x_926);
x_928 = l_IO_FS_Handle_putStrLn(x_861, x_927, x_916);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; 
x_929 = lean_ctor_get(x_928, 1);
lean_inc(x_929);
lean_dec(x_928);
x_930 = lean_io_prim_handle_truncate(x_861, x_929);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
if (lean_is_scalar(x_920)) {
 x_933 = lean_alloc_ctor(0, 2, 0);
} else {
 x_933 = x_920;
}
lean_ctor_set(x_933, 0, x_931);
lean_ctor_set(x_933, 1, x_919);
x_865 = x_933;
x_866 = x_932;
goto block_914;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; uint8_t x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_934 = lean_ctor_get(x_930, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_930, 1);
lean_inc(x_935);
lean_dec(x_930);
x_936 = lean_io_error_to_string(x_934);
x_937 = 3;
x_938 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set_uint8(x_938, sizeof(void*)*1, x_937);
x_939 = lean_array_get_size(x_919);
x_940 = lean_array_push(x_919, x_938);
if (lean_is_scalar(x_920)) {
 x_941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_941 = x_920;
 lean_ctor_set_tag(x_941, 1);
}
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
x_865 = x_941;
x_866 = x_935;
goto block_914;
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; uint8_t x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_942 = lean_ctor_get(x_928, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_928, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_944 = x_928;
} else {
 lean_dec_ref(x_928);
 x_944 = lean_box(0);
}
x_945 = lean_io_error_to_string(x_942);
x_946 = 3;
x_947 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_947, 0, x_945);
lean_ctor_set_uint8(x_947, sizeof(void*)*1, x_946);
x_948 = lean_array_get_size(x_919);
x_949 = lean_array_push(x_919, x_947);
if (lean_is_scalar(x_920)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_920;
 lean_ctor_set_tag(x_950, 1);
}
lean_ctor_set(x_950, 0, x_948);
lean_ctor_set(x_950, 1, x_949);
if (lean_is_scalar(x_944)) {
 x_951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_951 = x_944;
 lean_ctor_set_tag(x_951, 0);
}
lean_ctor_set(x_951, 0, x_950);
lean_ctor_set(x_951, 1, x_943);
return x_951;
}
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; uint8_t x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_952 = lean_ctor_get(x_915, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_953 = x_915;
} else {
 lean_dec_ref(x_915);
 x_953 = lean_box(0);
}
x_954 = lean_io_error_to_string(x_918);
x_955 = 3;
x_956 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_956, 0, x_954);
lean_ctor_set_uint8(x_956, sizeof(void*)*1, x_955);
x_957 = lean_array_get_size(x_952);
x_958 = lean_array_push(x_952, x_956);
x_959 = lean_io_prim_handle_unlock(x_861, x_916);
lean_dec(x_861);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; lean_object* x_961; 
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
lean_dec(x_959);
x_961 = lean_io_remove_file(x_24, x_960);
lean_dec(x_24);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_962 = lean_ctor_get(x_961, 1);
lean_inc(x_962);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_963 = x_961;
} else {
 lean_dec_ref(x_961);
 x_963 = lean_box(0);
}
if (lean_is_scalar(x_953)) {
 x_964 = lean_alloc_ctor(1, 2, 0);
} else {
 x_964 = x_953;
 lean_ctor_set_tag(x_964, 1);
}
lean_ctor_set(x_964, 0, x_957);
lean_ctor_set(x_964, 1, x_958);
if (lean_is_scalar(x_963)) {
 x_965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_965 = x_963;
}
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_962);
return x_965;
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_966 = lean_ctor_get(x_961, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_961, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_968 = x_961;
} else {
 lean_dec_ref(x_961);
 x_968 = lean_box(0);
}
x_969 = lean_io_error_to_string(x_966);
x_970 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set_uint8(x_970, sizeof(void*)*1, x_955);
x_971 = lean_array_push(x_958, x_970);
if (lean_is_scalar(x_953)) {
 x_972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_972 = x_953;
 lean_ctor_set_tag(x_972, 1);
}
lean_ctor_set(x_972, 0, x_957);
lean_ctor_set(x_972, 1, x_971);
if (lean_is_scalar(x_968)) {
 x_973 = lean_alloc_ctor(0, 2, 0);
} else {
 x_973 = x_968;
 lean_ctor_set_tag(x_973, 0);
}
lean_ctor_set(x_973, 0, x_972);
lean_ctor_set(x_973, 1, x_967);
return x_973;
}
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_24);
x_974 = lean_ctor_get(x_959, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_959, 1);
lean_inc(x_975);
if (lean_is_exclusive(x_959)) {
 lean_ctor_release(x_959, 0);
 lean_ctor_release(x_959, 1);
 x_976 = x_959;
} else {
 lean_dec_ref(x_959);
 x_976 = lean_box(0);
}
x_977 = lean_io_error_to_string(x_974);
x_978 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set_uint8(x_978, sizeof(void*)*1, x_955);
x_979 = lean_array_push(x_958, x_978);
if (lean_is_scalar(x_953)) {
 x_980 = lean_alloc_ctor(1, 2, 0);
} else {
 x_980 = x_953;
 lean_ctor_set_tag(x_980, 1);
}
lean_ctor_set(x_980, 0, x_957);
lean_ctor_set(x_980, 1, x_979);
if (lean_is_scalar(x_976)) {
 x_981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_981 = x_976;
 lean_ctor_set_tag(x_981, 0);
}
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_975);
return x_981;
}
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_917);
lean_dec(x_24);
x_982 = lean_ctor_get(x_915, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_983 = x_915;
} else {
 lean_dec_ref(x_915);
 x_983 = lean_box(0);
}
x_984 = lean_ctor_get(x_1, 0);
lean_inc(x_984);
x_985 = l_Lake_Env_leanGithash(x_984);
lean_dec(x_984);
x_986 = l_System_Platform_target;
lean_inc(x_863);
if (lean_is_scalar(x_864)) {
 x_987 = lean_alloc_ctor(0, 4, 0);
} else {
 x_987 = x_864;
}
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_985);
lean_ctor_set(x_987, 2, x_30);
lean_ctor_set(x_987, 3, x_863);
x_988 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_987);
x_989 = lean_unsigned_to_nat(80u);
x_990 = l_Lean_Json_pretty(x_988, x_989);
x_991 = l_IO_FS_Handle_putStrLn(x_861, x_990, x_916);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; 
x_992 = lean_ctor_get(x_991, 1);
lean_inc(x_992);
lean_dec(x_991);
x_993 = lean_io_prim_handle_truncate(x_861, x_992);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
if (lean_is_scalar(x_983)) {
 x_996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_996 = x_983;
}
lean_ctor_set(x_996, 0, x_994);
lean_ctor_set(x_996, 1, x_982);
x_865 = x_996;
x_866 = x_995;
goto block_914;
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_997 = lean_ctor_get(x_993, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_993, 1);
lean_inc(x_998);
lean_dec(x_993);
x_999 = lean_io_error_to_string(x_997);
x_1000 = 3;
x_1001 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set_uint8(x_1001, sizeof(void*)*1, x_1000);
x_1002 = lean_array_get_size(x_982);
x_1003 = lean_array_push(x_982, x_1001);
if (lean_is_scalar(x_983)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_983;
 lean_ctor_set_tag(x_1004, 1);
}
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
x_865 = x_1004;
x_866 = x_998;
goto block_914;
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1005 = lean_ctor_get(x_991, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_991, 1);
lean_inc(x_1006);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1007 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1007 = lean_box(0);
}
x_1008 = lean_io_error_to_string(x_1005);
x_1009 = 3;
x_1010 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1010, 0, x_1008);
lean_ctor_set_uint8(x_1010, sizeof(void*)*1, x_1009);
x_1011 = lean_array_get_size(x_982);
x_1012 = lean_array_push(x_982, x_1010);
if (lean_is_scalar(x_983)) {
 x_1013 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1013 = x_983;
 lean_ctor_set_tag(x_1013, 1);
}
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
if (lean_is_scalar(x_1007)) {
 x_1014 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1014 = x_1007;
 lean_ctor_set_tag(x_1014, 0);
}
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_1006);
return x_1014;
}
}
}
}
}
else
{
uint8_t x_1025; 
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1025 = !lean_is_exclusive(x_544);
if (x_1025 == 0)
{
lean_object* x_1026; 
x_1026 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1026, 0, x_544);
lean_ctor_set(x_1026, 1, x_545);
return x_1026;
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1027 = lean_ctor_get(x_544, 0);
x_1028 = lean_ctor_get(x_544, 1);
lean_inc(x_1028);
lean_inc(x_1027);
lean_dec(x_544);
x_1029 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1029, 0, x_1027);
lean_ctor_set(x_1029, 1, x_1028);
x_1030 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_545);
return x_1030;
}
}
}
block_1083:
{
lean_object* x_1036; lean_object* x_1037; uint8_t x_1045; lean_object* x_1046; 
lean_dec(x_1035);
x_1045 = 1;
x_1046 = lean_io_prim_handle_mk(x_27, x_1045, x_1034);
lean_dec(x_27);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; lean_object* x_1050; 
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1049 = 1;
x_1050 = lean_io_prim_handle_try_lock(x_1047, x_1049, x_1048);
if (lean_obj_tag(x_1050) == 0)
{
lean_object* x_1051; uint8_t x_1052; 
x_1051 = lean_ctor_get(x_1050, 0);
lean_inc(x_1051);
x_1052 = lean_unbox(x_1051);
lean_dec(x_1051);
if (x_1052 == 0)
{
lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1047);
lean_dec(x_523);
x_1053 = lean_ctor_get(x_1050, 1);
lean_inc(x_1053);
lean_dec(x_1050);
x_1054 = lean_io_prim_handle_unlock(x_521, x_1053);
lean_dec(x_521);
if (lean_obj_tag(x_1054) == 0)
{
lean_object* x_1055; lean_object* x_1056; 
x_1055 = lean_ctor_get(x_1054, 1);
lean_inc(x_1055);
lean_dec(x_1054);
x_1056 = l_Lake_importConfigFile___closed__11;
x_1036 = x_1056;
x_1037 = x_1055;
goto block_1044;
}
else
{
lean_object* x_1057; lean_object* x_1058; 
x_1057 = lean_ctor_get(x_1054, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1054, 1);
lean_inc(x_1058);
lean_dec(x_1054);
x_1036 = x_1057;
x_1037 = x_1058;
goto block_1044;
}
}
else
{
lean_object* x_1059; lean_object* x_1060; 
x_1059 = lean_ctor_get(x_1050, 1);
lean_inc(x_1059);
lean_dec(x_1050);
x_1060 = lean_io_prim_handle_unlock(x_521, x_1059);
lean_dec(x_521);
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; uint8_t x_1062; lean_object* x_1063; 
x_1061 = lean_ctor_get(x_1060, 1);
lean_inc(x_1061);
lean_dec(x_1060);
x_1062 = 3;
x_1063 = lean_io_prim_handle_mk(x_24, x_1062, x_1061);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_io_prim_handle_lock(x_1064, x_1049, x_1065);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; 
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
lean_dec(x_1066);
x_1068 = lean_io_prim_handle_unlock(x_1047, x_1067);
lean_dec(x_1047);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_528);
x_1069 = lean_ctor_get(x_1068, 1);
lean_inc(x_1069);
lean_dec(x_1068);
if (lean_is_scalar(x_523)) {
 x_1070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1070 = x_523;
}
lean_ctor_set(x_1070, 0, x_1064);
lean_ctor_set(x_1070, 1, x_527);
x_544 = x_1070;
x_545 = x_1069;
goto block_1031;
}
else
{
lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_1064);
lean_dec(x_523);
x_1071 = lean_ctor_get(x_1068, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1068, 1);
lean_inc(x_1072);
lean_dec(x_1068);
x_1036 = x_1071;
x_1037 = x_1072;
goto block_1044;
}
}
else
{
lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_1064);
lean_dec(x_1047);
lean_dec(x_523);
x_1073 = lean_ctor_get(x_1066, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1066, 1);
lean_inc(x_1074);
lean_dec(x_1066);
x_1036 = x_1073;
x_1037 = x_1074;
goto block_1044;
}
}
else
{
lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_1047);
lean_dec(x_523);
x_1075 = lean_ctor_get(x_1063, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1063, 1);
lean_inc(x_1076);
lean_dec(x_1063);
x_1036 = x_1075;
x_1037 = x_1076;
goto block_1044;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; 
lean_dec(x_1047);
lean_dec(x_523);
x_1077 = lean_ctor_get(x_1060, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1060, 1);
lean_inc(x_1078);
lean_dec(x_1060);
x_1036 = x_1077;
x_1037 = x_1078;
goto block_1044;
}
}
}
else
{
lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_1047);
lean_dec(x_523);
lean_dec(x_521);
x_1079 = lean_ctor_get(x_1050, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1050, 1);
lean_inc(x_1080);
lean_dec(x_1050);
x_1036 = x_1079;
x_1037 = x_1080;
goto block_1044;
}
}
else
{
lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_523);
lean_dec(x_521);
x_1081 = lean_ctor_get(x_1046, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1046, 1);
lean_inc(x_1082);
lean_dec(x_1046);
x_1036 = x_1081;
x_1037 = x_1082;
goto block_1044;
}
block_1044:
{
lean_object* x_1038; uint8_t x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1038 = lean_io_error_to_string(x_1036);
x_1039 = 3;
x_1040 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1040, 0, x_1038);
lean_ctor_set_uint8(x_1040, sizeof(void*)*1, x_1039);
x_1041 = lean_array_get_size(x_527);
x_1042 = lean_array_push(x_527, x_1040);
if (lean_is_scalar(x_528)) {
 x_1043 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1043 = x_528;
 lean_ctor_set_tag(x_1043, 1);
}
lean_ctor_set(x_1043, 0, x_1041);
lean_ctor_set(x_1043, 1, x_1042);
x_544 = x_1043;
x_545 = x_1037;
goto block_1031;
}
}
}
}
}
else
{
uint8_t x_1145; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1145 = !lean_is_exclusive(x_524);
if (x_1145 == 0)
{
lean_object* x_1146; 
x_1146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1146, 0, x_524);
lean_ctor_set(x_1146, 1, x_525);
return x_1146;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1147 = lean_ctor_get(x_524, 0);
x_1148 = lean_ctor_get(x_524, 1);
lean_inc(x_1148);
lean_inc(x_1147);
lean_dec(x_524);
x_1149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set(x_1149, 1, x_1148);
x_1150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_525);
return x_1150;
}
}
}
}
else
{
uint8_t x_1246; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1246 = !lean_is_exclusive(x_519);
if (x_1246 == 0)
{
lean_object* x_1247; 
x_1247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1247, 0, x_519);
lean_ctor_set(x_1247, 1, x_520);
return x_1247;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1248 = lean_ctor_get(x_519, 0);
x_1249 = lean_ctor_get(x_519, 1);
lean_inc(x_1249);
lean_inc(x_1248);
lean_dec(x_519);
x_1250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1250, 0, x_1248);
lean_ctor_set(x_1250, 1, x_1249);
x_1251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1251, 0, x_1250);
lean_ctor_set(x_1251, 1, x_520);
return x_1251;
}
}
}
block_1990:
{
lean_object* x_1255; 
x_1255 = lean_ctor_get(x_1253, 0);
lean_inc(x_1255);
if (lean_obj_tag(x_1255) == 0)
{
lean_object* x_1256; 
x_1256 = lean_ctor_get(x_1255, 0);
lean_inc(x_1256);
lean_dec(x_1255);
if (lean_obj_tag(x_1256) == 0)
{
uint8_t x_1257; 
lean_dec(x_1256);
x_1257 = !lean_is_exclusive(x_1253);
if (x_1257 == 0)
{
lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; lean_object* x_1261; 
x_1258 = lean_ctor_get(x_1253, 1);
x_1259 = lean_ctor_get(x_1253, 0);
lean_dec(x_1259);
x_1260 = 0;
x_1261 = lean_io_prim_handle_mk(x_24, x_1260, x_1254);
if (lean_obj_tag(x_1261) == 0)
{
lean_object* x_1262; lean_object* x_1263; 
x_1262 = lean_ctor_get(x_1261, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1261, 1);
lean_inc(x_1263);
lean_dec(x_1261);
lean_ctor_set(x_1253, 0, x_1262);
x_519 = x_1253;
x_520 = x_1263;
goto block_1252;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; uint8_t x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1264 = lean_ctor_get(x_1261, 0);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1261, 1);
lean_inc(x_1265);
lean_dec(x_1261);
x_1266 = lean_io_error_to_string(x_1264);
x_1267 = 3;
x_1268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set_uint8(x_1268, sizeof(void*)*1, x_1267);
x_1269 = lean_array_get_size(x_1258);
x_1270 = lean_array_push(x_1258, x_1268);
lean_ctor_set_tag(x_1253, 1);
lean_ctor_set(x_1253, 1, x_1270);
lean_ctor_set(x_1253, 0, x_1269);
x_519 = x_1253;
x_520 = x_1265;
goto block_1252;
}
}
else
{
lean_object* x_1271; uint8_t x_1272; lean_object* x_1273; 
x_1271 = lean_ctor_get(x_1253, 1);
lean_inc(x_1271);
lean_dec(x_1253);
x_1272 = 0;
x_1273 = lean_io_prim_handle_mk(x_24, x_1272, x_1254);
if (lean_obj_tag(x_1273) == 0)
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
x_1274 = lean_ctor_get(x_1273, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_1273, 1);
lean_inc(x_1275);
lean_dec(x_1273);
x_1276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1276, 0, x_1274);
lean_ctor_set(x_1276, 1, x_1271);
x_519 = x_1276;
x_520 = x_1275;
goto block_1252;
}
else
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; uint8_t x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1277 = lean_ctor_get(x_1273, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1273, 1);
lean_inc(x_1278);
lean_dec(x_1273);
x_1279 = lean_io_error_to_string(x_1277);
x_1280 = 3;
x_1281 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1281, 0, x_1279);
lean_ctor_set_uint8(x_1281, sizeof(void*)*1, x_1280);
x_1282 = lean_array_get_size(x_1271);
x_1283 = lean_array_push(x_1271, x_1281);
x_1284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1284, 0, x_1282);
lean_ctor_set(x_1284, 1, x_1283);
x_519 = x_1284;
x_520 = x_1278;
goto block_1252;
}
}
}
else
{
uint8_t x_1285; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1285 = !lean_is_exclusive(x_1253);
if (x_1285 == 0)
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; uint8_t x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1286 = lean_ctor_get(x_1253, 1);
x_1287 = lean_ctor_get(x_1253, 0);
lean_dec(x_1287);
x_1288 = lean_io_error_to_string(x_1256);
x_1289 = 3;
x_1290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1290, 0, x_1288);
lean_ctor_set_uint8(x_1290, sizeof(void*)*1, x_1289);
x_1291 = lean_array_get_size(x_1286);
x_1292 = lean_array_push(x_1286, x_1290);
lean_ctor_set_tag(x_1253, 1);
lean_ctor_set(x_1253, 1, x_1292);
lean_ctor_set(x_1253, 0, x_1291);
x_1293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1293, 0, x_1253);
lean_ctor_set(x_1293, 1, x_1254);
return x_1293;
}
else
{
lean_object* x_1294; lean_object* x_1295; uint8_t x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1294 = lean_ctor_get(x_1253, 1);
lean_inc(x_1294);
lean_dec(x_1253);
x_1295 = lean_io_error_to_string(x_1256);
x_1296 = 3;
x_1297 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1297, 0, x_1295);
lean_ctor_set_uint8(x_1297, sizeof(void*)*1, x_1296);
x_1298 = lean_array_get_size(x_1294);
x_1299 = lean_array_push(x_1294, x_1297);
x_1300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1300, 0, x_1298);
lean_ctor_set(x_1300, 1, x_1299);
x_1301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1301, 0, x_1300);
lean_ctor_set(x_1301, 1, x_1254);
return x_1301;
}
}
}
else
{
uint8_t x_1302; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_16);
x_1302 = !lean_is_exclusive(x_1253);
if (x_1302 == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; uint8_t x_1792; lean_object* x_1793; 
x_1303 = lean_ctor_get(x_1253, 1);
x_1304 = lean_ctor_get(x_1253, 0);
lean_dec(x_1304);
x_1305 = lean_ctor_get(x_1255, 0);
lean_inc(x_1305);
if (lean_is_exclusive(x_1255)) {
 lean_ctor_release(x_1255, 0);
 x_1306 = x_1255;
} else {
 lean_dec_ref(x_1255);
 x_1306 = lean_box(0);
}
x_1792 = 1;
x_1793 = lean_io_prim_handle_lock(x_1305, x_1792, x_1254);
if (lean_obj_tag(x_1793) == 0)
{
lean_object* x_1794; lean_object* x_1795; 
x_1794 = lean_ctor_get(x_1793, 0);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_1793, 1);
lean_inc(x_1795);
lean_dec(x_1793);
lean_ctor_set(x_1253, 0, x_1794);
x_1307 = x_1253;
x_1308 = x_1795;
goto block_1791;
}
else
{
lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; uint8_t x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; 
x_1796 = lean_ctor_get(x_1793, 0);
lean_inc(x_1796);
x_1797 = lean_ctor_get(x_1793, 1);
lean_inc(x_1797);
lean_dec(x_1793);
x_1798 = lean_io_error_to_string(x_1796);
x_1799 = 3;
x_1800 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1800, 0, x_1798);
lean_ctor_set_uint8(x_1800, sizeof(void*)*1, x_1799);
x_1801 = lean_array_get_size(x_1303);
x_1802 = lean_array_push(x_1303, x_1800);
lean_ctor_set_tag(x_1253, 1);
lean_ctor_set(x_1253, 1, x_1802);
lean_ctor_set(x_1253, 0, x_1801);
x_1307 = x_1253;
x_1308 = x_1797;
goto block_1791;
}
block_1791:
{
if (lean_obj_tag(x_1307) == 0)
{
uint8_t x_1309; 
x_1309 = !lean_is_exclusive(x_1307);
if (x_1309 == 0)
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1407; lean_object* x_1408; lean_object* x_1616; 
x_1310 = lean_ctor_get(x_1307, 0);
lean_dec(x_1310);
x_1311 = lean_ctor_get(x_1, 4);
lean_inc(x_1311);
x_1616 = lean_io_remove_file(x_21, x_1308);
if (lean_obj_tag(x_1616) == 0)
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; 
x_1617 = lean_ctor_get(x_1616, 0);
lean_inc(x_1617);
x_1618 = lean_ctor_get(x_1616, 1);
lean_inc(x_1618);
lean_dec(x_1616);
if (lean_is_scalar(x_1306)) {
 x_1619 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1619 = x_1306;
}
lean_ctor_set(x_1619, 0, x_1617);
lean_ctor_set(x_1307, 0, x_1619);
x_1407 = x_1307;
x_1408 = x_1618;
goto block_1615;
}
else
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1620 = lean_ctor_get(x_1616, 0);
lean_inc(x_1620);
x_1621 = lean_ctor_get(x_1616, 1);
lean_inc(x_1621);
lean_dec(x_1616);
if (lean_is_scalar(x_1306)) {
 x_1622 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1622 = x_1306;
 lean_ctor_set_tag(x_1622, 0);
}
lean_ctor_set(x_1622, 0, x_1620);
lean_ctor_set(x_1307, 0, x_1622);
x_1407 = x_1307;
x_1408 = x_1621;
goto block_1615;
}
block_1406:
{
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1314 = lean_ctor_get(x_1312, 1);
lean_inc(x_1314);
lean_dec(x_1312);
x_1315 = lean_ctor_get(x_1, 5);
lean_inc(x_1315);
lean_dec(x_1);
x_1316 = l_Lake_elabConfigFile(x_6, x_1311, x_1315, x_8, x_1314, x_1313);
x_1317 = lean_ctor_get(x_1316, 0);
lean_inc(x_1317);
if (lean_obj_tag(x_1317) == 0)
{
lean_object* x_1318; uint8_t x_1319; 
x_1318 = lean_ctor_get(x_1316, 1);
lean_inc(x_1318);
lean_dec(x_1316);
x_1319 = !lean_is_exclusive(x_1317);
if (x_1319 == 0)
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1320 = lean_ctor_get(x_1317, 0);
x_1321 = lean_ctor_get(x_1317, 1);
lean_inc(x_1320);
x_1322 = lean_write_module(x_1320, x_21, x_1318);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; 
x_1323 = lean_ctor_get(x_1322, 1);
lean_inc(x_1323);
lean_dec(x_1322);
x_1324 = lean_io_prim_handle_unlock(x_1305, x_1323);
lean_dec(x_1305);
if (lean_obj_tag(x_1324) == 0)
{
uint8_t x_1325; 
x_1325 = !lean_is_exclusive(x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; 
x_1326 = lean_ctor_get(x_1324, 0);
lean_dec(x_1326);
lean_ctor_set(x_1324, 0, x_1317);
return x_1324;
}
else
{
lean_object* x_1327; lean_object* x_1328; 
x_1327 = lean_ctor_get(x_1324, 1);
lean_inc(x_1327);
lean_dec(x_1324);
x_1328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1328, 0, x_1317);
lean_ctor_set(x_1328, 1, x_1327);
return x_1328;
}
}
else
{
uint8_t x_1329; 
lean_dec(x_1320);
x_1329 = !lean_is_exclusive(x_1324);
if (x_1329 == 0)
{
lean_object* x_1330; lean_object* x_1331; uint8_t x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1330 = lean_ctor_get(x_1324, 0);
x_1331 = lean_io_error_to_string(x_1330);
x_1332 = 3;
x_1333 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1333, 0, x_1331);
lean_ctor_set_uint8(x_1333, sizeof(void*)*1, x_1332);
x_1334 = lean_array_get_size(x_1321);
x_1335 = lean_array_push(x_1321, x_1333);
lean_ctor_set_tag(x_1317, 1);
lean_ctor_set(x_1317, 1, x_1335);
lean_ctor_set(x_1317, 0, x_1334);
lean_ctor_set_tag(x_1324, 0);
lean_ctor_set(x_1324, 0, x_1317);
return x_1324;
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; uint8_t x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
x_1336 = lean_ctor_get(x_1324, 0);
x_1337 = lean_ctor_get(x_1324, 1);
lean_inc(x_1337);
lean_inc(x_1336);
lean_dec(x_1324);
x_1338 = lean_io_error_to_string(x_1336);
x_1339 = 3;
x_1340 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1340, 0, x_1338);
lean_ctor_set_uint8(x_1340, sizeof(void*)*1, x_1339);
x_1341 = lean_array_get_size(x_1321);
x_1342 = lean_array_push(x_1321, x_1340);
lean_ctor_set_tag(x_1317, 1);
lean_ctor_set(x_1317, 1, x_1342);
lean_ctor_set(x_1317, 0, x_1341);
x_1343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1343, 0, x_1317);
lean_ctor_set(x_1343, 1, x_1337);
return x_1343;
}
}
}
else
{
uint8_t x_1344; 
lean_dec(x_1320);
lean_dec(x_1305);
x_1344 = !lean_is_exclusive(x_1322);
if (x_1344 == 0)
{
lean_object* x_1345; lean_object* x_1346; uint8_t x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1345 = lean_ctor_get(x_1322, 0);
x_1346 = lean_io_error_to_string(x_1345);
x_1347 = 3;
x_1348 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1348, 0, x_1346);
lean_ctor_set_uint8(x_1348, sizeof(void*)*1, x_1347);
x_1349 = lean_array_get_size(x_1321);
x_1350 = lean_array_push(x_1321, x_1348);
lean_ctor_set_tag(x_1317, 1);
lean_ctor_set(x_1317, 1, x_1350);
lean_ctor_set(x_1317, 0, x_1349);
lean_ctor_set_tag(x_1322, 0);
lean_ctor_set(x_1322, 0, x_1317);
return x_1322;
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; uint8_t x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1351 = lean_ctor_get(x_1322, 0);
x_1352 = lean_ctor_get(x_1322, 1);
lean_inc(x_1352);
lean_inc(x_1351);
lean_dec(x_1322);
x_1353 = lean_io_error_to_string(x_1351);
x_1354 = 3;
x_1355 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1355, 0, x_1353);
lean_ctor_set_uint8(x_1355, sizeof(void*)*1, x_1354);
x_1356 = lean_array_get_size(x_1321);
x_1357 = lean_array_push(x_1321, x_1355);
lean_ctor_set_tag(x_1317, 1);
lean_ctor_set(x_1317, 1, x_1357);
lean_ctor_set(x_1317, 0, x_1356);
x_1358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1358, 0, x_1317);
lean_ctor_set(x_1358, 1, x_1352);
return x_1358;
}
}
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
x_1359 = lean_ctor_get(x_1317, 0);
x_1360 = lean_ctor_get(x_1317, 1);
lean_inc(x_1360);
lean_inc(x_1359);
lean_dec(x_1317);
lean_inc(x_1359);
x_1361 = lean_write_module(x_1359, x_21, x_1318);
if (lean_obj_tag(x_1361) == 0)
{
lean_object* x_1362; lean_object* x_1363; 
x_1362 = lean_ctor_get(x_1361, 1);
lean_inc(x_1362);
lean_dec(x_1361);
x_1363 = lean_io_prim_handle_unlock(x_1305, x_1362);
lean_dec(x_1305);
if (lean_obj_tag(x_1363) == 0)
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1364 = lean_ctor_get(x_1363, 1);
lean_inc(x_1364);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1365 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1365 = lean_box(0);
}
x_1366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1366, 0, x_1359);
lean_ctor_set(x_1366, 1, x_1360);
if (lean_is_scalar(x_1365)) {
 x_1367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1367 = x_1365;
}
lean_ctor_set(x_1367, 0, x_1366);
lean_ctor_set(x_1367, 1, x_1364);
return x_1367;
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; uint8_t x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_dec(x_1359);
x_1368 = lean_ctor_get(x_1363, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1363, 1);
lean_inc(x_1369);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1370 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1370 = lean_box(0);
}
x_1371 = lean_io_error_to_string(x_1368);
x_1372 = 3;
x_1373 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1373, 0, x_1371);
lean_ctor_set_uint8(x_1373, sizeof(void*)*1, x_1372);
x_1374 = lean_array_get_size(x_1360);
x_1375 = lean_array_push(x_1360, x_1373);
x_1376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1376, 0, x_1374);
lean_ctor_set(x_1376, 1, x_1375);
if (lean_is_scalar(x_1370)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1370;
 lean_ctor_set_tag(x_1377, 0);
}
lean_ctor_set(x_1377, 0, x_1376);
lean_ctor_set(x_1377, 1, x_1369);
return x_1377;
}
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; uint8_t x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
lean_dec(x_1359);
lean_dec(x_1305);
x_1378 = lean_ctor_get(x_1361, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1361, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1361)) {
 lean_ctor_release(x_1361, 0);
 lean_ctor_release(x_1361, 1);
 x_1380 = x_1361;
} else {
 lean_dec_ref(x_1361);
 x_1380 = lean_box(0);
}
x_1381 = lean_io_error_to_string(x_1378);
x_1382 = 3;
x_1383 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1383, 0, x_1381);
lean_ctor_set_uint8(x_1383, sizeof(void*)*1, x_1382);
x_1384 = lean_array_get_size(x_1360);
x_1385 = lean_array_push(x_1360, x_1383);
x_1386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1386, 0, x_1384);
lean_ctor_set(x_1386, 1, x_1385);
if (lean_is_scalar(x_1380)) {
 x_1387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1387 = x_1380;
 lean_ctor_set_tag(x_1387, 0);
}
lean_ctor_set(x_1387, 0, x_1386);
lean_ctor_set(x_1387, 1, x_1379);
return x_1387;
}
}
}
else
{
uint8_t x_1388; 
lean_dec(x_1305);
lean_dec(x_21);
x_1388 = !lean_is_exclusive(x_1316);
if (x_1388 == 0)
{
lean_object* x_1389; uint8_t x_1390; 
x_1389 = lean_ctor_get(x_1316, 0);
lean_dec(x_1389);
x_1390 = !lean_is_exclusive(x_1317);
if (x_1390 == 0)
{
return x_1316;
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1391 = lean_ctor_get(x_1317, 0);
x_1392 = lean_ctor_get(x_1317, 1);
lean_inc(x_1392);
lean_inc(x_1391);
lean_dec(x_1317);
x_1393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1393, 0, x_1391);
lean_ctor_set(x_1393, 1, x_1392);
lean_ctor_set(x_1316, 0, x_1393);
return x_1316;
}
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1394 = lean_ctor_get(x_1316, 1);
lean_inc(x_1394);
lean_dec(x_1316);
x_1395 = lean_ctor_get(x_1317, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1317, 1);
lean_inc(x_1396);
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 lean_ctor_release(x_1317, 1);
 x_1397 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1397 = lean_box(0);
}
if (lean_is_scalar(x_1397)) {
 x_1398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1398 = x_1397;
}
lean_ctor_set(x_1398, 0, x_1395);
lean_ctor_set(x_1398, 1, x_1396);
x_1399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1399, 0, x_1398);
lean_ctor_set(x_1399, 1, x_1394);
return x_1399;
}
}
}
else
{
uint8_t x_1400; 
lean_dec(x_1311);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1400 = !lean_is_exclusive(x_1312);
if (x_1400 == 0)
{
lean_object* x_1401; 
x_1401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1401, 0, x_1312);
lean_ctor_set(x_1401, 1, x_1313);
return x_1401;
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
x_1402 = lean_ctor_get(x_1312, 0);
x_1403 = lean_ctor_get(x_1312, 1);
lean_inc(x_1403);
lean_inc(x_1402);
lean_dec(x_1312);
x_1404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1404, 0, x_1402);
lean_ctor_set(x_1404, 1, x_1403);
x_1405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1405, 0, x_1404);
lean_ctor_set(x_1405, 1, x_1313);
return x_1405;
}
}
}
block_1615:
{
lean_object* x_1409; 
x_1409 = lean_ctor_get(x_1407, 0);
lean_inc(x_1409);
if (lean_obj_tag(x_1409) == 0)
{
lean_object* x_1410; 
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
lean_dec(x_1409);
if (lean_obj_tag(x_1410) == 11)
{
uint8_t x_1411; 
lean_dec(x_1410);
lean_dec(x_24);
x_1411 = !lean_is_exclusive(x_1407);
if (x_1411 == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; 
x_1412 = lean_ctor_get(x_1407, 1);
x_1413 = lean_ctor_get(x_1407, 0);
lean_dec(x_1413);
x_1414 = lean_ctor_get(x_1, 0);
lean_inc(x_1414);
x_1415 = l_Lake_Env_leanGithash(x_1414);
lean_dec(x_1414);
x_1416 = l_System_Platform_target;
lean_inc(x_1311);
x_1417 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1417, 0, x_1416);
lean_ctor_set(x_1417, 1, x_1415);
lean_ctor_set(x_1417, 2, x_30);
lean_ctor_set(x_1417, 3, x_1311);
x_1418 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1417);
x_1419 = lean_unsigned_to_nat(80u);
x_1420 = l_Lean_Json_pretty(x_1418, x_1419);
x_1421 = l_IO_FS_Handle_putStrLn(x_1305, x_1420, x_1408);
if (lean_obj_tag(x_1421) == 0)
{
lean_object* x_1422; lean_object* x_1423; 
x_1422 = lean_ctor_get(x_1421, 1);
lean_inc(x_1422);
lean_dec(x_1421);
x_1423 = lean_io_prim_handle_truncate(x_1305, x_1422);
if (lean_obj_tag(x_1423) == 0)
{
lean_object* x_1424; lean_object* x_1425; 
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1423, 1);
lean_inc(x_1425);
lean_dec(x_1423);
lean_ctor_set(x_1407, 0, x_1424);
x_1312 = x_1407;
x_1313 = x_1425;
goto block_1406;
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
x_1426 = lean_ctor_get(x_1423, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1423, 1);
lean_inc(x_1427);
lean_dec(x_1423);
x_1428 = lean_io_error_to_string(x_1426);
x_1429 = 3;
x_1430 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1430, 0, x_1428);
lean_ctor_set_uint8(x_1430, sizeof(void*)*1, x_1429);
x_1431 = lean_array_get_size(x_1412);
x_1432 = lean_array_push(x_1412, x_1430);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1432);
lean_ctor_set(x_1407, 0, x_1431);
x_1312 = x_1407;
x_1313 = x_1427;
goto block_1406;
}
}
else
{
uint8_t x_1433; 
lean_dec(x_1311);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1433 = !lean_is_exclusive(x_1421);
if (x_1433 == 0)
{
lean_object* x_1434; lean_object* x_1435; uint8_t x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
x_1434 = lean_ctor_get(x_1421, 0);
x_1435 = lean_io_error_to_string(x_1434);
x_1436 = 3;
x_1437 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1437, 0, x_1435);
lean_ctor_set_uint8(x_1437, sizeof(void*)*1, x_1436);
x_1438 = lean_array_get_size(x_1412);
x_1439 = lean_array_push(x_1412, x_1437);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1439);
lean_ctor_set(x_1407, 0, x_1438);
lean_ctor_set_tag(x_1421, 0);
lean_ctor_set(x_1421, 0, x_1407);
return x_1421;
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; uint8_t x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1440 = lean_ctor_get(x_1421, 0);
x_1441 = lean_ctor_get(x_1421, 1);
lean_inc(x_1441);
lean_inc(x_1440);
lean_dec(x_1421);
x_1442 = lean_io_error_to_string(x_1440);
x_1443 = 3;
x_1444 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1444, 0, x_1442);
lean_ctor_set_uint8(x_1444, sizeof(void*)*1, x_1443);
x_1445 = lean_array_get_size(x_1412);
x_1446 = lean_array_push(x_1412, x_1444);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1446);
lean_ctor_set(x_1407, 0, x_1445);
x_1447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1447, 0, x_1407);
lean_ctor_set(x_1447, 1, x_1441);
return x_1447;
}
}
}
else
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
x_1448 = lean_ctor_get(x_1407, 1);
lean_inc(x_1448);
lean_dec(x_1407);
x_1449 = lean_ctor_get(x_1, 0);
lean_inc(x_1449);
x_1450 = l_Lake_Env_leanGithash(x_1449);
lean_dec(x_1449);
x_1451 = l_System_Platform_target;
lean_inc(x_1311);
x_1452 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1452, 0, x_1451);
lean_ctor_set(x_1452, 1, x_1450);
lean_ctor_set(x_1452, 2, x_30);
lean_ctor_set(x_1452, 3, x_1311);
x_1453 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1452);
x_1454 = lean_unsigned_to_nat(80u);
x_1455 = l_Lean_Json_pretty(x_1453, x_1454);
x_1456 = l_IO_FS_Handle_putStrLn(x_1305, x_1455, x_1408);
if (lean_obj_tag(x_1456) == 0)
{
lean_object* x_1457; lean_object* x_1458; 
x_1457 = lean_ctor_get(x_1456, 1);
lean_inc(x_1457);
lean_dec(x_1456);
x_1458 = lean_io_prim_handle_truncate(x_1305, x_1457);
if (lean_obj_tag(x_1458) == 0)
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
x_1459 = lean_ctor_get(x_1458, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1458, 1);
lean_inc(x_1460);
lean_dec(x_1458);
x_1461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1461, 0, x_1459);
lean_ctor_set(x_1461, 1, x_1448);
x_1312 = x_1461;
x_1313 = x_1460;
goto block_1406;
}
else
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; uint8_t x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
x_1462 = lean_ctor_get(x_1458, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1458, 1);
lean_inc(x_1463);
lean_dec(x_1458);
x_1464 = lean_io_error_to_string(x_1462);
x_1465 = 3;
x_1466 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1466, 0, x_1464);
lean_ctor_set_uint8(x_1466, sizeof(void*)*1, x_1465);
x_1467 = lean_array_get_size(x_1448);
x_1468 = lean_array_push(x_1448, x_1466);
x_1469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1469, 0, x_1467);
lean_ctor_set(x_1469, 1, x_1468);
x_1312 = x_1469;
x_1313 = x_1463;
goto block_1406;
}
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; uint8_t x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; 
lean_dec(x_1311);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1470 = lean_ctor_get(x_1456, 0);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1456, 1);
lean_inc(x_1471);
if (lean_is_exclusive(x_1456)) {
 lean_ctor_release(x_1456, 0);
 lean_ctor_release(x_1456, 1);
 x_1472 = x_1456;
} else {
 lean_dec_ref(x_1456);
 x_1472 = lean_box(0);
}
x_1473 = lean_io_error_to_string(x_1470);
x_1474 = 3;
x_1475 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1475, 0, x_1473);
lean_ctor_set_uint8(x_1475, sizeof(void*)*1, x_1474);
x_1476 = lean_array_get_size(x_1448);
x_1477 = lean_array_push(x_1448, x_1475);
x_1478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1478, 0, x_1476);
lean_ctor_set(x_1478, 1, x_1477);
if (lean_is_scalar(x_1472)) {
 x_1479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1479 = x_1472;
 lean_ctor_set_tag(x_1479, 0);
}
lean_ctor_set(x_1479, 0, x_1478);
lean_ctor_set(x_1479, 1, x_1471);
return x_1479;
}
}
}
else
{
uint8_t x_1480; 
lean_dec(x_1311);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1480 = !lean_is_exclusive(x_1407);
if (x_1480 == 0)
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; uint8_t x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
x_1481 = lean_ctor_get(x_1407, 1);
x_1482 = lean_ctor_get(x_1407, 0);
lean_dec(x_1482);
x_1483 = lean_io_error_to_string(x_1410);
x_1484 = 3;
x_1485 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1485, 0, x_1483);
lean_ctor_set_uint8(x_1485, sizeof(void*)*1, x_1484);
x_1486 = lean_array_get_size(x_1481);
x_1487 = lean_array_push(x_1481, x_1485);
x_1488 = lean_io_prim_handle_unlock(x_1305, x_1408);
lean_dec(x_1305);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; lean_object* x_1490; 
x_1489 = lean_ctor_get(x_1488, 1);
lean_inc(x_1489);
lean_dec(x_1488);
x_1490 = lean_io_remove_file(x_24, x_1489);
lean_dec(x_24);
if (lean_obj_tag(x_1490) == 0)
{
uint8_t x_1491; 
x_1491 = !lean_is_exclusive(x_1490);
if (x_1491 == 0)
{
lean_object* x_1492; 
x_1492 = lean_ctor_get(x_1490, 0);
lean_dec(x_1492);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1487);
lean_ctor_set(x_1407, 0, x_1486);
lean_ctor_set(x_1490, 0, x_1407);
return x_1490;
}
else
{
lean_object* x_1493; lean_object* x_1494; 
x_1493 = lean_ctor_get(x_1490, 1);
lean_inc(x_1493);
lean_dec(x_1490);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1487);
lean_ctor_set(x_1407, 0, x_1486);
x_1494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1494, 0, x_1407);
lean_ctor_set(x_1494, 1, x_1493);
return x_1494;
}
}
else
{
uint8_t x_1495; 
x_1495 = !lean_is_exclusive(x_1490);
if (x_1495 == 0)
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1496 = lean_ctor_get(x_1490, 0);
x_1497 = lean_io_error_to_string(x_1496);
x_1498 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1498, 0, x_1497);
lean_ctor_set_uint8(x_1498, sizeof(void*)*1, x_1484);
x_1499 = lean_array_push(x_1487, x_1498);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1499);
lean_ctor_set(x_1407, 0, x_1486);
lean_ctor_set_tag(x_1490, 0);
lean_ctor_set(x_1490, 0, x_1407);
return x_1490;
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1500 = lean_ctor_get(x_1490, 0);
x_1501 = lean_ctor_get(x_1490, 1);
lean_inc(x_1501);
lean_inc(x_1500);
lean_dec(x_1490);
x_1502 = lean_io_error_to_string(x_1500);
x_1503 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1503, 0, x_1502);
lean_ctor_set_uint8(x_1503, sizeof(void*)*1, x_1484);
x_1504 = lean_array_push(x_1487, x_1503);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1504);
lean_ctor_set(x_1407, 0, x_1486);
x_1505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1505, 0, x_1407);
lean_ctor_set(x_1505, 1, x_1501);
return x_1505;
}
}
}
else
{
uint8_t x_1506; 
lean_dec(x_24);
x_1506 = !lean_is_exclusive(x_1488);
if (x_1506 == 0)
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; 
x_1507 = lean_ctor_get(x_1488, 0);
x_1508 = lean_io_error_to_string(x_1507);
x_1509 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1509, 0, x_1508);
lean_ctor_set_uint8(x_1509, sizeof(void*)*1, x_1484);
x_1510 = lean_array_push(x_1487, x_1509);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1510);
lean_ctor_set(x_1407, 0, x_1486);
lean_ctor_set_tag(x_1488, 0);
lean_ctor_set(x_1488, 0, x_1407);
return x_1488;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
x_1511 = lean_ctor_get(x_1488, 0);
x_1512 = lean_ctor_get(x_1488, 1);
lean_inc(x_1512);
lean_inc(x_1511);
lean_dec(x_1488);
x_1513 = lean_io_error_to_string(x_1511);
x_1514 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1514, 0, x_1513);
lean_ctor_set_uint8(x_1514, sizeof(void*)*1, x_1484);
x_1515 = lean_array_push(x_1487, x_1514);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1515);
lean_ctor_set(x_1407, 0, x_1486);
x_1516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1516, 0, x_1407);
lean_ctor_set(x_1516, 1, x_1512);
return x_1516;
}
}
}
else
{
lean_object* x_1517; lean_object* x_1518; uint8_t x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
x_1517 = lean_ctor_get(x_1407, 1);
lean_inc(x_1517);
lean_dec(x_1407);
x_1518 = lean_io_error_to_string(x_1410);
x_1519 = 3;
x_1520 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set_uint8(x_1520, sizeof(void*)*1, x_1519);
x_1521 = lean_array_get_size(x_1517);
x_1522 = lean_array_push(x_1517, x_1520);
x_1523 = lean_io_prim_handle_unlock(x_1305, x_1408);
lean_dec(x_1305);
if (lean_obj_tag(x_1523) == 0)
{
lean_object* x_1524; lean_object* x_1525; 
x_1524 = lean_ctor_get(x_1523, 1);
lean_inc(x_1524);
lean_dec(x_1523);
x_1525 = lean_io_remove_file(x_24, x_1524);
lean_dec(x_24);
if (lean_obj_tag(x_1525) == 0)
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
x_1526 = lean_ctor_get(x_1525, 1);
lean_inc(x_1526);
if (lean_is_exclusive(x_1525)) {
 lean_ctor_release(x_1525, 0);
 lean_ctor_release(x_1525, 1);
 x_1527 = x_1525;
} else {
 lean_dec_ref(x_1525);
 x_1527 = lean_box(0);
}
x_1528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1528, 0, x_1521);
lean_ctor_set(x_1528, 1, x_1522);
if (lean_is_scalar(x_1527)) {
 x_1529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1529 = x_1527;
}
lean_ctor_set(x_1529, 0, x_1528);
lean_ctor_set(x_1529, 1, x_1526);
return x_1529;
}
else
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; 
x_1530 = lean_ctor_get(x_1525, 0);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1525, 1);
lean_inc(x_1531);
if (lean_is_exclusive(x_1525)) {
 lean_ctor_release(x_1525, 0);
 lean_ctor_release(x_1525, 1);
 x_1532 = x_1525;
} else {
 lean_dec_ref(x_1525);
 x_1532 = lean_box(0);
}
x_1533 = lean_io_error_to_string(x_1530);
x_1534 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set_uint8(x_1534, sizeof(void*)*1, x_1519);
x_1535 = lean_array_push(x_1522, x_1534);
x_1536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1536, 0, x_1521);
lean_ctor_set(x_1536, 1, x_1535);
if (lean_is_scalar(x_1532)) {
 x_1537 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1537 = x_1532;
 lean_ctor_set_tag(x_1537, 0);
}
lean_ctor_set(x_1537, 0, x_1536);
lean_ctor_set(x_1537, 1, x_1531);
return x_1537;
}
}
else
{
lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; 
lean_dec(x_24);
x_1538 = lean_ctor_get(x_1523, 0);
lean_inc(x_1538);
x_1539 = lean_ctor_get(x_1523, 1);
lean_inc(x_1539);
if (lean_is_exclusive(x_1523)) {
 lean_ctor_release(x_1523, 0);
 lean_ctor_release(x_1523, 1);
 x_1540 = x_1523;
} else {
 lean_dec_ref(x_1523);
 x_1540 = lean_box(0);
}
x_1541 = lean_io_error_to_string(x_1538);
x_1542 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1542, 0, x_1541);
lean_ctor_set_uint8(x_1542, sizeof(void*)*1, x_1519);
x_1543 = lean_array_push(x_1522, x_1542);
x_1544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1544, 0, x_1521);
lean_ctor_set(x_1544, 1, x_1543);
if (lean_is_scalar(x_1540)) {
 x_1545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1545 = x_1540;
 lean_ctor_set_tag(x_1545, 0);
}
lean_ctor_set(x_1545, 0, x_1544);
lean_ctor_set(x_1545, 1, x_1539);
return x_1545;
}
}
}
}
else
{
uint8_t x_1546; 
lean_dec(x_1409);
lean_dec(x_24);
x_1546 = !lean_is_exclusive(x_1407);
if (x_1546 == 0)
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; 
x_1547 = lean_ctor_get(x_1407, 1);
x_1548 = lean_ctor_get(x_1407, 0);
lean_dec(x_1548);
x_1549 = lean_ctor_get(x_1, 0);
lean_inc(x_1549);
x_1550 = l_Lake_Env_leanGithash(x_1549);
lean_dec(x_1549);
x_1551 = l_System_Platform_target;
lean_inc(x_1311);
x_1552 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1552, 0, x_1551);
lean_ctor_set(x_1552, 1, x_1550);
lean_ctor_set(x_1552, 2, x_30);
lean_ctor_set(x_1552, 3, x_1311);
x_1553 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1552);
x_1554 = lean_unsigned_to_nat(80u);
x_1555 = l_Lean_Json_pretty(x_1553, x_1554);
x_1556 = l_IO_FS_Handle_putStrLn(x_1305, x_1555, x_1408);
if (lean_obj_tag(x_1556) == 0)
{
lean_object* x_1557; lean_object* x_1558; 
x_1557 = lean_ctor_get(x_1556, 1);
lean_inc(x_1557);
lean_dec(x_1556);
x_1558 = lean_io_prim_handle_truncate(x_1305, x_1557);
if (lean_obj_tag(x_1558) == 0)
{
lean_object* x_1559; lean_object* x_1560; 
x_1559 = lean_ctor_get(x_1558, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1558, 1);
lean_inc(x_1560);
lean_dec(x_1558);
lean_ctor_set(x_1407, 0, x_1559);
x_1312 = x_1407;
x_1313 = x_1560;
goto block_1406;
}
else
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; uint8_t x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
x_1561 = lean_ctor_get(x_1558, 0);
lean_inc(x_1561);
x_1562 = lean_ctor_get(x_1558, 1);
lean_inc(x_1562);
lean_dec(x_1558);
x_1563 = lean_io_error_to_string(x_1561);
x_1564 = 3;
x_1565 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1565, 0, x_1563);
lean_ctor_set_uint8(x_1565, sizeof(void*)*1, x_1564);
x_1566 = lean_array_get_size(x_1547);
x_1567 = lean_array_push(x_1547, x_1565);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1567);
lean_ctor_set(x_1407, 0, x_1566);
x_1312 = x_1407;
x_1313 = x_1562;
goto block_1406;
}
}
else
{
uint8_t x_1568; 
lean_dec(x_1311);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1568 = !lean_is_exclusive(x_1556);
if (x_1568 == 0)
{
lean_object* x_1569; lean_object* x_1570; uint8_t x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; 
x_1569 = lean_ctor_get(x_1556, 0);
x_1570 = lean_io_error_to_string(x_1569);
x_1571 = 3;
x_1572 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1572, 0, x_1570);
lean_ctor_set_uint8(x_1572, sizeof(void*)*1, x_1571);
x_1573 = lean_array_get_size(x_1547);
x_1574 = lean_array_push(x_1547, x_1572);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1574);
lean_ctor_set(x_1407, 0, x_1573);
lean_ctor_set_tag(x_1556, 0);
lean_ctor_set(x_1556, 0, x_1407);
return x_1556;
}
else
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; uint8_t x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1575 = lean_ctor_get(x_1556, 0);
x_1576 = lean_ctor_get(x_1556, 1);
lean_inc(x_1576);
lean_inc(x_1575);
lean_dec(x_1556);
x_1577 = lean_io_error_to_string(x_1575);
x_1578 = 3;
x_1579 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1579, 0, x_1577);
lean_ctor_set_uint8(x_1579, sizeof(void*)*1, x_1578);
x_1580 = lean_array_get_size(x_1547);
x_1581 = lean_array_push(x_1547, x_1579);
lean_ctor_set_tag(x_1407, 1);
lean_ctor_set(x_1407, 1, x_1581);
lean_ctor_set(x_1407, 0, x_1580);
x_1582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1582, 0, x_1407);
lean_ctor_set(x_1582, 1, x_1576);
return x_1582;
}
}
}
else
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1583 = lean_ctor_get(x_1407, 1);
lean_inc(x_1583);
lean_dec(x_1407);
x_1584 = lean_ctor_get(x_1, 0);
lean_inc(x_1584);
x_1585 = l_Lake_Env_leanGithash(x_1584);
lean_dec(x_1584);
x_1586 = l_System_Platform_target;
lean_inc(x_1311);
x_1587 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1587, 0, x_1586);
lean_ctor_set(x_1587, 1, x_1585);
lean_ctor_set(x_1587, 2, x_30);
lean_ctor_set(x_1587, 3, x_1311);
x_1588 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1587);
x_1589 = lean_unsigned_to_nat(80u);
x_1590 = l_Lean_Json_pretty(x_1588, x_1589);
x_1591 = l_IO_FS_Handle_putStrLn(x_1305, x_1590, x_1408);
if (lean_obj_tag(x_1591) == 0)
{
lean_object* x_1592; lean_object* x_1593; 
x_1592 = lean_ctor_get(x_1591, 1);
lean_inc(x_1592);
lean_dec(x_1591);
x_1593 = lean_io_prim_handle_truncate(x_1305, x_1592);
if (lean_obj_tag(x_1593) == 0)
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; 
x_1594 = lean_ctor_get(x_1593, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1593, 1);
lean_inc(x_1595);
lean_dec(x_1593);
x_1596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1596, 0, x_1594);
lean_ctor_set(x_1596, 1, x_1583);
x_1312 = x_1596;
x_1313 = x_1595;
goto block_1406;
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; uint8_t x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; 
x_1597 = lean_ctor_get(x_1593, 0);
lean_inc(x_1597);
x_1598 = lean_ctor_get(x_1593, 1);
lean_inc(x_1598);
lean_dec(x_1593);
x_1599 = lean_io_error_to_string(x_1597);
x_1600 = 3;
x_1601 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1601, 0, x_1599);
lean_ctor_set_uint8(x_1601, sizeof(void*)*1, x_1600);
x_1602 = lean_array_get_size(x_1583);
x_1603 = lean_array_push(x_1583, x_1601);
x_1604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1604, 0, x_1602);
lean_ctor_set(x_1604, 1, x_1603);
x_1312 = x_1604;
x_1313 = x_1598;
goto block_1406;
}
}
else
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; uint8_t x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; 
lean_dec(x_1311);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1605 = lean_ctor_get(x_1591, 0);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1591, 1);
lean_inc(x_1606);
if (lean_is_exclusive(x_1591)) {
 lean_ctor_release(x_1591, 0);
 lean_ctor_release(x_1591, 1);
 x_1607 = x_1591;
} else {
 lean_dec_ref(x_1591);
 x_1607 = lean_box(0);
}
x_1608 = lean_io_error_to_string(x_1605);
x_1609 = 3;
x_1610 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1610, 0, x_1608);
lean_ctor_set_uint8(x_1610, sizeof(void*)*1, x_1609);
x_1611 = lean_array_get_size(x_1583);
x_1612 = lean_array_push(x_1583, x_1610);
x_1613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1613, 0, x_1611);
lean_ctor_set(x_1613, 1, x_1612);
if (lean_is_scalar(x_1607)) {
 x_1614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1614 = x_1607;
 lean_ctor_set_tag(x_1614, 0);
}
lean_ctor_set(x_1614, 0, x_1613);
lean_ctor_set(x_1614, 1, x_1606);
return x_1614;
}
}
}
}
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1675; lean_object* x_1676; lean_object* x_1776; 
x_1623 = lean_ctor_get(x_1307, 1);
lean_inc(x_1623);
lean_dec(x_1307);
x_1624 = lean_ctor_get(x_1, 4);
lean_inc(x_1624);
x_1776 = lean_io_remove_file(x_21, x_1308);
if (lean_obj_tag(x_1776) == 0)
{
lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; 
x_1777 = lean_ctor_get(x_1776, 0);
lean_inc(x_1777);
x_1778 = lean_ctor_get(x_1776, 1);
lean_inc(x_1778);
lean_dec(x_1776);
if (lean_is_scalar(x_1306)) {
 x_1779 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1779 = x_1306;
}
lean_ctor_set(x_1779, 0, x_1777);
x_1780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1780, 0, x_1779);
lean_ctor_set(x_1780, 1, x_1623);
x_1675 = x_1780;
x_1676 = x_1778;
goto block_1775;
}
else
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; 
x_1781 = lean_ctor_get(x_1776, 0);
lean_inc(x_1781);
x_1782 = lean_ctor_get(x_1776, 1);
lean_inc(x_1782);
lean_dec(x_1776);
if (lean_is_scalar(x_1306)) {
 x_1783 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1783 = x_1306;
 lean_ctor_set_tag(x_1783, 0);
}
lean_ctor_set(x_1783, 0, x_1781);
x_1784 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1784, 0, x_1783);
lean_ctor_set(x_1784, 1, x_1623);
x_1675 = x_1784;
x_1676 = x_1782;
goto block_1775;
}
block_1674:
{
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; 
x_1627 = lean_ctor_get(x_1625, 1);
lean_inc(x_1627);
lean_dec(x_1625);
x_1628 = lean_ctor_get(x_1, 5);
lean_inc(x_1628);
lean_dec(x_1);
x_1629 = l_Lake_elabConfigFile(x_6, x_1624, x_1628, x_8, x_1627, x_1626);
x_1630 = lean_ctor_get(x_1629, 0);
lean_inc(x_1630);
if (lean_obj_tag(x_1630) == 0)
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
x_1631 = lean_ctor_get(x_1629, 1);
lean_inc(x_1631);
lean_dec(x_1629);
x_1632 = lean_ctor_get(x_1630, 0);
lean_inc(x_1632);
x_1633 = lean_ctor_get(x_1630, 1);
lean_inc(x_1633);
if (lean_is_exclusive(x_1630)) {
 lean_ctor_release(x_1630, 0);
 lean_ctor_release(x_1630, 1);
 x_1634 = x_1630;
} else {
 lean_dec_ref(x_1630);
 x_1634 = lean_box(0);
}
lean_inc(x_1632);
x_1635 = lean_write_module(x_1632, x_21, x_1631);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; lean_object* x_1637; 
x_1636 = lean_ctor_get(x_1635, 1);
lean_inc(x_1636);
lean_dec(x_1635);
x_1637 = lean_io_prim_handle_unlock(x_1305, x_1636);
lean_dec(x_1305);
if (lean_obj_tag(x_1637) == 0)
{
lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; 
x_1638 = lean_ctor_get(x_1637, 1);
lean_inc(x_1638);
if (lean_is_exclusive(x_1637)) {
 lean_ctor_release(x_1637, 0);
 lean_ctor_release(x_1637, 1);
 x_1639 = x_1637;
} else {
 lean_dec_ref(x_1637);
 x_1639 = lean_box(0);
}
if (lean_is_scalar(x_1634)) {
 x_1640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1640 = x_1634;
}
lean_ctor_set(x_1640, 0, x_1632);
lean_ctor_set(x_1640, 1, x_1633);
if (lean_is_scalar(x_1639)) {
 x_1641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1641 = x_1639;
}
lean_ctor_set(x_1641, 0, x_1640);
lean_ctor_set(x_1641, 1, x_1638);
return x_1641;
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; uint8_t x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
lean_dec(x_1632);
x_1642 = lean_ctor_get(x_1637, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1637, 1);
lean_inc(x_1643);
if (lean_is_exclusive(x_1637)) {
 lean_ctor_release(x_1637, 0);
 lean_ctor_release(x_1637, 1);
 x_1644 = x_1637;
} else {
 lean_dec_ref(x_1637);
 x_1644 = lean_box(0);
}
x_1645 = lean_io_error_to_string(x_1642);
x_1646 = 3;
x_1647 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1647, 0, x_1645);
lean_ctor_set_uint8(x_1647, sizeof(void*)*1, x_1646);
x_1648 = lean_array_get_size(x_1633);
x_1649 = lean_array_push(x_1633, x_1647);
if (lean_is_scalar(x_1634)) {
 x_1650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1650 = x_1634;
 lean_ctor_set_tag(x_1650, 1);
}
lean_ctor_set(x_1650, 0, x_1648);
lean_ctor_set(x_1650, 1, x_1649);
if (lean_is_scalar(x_1644)) {
 x_1651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1651 = x_1644;
 lean_ctor_set_tag(x_1651, 0);
}
lean_ctor_set(x_1651, 0, x_1650);
lean_ctor_set(x_1651, 1, x_1643);
return x_1651;
}
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; uint8_t x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; 
lean_dec(x_1632);
lean_dec(x_1305);
x_1652 = lean_ctor_get(x_1635, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1635, 1);
lean_inc(x_1653);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1654 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1654 = lean_box(0);
}
x_1655 = lean_io_error_to_string(x_1652);
x_1656 = 3;
x_1657 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1657, 0, x_1655);
lean_ctor_set_uint8(x_1657, sizeof(void*)*1, x_1656);
x_1658 = lean_array_get_size(x_1633);
x_1659 = lean_array_push(x_1633, x_1657);
if (lean_is_scalar(x_1634)) {
 x_1660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1660 = x_1634;
 lean_ctor_set_tag(x_1660, 1);
}
lean_ctor_set(x_1660, 0, x_1658);
lean_ctor_set(x_1660, 1, x_1659);
if (lean_is_scalar(x_1654)) {
 x_1661 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1661 = x_1654;
 lean_ctor_set_tag(x_1661, 0);
}
lean_ctor_set(x_1661, 0, x_1660);
lean_ctor_set(x_1661, 1, x_1653);
return x_1661;
}
}
else
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
lean_dec(x_1305);
lean_dec(x_21);
x_1662 = lean_ctor_get(x_1629, 1);
lean_inc(x_1662);
if (lean_is_exclusive(x_1629)) {
 lean_ctor_release(x_1629, 0);
 lean_ctor_release(x_1629, 1);
 x_1663 = x_1629;
} else {
 lean_dec_ref(x_1629);
 x_1663 = lean_box(0);
}
x_1664 = lean_ctor_get(x_1630, 0);
lean_inc(x_1664);
x_1665 = lean_ctor_get(x_1630, 1);
lean_inc(x_1665);
if (lean_is_exclusive(x_1630)) {
 lean_ctor_release(x_1630, 0);
 lean_ctor_release(x_1630, 1);
 x_1666 = x_1630;
} else {
 lean_dec_ref(x_1630);
 x_1666 = lean_box(0);
}
if (lean_is_scalar(x_1666)) {
 x_1667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1667 = x_1666;
}
lean_ctor_set(x_1667, 0, x_1664);
lean_ctor_set(x_1667, 1, x_1665);
if (lean_is_scalar(x_1663)) {
 x_1668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1668 = x_1663;
}
lean_ctor_set(x_1668, 0, x_1667);
lean_ctor_set(x_1668, 1, x_1662);
return x_1668;
}
}
else
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
lean_dec(x_1624);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1669 = lean_ctor_get(x_1625, 0);
lean_inc(x_1669);
x_1670 = lean_ctor_get(x_1625, 1);
lean_inc(x_1670);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1671 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1671 = lean_box(0);
}
if (lean_is_scalar(x_1671)) {
 x_1672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1672 = x_1671;
}
lean_ctor_set(x_1672, 0, x_1669);
lean_ctor_set(x_1672, 1, x_1670);
x_1673 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1673, 0, x_1672);
lean_ctor_set(x_1673, 1, x_1626);
return x_1673;
}
}
block_1775:
{
lean_object* x_1677; 
x_1677 = lean_ctor_get(x_1675, 0);
lean_inc(x_1677);
if (lean_obj_tag(x_1677) == 0)
{
lean_object* x_1678; 
x_1678 = lean_ctor_get(x_1677, 0);
lean_inc(x_1678);
lean_dec(x_1677);
if (lean_obj_tag(x_1678) == 11)
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; 
lean_dec(x_1678);
lean_dec(x_24);
x_1679 = lean_ctor_get(x_1675, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1675)) {
 lean_ctor_release(x_1675, 0);
 lean_ctor_release(x_1675, 1);
 x_1680 = x_1675;
} else {
 lean_dec_ref(x_1675);
 x_1680 = lean_box(0);
}
x_1681 = lean_ctor_get(x_1, 0);
lean_inc(x_1681);
x_1682 = l_Lake_Env_leanGithash(x_1681);
lean_dec(x_1681);
x_1683 = l_System_Platform_target;
lean_inc(x_1624);
x_1684 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1684, 0, x_1683);
lean_ctor_set(x_1684, 1, x_1682);
lean_ctor_set(x_1684, 2, x_30);
lean_ctor_set(x_1684, 3, x_1624);
x_1685 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1684);
x_1686 = lean_unsigned_to_nat(80u);
x_1687 = l_Lean_Json_pretty(x_1685, x_1686);
x_1688 = l_IO_FS_Handle_putStrLn(x_1305, x_1687, x_1676);
if (lean_obj_tag(x_1688) == 0)
{
lean_object* x_1689; lean_object* x_1690; 
x_1689 = lean_ctor_get(x_1688, 1);
lean_inc(x_1689);
lean_dec(x_1688);
x_1690 = lean_io_prim_handle_truncate(x_1305, x_1689);
if (lean_obj_tag(x_1690) == 0)
{
lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; 
x_1691 = lean_ctor_get(x_1690, 0);
lean_inc(x_1691);
x_1692 = lean_ctor_get(x_1690, 1);
lean_inc(x_1692);
lean_dec(x_1690);
if (lean_is_scalar(x_1680)) {
 x_1693 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1693 = x_1680;
}
lean_ctor_set(x_1693, 0, x_1691);
lean_ctor_set(x_1693, 1, x_1679);
x_1625 = x_1693;
x_1626 = x_1692;
goto block_1674;
}
else
{
lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; uint8_t x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; 
x_1694 = lean_ctor_get(x_1690, 0);
lean_inc(x_1694);
x_1695 = lean_ctor_get(x_1690, 1);
lean_inc(x_1695);
lean_dec(x_1690);
x_1696 = lean_io_error_to_string(x_1694);
x_1697 = 3;
x_1698 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1698, 0, x_1696);
lean_ctor_set_uint8(x_1698, sizeof(void*)*1, x_1697);
x_1699 = lean_array_get_size(x_1679);
x_1700 = lean_array_push(x_1679, x_1698);
if (lean_is_scalar(x_1680)) {
 x_1701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1701 = x_1680;
 lean_ctor_set_tag(x_1701, 1);
}
lean_ctor_set(x_1701, 0, x_1699);
lean_ctor_set(x_1701, 1, x_1700);
x_1625 = x_1701;
x_1626 = x_1695;
goto block_1674;
}
}
else
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; uint8_t x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; 
lean_dec(x_1624);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1702 = lean_ctor_get(x_1688, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1688, 1);
lean_inc(x_1703);
if (lean_is_exclusive(x_1688)) {
 lean_ctor_release(x_1688, 0);
 lean_ctor_release(x_1688, 1);
 x_1704 = x_1688;
} else {
 lean_dec_ref(x_1688);
 x_1704 = lean_box(0);
}
x_1705 = lean_io_error_to_string(x_1702);
x_1706 = 3;
x_1707 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1707, 0, x_1705);
lean_ctor_set_uint8(x_1707, sizeof(void*)*1, x_1706);
x_1708 = lean_array_get_size(x_1679);
x_1709 = lean_array_push(x_1679, x_1707);
if (lean_is_scalar(x_1680)) {
 x_1710 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1710 = x_1680;
 lean_ctor_set_tag(x_1710, 1);
}
lean_ctor_set(x_1710, 0, x_1708);
lean_ctor_set(x_1710, 1, x_1709);
if (lean_is_scalar(x_1704)) {
 x_1711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1711 = x_1704;
 lean_ctor_set_tag(x_1711, 0);
}
lean_ctor_set(x_1711, 0, x_1710);
lean_ctor_set(x_1711, 1, x_1703);
return x_1711;
}
}
else
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; uint8_t x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; 
lean_dec(x_1624);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1712 = lean_ctor_get(x_1675, 1);
lean_inc(x_1712);
if (lean_is_exclusive(x_1675)) {
 lean_ctor_release(x_1675, 0);
 lean_ctor_release(x_1675, 1);
 x_1713 = x_1675;
} else {
 lean_dec_ref(x_1675);
 x_1713 = lean_box(0);
}
x_1714 = lean_io_error_to_string(x_1678);
x_1715 = 3;
x_1716 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1716, 0, x_1714);
lean_ctor_set_uint8(x_1716, sizeof(void*)*1, x_1715);
x_1717 = lean_array_get_size(x_1712);
x_1718 = lean_array_push(x_1712, x_1716);
x_1719 = lean_io_prim_handle_unlock(x_1305, x_1676);
lean_dec(x_1305);
if (lean_obj_tag(x_1719) == 0)
{
lean_object* x_1720; lean_object* x_1721; 
x_1720 = lean_ctor_get(x_1719, 1);
lean_inc(x_1720);
lean_dec(x_1719);
x_1721 = lean_io_remove_file(x_24, x_1720);
lean_dec(x_24);
if (lean_obj_tag(x_1721) == 0)
{
lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; 
x_1722 = lean_ctor_get(x_1721, 1);
lean_inc(x_1722);
if (lean_is_exclusive(x_1721)) {
 lean_ctor_release(x_1721, 0);
 lean_ctor_release(x_1721, 1);
 x_1723 = x_1721;
} else {
 lean_dec_ref(x_1721);
 x_1723 = lean_box(0);
}
if (lean_is_scalar(x_1713)) {
 x_1724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1724 = x_1713;
 lean_ctor_set_tag(x_1724, 1);
}
lean_ctor_set(x_1724, 0, x_1717);
lean_ctor_set(x_1724, 1, x_1718);
if (lean_is_scalar(x_1723)) {
 x_1725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1725 = x_1723;
}
lean_ctor_set(x_1725, 0, x_1724);
lean_ctor_set(x_1725, 1, x_1722);
return x_1725;
}
else
{
lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; 
x_1726 = lean_ctor_get(x_1721, 0);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1721, 1);
lean_inc(x_1727);
if (lean_is_exclusive(x_1721)) {
 lean_ctor_release(x_1721, 0);
 lean_ctor_release(x_1721, 1);
 x_1728 = x_1721;
} else {
 lean_dec_ref(x_1721);
 x_1728 = lean_box(0);
}
x_1729 = lean_io_error_to_string(x_1726);
x_1730 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1730, 0, x_1729);
lean_ctor_set_uint8(x_1730, sizeof(void*)*1, x_1715);
x_1731 = lean_array_push(x_1718, x_1730);
if (lean_is_scalar(x_1713)) {
 x_1732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1732 = x_1713;
 lean_ctor_set_tag(x_1732, 1);
}
lean_ctor_set(x_1732, 0, x_1717);
lean_ctor_set(x_1732, 1, x_1731);
if (lean_is_scalar(x_1728)) {
 x_1733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1733 = x_1728;
 lean_ctor_set_tag(x_1733, 0);
}
lean_ctor_set(x_1733, 0, x_1732);
lean_ctor_set(x_1733, 1, x_1727);
return x_1733;
}
}
else
{
lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; 
lean_dec(x_24);
x_1734 = lean_ctor_get(x_1719, 0);
lean_inc(x_1734);
x_1735 = lean_ctor_get(x_1719, 1);
lean_inc(x_1735);
if (lean_is_exclusive(x_1719)) {
 lean_ctor_release(x_1719, 0);
 lean_ctor_release(x_1719, 1);
 x_1736 = x_1719;
} else {
 lean_dec_ref(x_1719);
 x_1736 = lean_box(0);
}
x_1737 = lean_io_error_to_string(x_1734);
x_1738 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1738, 0, x_1737);
lean_ctor_set_uint8(x_1738, sizeof(void*)*1, x_1715);
x_1739 = lean_array_push(x_1718, x_1738);
if (lean_is_scalar(x_1713)) {
 x_1740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1740 = x_1713;
 lean_ctor_set_tag(x_1740, 1);
}
lean_ctor_set(x_1740, 0, x_1717);
lean_ctor_set(x_1740, 1, x_1739);
if (lean_is_scalar(x_1736)) {
 x_1741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1741 = x_1736;
 lean_ctor_set_tag(x_1741, 0);
}
lean_ctor_set(x_1741, 0, x_1740);
lean_ctor_set(x_1741, 1, x_1735);
return x_1741;
}
}
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; 
lean_dec(x_1677);
lean_dec(x_24);
x_1742 = lean_ctor_get(x_1675, 1);
lean_inc(x_1742);
if (lean_is_exclusive(x_1675)) {
 lean_ctor_release(x_1675, 0);
 lean_ctor_release(x_1675, 1);
 x_1743 = x_1675;
} else {
 lean_dec_ref(x_1675);
 x_1743 = lean_box(0);
}
x_1744 = lean_ctor_get(x_1, 0);
lean_inc(x_1744);
x_1745 = l_Lake_Env_leanGithash(x_1744);
lean_dec(x_1744);
x_1746 = l_System_Platform_target;
lean_inc(x_1624);
x_1747 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1747, 0, x_1746);
lean_ctor_set(x_1747, 1, x_1745);
lean_ctor_set(x_1747, 2, x_30);
lean_ctor_set(x_1747, 3, x_1624);
x_1748 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1747);
x_1749 = lean_unsigned_to_nat(80u);
x_1750 = l_Lean_Json_pretty(x_1748, x_1749);
x_1751 = l_IO_FS_Handle_putStrLn(x_1305, x_1750, x_1676);
if (lean_obj_tag(x_1751) == 0)
{
lean_object* x_1752; lean_object* x_1753; 
x_1752 = lean_ctor_get(x_1751, 1);
lean_inc(x_1752);
lean_dec(x_1751);
x_1753 = lean_io_prim_handle_truncate(x_1305, x_1752);
if (lean_obj_tag(x_1753) == 0)
{
lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; 
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1753, 1);
lean_inc(x_1755);
lean_dec(x_1753);
if (lean_is_scalar(x_1743)) {
 x_1756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1756 = x_1743;
}
lean_ctor_set(x_1756, 0, x_1754);
lean_ctor_set(x_1756, 1, x_1742);
x_1625 = x_1756;
x_1626 = x_1755;
goto block_1674;
}
else
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; uint8_t x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; 
x_1757 = lean_ctor_get(x_1753, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1753, 1);
lean_inc(x_1758);
lean_dec(x_1753);
x_1759 = lean_io_error_to_string(x_1757);
x_1760 = 3;
x_1761 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1761, 0, x_1759);
lean_ctor_set_uint8(x_1761, sizeof(void*)*1, x_1760);
x_1762 = lean_array_get_size(x_1742);
x_1763 = lean_array_push(x_1742, x_1761);
if (lean_is_scalar(x_1743)) {
 x_1764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1764 = x_1743;
 lean_ctor_set_tag(x_1764, 1);
}
lean_ctor_set(x_1764, 0, x_1762);
lean_ctor_set(x_1764, 1, x_1763);
x_1625 = x_1764;
x_1626 = x_1758;
goto block_1674;
}
}
else
{
lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; uint8_t x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
lean_dec(x_1624);
lean_dec(x_1305);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1765 = lean_ctor_get(x_1751, 0);
lean_inc(x_1765);
x_1766 = lean_ctor_get(x_1751, 1);
lean_inc(x_1766);
if (lean_is_exclusive(x_1751)) {
 lean_ctor_release(x_1751, 0);
 lean_ctor_release(x_1751, 1);
 x_1767 = x_1751;
} else {
 lean_dec_ref(x_1751);
 x_1767 = lean_box(0);
}
x_1768 = lean_io_error_to_string(x_1765);
x_1769 = 3;
x_1770 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1770, 0, x_1768);
lean_ctor_set_uint8(x_1770, sizeof(void*)*1, x_1769);
x_1771 = lean_array_get_size(x_1742);
x_1772 = lean_array_push(x_1742, x_1770);
if (lean_is_scalar(x_1743)) {
 x_1773 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1773 = x_1743;
 lean_ctor_set_tag(x_1773, 1);
}
lean_ctor_set(x_1773, 0, x_1771);
lean_ctor_set(x_1773, 1, x_1772);
if (lean_is_scalar(x_1767)) {
 x_1774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1774 = x_1767;
 lean_ctor_set_tag(x_1774, 0);
}
lean_ctor_set(x_1774, 0, x_1773);
lean_ctor_set(x_1774, 1, x_1766);
return x_1774;
}
}
}
}
}
else
{
uint8_t x_1785; 
lean_dec(x_1306);
lean_dec(x_1305);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1785 = !lean_is_exclusive(x_1307);
if (x_1785 == 0)
{
lean_object* x_1786; 
x_1786 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1786, 0, x_1307);
lean_ctor_set(x_1786, 1, x_1308);
return x_1786;
}
else
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; 
x_1787 = lean_ctor_get(x_1307, 0);
x_1788 = lean_ctor_get(x_1307, 1);
lean_inc(x_1788);
lean_inc(x_1787);
lean_dec(x_1307);
x_1789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1789, 0, x_1787);
lean_ctor_set(x_1789, 1, x_1788);
x_1790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1790, 0, x_1789);
lean_ctor_set(x_1790, 1, x_1308);
return x_1790;
}
}
}
}
else
{
lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; uint8_t x_1977; lean_object* x_1978; 
x_1803 = lean_ctor_get(x_1253, 1);
lean_inc(x_1803);
lean_dec(x_1253);
x_1804 = lean_ctor_get(x_1255, 0);
lean_inc(x_1804);
if (lean_is_exclusive(x_1255)) {
 lean_ctor_release(x_1255, 0);
 x_1805 = x_1255;
} else {
 lean_dec_ref(x_1255);
 x_1805 = lean_box(0);
}
x_1977 = 1;
x_1978 = lean_io_prim_handle_lock(x_1804, x_1977, x_1254);
if (lean_obj_tag(x_1978) == 0)
{
lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; 
x_1979 = lean_ctor_get(x_1978, 0);
lean_inc(x_1979);
x_1980 = lean_ctor_get(x_1978, 1);
lean_inc(x_1980);
lean_dec(x_1978);
x_1981 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1981, 0, x_1979);
lean_ctor_set(x_1981, 1, x_1803);
x_1806 = x_1981;
x_1807 = x_1980;
goto block_1976;
}
else
{
lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; uint8_t x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; 
x_1982 = lean_ctor_get(x_1978, 0);
lean_inc(x_1982);
x_1983 = lean_ctor_get(x_1978, 1);
lean_inc(x_1983);
lean_dec(x_1978);
x_1984 = lean_io_error_to_string(x_1982);
x_1985 = 3;
x_1986 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1986, 0, x_1984);
lean_ctor_set_uint8(x_1986, sizeof(void*)*1, x_1985);
x_1987 = lean_array_get_size(x_1803);
x_1988 = lean_array_push(x_1803, x_1986);
x_1989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1989, 0, x_1987);
lean_ctor_set(x_1989, 1, x_1988);
x_1806 = x_1989;
x_1807 = x_1983;
goto block_1976;
}
block_1976:
{
if (lean_obj_tag(x_1806) == 0)
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1861; lean_object* x_1862; lean_object* x_1962; 
x_1808 = lean_ctor_get(x_1806, 1);
lean_inc(x_1808);
if (lean_is_exclusive(x_1806)) {
 lean_ctor_release(x_1806, 0);
 lean_ctor_release(x_1806, 1);
 x_1809 = x_1806;
} else {
 lean_dec_ref(x_1806);
 x_1809 = lean_box(0);
}
x_1810 = lean_ctor_get(x_1, 4);
lean_inc(x_1810);
x_1962 = lean_io_remove_file(x_21, x_1807);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; 
x_1963 = lean_ctor_get(x_1962, 0);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1962, 1);
lean_inc(x_1964);
lean_dec(x_1962);
if (lean_is_scalar(x_1805)) {
 x_1965 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1965 = x_1805;
}
lean_ctor_set(x_1965, 0, x_1963);
if (lean_is_scalar(x_1809)) {
 x_1966 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1966 = x_1809;
}
lean_ctor_set(x_1966, 0, x_1965);
lean_ctor_set(x_1966, 1, x_1808);
x_1861 = x_1966;
x_1862 = x_1964;
goto block_1961;
}
else
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; 
x_1967 = lean_ctor_get(x_1962, 0);
lean_inc(x_1967);
x_1968 = lean_ctor_get(x_1962, 1);
lean_inc(x_1968);
lean_dec(x_1962);
if (lean_is_scalar(x_1805)) {
 x_1969 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1969 = x_1805;
 lean_ctor_set_tag(x_1969, 0);
}
lean_ctor_set(x_1969, 0, x_1967);
if (lean_is_scalar(x_1809)) {
 x_1970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1970 = x_1809;
}
lean_ctor_set(x_1970, 0, x_1969);
lean_ctor_set(x_1970, 1, x_1808);
x_1861 = x_1970;
x_1862 = x_1968;
goto block_1961;
}
block_1860:
{
if (lean_obj_tag(x_1811) == 0)
{
lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; 
x_1813 = lean_ctor_get(x_1811, 1);
lean_inc(x_1813);
lean_dec(x_1811);
x_1814 = lean_ctor_get(x_1, 5);
lean_inc(x_1814);
lean_dec(x_1);
x_1815 = l_Lake_elabConfigFile(x_6, x_1810, x_1814, x_8, x_1813, x_1812);
x_1816 = lean_ctor_get(x_1815, 0);
lean_inc(x_1816);
if (lean_obj_tag(x_1816) == 0)
{
lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; 
x_1817 = lean_ctor_get(x_1815, 1);
lean_inc(x_1817);
lean_dec(x_1815);
x_1818 = lean_ctor_get(x_1816, 0);
lean_inc(x_1818);
x_1819 = lean_ctor_get(x_1816, 1);
lean_inc(x_1819);
if (lean_is_exclusive(x_1816)) {
 lean_ctor_release(x_1816, 0);
 lean_ctor_release(x_1816, 1);
 x_1820 = x_1816;
} else {
 lean_dec_ref(x_1816);
 x_1820 = lean_box(0);
}
lean_inc(x_1818);
x_1821 = lean_write_module(x_1818, x_21, x_1817);
if (lean_obj_tag(x_1821) == 0)
{
lean_object* x_1822; lean_object* x_1823; 
x_1822 = lean_ctor_get(x_1821, 1);
lean_inc(x_1822);
lean_dec(x_1821);
x_1823 = lean_io_prim_handle_unlock(x_1804, x_1822);
lean_dec(x_1804);
if (lean_obj_tag(x_1823) == 0)
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; 
x_1824 = lean_ctor_get(x_1823, 1);
lean_inc(x_1824);
if (lean_is_exclusive(x_1823)) {
 lean_ctor_release(x_1823, 0);
 lean_ctor_release(x_1823, 1);
 x_1825 = x_1823;
} else {
 lean_dec_ref(x_1823);
 x_1825 = lean_box(0);
}
if (lean_is_scalar(x_1820)) {
 x_1826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1826 = x_1820;
}
lean_ctor_set(x_1826, 0, x_1818);
lean_ctor_set(x_1826, 1, x_1819);
if (lean_is_scalar(x_1825)) {
 x_1827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1827 = x_1825;
}
lean_ctor_set(x_1827, 0, x_1826);
lean_ctor_set(x_1827, 1, x_1824);
return x_1827;
}
else
{
lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; uint8_t x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; 
lean_dec(x_1818);
x_1828 = lean_ctor_get(x_1823, 0);
lean_inc(x_1828);
x_1829 = lean_ctor_get(x_1823, 1);
lean_inc(x_1829);
if (lean_is_exclusive(x_1823)) {
 lean_ctor_release(x_1823, 0);
 lean_ctor_release(x_1823, 1);
 x_1830 = x_1823;
} else {
 lean_dec_ref(x_1823);
 x_1830 = lean_box(0);
}
x_1831 = lean_io_error_to_string(x_1828);
x_1832 = 3;
x_1833 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1833, 0, x_1831);
lean_ctor_set_uint8(x_1833, sizeof(void*)*1, x_1832);
x_1834 = lean_array_get_size(x_1819);
x_1835 = lean_array_push(x_1819, x_1833);
if (lean_is_scalar(x_1820)) {
 x_1836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1836 = x_1820;
 lean_ctor_set_tag(x_1836, 1);
}
lean_ctor_set(x_1836, 0, x_1834);
lean_ctor_set(x_1836, 1, x_1835);
if (lean_is_scalar(x_1830)) {
 x_1837 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1837 = x_1830;
 lean_ctor_set_tag(x_1837, 0);
}
lean_ctor_set(x_1837, 0, x_1836);
lean_ctor_set(x_1837, 1, x_1829);
return x_1837;
}
}
else
{
lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; uint8_t x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; 
lean_dec(x_1818);
lean_dec(x_1804);
x_1838 = lean_ctor_get(x_1821, 0);
lean_inc(x_1838);
x_1839 = lean_ctor_get(x_1821, 1);
lean_inc(x_1839);
if (lean_is_exclusive(x_1821)) {
 lean_ctor_release(x_1821, 0);
 lean_ctor_release(x_1821, 1);
 x_1840 = x_1821;
} else {
 lean_dec_ref(x_1821);
 x_1840 = lean_box(0);
}
x_1841 = lean_io_error_to_string(x_1838);
x_1842 = 3;
x_1843 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1843, 0, x_1841);
lean_ctor_set_uint8(x_1843, sizeof(void*)*1, x_1842);
x_1844 = lean_array_get_size(x_1819);
x_1845 = lean_array_push(x_1819, x_1843);
if (lean_is_scalar(x_1820)) {
 x_1846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1846 = x_1820;
 lean_ctor_set_tag(x_1846, 1);
}
lean_ctor_set(x_1846, 0, x_1844);
lean_ctor_set(x_1846, 1, x_1845);
if (lean_is_scalar(x_1840)) {
 x_1847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1847 = x_1840;
 lean_ctor_set_tag(x_1847, 0);
}
lean_ctor_set(x_1847, 0, x_1846);
lean_ctor_set(x_1847, 1, x_1839);
return x_1847;
}
}
else
{
lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; 
lean_dec(x_1804);
lean_dec(x_21);
x_1848 = lean_ctor_get(x_1815, 1);
lean_inc(x_1848);
if (lean_is_exclusive(x_1815)) {
 lean_ctor_release(x_1815, 0);
 lean_ctor_release(x_1815, 1);
 x_1849 = x_1815;
} else {
 lean_dec_ref(x_1815);
 x_1849 = lean_box(0);
}
x_1850 = lean_ctor_get(x_1816, 0);
lean_inc(x_1850);
x_1851 = lean_ctor_get(x_1816, 1);
lean_inc(x_1851);
if (lean_is_exclusive(x_1816)) {
 lean_ctor_release(x_1816, 0);
 lean_ctor_release(x_1816, 1);
 x_1852 = x_1816;
} else {
 lean_dec_ref(x_1816);
 x_1852 = lean_box(0);
}
if (lean_is_scalar(x_1852)) {
 x_1853 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1853 = x_1852;
}
lean_ctor_set(x_1853, 0, x_1850);
lean_ctor_set(x_1853, 1, x_1851);
if (lean_is_scalar(x_1849)) {
 x_1854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1854 = x_1849;
}
lean_ctor_set(x_1854, 0, x_1853);
lean_ctor_set(x_1854, 1, x_1848);
return x_1854;
}
}
else
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; 
lean_dec(x_1810);
lean_dec(x_1804);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1855 = lean_ctor_get(x_1811, 0);
lean_inc(x_1855);
x_1856 = lean_ctor_get(x_1811, 1);
lean_inc(x_1856);
if (lean_is_exclusive(x_1811)) {
 lean_ctor_release(x_1811, 0);
 lean_ctor_release(x_1811, 1);
 x_1857 = x_1811;
} else {
 lean_dec_ref(x_1811);
 x_1857 = lean_box(0);
}
if (lean_is_scalar(x_1857)) {
 x_1858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1858 = x_1857;
}
lean_ctor_set(x_1858, 0, x_1855);
lean_ctor_set(x_1858, 1, x_1856);
x_1859 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1859, 0, x_1858);
lean_ctor_set(x_1859, 1, x_1812);
return x_1859;
}
}
block_1961:
{
lean_object* x_1863; 
x_1863 = lean_ctor_get(x_1861, 0);
lean_inc(x_1863);
if (lean_obj_tag(x_1863) == 0)
{
lean_object* x_1864; 
x_1864 = lean_ctor_get(x_1863, 0);
lean_inc(x_1864);
lean_dec(x_1863);
if (lean_obj_tag(x_1864) == 11)
{
lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
lean_dec(x_1864);
lean_dec(x_24);
x_1865 = lean_ctor_get(x_1861, 1);
lean_inc(x_1865);
if (lean_is_exclusive(x_1861)) {
 lean_ctor_release(x_1861, 0);
 lean_ctor_release(x_1861, 1);
 x_1866 = x_1861;
} else {
 lean_dec_ref(x_1861);
 x_1866 = lean_box(0);
}
x_1867 = lean_ctor_get(x_1, 0);
lean_inc(x_1867);
x_1868 = l_Lake_Env_leanGithash(x_1867);
lean_dec(x_1867);
x_1869 = l_System_Platform_target;
lean_inc(x_1810);
x_1870 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1870, 0, x_1869);
lean_ctor_set(x_1870, 1, x_1868);
lean_ctor_set(x_1870, 2, x_30);
lean_ctor_set(x_1870, 3, x_1810);
x_1871 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1870);
x_1872 = lean_unsigned_to_nat(80u);
x_1873 = l_Lean_Json_pretty(x_1871, x_1872);
x_1874 = l_IO_FS_Handle_putStrLn(x_1804, x_1873, x_1862);
if (lean_obj_tag(x_1874) == 0)
{
lean_object* x_1875; lean_object* x_1876; 
x_1875 = lean_ctor_get(x_1874, 1);
lean_inc(x_1875);
lean_dec(x_1874);
x_1876 = lean_io_prim_handle_truncate(x_1804, x_1875);
if (lean_obj_tag(x_1876) == 0)
{
lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; 
x_1877 = lean_ctor_get(x_1876, 0);
lean_inc(x_1877);
x_1878 = lean_ctor_get(x_1876, 1);
lean_inc(x_1878);
lean_dec(x_1876);
if (lean_is_scalar(x_1866)) {
 x_1879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1879 = x_1866;
}
lean_ctor_set(x_1879, 0, x_1877);
lean_ctor_set(x_1879, 1, x_1865);
x_1811 = x_1879;
x_1812 = x_1878;
goto block_1860;
}
else
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; uint8_t x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; 
x_1880 = lean_ctor_get(x_1876, 0);
lean_inc(x_1880);
x_1881 = lean_ctor_get(x_1876, 1);
lean_inc(x_1881);
lean_dec(x_1876);
x_1882 = lean_io_error_to_string(x_1880);
x_1883 = 3;
x_1884 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1884, 0, x_1882);
lean_ctor_set_uint8(x_1884, sizeof(void*)*1, x_1883);
x_1885 = lean_array_get_size(x_1865);
x_1886 = lean_array_push(x_1865, x_1884);
if (lean_is_scalar(x_1866)) {
 x_1887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1887 = x_1866;
 lean_ctor_set_tag(x_1887, 1);
}
lean_ctor_set(x_1887, 0, x_1885);
lean_ctor_set(x_1887, 1, x_1886);
x_1811 = x_1887;
x_1812 = x_1881;
goto block_1860;
}
}
else
{
lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; uint8_t x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; 
lean_dec(x_1810);
lean_dec(x_1804);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1888 = lean_ctor_get(x_1874, 0);
lean_inc(x_1888);
x_1889 = lean_ctor_get(x_1874, 1);
lean_inc(x_1889);
if (lean_is_exclusive(x_1874)) {
 lean_ctor_release(x_1874, 0);
 lean_ctor_release(x_1874, 1);
 x_1890 = x_1874;
} else {
 lean_dec_ref(x_1874);
 x_1890 = lean_box(0);
}
x_1891 = lean_io_error_to_string(x_1888);
x_1892 = 3;
x_1893 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1893, 0, x_1891);
lean_ctor_set_uint8(x_1893, sizeof(void*)*1, x_1892);
x_1894 = lean_array_get_size(x_1865);
x_1895 = lean_array_push(x_1865, x_1893);
if (lean_is_scalar(x_1866)) {
 x_1896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1896 = x_1866;
 lean_ctor_set_tag(x_1896, 1);
}
lean_ctor_set(x_1896, 0, x_1894);
lean_ctor_set(x_1896, 1, x_1895);
if (lean_is_scalar(x_1890)) {
 x_1897 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1897 = x_1890;
 lean_ctor_set_tag(x_1897, 0);
}
lean_ctor_set(x_1897, 0, x_1896);
lean_ctor_set(x_1897, 1, x_1889);
return x_1897;
}
}
else
{
lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; uint8_t x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; 
lean_dec(x_1810);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1898 = lean_ctor_get(x_1861, 1);
lean_inc(x_1898);
if (lean_is_exclusive(x_1861)) {
 lean_ctor_release(x_1861, 0);
 lean_ctor_release(x_1861, 1);
 x_1899 = x_1861;
} else {
 lean_dec_ref(x_1861);
 x_1899 = lean_box(0);
}
x_1900 = lean_io_error_to_string(x_1864);
x_1901 = 3;
x_1902 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1902, 0, x_1900);
lean_ctor_set_uint8(x_1902, sizeof(void*)*1, x_1901);
x_1903 = lean_array_get_size(x_1898);
x_1904 = lean_array_push(x_1898, x_1902);
x_1905 = lean_io_prim_handle_unlock(x_1804, x_1862);
lean_dec(x_1804);
if (lean_obj_tag(x_1905) == 0)
{
lean_object* x_1906; lean_object* x_1907; 
x_1906 = lean_ctor_get(x_1905, 1);
lean_inc(x_1906);
lean_dec(x_1905);
x_1907 = lean_io_remove_file(x_24, x_1906);
lean_dec(x_24);
if (lean_obj_tag(x_1907) == 0)
{
lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; 
x_1908 = lean_ctor_get(x_1907, 1);
lean_inc(x_1908);
if (lean_is_exclusive(x_1907)) {
 lean_ctor_release(x_1907, 0);
 lean_ctor_release(x_1907, 1);
 x_1909 = x_1907;
} else {
 lean_dec_ref(x_1907);
 x_1909 = lean_box(0);
}
if (lean_is_scalar(x_1899)) {
 x_1910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1910 = x_1899;
 lean_ctor_set_tag(x_1910, 1);
}
lean_ctor_set(x_1910, 0, x_1903);
lean_ctor_set(x_1910, 1, x_1904);
if (lean_is_scalar(x_1909)) {
 x_1911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1911 = x_1909;
}
lean_ctor_set(x_1911, 0, x_1910);
lean_ctor_set(x_1911, 1, x_1908);
return x_1911;
}
else
{
lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; 
x_1912 = lean_ctor_get(x_1907, 0);
lean_inc(x_1912);
x_1913 = lean_ctor_get(x_1907, 1);
lean_inc(x_1913);
if (lean_is_exclusive(x_1907)) {
 lean_ctor_release(x_1907, 0);
 lean_ctor_release(x_1907, 1);
 x_1914 = x_1907;
} else {
 lean_dec_ref(x_1907);
 x_1914 = lean_box(0);
}
x_1915 = lean_io_error_to_string(x_1912);
x_1916 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1916, 0, x_1915);
lean_ctor_set_uint8(x_1916, sizeof(void*)*1, x_1901);
x_1917 = lean_array_push(x_1904, x_1916);
if (lean_is_scalar(x_1899)) {
 x_1918 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1918 = x_1899;
 lean_ctor_set_tag(x_1918, 1);
}
lean_ctor_set(x_1918, 0, x_1903);
lean_ctor_set(x_1918, 1, x_1917);
if (lean_is_scalar(x_1914)) {
 x_1919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1919 = x_1914;
 lean_ctor_set_tag(x_1919, 0);
}
lean_ctor_set(x_1919, 0, x_1918);
lean_ctor_set(x_1919, 1, x_1913);
return x_1919;
}
}
else
{
lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; 
lean_dec(x_24);
x_1920 = lean_ctor_get(x_1905, 0);
lean_inc(x_1920);
x_1921 = lean_ctor_get(x_1905, 1);
lean_inc(x_1921);
if (lean_is_exclusive(x_1905)) {
 lean_ctor_release(x_1905, 0);
 lean_ctor_release(x_1905, 1);
 x_1922 = x_1905;
} else {
 lean_dec_ref(x_1905);
 x_1922 = lean_box(0);
}
x_1923 = lean_io_error_to_string(x_1920);
x_1924 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1924, 0, x_1923);
lean_ctor_set_uint8(x_1924, sizeof(void*)*1, x_1901);
x_1925 = lean_array_push(x_1904, x_1924);
if (lean_is_scalar(x_1899)) {
 x_1926 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1926 = x_1899;
 lean_ctor_set_tag(x_1926, 1);
}
lean_ctor_set(x_1926, 0, x_1903);
lean_ctor_set(x_1926, 1, x_1925);
if (lean_is_scalar(x_1922)) {
 x_1927 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1927 = x_1922;
 lean_ctor_set_tag(x_1927, 0);
}
lean_ctor_set(x_1927, 0, x_1926);
lean_ctor_set(x_1927, 1, x_1921);
return x_1927;
}
}
}
else
{
lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; 
lean_dec(x_1863);
lean_dec(x_24);
x_1928 = lean_ctor_get(x_1861, 1);
lean_inc(x_1928);
if (lean_is_exclusive(x_1861)) {
 lean_ctor_release(x_1861, 0);
 lean_ctor_release(x_1861, 1);
 x_1929 = x_1861;
} else {
 lean_dec_ref(x_1861);
 x_1929 = lean_box(0);
}
x_1930 = lean_ctor_get(x_1, 0);
lean_inc(x_1930);
x_1931 = l_Lake_Env_leanGithash(x_1930);
lean_dec(x_1930);
x_1932 = l_System_Platform_target;
lean_inc(x_1810);
x_1933 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1933, 0, x_1932);
lean_ctor_set(x_1933, 1, x_1931);
lean_ctor_set(x_1933, 2, x_30);
lean_ctor_set(x_1933, 3, x_1810);
x_1934 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032_(x_1933);
x_1935 = lean_unsigned_to_nat(80u);
x_1936 = l_Lean_Json_pretty(x_1934, x_1935);
x_1937 = l_IO_FS_Handle_putStrLn(x_1804, x_1936, x_1862);
if (lean_obj_tag(x_1937) == 0)
{
lean_object* x_1938; lean_object* x_1939; 
x_1938 = lean_ctor_get(x_1937, 1);
lean_inc(x_1938);
lean_dec(x_1937);
x_1939 = lean_io_prim_handle_truncate(x_1804, x_1938);
if (lean_obj_tag(x_1939) == 0)
{
lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; 
x_1940 = lean_ctor_get(x_1939, 0);
lean_inc(x_1940);
x_1941 = lean_ctor_get(x_1939, 1);
lean_inc(x_1941);
lean_dec(x_1939);
if (lean_is_scalar(x_1929)) {
 x_1942 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1942 = x_1929;
}
lean_ctor_set(x_1942, 0, x_1940);
lean_ctor_set(x_1942, 1, x_1928);
x_1811 = x_1942;
x_1812 = x_1941;
goto block_1860;
}
else
{
lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; uint8_t x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; 
x_1943 = lean_ctor_get(x_1939, 0);
lean_inc(x_1943);
x_1944 = lean_ctor_get(x_1939, 1);
lean_inc(x_1944);
lean_dec(x_1939);
x_1945 = lean_io_error_to_string(x_1943);
x_1946 = 3;
x_1947 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1947, 0, x_1945);
lean_ctor_set_uint8(x_1947, sizeof(void*)*1, x_1946);
x_1948 = lean_array_get_size(x_1928);
x_1949 = lean_array_push(x_1928, x_1947);
if (lean_is_scalar(x_1929)) {
 x_1950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1950 = x_1929;
 lean_ctor_set_tag(x_1950, 1);
}
lean_ctor_set(x_1950, 0, x_1948);
lean_ctor_set(x_1950, 1, x_1949);
x_1811 = x_1950;
x_1812 = x_1944;
goto block_1860;
}
}
else
{
lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; uint8_t x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; 
lean_dec(x_1810);
lean_dec(x_1804);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1951 = lean_ctor_get(x_1937, 0);
lean_inc(x_1951);
x_1952 = lean_ctor_get(x_1937, 1);
lean_inc(x_1952);
if (lean_is_exclusive(x_1937)) {
 lean_ctor_release(x_1937, 0);
 lean_ctor_release(x_1937, 1);
 x_1953 = x_1937;
} else {
 lean_dec_ref(x_1937);
 x_1953 = lean_box(0);
}
x_1954 = lean_io_error_to_string(x_1951);
x_1955 = 3;
x_1956 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1956, 0, x_1954);
lean_ctor_set_uint8(x_1956, sizeof(void*)*1, x_1955);
x_1957 = lean_array_get_size(x_1928);
x_1958 = lean_array_push(x_1928, x_1956);
if (lean_is_scalar(x_1929)) {
 x_1959 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1959 = x_1929;
 lean_ctor_set_tag(x_1959, 1);
}
lean_ctor_set(x_1959, 0, x_1957);
lean_ctor_set(x_1959, 1, x_1958);
if (lean_is_scalar(x_1953)) {
 x_1960 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1960 = x_1953;
 lean_ctor_set_tag(x_1960, 0);
}
lean_ctor_set(x_1960, 0, x_1959);
lean_ctor_set(x_1960, 1, x_1952);
return x_1960;
}
}
}
}
else
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; 
lean_dec(x_1805);
lean_dec(x_1804);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1971 = lean_ctor_get(x_1806, 0);
lean_inc(x_1971);
x_1972 = lean_ctor_get(x_1806, 1);
lean_inc(x_1972);
if (lean_is_exclusive(x_1806)) {
 lean_ctor_release(x_1806, 0);
 lean_ctor_release(x_1806, 1);
 x_1973 = x_1806;
} else {
 lean_dec_ref(x_1806);
 x_1973 = lean_box(0);
}
if (lean_is_scalar(x_1973)) {
 x_1974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1974 = x_1973;
}
lean_ctor_set(x_1974, 0, x_1971);
lean_ctor_set(x_1974, 1, x_1972);
x_1975 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1975, 0, x_1974);
lean_ctor_set(x_1975, 1, x_1807);
return x_1975;
}
}
}
}
}
}
else
{
uint8_t x_2081; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2081 = !lean_is_exclusive(x_28);
if (x_2081 == 0)
{
lean_object* x_2082; 
x_2082 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2082, 0, x_28);
lean_ctor_set(x_2082, 1, x_29);
return x_2082;
}
else
{
lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; 
x_2083 = lean_ctor_get(x_28, 0);
x_2084 = lean_ctor_get(x_28, 1);
lean_inc(x_2084);
lean_inc(x_2083);
lean_dec(x_28);
x_2085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2085, 0, x_2083);
lean_ctor_set(x_2085, 1, x_2084);
x_2086 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2086, 0, x_2085);
lean_ctor_set(x_2086, 1, x_29);
return x_2086;
}
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Frontend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instBEqImport__lake___closed__1 = _init_l_Lake_instBEqImport__lake___closed__1();
lean_mark_persistent(l_Lake_instBEqImport__lake___closed__1);
l_Lake_instBEqImport__lake = _init_l_Lake_instBEqImport__lake();
lean_mark_persistent(l_Lake_instBEqImport__lake);
l_Lake_instHashableImport__lake___closed__1 = _init_l_Lake_instHashableImport__lake___closed__1();
lean_mark_persistent(l_Lake_instHashableImport__lake___closed__1);
l_Lake_instHashableImport__lake = _init_l_Lake_instHashableImport__lake();
lean_mark_persistent(l_Lake_instHashableImport__lake);
res = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lake_importEnvCache = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_importEnvCache);
lean_dec_ref(res);
l_Lake_importModulesUsingCache___lambda__1___closed__1 = _init_l_Lake_importModulesUsingCache___lambda__1___closed__1();
lean_mark_persistent(l_Lake_importModulesUsingCache___lambda__1___closed__1);
l_Lake_processHeader___closed__1 = _init_l_Lake_processHeader___closed__1();
lean_mark_persistent(l_Lake_processHeader___closed__1);
l_Lake_configModuleName___closed__1 = _init_l_Lake_configModuleName___closed__1();
lean_mark_persistent(l_Lake_configModuleName___closed__1);
l_Lake_configModuleName___closed__2 = _init_l_Lake_configModuleName___closed__2();
lean_mark_persistent(l_Lake_configModuleName___closed__2);
l_Lake_configModuleName = _init_l_Lake_configModuleName();
lean_mark_persistent(l_Lake_configModuleName);
l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1 = _init_l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1);
l_Lake_elabConfigFile___closed__1 = _init_l_Lake_elabConfigFile___closed__1();
lean_mark_persistent(l_Lake_elabConfigFile___closed__1);
l_Lake_elabConfigFile___closed__2 = _init_l_Lake_elabConfigFile___closed__2();
lean_mark_persistent(l_Lake_elabConfigFile___closed__2);
l_Lake_elabConfigFile___closed__3 = _init_l_Lake_elabConfigFile___closed__3();
lean_mark_persistent(l_Lake_elabConfigFile___closed__3);
l_Lake_importConfigFileCore_lakeExts___closed__1 = _init_l_Lake_importConfigFileCore_lakeExts___closed__1();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__1);
l_Lake_importConfigFileCore_lakeExts___closed__2 = _init_l_Lake_importConfigFileCore_lakeExts___closed__2();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__2);
l_Lake_importConfigFileCore_lakeExts___closed__3 = _init_l_Lake_importConfigFileCore_lakeExts___closed__3();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__3);
l_Lake_importConfigFileCore_lakeExts___closed__4 = _init_l_Lake_importConfigFileCore_lakeExts___closed__4();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__4);
l_Lake_importConfigFileCore_lakeExts___closed__5 = _init_l_Lake_importConfigFileCore_lakeExts___closed__5();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__5);
l_Lake_importConfigFileCore_lakeExts___closed__6 = _init_l_Lake_importConfigFileCore_lakeExts___closed__6();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__6);
l_Lake_importConfigFileCore_lakeExts___closed__7 = _init_l_Lake_importConfigFileCore_lakeExts___closed__7();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__7);
l_Lake_importConfigFileCore_lakeExts___closed__8 = _init_l_Lake_importConfigFileCore_lakeExts___closed__8();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__8);
l_Lake_importConfigFileCore_lakeExts___closed__9 = _init_l_Lake_importConfigFileCore_lakeExts___closed__9();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__9);
l_Lake_importConfigFileCore_lakeExts___closed__10 = _init_l_Lake_importConfigFileCore_lakeExts___closed__10();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__10);
l_Lake_importConfigFileCore_lakeExts___closed__11 = _init_l_Lake_importConfigFileCore_lakeExts___closed__11();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__11);
l_Lake_importConfigFileCore_lakeExts___closed__12 = _init_l_Lake_importConfigFileCore_lakeExts___closed__12();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__12);
l_Lake_importConfigFileCore_lakeExts___closed__13 = _init_l_Lake_importConfigFileCore_lakeExts___closed__13();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__13);
l_Lake_importConfigFileCore_lakeExts___closed__14 = _init_l_Lake_importConfigFileCore_lakeExts___closed__14();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__14);
l_Lake_importConfigFileCore_lakeExts___closed__15 = _init_l_Lake_importConfigFileCore_lakeExts___closed__15();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__15);
l_Lake_importConfigFileCore_lakeExts___closed__16 = _init_l_Lake_importConfigFileCore_lakeExts___closed__16();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__16);
l_Lake_importConfigFileCore_lakeExts___closed__17 = _init_l_Lake_importConfigFileCore_lakeExts___closed__17();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__17);
l_Lake_importConfigFileCore_lakeExts___closed__18 = _init_l_Lake_importConfigFileCore_lakeExts___closed__18();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__18);
l_Lake_importConfigFileCore_lakeExts___closed__19 = _init_l_Lake_importConfigFileCore_lakeExts___closed__19();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__19);
l_Lake_importConfigFileCore_lakeExts___closed__20 = _init_l_Lake_importConfigFileCore_lakeExts___closed__20();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__20);
l_Lake_importConfigFileCore_lakeExts___closed__21 = _init_l_Lake_importConfigFileCore_lakeExts___closed__21();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__21);
l_Lake_importConfigFileCore_lakeExts___closed__22 = _init_l_Lake_importConfigFileCore_lakeExts___closed__22();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__22);
l_Lake_importConfigFileCore_lakeExts___closed__23 = _init_l_Lake_importConfigFileCore_lakeExts___closed__23();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__23);
l_Lake_importConfigFileCore_lakeExts___closed__24 = _init_l_Lake_importConfigFileCore_lakeExts___closed__24();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__24);
l_Lake_importConfigFileCore_lakeExts___closed__25 = _init_l_Lake_importConfigFileCore_lakeExts___closed__25();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__25);
l_Lake_importConfigFileCore_lakeExts___closed__26 = _init_l_Lake_importConfigFileCore_lakeExts___closed__26();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__26);
l_Lake_importConfigFileCore_lakeExts___closed__27 = _init_l_Lake_importConfigFileCore_lakeExts___closed__27();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__27);
l_Lake_importConfigFileCore_lakeExts___closed__28 = _init_l_Lake_importConfigFileCore_lakeExts___closed__28();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__28);
l_Lake_importConfigFileCore_lakeExts___closed__29 = _init_l_Lake_importConfigFileCore_lakeExts___closed__29();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__29);
l_Lake_importConfigFileCore_lakeExts___closed__30 = _init_l_Lake_importConfigFileCore_lakeExts___closed__30();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__30);
l_Lake_importConfigFileCore_lakeExts___closed__31 = _init_l_Lake_importConfigFileCore_lakeExts___closed__31();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__31);
l_Lake_importConfigFileCore_lakeExts___closed__32 = _init_l_Lake_importConfigFileCore_lakeExts___closed__32();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__32);
l_Lake_importConfigFileCore_lakeExts___closed__33 = _init_l_Lake_importConfigFileCore_lakeExts___closed__33();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__33);
l_Lake_importConfigFileCore_lakeExts___closed__34 = _init_l_Lake_importConfigFileCore_lakeExts___closed__34();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__34);
l_Lake_importConfigFileCore_lakeExts___closed__35 = _init_l_Lake_importConfigFileCore_lakeExts___closed__35();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__35);
l_Lake_importConfigFileCore_lakeExts___closed__36 = _init_l_Lake_importConfigFileCore_lakeExts___closed__36();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__36);
l_Lake_importConfigFileCore_lakeExts___closed__37 = _init_l_Lake_importConfigFileCore_lakeExts___closed__37();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__37);
l_Lake_importConfigFileCore_lakeExts___closed__38 = _init_l_Lake_importConfigFileCore_lakeExts___closed__38();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__38);
l_Lake_importConfigFileCore_lakeExts___closed__39 = _init_l_Lake_importConfigFileCore_lakeExts___closed__39();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__39);
l_Lake_importConfigFileCore_lakeExts___closed__40 = _init_l_Lake_importConfigFileCore_lakeExts___closed__40();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__40);
l_Lake_importConfigFileCore_lakeExts___closed__41 = _init_l_Lake_importConfigFileCore_lakeExts___closed__41();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__41);
l_Lake_importConfigFileCore_lakeExts___closed__42 = _init_l_Lake_importConfigFileCore_lakeExts___closed__42();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__42);
l_Lake_importConfigFileCore_lakeExts___closed__43 = _init_l_Lake_importConfigFileCore_lakeExts___closed__43();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__43);
l_Lake_importConfigFileCore_lakeExts___closed__44 = _init_l_Lake_importConfigFileCore_lakeExts___closed__44();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__44);
l_Lake_importConfigFileCore_lakeExts___closed__45 = _init_l_Lake_importConfigFileCore_lakeExts___closed__45();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__45);
l_Lake_importConfigFileCore_lakeExts___closed__46 = _init_l_Lake_importConfigFileCore_lakeExts___closed__46();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__46);
l_Lake_importConfigFileCore_lakeExts___closed__47 = _init_l_Lake_importConfigFileCore_lakeExts___closed__47();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__47);
l_Lake_importConfigFileCore_lakeExts___closed__48 = _init_l_Lake_importConfigFileCore_lakeExts___closed__48();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__48);
l_Lake_importConfigFileCore_lakeExts___closed__49 = _init_l_Lake_importConfigFileCore_lakeExts___closed__49();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__49);
l_Lake_importConfigFileCore_lakeExts___closed__50 = _init_l_Lake_importConfigFileCore_lakeExts___closed__50();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__50);
l_Lake_importConfigFileCore_lakeExts___closed__51 = _init_l_Lake_importConfigFileCore_lakeExts___closed__51();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__51);
l_Lake_importConfigFileCore_lakeExts___closed__52 = _init_l_Lake_importConfigFileCore_lakeExts___closed__52();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__52);
l_Lake_importConfigFileCore_lakeExts___closed__53 = _init_l_Lake_importConfigFileCore_lakeExts___closed__53();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__53);
l_Lake_importConfigFileCore_lakeExts___closed__54 = _init_l_Lake_importConfigFileCore_lakeExts___closed__54();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts___closed__54);
l_Lake_importConfigFileCore_lakeExts = _init_l_Lake_importConfigFileCore_lakeExts();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts);
l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1);
l_Lake_importConfigFileCore___closed__1 = _init_l_Lake_importConfigFileCore___closed__1();
lean_mark_persistent(l_Lake_importConfigFileCore___closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__2);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__4 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__4();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__4);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1032____closed__5);
l_Lake_instToJsonConfigTrace___closed__1 = _init_l_Lake_instToJsonConfigTrace___closed__1();
lean_mark_persistent(l_Lake_instToJsonConfigTrace___closed__1);
l_Lake_instToJsonConfigTrace = _init_l_Lake_instToJsonConfigTrace();
lean_mark_persistent(l_Lake_instToJsonConfigTrace);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__2);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__3 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__3();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____spec__1___closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__1 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__1();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__2 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__2();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__2);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__3 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__3();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__4 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__4();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__4);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__5);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__6 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__6();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__6);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__7 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__7();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__7);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__8 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__8();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__8);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__9);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__10);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__11 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__11();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__11);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__12 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__12();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__12);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__13 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__13();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__13);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__14);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__15 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__15();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__15);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__16 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__16();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__16);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__17 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__17();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__17);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__18);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__19 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__19();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__19);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__20 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__20();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__20);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__21 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__21();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__21);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1108____closed__22);
l_Lake_instFromJsonConfigTrace___closed__1 = _init_l_Lake_instFromJsonConfigTrace___closed__1();
lean_mark_persistent(l_Lake_instFromJsonConfigTrace___closed__1);
l_Lake_instFromJsonConfigTrace = _init_l_Lake_instFromJsonConfigTrace();
lean_mark_persistent(l_Lake_instFromJsonConfigTrace);
l_Lake_importConfigFile___closed__1 = _init_l_Lake_importConfigFile___closed__1();
lean_mark_persistent(l_Lake_importConfigFile___closed__1);
l_Lake_importConfigFile___closed__2 = _init_l_Lake_importConfigFile___closed__2();
lean_mark_persistent(l_Lake_importConfigFile___closed__2);
l_Lake_importConfigFile___closed__3 = _init_l_Lake_importConfigFile___closed__3();
lean_mark_persistent(l_Lake_importConfigFile___closed__3);
l_Lake_importConfigFile___closed__4 = _init_l_Lake_importConfigFile___closed__4();
lean_mark_persistent(l_Lake_importConfigFile___closed__4);
l_Lake_importConfigFile___closed__5 = _init_l_Lake_importConfigFile___closed__5();
lean_mark_persistent(l_Lake_importConfigFile___closed__5);
l_Lake_importConfigFile___closed__6 = _init_l_Lake_importConfigFile___closed__6();
lean_mark_persistent(l_Lake_importConfigFile___closed__6);
l_Lake_importConfigFile___closed__7 = _init_l_Lake_importConfigFile___closed__7();
lean_mark_persistent(l_Lake_importConfigFile___closed__7);
l_Lake_importConfigFile___closed__8 = _init_l_Lake_importConfigFile___closed__8();
lean_mark_persistent(l_Lake_importConfigFile___closed__8);
l_Lake_importConfigFile___closed__9 = _init_l_Lake_importConfigFile___closed__9();
lean_mark_persistent(l_Lake_importConfigFile___closed__9);
l_Lake_importConfigFile___closed__10 = _init_l_Lake_importConfigFile___closed__10();
lean_mark_persistent(l_Lake_importConfigFile___closed__10);
l_Lake_importConfigFile___closed__11 = _init_l_Lake_importConfigFile___closed__11();
lean_mark_persistent(l_Lake_importConfigFile___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
